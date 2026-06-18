//! A dock panel for managing SSH remote-development port forwards at runtime.
//!
//! Zed historically only applied port forwards once, at connection time, from
//! `ssh_connections[].port_forwards` in settings. This panel adds runtime
//! management: forwards can be added and removed on a live connection without
//! reconnecting, and (in later phases) remote listening ports are auto-detected.
//!
//! Each forward is backed by a dedicated `ssh -N -L ...` child process that
//! multiplexes over the existing SSH control master (see
//! [`remote::RemoteClient::build_forward_ports_command`]). Killing the child
//! tears down exactly that forward, which is why the child handle lives inside
//! [`ActiveForward`] and is dropped on removal.

use anyhow::{Context as _, Result};
use client::proto;
use editor::Editor;
use futures::{AsyncBufReadExt as _, StreamExt as _, io::BufReader};
use gpui::{
    AnyElement, App, AsyncWindowContext, ClipboardItem, Entity, EventEmitter, FocusHandle,
    Focusable, ScrollHandle, Subscription, Task, WeakEntity, Window, actions,
};
use project::Project;
use recent_projects::RemoteSettings;
use remote::{
    ConnectionState, RemoteClient, RemoteClientEvent, RemoteConnectionOptions, SshPortForwardOption,
};
use settings::{RegisterSetting, Settings as _, SettingsContent, SettingsStore};
use std::collections::HashSet;
use std::time::Duration;
use ui::{ListItem, Tooltip, WithScrollbar, prelude::*};
use util::ResultExt as _;
use util::command::{Child, Stdio, new_command};
use workspace::{
    Workspace,
    dock::{DockPosition, Panel, PanelEvent},
};

/// How often the panel polls the remote host for listening ports.
const PORT_POLL_INTERVAL: Duration = Duration::from_secs(3);

/// Settings for the ports panel.
#[derive(RegisterSetting)]
pub struct PortsPanelSettings {
    pub auto_forward: bool,
}

impl settings::Settings for PortsPanelSettings {
    fn from_settings(content: &SettingsContent) -> Self {
        let ports_panel = content.ports_panel.clone().unwrap_or_default();
        Self {
            auto_forward: ports_panel.auto_forward.unwrap_or(false),
        }
    }
}

const PORTS_PANEL_KEY: &str = "PortsPanel";

actions!(
    ports_panel,
    [
        /// Toggles focus on the ports panel.
        ToggleFocus,
    ]
);

pub fn init(cx: &mut App) {
    cx.observe_new(|workspace: &mut Workspace, _window, _: &mut Context<Workspace>| {
        workspace.register_action(|workspace, _: &ToggleFocus, window, cx| {
            workspace.toggle_panel_focus::<PortsPanel>(window, cx);
        });
    })
    .detach();
}

/// Local identifier for a forward managed by this panel.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ForwardId(u64);

/// Where a forward originated from. Used to keep panel-managed forwards separate
/// from settings-managed ones so a settings edit doesn't clobber manual entries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForwardSource {
    Manual,
    Settings,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForwardState {
    /// Spawned but not yet known to be listening, or awaiting (re)connection.
    Pending,
    /// The forwarding process is running.
    Active,
    /// The forward failed to establish (e.g. local port already in use).
    Failed(String),
}

/// Identifies a forward by its endpoints, for diffing against settings.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ForwardKey {
    local_host: String,
    local_port: u16,
    remote_host: String,
    remote_port: u16,
}

impl ForwardKey {
    fn from_option(option: &SshPortForwardOption) -> Self {
        // Matches the `-L` defaults applied in `remote::transport::ssh`.
        Self {
            local_host: option
                .local_host
                .clone()
                .unwrap_or_else(|| "localhost".to_string()),
            local_port: option.local_port,
            remote_host: option
                .remote_host
                .clone()
                .unwrap_or_else(|| "localhost".to_string()),
            remote_port: option.remote_port,
        }
    }
}

/// A single runtime port forward and the child process backing it.
struct ActiveForward {
    id: ForwardId,
    local_host: String,
    local_port: u16,
    remote_host: String,
    remote_port: u16,
    source: ForwardSource,
    /// When `true` we own a `ssh -N -L` child for this forward. When `false`
    /// the SSH control master itself owns it (a connect-time static forward),
    /// so we only display it and never spawn or kill a child.
    managed: bool,
    state: ForwardState,
    /// Dropping this kills the `ssh -N -L` tunnel (`kill_on_drop`).
    child: Option<Child>,
}

impl ActiveForward {
    fn key(&self) -> ForwardKey {
        ForwardKey {
            local_host: self.local_host.clone(),
            local_port: self.local_port,
            remote_host: self.remote_host.clone(),
            remote_port: self.remote_port,
        }
    }
}

/// A cloneable snapshot of a forward used for rendering. [`ActiveForward`] holds
/// a non-`Clone` child handle, so the view renders from these instead.
#[derive(Clone)]
struct ForwardDisplay {
    id: ForwardId,
    local_host: String,
    local_port: u16,
    remote_host: String,
    remote_port: u16,
    source: ForwardSource,
    managed: bool,
    state: ForwardState,
}

/// Owns the set of runtime forwards for a single remote connection and keeps
/// them in sync with the connection's lifecycle.
pub struct ForwardManager {
    remote_client: WeakEntity<RemoteClient>,
    forwards: Vec<ActiveForward>,
    next_id: u64,
    connection_state: ConnectionState,
    /// Remote listening ports last reported by the remote server.
    detected: Vec<proto::ListeningPort>,
    /// Remote ports we've already auto-forwarded, so we don't keep retrying.
    auto_forwarded: HashSet<u16>,
    poll_task: Option<Task<()>>,
    _subscriptions: Vec<Subscription>,
}

/// A cloneable snapshot of a detected-but-not-yet-forwarded remote port.
#[derive(Clone)]
struct DetectedRow {
    port: u16,
    address: String,
    process_name: Option<String>,
}

impl ForwardManager {
    pub fn new(remote_client: Entity<RemoteClient>, cx: &mut Context<Self>) -> Self {
        let connection_state = remote_client.read(cx).connection_state();
        let subscriptions = vec![
            cx.observe(&remote_client, |this, client, cx| {
                let new_state = client.read(cx).connection_state();
                this.on_connection_state(new_state, cx);
            }),
            cx.subscribe(&remote_client, |this, _client, event, cx| match event {
                RemoteClientEvent::Disconnected { .. } => {
                    this.on_connection_state(ConnectionState::Disconnected, cx)
                }
            }),
            cx.observe_global::<SettingsStore>(|this, cx| this.reconcile_with_settings(cx)),
        ];

        let mut this = Self {
            remote_client: remote_client.downgrade(),
            forwards: Vec::new(),
            next_id: 1,
            connection_state,
            detected: Vec::new(),
            auto_forwarded: HashSet::new(),
            poll_task: None,
            _subscriptions: subscriptions,
        };
        this.seed_master_owned(cx);
        this.reconcile_with_settings(cx);
        this
    }

    /// Starts or stops polling the remote host for listening ports. The panel
    /// drives this from its active state so we don't poll while hidden.
    pub fn set_polling(&mut self, enabled: bool, cx: &mut Context<Self>) {
        if enabled {
            if self.poll_task.is_none() {
                self.poll_task = Some(self.start_polling(cx));
            }
        } else {
            self.poll_task = None;
            if !self.detected.is_empty() {
                self.detected.clear();
                cx.notify();
            }
        }
    }

    fn start_polling(&self, cx: &mut Context<Self>) -> Task<()> {
        cx.spawn(async move |this, cx| {
            loop {
                let proto_client = this
                    .update(cx, |this, cx| {
                        let remote_client = this.remote_client.upgrade()?;
                        if remote_client.read(cx).connection_state() != ConnectionState::Connected {
                            return None;
                        }
                        Some(remote_client.read(cx).proto_client())
                    })
                    .ok()
                    .flatten();

                if let Some(proto_client) = proto_client {
                    let response = proto_client
                        .request(proto::GetListeningPorts {
                            project_id: proto::REMOTE_SERVER_PROJECT_ID,
                        })
                        .await;
                    match response {
                        Ok(response) => {
                            this.update(cx, |this, cx| this.on_detected(response.ports, cx))
                                .ok();
                        }
                        Err(error) => {
                            log::debug!("failed to query remote listening ports: {error:#}");
                        }
                    }
                }

                cx.background_executor().timer(PORT_POLL_INTERVAL).await;
            }
        })
    }

    fn on_detected(&mut self, ports: Vec<proto::ListeningPort>, cx: &mut Context<Self>) {
        self.detected = ports;

        if PortsPanelSettings::get_global(cx).auto_forward {
            let forwarded: HashSet<u16> = self
                .forwards
                .iter()
                .map(|forward| forward.remote_port)
                .collect();
            let to_forward: Vec<u16> = self
                .detected
                .iter()
                .map(|port| port.port as u16)
                .filter(|port| !forwarded.contains(port) && !self.auto_forwarded.contains(port))
                .collect();
            for port in to_forward {
                self.auto_forwarded.insert(port);
                self.forward_detected(port, cx);
            }
        }

        cx.notify();
    }

    /// Forwards `remote_host:remote_port` to the local machine. Prefers binding
    /// the same local port, but falls back to an automatically-allocated one if
    /// it's already in use.
    pub fn forward_to(&mut self, remote_host: String, remote_port: u16, cx: &mut Context<Self>) {
        let local_port = if std::net::TcpListener::bind(("127.0.0.1", remote_port)).is_ok() {
            remote_port
        } else {
            0
        };
        self.add_forward(
            local_port,
            "127.0.0.1".to_string(),
            remote_host,
            remote_port,
            ForwardSource::Manual,
            cx,
        )
        .log_err();
    }

    /// Forwards a detected remote port (always on the remote's `localhost`).
    pub fn forward_detected(&mut self, remote_port: u16, cx: &mut Context<Self>) {
        self.forward_to("localhost".to_string(), remote_port, cx);
    }

    fn detected_rows(&self) -> Vec<DetectedRow> {
        let forwarded: HashSet<u16> = self
            .forwards
            .iter()
            .map(|forward| forward.remote_port)
            .collect();
        let mut rows: Vec<DetectedRow> = self
            .detected
            .iter()
            .filter(|port| !forwarded.contains(&(port.port as u16)))
            .map(|port| DetectedRow {
                port: port.port as u16,
                address: port.address.clone(),
                process_name: port.process_name.clone(),
            })
            .collect();
        // Surface named services first (easier to recognize), then sort by port.
        rows.sort_by(|a, b| {
            a.process_name
                .is_none()
                .cmp(&b.process_name.is_none())
                .then(a.port.cmp(&b.port))
        });
        rows
    }

    /// Records the connect-time static forwards (applied as `-L` on the SSH
    /// master) as display-only rows so we don't spawn duplicate children for
    /// them and so the user can see/copy them.
    fn seed_master_owned(&mut self, cx: &Context<Self>) {
        let Some(remote_client) = self.remote_client.upgrade() else {
            return;
        };
        let RemoteConnectionOptions::Ssh(options) = remote_client.read(cx).connection_options()
        else {
            return;
        };
        let connected = self.connection_state == ConnectionState::Connected;
        for option in options.port_forwards.unwrap_or_default() {
            let key = ForwardKey::from_option(&option);
            let id = ForwardId(self.next_id);
            self.next_id += 1;
            self.forwards.push(ActiveForward {
                id,
                local_host: key.local_host,
                local_port: key.local_port,
                remote_host: key.remote_host,
                remote_port: key.remote_port,
                source: ForwardSource::Settings,
                managed: false,
                state: if connected {
                    ForwardState::Active
                } else {
                    ForwardState::Pending
                },
                child: None,
            });
        }
    }

    pub fn forwards_len(&self) -> usize {
        self.forwards.len()
    }

    fn display_rows(&self) -> Vec<ForwardDisplay> {
        self.forwards
            .iter()
            .map(|forward| ForwardDisplay {
                id: forward.id,
                local_host: forward.local_host.clone(),
                local_port: forward.local_port,
                remote_host: forward.remote_host.clone(),
                remote_port: forward.remote_port,
                source: forward.source,
                managed: forward.managed,
                state: forward.state.clone(),
            })
            .collect()
    }

    /// Starts a new forward. `local_port` of 0 means "allocate a free local port".
    /// Returns the assigned id; the forward is established asynchronously and may
    /// later transition to [`ForwardState::Failed`] if the tunnel can't bind.
    pub fn add_forward(
        &mut self,
        local_port: u16,
        local_host: String,
        remote_host: String,
        remote_port: u16,
        source: ForwardSource,
        cx: &mut Context<Self>,
    ) -> Result<ForwardId> {
        let local_port = if local_port == 0 {
            allocate_local_port()?
        } else {
            local_port
        };
        let id = ForwardId(self.next_id);
        self.next_id += 1;

        let child = self.spawn_child(local_port, &remote_host, remote_port, cx)?;
        self.forwards.push(ActiveForward {
            id,
            local_host,
            local_port,
            remote_host,
            remote_port,
            source,
            managed: true,
            state: ForwardState::Pending,
            child: None,
        });
        self.attach_child(id, child, cx);
        cx.notify();
        Ok(id)
    }

    pub fn remove_forward(&mut self, id: ForwardId, cx: &mut Context<Self>) {
        // Dropping the child via `retain` kills the tunnel.
        self.forwards.retain(|forward| forward.id != id);
        cx.notify();
    }

    fn spawn_child(
        &self,
        local_port: u16,
        remote_host: &str,
        remote_port: u16,
        cx: &App,
    ) -> Result<Child> {
        let remote_client = self
            .remote_client
            .upgrade()
            .context("remote connection is no longer available")?;
        let template = remote_client.read(cx).build_forward_ports_command(vec![(
            local_port,
            remote_host.to_string(),
            remote_port,
        )])?;

        let mut command = new_command(&template.program);
        command.args(&template.args);
        command.envs(&template.env);
        command.stdin(Stdio::null());
        command.stdout(Stdio::piped());
        command.stderr(Stdio::piped());
        command.kill_on_drop(true);
        command
            .spawn()
            .context("failed to spawn ssh port forward process")
    }

    /// Stores a freshly spawned child against `id`, marks it active, and starts a
    /// reader that flips the forward to [`ForwardState::Failed`] on a bind error.
    fn attach_child(&mut self, id: ForwardId, mut child: Child, cx: &mut Context<Self>) {
        let stderr = child.stderr.take();
        if let Some(forward) = self.forwards.iter_mut().find(|forward| forward.id == id) {
            forward.child = Some(child);
            forward.state = ForwardState::Active;
        }

        let Some(stderr) = stderr else {
            return;
        };
        cx.spawn(async move |this, cx| {
            let mut lines = BufReader::new(stderr).lines();
            while let Some(Ok(line)) = lines.next().await {
                log::warn!("ssh port forward stderr: {line}");
                if is_bind_failure(&line) {
                    this.update(cx, |this, cx| this.mark_failed(id, line.clone(), cx))
                        .ok();
                }
            }
        })
        .detach();
    }

    fn mark_failed(&mut self, id: ForwardId, message: String, cx: &mut Context<Self>) {
        if let Some(forward) = self.forwards.iter_mut().find(|forward| forward.id == id) {
            forward.child = None;
            forward.state = ForwardState::Failed(message);
        }
        cx.notify();
    }

    fn on_connection_state(&mut self, new_state: ConnectionState, cx: &mut Context<Self>) {
        let old_state = self.connection_state;
        if old_state == new_state {
            return;
        }
        self.connection_state = new_state;

        match new_state {
            // On (re)connection the control master is rebuilt, which kills our
            // tunnel children, so re-establish anything that lost its child.
            ConnectionState::Connected => {
                if old_state != ConnectionState::Connected {
                    self.respawn_dead(cx);
                }
            }
            ConnectionState::Connecting
            | ConnectionState::Reconnecting
            | ConnectionState::HeartbeatMissed
            | ConnectionState::Disconnected => {
                if old_state == ConnectionState::Connected {
                    self.teardown_children(cx);
                }
            }
        }
        cx.notify();
    }

    fn teardown_children(&mut self, cx: &mut Context<Self>) {
        for forward in self.forwards.iter_mut() {
            forward.child = None;
            forward.state = ForwardState::Pending;
        }
        cx.notify();
    }

    fn respawn_dead(&mut self, cx: &mut Context<Self>) {
        // Master-owned (static) forwards are re-applied by the control master on
        // reconnect, so we only mark them active; we re-spawn our own children.
        let to_spawn: Vec<(ForwardId, u16, String, u16)> = self
            .forwards
            .iter()
            .filter(|forward| forward.managed && forward.child.is_none())
            .map(|forward| {
                (
                    forward.id,
                    forward.local_port,
                    forward.remote_host.clone(),
                    forward.remote_port,
                )
            })
            .collect();

        for forward in self.forwards.iter_mut() {
            if !forward.managed {
                forward.state = ForwardState::Active;
            }
        }

        for (id, local_port, remote_host, remote_port) in to_spawn {
            match self.spawn_child(local_port, &remote_host, remote_port, cx) {
                Ok(child) => self.attach_child(id, child, cx),
                Err(error) => self.mark_failed(id, error.to_string(), cx),
            }
        }
    }

    /// Brings the live set of forwards in line with the current settings:
    /// spawns children for newly-added settings forwards and removes the
    /// children of settings forwards that were deleted. Manual (panel-added)
    /// and master-owned forwards are left untouched.
    fn reconcile_with_settings(&mut self, cx: &mut Context<Self>) {
        let Some(remote_client) = self.remote_client.upgrade() else {
            return;
        };
        let RemoteConnectionOptions::Ssh(options) = remote_client.read(cx).connection_options()
        else {
            return;
        };

        let desired: Vec<SshPortForwardOption> = RemoteSettings::get_global(cx)
            .connection_options_for(options.host.to_string(), options.port, options.username)
            .port_forwards
            .unwrap_or_default();
        let desired_keys: HashSet<ForwardKey> =
            desired.iter().map(ForwardKey::from_option).collect();

        let existing_keys: HashSet<ForwardKey> = self
            .forwards
            .iter()
            .filter(|forward| forward.source == ForwardSource::Settings)
            .map(ActiveForward::key)
            .collect();
        let managed_keys: HashSet<ForwardKey> = self
            .forwards
            .iter()
            .filter(|forward| forward.source == ForwardSource::Settings && forward.managed)
            .map(ActiveForward::key)
            .collect();

        let (to_add, to_remove) =
            compute_forward_diff(&desired_keys, &existing_keys, &managed_keys);

        let before = self.forwards.len();
        self.forwards.retain(|forward| {
            !(forward.source == ForwardSource::Settings
                && forward.managed
                && to_remove.contains(&forward.key()))
        });
        let mut changed = self.forwards.len() != before;

        for key in to_add {
            match self.spawn_child(key.local_port, &key.remote_host, key.remote_port, cx) {
                Ok(child) => {
                    let id = ForwardId(self.next_id);
                    self.next_id += 1;
                    self.forwards.push(ActiveForward {
                        id,
                        local_host: key.local_host.clone(),
                        local_port: key.local_port,
                        remote_host: key.remote_host.clone(),
                        remote_port: key.remote_port,
                        source: ForwardSource::Settings,
                        managed: true,
                        state: ForwardState::Pending,
                        child: None,
                    });
                    self.attach_child(id, child, cx);
                    changed = true;
                }
                Err(error) => {
                    log::error!("failed to start settings-configured port forward: {error:#}");
                }
            }
        }

        if changed {
            cx.notify();
        }
    }
}

/// Pure diff for settings reconciliation. `existing` is the set of all
/// settings-sourced forward keys (master-owned and managed); `managed` is the
/// subset we own a child for. Returns the forwards to spawn and the keys whose
/// managed children to tear down.
fn compute_forward_diff(
    desired: &HashSet<ForwardKey>,
    existing: &HashSet<ForwardKey>,
    managed: &HashSet<ForwardKey>,
) -> (Vec<ForwardKey>, HashSet<ForwardKey>) {
    let to_add = desired.difference(existing).cloned().collect();
    let to_remove = managed
        .iter()
        .filter(|key| !desired.contains(key))
        .cloned()
        .collect();
    (to_add, to_remove)
}

fn allocate_local_port() -> Result<u16> {
    let listener = std::net::TcpListener::bind("127.0.0.1:0")
        .context("failed to allocate a free local port")?;
    let port = listener.local_addr()?.port();
    // Closing the listener frees the port for ssh to bind. There is an inherent
    // race here; if ssh loses it, the forward surfaces a bind error in stderr.
    drop(listener);
    Ok(port)
}

fn is_bind_failure(line: &str) -> bool {
    let line = line.to_ascii_lowercase();
    line.contains("address already in use")
        || line.contains("cannot listen to port")
        || line.contains("bind:")
        || line.contains("permission denied")
}

fn parse_port(text: &str) -> Option<u16> {
    let text = text.trim();
    if text.is_empty() {
        return None;
    }
    text.parse::<u16>().ok()
}

/// Parses the quick-add field into `(remote_host, remote_port)`. Accepts a bare
/// port (`"3000"` → `localhost`) or `"host:port"`. Splits on the last colon and
/// strips brackets so IPv6 literals like `[::1]:3000` work.
fn parse_quick_add(text: &str) -> Option<(String, u16)> {
    let text = text.trim();
    if text.is_empty() {
        return None;
    }
    match text.rsplit_once(':') {
        None => parse_port(text).map(|port| ("localhost".to_string(), port)),
        Some((host, port)) => {
            let port = parse_port(port)?;
            let host = host.trim().trim_start_matches('[').trim_end_matches(']');
            let host = if host.is_empty() {
                "localhost".to_string()
            } else {
                host.to_string()
            };
            Some((host, port))
        }
    }
}

pub struct PortsPanel {
    project: Entity<Project>,
    manager: Option<Entity<ForwardManager>>,
    focus_handle: FocusHandle,
    quick_add_editor: Entity<Editor>,
    scroll_handle: ScrollHandle,
    position: DockPosition,
    _subscriptions: Vec<Subscription>,
}

impl PortsPanel {
    pub async fn load(
        workspace: WeakEntity<Workspace>,
        mut cx: AsyncWindowContext,
    ) -> Result<Entity<Self>> {
        workspace.update_in(&mut cx, |workspace, window, cx| {
            PortsPanel::new(workspace, window, cx)
        })
    }

    pub fn new(
        workspace: &Workspace,
        window: &mut Window,
        cx: &mut Context<Workspace>,
    ) -> Entity<Self> {
        let project = workspace.project().clone();
        cx.new(|cx| {
            let focus_handle = cx.focus_handle();

            // The project may not have its remote connection attached yet when
            // the panel is first created, so re-check whenever the project changes.
            let subscriptions =
                vec![cx.observe(&project, |this: &mut Self, _, cx| this.ensure_manager(cx))];

            let quick_add_editor = cx.new(|cx| {
                let mut editor = Editor::single_line(window, cx);
                editor.set_placeholder_text("Forward a port (e.g. 3000 or host:3000)", window, cx);
                editor
            });

            let mut this = Self {
                project,
                manager: None,
                focus_handle,
                quick_add_editor,
                scroll_handle: ScrollHandle::new(),
                position: DockPosition::Bottom,
                _subscriptions: subscriptions,
            };
            this.ensure_manager(cx);
            log::info!(
                "ports_panel: panel created (has_remote_client={}, manager_active={})",
                this.project.read(cx).remote_client().is_some(),
                this.manager.is_some(),
            );
            this
        })
    }

    /// Creates the forward manager once the project has an SSH remote connection.
    /// Local projects have no remote client, and WSL/Docker remotes that share
    /// the host network interface don't need forwarding.
    fn ensure_manager(&mut self, cx: &mut Context<Self>) {
        if self.manager.is_some() {
            return;
        }
        let Some(remote_client) = self.project.read(cx).remote_client() else {
            return;
        };
        if remote_client.read(cx).shares_network_interface() {
            return;
        }
        log::info!("ports_panel: creating forward manager for remote project");
        let manager = cx.new(|cx| ForwardManager::new(remote_client, cx));
        self._subscriptions
            .push(cx.observe(&manager, |_, _, cx| cx.notify()));
        self.manager = Some(manager);
        cx.notify();
    }

    /// Forwards the port typed into the quick-add field. Accepts a bare port
    /// (`3000`, assuming `localhost`) or `host:port`, and binds the same local
    /// port (falling back to an auto-allocated one if it's taken).
    fn confirm_quick_add(&mut self, _: &menu::Confirm, window: &mut Window, cx: &mut Context<Self>) {
        let Some(manager) = self.manager.clone() else {
            return;
        };
        let Some((remote_host, remote_port)) =
            parse_quick_add(&self.quick_add_editor.read(cx).text(cx))
        else {
            return;
        };

        manager.update(cx, |manager, cx| {
            manager.forward_to(remote_host, remote_port, cx);
        });

        self.quick_add_editor
            .update(cx, |editor, cx| editor.set_text("", window, cx));
        cx.notify();
    }

    fn render_quick_add(&self, cx: &mut Context<Self>) -> impl IntoElement {
        h_flex()
            .gap_1p5()
            .p_2()
            .border_b_1()
            .border_color(cx.theme().colors().border)
            .child(
                Icon::new(IconName::Plus)
                    .size(IconSize::Small)
                    .color(Color::Muted),
            )
            .child(
                div()
                    .flex_1()
                    .px_1p5()
                    .py_0p5()
                    .border_1()
                    .border_color(cx.theme().colors().border)
                    .rounded_md()
                    .child(self.quick_add_editor.clone()),
            )
            .child(
                IconButton::new("quick-add-forward", IconName::Return)
                    .icon_size(IconSize::Small)
                    .tooltip(Tooltip::text("Forward port"))
                    .on_click(cx.listener(|this, _, window, cx| {
                        this.confirm_quick_add(&menu::Confirm, window, cx)
                    })),
            )
    }

    fn render_forward_row(&self, row: ForwardDisplay, cx: &mut Context<Self>) -> impl IntoElement {
        let id = row.id;
        let local_url = format!("http://127.0.0.1:{}", row.local_port);
        let (status_icon, status_color) = match &row.state {
            ForwardState::Active => (IconName::Check, Color::Success),
            ForwardState::Pending => (IconName::ArrowCircle, Color::Muted),
            ForwardState::Failed(_) => (IconName::XCircle, Color::Error),
        };
        let label = format!(
            "{}:{} → {}:{}",
            row.local_host, row.local_port, row.remote_host, row.remote_port
        );
        let failure = match &row.state {
            ForwardState::Failed(message) => Some(message.clone()),
            _ => None,
        };

        ListItem::new(("port-forward", id.0))
            .start_slot(
                Icon::new(status_icon)
                    .color(status_color)
                    .size(IconSize::Small),
            )
            .child(
                v_flex()
                    .child(Label::new(label))
                    .when(row.source == ForwardSource::Settings, |this| {
                        this.child(
                            Label::new("via settings")
                                .size(LabelSize::Small)
                                .color(Color::Muted),
                        )
                    })
                    .when_some(failure, |this, message| {
                        this.child(
                            Label::new(message)
                                .size(LabelSize::Small)
                                .color(Color::Error),
                        )
                    }),
            )
            .end_slot(
                h_flex()
                    .gap_1()
                    .child(
                        IconButton::new(("open", id.0), IconName::ArrowUpRight)
                            .icon_size(IconSize::Small)
                            .tooltip(Tooltip::text("Open in browser"))
                            .on_click({
                                let url = local_url.clone();
                                move |_, _, cx| cx.open_url(&url)
                            }),
                    )
                    .child(
                        IconButton::new(("copy", id.0), IconName::Copy)
                            .icon_size(IconSize::Small)
                            .tooltip(Tooltip::text("Copy local URL"))
                            .on_click({
                                let url = local_url;
                                move |_, _, cx| {
                                    cx.write_to_clipboard(ClipboardItem::new_string(url.clone()))
                                }
                            }),
                    )
                    .when(row.managed, |this| {
                        this.child(
                            IconButton::new(("remove", id.0), IconName::Trash)
                                .icon_size(IconSize::Small)
                                .tooltip(Tooltip::text("Remove forward"))
                                .on_click(cx.listener(move |this, _, _, cx| {
                                    if let Some(manager) = this.manager.clone() {
                                        manager.update(cx, |manager, cx| {
                                            manager.remove_forward(id, cx)
                                        });
                                    }
                                })),
                        )
                    }),
            )
    }

    fn render_detected_row(&self, row: DetectedRow, cx: &mut Context<Self>) -> impl IntoElement {
        let port = row.port;
        let address = format!("{}:{}", row.address, port);
        let primary = match row.process_name.as_deref() {
            Some(name) if !name.is_empty() => name.to_string(),
            _ => address.clone(),
        };
        let secondary = (primary != address).then_some(address);

        ListItem::new(("detected", port as u64))
            .start_slot(
                Icon::new(IconName::Server)
                    .color(Color::Muted)
                    .size(IconSize::Small),
            )
            .child(
                v_flex()
                    .child(Label::new(primary))
                    .when_some(secondary, |this, address| {
                        this.child(
                            Label::new(address)
                                .size(LabelSize::Small)
                                .color(Color::Muted),
                        )
                    }),
            )
            .end_slot(
                IconButton::new(("forward", port as u64), IconName::Plus)
                    .icon_size(IconSize::Small)
                    .tooltip(Tooltip::text("Forward this port"))
                    .on_click(cx.listener(move |this, _, _, cx| {
                        if let Some(manager) = this.manager.clone() {
                            manager.update(cx, |manager, cx| manager.forward_detected(port, cx));
                        }
                    })),
            )
    }

    fn render_section_header(&self, title: &'static str) -> impl IntoElement {
        div().px_2().pt_2().child(
            Label::new(title)
                .size(LabelSize::Small)
                .color(Color::Muted),
        )
    }

    fn render_empty_state(&self, message: &'static str) -> AnyElement {
        v_flex()
            .size_full()
            .items_center()
            .justify_center()
            .gap_2()
            .p_4()
            .child(
                Icon::new(IconName::Server)
                    .size(IconSize::Medium)
                    .color(Color::Muted),
            )
            .child(Label::new(message).color(Color::Muted))
            .into_any_element()
    }

    fn render_body(&mut self, window: &mut Window, cx: &mut Context<Self>) -> AnyElement {
        let Some(manager) = self.manager.clone() else {
            return self
                .render_empty_state("Port forwarding is available for SSH remote projects.");
        };

        let forwards = manager.read(cx).display_rows();
        let detected = manager.read(cx).detected_rows();

        if forwards.is_empty() && detected.is_empty() {
            return self.render_empty_state("No forwarded or detected ports yet.");
        }

        let mut container = v_flex()
            .id("ports-body")
            .size_full()
            .gap_1()
            .p_1()
            .overflow_y_scroll()
            .track_scroll(&self.scroll_handle);

        if !forwards.is_empty() {
            container = container.child(self.render_section_header("Forwarded ports"));
            for row in forwards {
                container = container.child(self.render_forward_row(row, cx).into_any_element());
            }
        }

        if !detected.is_empty() {
            container = container.child(self.render_section_header("Detected ports"));
            for row in detected {
                container = container.child(self.render_detected_row(row, cx).into_any_element());
            }
        }

        container
            .vertical_scrollbar_for(&self.scroll_handle, window, cx)
            .into_any_element()
    }
}

impl Focusable for PortsPanel {
    fn focus_handle(&self, _: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl EventEmitter<PanelEvent> for PortsPanel {}

impl Render for PortsPanel {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        v_flex()
            .size_full()
            .key_context("PortsPanel")
            .track_focus(&self.focus_handle)
            .on_action(cx.listener(Self::confirm_quick_add))
            .when(self.manager.is_some(), |this| {
                this.child(self.render_quick_add(cx))
            })
            .child(self.render_body(window, cx))
    }
}

impl Panel for PortsPanel {
    fn persistent_name() -> &'static str {
        "PortsPanel"
    }

    fn panel_key() -> &'static str {
        PORTS_PANEL_KEY
    }

    fn position(&self, _window: &Window, _cx: &App) -> DockPosition {
        self.position
    }

    fn position_is_valid(&self, _position: DockPosition) -> bool {
        true
    }

    fn set_position(&mut self, position: DockPosition, _window: &mut Window, cx: &mut Context<Self>) {
        self.position = position;
        cx.notify();
    }

    fn default_size(&self, _window: &Window, _cx: &App) -> Pixels {
        px(300.)
    }

    fn icon(&self, _window: &Window, _cx: &App) -> Option<IconName> {
        Some(IconName::Server)
    }

    fn icon_tooltip(&self, _window: &Window, _cx: &App) -> Option<&'static str> {
        Some("Ports")
    }

    fn toggle_action(&self) -> Box<dyn gpui::Action> {
        Box::new(ToggleFocus)
    }

    fn activation_priority(&self) -> u32 {
        9
    }

    fn set_active(&mut self, active: bool, _window: &mut Window, cx: &mut Context<Self>) {
        if let Some(manager) = self.manager.clone() {
            manager.update(cx, |manager, cx| manager.set_polling(active, cx));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_port() {
        assert_eq!(parse_port(""), None);
        assert_eq!(parse_port("   "), None);
        assert_eq!(parse_port("not-a-port"), None);
        assert_eq!(parse_port("70000"), None);
        assert_eq!(parse_port(" 8080 "), Some(8080));
        assert_eq!(parse_port("0"), Some(0));
    }

    #[test]
    fn test_parse_quick_add() {
        assert_eq!(parse_quick_add(""), None);
        assert_eq!(parse_quick_add("not-a-port"), None);
        assert_eq!(
            parse_quick_add("3000"),
            Some(("localhost".to_string(), 3000))
        );
        assert_eq!(
            parse_quick_add(" 8080 "),
            Some(("localhost".to_string(), 8080))
        );
        assert_eq!(
            parse_quick_add("db.internal:5432"),
            Some(("db.internal".to_string(), 5432))
        );
        assert_eq!(parse_quick_add("[::1]:3000"), Some(("::1".to_string(), 3000)));
        assert_eq!(
            parse_quick_add(":9000"),
            Some(("localhost".to_string(), 9000))
        );
        assert_eq!(parse_quick_add("host:notaport"), None);
    }

    fn key(local_port: u16, remote_port: u16) -> ForwardKey {
        ForwardKey {
            local_host: "localhost".to_string(),
            local_port,
            remote_host: "localhost".to_string(),
            remote_port,
        }
    }

    #[test]
    fn test_compute_forward_diff() {
        let a = key(3000, 3000);
        let b = key(8080, 8080);
        let c = key(5173, 5173);

        // `a` is master-owned (existing, not managed); `b` is managed; `c` is new.
        let existing: HashSet<_> = [a.clone(), b.clone()].into_iter().collect();
        let managed: HashSet<_> = [b.clone()].into_iter().collect();
        let desired: HashSet<_> = [a.clone(), c.clone()].into_iter().collect();

        let (to_add, to_remove) = compute_forward_diff(&desired, &existing, &managed);

        // `c` is newly desired; `a` already exists (master-owned) so isn't re-added.
        assert_eq!(to_add, vec![c]);
        // `b` (managed) is no longer desired, so its child is torn down.
        assert_eq!(to_remove, [b].into_iter().collect::<HashSet<_>>());
        // `a` is removed from neither: it isn't managed, so we can't cancel it.
        assert!(!to_remove.contains(&a));
    }

    #[test]
    fn test_is_bind_failure() {
        assert!(is_bind_failure(
            "bind [127.0.0.1]:8080: Address already in use"
        ));
        assert!(is_bind_failure("cannot listen to port: 8080"));
        assert!(is_bind_failure("bind: Cannot assign requested address"));
        assert!(!is_bind_failure("Warning: Permanently added host"));
    }
}
