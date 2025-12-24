/// Dashboard WebUI Component
///
/// Real-time metrics and visualization dashboard
/// - Frontend: Leptos/Yew with WebSocket client
/// - Updates: Real-time via WebSocket from timeline service
/// - Visualization: Agent topology (Sierpinski graph), metrics
/// - Interactivity: Query builder, filter controls

use spin_sdk::{http::{Request, Response}, http_component};

#[http_component]
fn handle_dashboard(req: Request) -> anyhow::Result<Response> {
    // Dashboard serves HTML UI for visualization
    // Routes:
    // GET / → Main dashboard HTML + assets
    // GET /api/metrics → JSON metrics endpoint
    // WebSocket /ws → Real-time updates

    let path = req.path();

    let html = if path == "/" || path.is_empty() {
        DASHBOARD_HTML
    } else {
        return Ok(Response::builder()
            .status(404)
            .header("Content-Type", "text/plain")
            .body("Not found")
            .build());
    };

    Ok(Response::builder()
        .status(200)
        .header("Content-Type", "text/html")
        .body(html)
        .build())
}

// Placeholder HTML - will be expanded with real dashboard
const DASHBOARD_HTML: &str = r#"<!DOCTYPE html>
<html>
<head>
    <title>CRDT Skill Verification Network - Dashboard</title>
    <style>
        body { font-family: sans-serif; margin: 20px; }
        h1 { color: #333; }
        .status { padding: 10px; margin: 10px 0; border-radius: 5px; }
        .ok { background-color: #d4edda; }
        .pending { background-color: #fff3cd; }
    </style>
</head>
<body>
    <h1>CRDT Skill Verification Network</h1>
    <div class="status ok">✓ Dashboard initialized</div>
    <p>Real-time metrics and visualization dashboard</p>
    <ul>
        <li>Agent topology (Sierpinski graph)</li>
        <li>Vector clock synchronization</li>
        <li>CRDT merge cache metrics</li>
        <li>E-Graph saturation progress</li>
        <li>17-Agent skill verification status</li>
        <li>Interaction timeline events</li>
    </ul>
</body>
</html>"#;
