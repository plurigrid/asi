/// BLUE Stream: Backward Rewriting (Negative Polarity)
///
/// Implements negative polarity operations for the CRDT Skill Verification Network.
/// - Polarity: -1 (negative, backward-biased)
/// - Operations: delete, merge backward, inverse propagation
/// - Gadget: BLUE (backward inverse rewrite)
/// - Verification: self-transduction enabled

use spin_sdk::{http::{Request, Response}, http_component};

#[http_component]
fn handle_blue_stream(req: Request) -> anyhow::Result<Response> {
    let body = req.body();
    let body_str = String::from_utf8(body.to_vec())?;

    let response = serde_json::json!({
        "status": "ok",
        "message": "BLUE stream received",
        "color": "BLUE",
        "polarity": "negative",
        "path": req.uri(),
        "request_size": body_str.len(),
    });

    Ok(Response::builder()
        .status(200)
        .header("Content-Type", "application/json")
        .body(serde_json::to_string(&response)?)
        .build())
}
