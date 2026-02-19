# 11 -- Implementation Roadmap and Protocol Selection Matrix

**Date**: 2026-02-19
**Scope**: Practical decision guidance for teams choosing among 40+ agentic ecosystem efforts identified in prior research.

This note extends:

- `07-interoperability-convergence.md` for dependency and convergence relationships
- `08-synthesis-and-recommendations.md` for the prior recommendation summary
- `09-ANP-deep-dive.md` for identity/discovery risk and implementation details

## 1. Executive Snapshot

Agentic interoperability is currently in a **bimodal phase**:

- **Converged layer**: MCP for tool access is effectively standardized across major frameworks.
- **Fragmented layer**: Agent-to-agent and identity/discovery remain unsettled across A2A, ANP, LMOS, Agora, NANDA, AGNTCY, and framework-specific alternatives.

The strongest strategic stance is to **build on MCP now** for immediate interoperability while treating agent-to-agent and identity as a staged roadmap with explicit abstractions.

---

## 2. Fast Decision Matrix (2026)

| Use Case | Short-Term Best Protocols | Why |
|---|---|---|
| Internal tooling assistants (IDE, operations bots, CI agents) | **MCP + AGENTS.md** | Fast adoption, immediate developer tooling support, low coordination overhead |
| Multi-agent workflows inside one platform/team | **A2A + MCP** | Ready for structured task delegation and conversation-like orchestration |
| Cross-organization AI-to-AI automation | **ANP (cardinality-light identity-first)** for discovery + A2A for tasking + MCP adapters | ANP gives open discovery/identity baseline; A2A gives message/task semantics |
| Regulated enterprise environments | **AGNTCY + MCP + enterprise IDM/OIDC bridge** | Registry/discovery + signature and supply-chain controls |
| Retail/commercial checkout | **ACP-Commerce + AP2** (where available) | ACP covers UX + payment authorization flows; AP2 closes rails-level execution |
| Crypto-native or on-chain agents | **AITP (pilot) + wallet signing** | Built-in payment/delegation primitives but ecosystem is smaller |

---

## 3. Risk-Balanced Protocol Strategy

### 3.1 Risk-Weighted Prioritization

**Adopt immediately (Low risk, high value)**

1. MCP for every tool surface
2. MCP security hardening (least-privilege tool catalogs, schema strictness, approval gates)
3. AGENTS.md alignment per repo to reduce integration drift

**Adopt in controlled pilots (Medium risk, high strategic value)**

4. A2A as inter-agent contract for internal tasks
5. ANP or AGNTCY for identity/discovery experiments
6. agents.json where public endpoint discovery is needed

**Monitor and prototype (High strategic value, higher uncertainty)

7. LMOS if you need DID-first stack + Kubernetes-native agent fabric
8. LangGraph Agent Protocol in LangGraph-first environments only
9. AITP/AP2 for regulated payment automation pilots

### 3.2 De-commitment Rule (go/no-go signals)

- **Continue** a protocol if production integrations appear in at least 2 major dependencies or deployments.
- **Contain** by adapter boundary when a protocol lacks tooling support or has identity ambiguity.
- **Pause** if security model depends on undocumented assumptions (e.g., non-verifiable delegation claims).

---

## 4. Recommended 90-Day Adoption Path

### Phase 1 (Weeks 1-2): Standardize Foundation
- Implement MCP-only baseline for all tool calls in your platform.
- Establish explicit AGENTS.md instructions per repository.
- Add schema/version checks + audit logging for all MCP interactions.

### Phase 2 (Weeks 3-6): Add inter-agent coordination
- Introduce A2A contracts for agent handoff and escalation.
- Define canonical `agent_card` / capability schema mapping to your internal registry.
- Add fallback adapter route: if peer does not support A2A, execute via MCP-native orchestration.

### Phase 3 (Weeks 7-12): Identity/discovery hardening
- Pilot ANP or AGNTCY directory model in a non-critical domain.
- Add OIDC/OAuth and key-anchored signatures at invocation boundaries.
- Draft policy for trust tiers (internal, partner, public).

### Phase 4 (Month 4+): Commerce and external expansion
- Evaluate ACP-Commerce vs AP2 depending on payment flows.
- For EU-centric or DID-first requirements, evaluate LMOS compatibility.
- Keep protocol abstraction layer to avoid lock-in to one stack.

---

## 5. API/Protocol Surface Alignment Checklist

- **Message format**: ensure each inter-agent message carries stable conversation/task IDs.
- **Identity**: every delegated action must be traceable to a human or service principal.
- **Authorization**: human-in-the-loop policy where high-risk actions are required.
- **Compliance hooks**: append machine-verifiable evidence of decisions.
- **Observability**: measure latency, negotiation failure reasons, and cross-protocol translation losses.
- **Adapters**: standardize tool adapters as first-class components (MCP ↔ A2A ↔ ANP ↔ payment rails).

---

## 6. Comparative Decision Table

| Criterion | MCP | A2A | ANP | LMOS | AGNTCY | AP2 | ACP-Commerce |
|---|---|---|---|---|---|---|---|
| Tool interoperability today | High | Medium | Low/Medium | Medium | Low | Low | Medium |
| Multi-agent tasking today | Low/None | High | Medium | Medium | Low | Low | None |
| Identity depth | Low/medium | Medium | High | High | High | Medium | Low |
| Discovery | Low | Medium | Medium | High | High | Low | Low |
| Commerce coverage | Low | Low | Medium | Low | Low | High | Medium |
| Enterprise governance fit | High | Medium | Medium | Medium | High | Medium | Medium |
| Standardization uncertainty | Low | Medium | Medium/High | Medium | Medium | High | Medium |

---

## 7. Key Watch Points (for next quarter)

1. Linux Foundation status changes for A2A governance and LF role clarity.
2. ANP charter and identity document updates in W3C CG.
3. IETF progress on a2t/agent-id/audit drafts.
4. AP2 adoption by major PSP and wallet ecosystems.
5. AGNTCY and NANDA interoperability test cases (especially cross-protocol adapters).
6. Master/Visa implementation playbooks for AI agent payment behavior.

---

## 8. Final Recommendation

If you need **operational interoperability now**: deploy MCP first.

If you need **cross-organizational autonomy next**: layer A2A plus a lightweight identity/discovery plane (ANP or AGNTCY/NANDA style) under an adapter architecture.

If you need **payments and finance-grade trust**: evaluate ACP-Commerce and AP2 in tandem, with explicit card-network guardrails.

In short: **default to a practical “MCP + A2A + modular identity adapter” architecture**, with protocol-specific adapters to avoid lock-in as standards converge.

## 9. Teaching the Implementation: Hands-On Playbook

### 9.1 Team Setup

Assign each protocol layer a clear owner so execution is teachable and repeatable:

- **Tool Surface Owner**: MCP server catalog, schema validation, and tool access controls.
- **Conversation/Workflow Owner**: A2A handoff protocol, escalation paths, and task lifecycle.
- **Identity/Discovery Owner**: ANP/AGNTCY candidate registry, trust levels, and revocation.
- **Commerce/Payments Owner** (if applicable): AP2 or ACP-Commerce pilot governance, evidence logs, fallback controls.
- **Observability Owner**: cross-protocol tracing, error taxonomy, and SLA reporting.

Use a simple RACI-like table with these owners and add a named escalation person per team.

### 9.2 Practical Rollout Pattern

For each phase, track:

1. **Inputs** (code/config that must exist before starting).
2. **Activities** (exact changes).
3. **Acceptance test** (smoke test that proves the phase is complete).
4. **Rollback rule** (what breaks the phase and triggers pause).

#### Phase 1 (MCP Baseline)
- **Inputs**: existing tool clients, minimal auth, one staging environment.
- **Activities**:
  - Define `tools.json` or equivalent tool schema registry.
  - Gate tool calls behind an allowlist and per-tool confidence tier.
  - Add structured logs with `protocol`, `tool_id`, `actor_id`, `trace_id`.
- **Acceptance test**: 1 critical workflow runs using only MCP with zero manual exceptions.
- **Rollback rule**: any unauthorized tool invocation or schema mismatch in production traffic.

#### Phase 2 (A2A + Adapter Boundary)
- **Inputs**: Phase 1 logs + baseline task taxonomy.
- **Activities**:
  - Add an inter-agent message schema (`task_id`, `conversation_id`, `delegation_owner`).
  - Implement route: **A2A -> MCP adapter** for non-native peers.
  - Add timeout/backoff and circuit-breaker for peer failures.
- **Acceptance test**: 2 independent agents exchange and complete one delegated task chain end-to-end.
- **Rollback rule**: delegated task failure rate exceeds agreed threshold for 24h without safety improvement.

#### Phase 3 (Identity/Discovery Pilot)
- **Inputs**: completed delegated task routing, non-critical production segment.
- **Activities**:
  - Pilot ANP/AGNTCY directory with signed endpoint descriptors.
  - Add trust-level policy (`internal`, `partner`, `public`) with clear capability caps.
  - Introduce revocation path for stale keys and leaked credentials.
- **Acceptance test**: identity/endpoint selection fails safe when descriptors are invalid, and succeeds for valid test fixtures.
- **Rollback rule**: inability to prove attribution for any high-risk action.

#### Phase 4 (Payment/Commerce Expansion)
- **Inputs**: risk and compliance approvals.
- **Activities**:
  - Integrate payment protocol only behind a dedicated adapter.
  - Add explicit user-confirmation gate for transfer and settlement operations.
  - Emit legal/compliance evidence artifacts per transaction.
- **Acceptance test**: simulated and real dry-run transactions complete with reconciliation records.
- **Rollback rule**: any compliance or chargeback risk spike without audit trail support.

### 9.3 Minimal Architecture Blueprint

Use three explicit layers:

1. **Protocol Adapters**: MCP/A2A/ANP/ACP/AP2 connectors.
2. **Execution Core**: deterministic orchestrator that owns task state and policy enforcement.
3. **Policy and Audit Plane**: auth, authorization, evidence, and observability.

Keep adapters stateless where possible; make the execution core the single source of truth for task status.

### 9.4 KPI Pack

- **Latency**: median and p95 delegation round-trip by protocol.
- **Safety**: unauthorized escalation count and failed policy decision rate.
- **Reliability**: successful handoff percentage and dead-letter queue size.
- **Convergence**: adapter translation errors per week by source/target protocol.
- **Cost**: incremental run cost per delegated task and operator intervention minutes.

Track these weekly in one dashboard so protocol comparison remains data-driven.

### 9.5 Learning and Next Session

At the end of each 2-week sprint:

- run a **post-mortem-by-protocol** (what failed, what translated poorly, what changed),
- capture one refactoring decision to reduce lock-in risk,
- and update the next sprint’s **selection matrix weights** before adding a new protocol.
