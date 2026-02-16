---
name: mcp-orchestrator
description: 'MCP agent orchestration patterns: planner/worker, swarm, evaluator-optimizer.
  Composable multi-agent coordination.'
source: lastmile-ai/mcp-agent (tree-sitter extracted)
license: MIT
gf3_category: ZERO
---

# MCP Orchestrator Skill

> **Source**: [lastmile-ai/mcp-agent](https://github.com/lastmile-ai/mcp-agent) - tree-sitter extracted
> **Key files**: `src/mcp_agent/workflows/orchestrator/`, `src/mcp_agent/workflows/swarm/`

## Workflow Patterns (from tree-sitter)

```
mcp-agent/src/mcp_agent/workflows/
├── orchestrator/        # Planner + worker coordination
├── swarm/               # OpenAI Swarm-compatible handoffs
├── parallel/            # Parallel task execution
├── router/              # Intent-based routing
├── intent_classifier/   # Embedding-based classification
├── evaluator_optimizer/ # Iterative refinement
└── deep_orchestrator/   # Long-horizon research
```

## Swarm Classes (tree-sitter extracted)

From `src/mcp_agent/workflows/swarm/swarm.py`:

```python
# Classes (6 total):
# - AgentResource: Pydantic model for agent state
# - AgentFunctionResultResource: Result wrapper
# - SwarmAgent: Individual swarm agent
# - AgentFunctionResult: Function call result
# - Swarm: Main swarm coordinator
# - DoneAgent: Terminal agent for completion

# Key methods:
# - call_tool: Execute tool via MCP
# - create_transfer_to_agent_tool: Handoff creation
# - pre_tool_call / post_tool_call: Hooks
# - set_agent: Switch active agent
# - should_continue: Termination check
```

## Orchestrator Pattern

```python
from mcp_agent.agents.agent import Agent
from mcp_agent.workflows.orchestrator import Orchestrator
from mcp_agent.workflows.llm import AnthropicAugmentedLLM

# Define specialized worker agents
finder_agent = Agent(
    name="finder",
    instructions="Search for relevant information using available tools.",
    server_names=["fetch", "filesystem"]
)

writer_agent = Agent(
    name="writer",
    instructions="Write clear, engaging content based on research.",
    server_names=["filesystem"]
)

proofreader = Agent(
    name="proofreader",
    instructions="Check grammar, style, and factual accuracy.",
    server_names=[]
)

# Create orchestrator
orchestrator = Orchestrator(
    llm_factory=AnthropicAugmentedLLM,
    available_agents=[finder_agent, writer_agent, proofreader],
)

# Execute task with automatic parallelization
task = "Research AI safety, write a summary, and proofread it."
result = await orchestrator.generate_str(
    task, 
    RequestParams(model="claude-sonnet-4-20250514")
)
```

## Swarm Pattern (Handoffs)

```python
from mcp_agent.workflows.swarm import Swarm, SwarmAgent, AgentFunctionResult

# Define agents with handoff capabilities
class SalesAgent(SwarmAgent):
    def __init__(self):
        super().__init__(
            name="sales",
            instructions="Handle sales inquiries. Transfer to support for issues.",
        )
    
    async def call_tool(self, request: CallToolRequest) -> CallToolResult:
        if request.params.name == "transfer_to_support":
            # Handoff to support agent
            return AgentFunctionResult(
                value="Transferring to support...",
                agent="support"  # Target agent name
            )
        return await super().call_tool(request)


class SupportAgent(SwarmAgent):
    def __init__(self):
        super().__init__(
            name="support",
            instructions="Handle technical support. Escalate complex issues.",
        )


# Create swarm
swarm = Swarm()
swarm.register_agent(SalesAgent())
swarm.register_agent(SupportAgent())

# Run with automatic handoffs
result = await swarm.run(
    initial_agent="sales",
    messages=[{"role": "user", "content": "I have a billing issue"}]
)
```

## Evaluator-Optimizer Pattern

```python
from mcp_agent.workflows.evaluator_optimizer import EvaluatorOptimizer

# Create iterative refinement workflow
evaluator_optimizer = EvaluatorOptimizer(
    generator_llm=AnthropicAugmentedLLM,
    evaluator_llm=OpenAIAugmentedLLM,
    max_iterations=3,
    acceptance_threshold=0.8,
)

# Generate with evaluation loop
result = await evaluator_optimizer.generate_str(
    task="Write a haiku about recursion",
    evaluation_criteria="Must follow 5-7-5 syllable pattern and be technically accurate"
)
```

## Composable Workflows

```python
# Compose evaluator-optimizer as planner in orchestrator
smart_planner = EvaluatorOptimizer(
    generator_llm=AnthropicAugmentedLLM,
    evaluator_llm=AnthropicAugmentedLLM,
    max_iterations=2,
)

# Use as orchestrator's planning LLM
orchestrator = Orchestrator(
    llm_factory=lambda: smart_planner,  # Composed!
    available_agents=[finder_agent, writer_agent],
)
```

## Tool Hooks (tree-sitter extracted)

```python
class SwarmAgent:
    async def pre_tool_call(
        self, 
        tool: Tool, 
        arguments: dict
    ) -> tuple[Tool, dict]:
        """Hook before tool execution.
        
        Can modify tool or arguments before call.
        """
        # Add tracing, validation, etc.
        return tool, arguments
    
    async def post_tool_call(
        self,
        tool: Tool,
        arguments: dict,
        result: CallToolResult,
    ) -> CallToolResult:
        """Hook after tool execution.
        
        Can modify or log results.
        """
        # Transform result, log, etc.
        return result
```

## GF(3) Agent Coordination

```python
def agent_role_to_trit(role: str) -> int:
    """Map agent roles to GF(3) trits."""
    ROLE_TRITS = {
        # PLUS: Generative roles
        "writer": 1,
        "generator": 1,
        "creator": 1,
        
        # MINUS: Evaluative roles
        "evaluator": -1,
        "proofreader": -1,
        "validator": -1,
        
        # ZERO: Coordination roles
        "orchestrator": 0,
        "router": 0,
        "planner": 0,
    }
    return ROLE_TRITS.get(role.lower(), 0)


def verify_swarm_balance(agents: list[SwarmAgent]) -> bool:
    """Verify GF(3) conservation in swarm composition."""
    trits = [agent_role_to_trit(a.name) for a in agents]
    return sum(trits) % 3 == 0


# Example: balanced team
team = [
    SwarmAgent(name="writer"),      # +1
    SwarmAgent(name="evaluator"),   # -1
    SwarmAgent(name="planner"),     # 0
]
assert verify_swarm_balance(team)  # 1 + (-1) + 0 = 0 ✓
```

## Deep Orchestrator (Long-Horizon)

```python
from mcp_agent.workflows.deep_orchestrator import DeepOrchestrator

# For multi-step research tasks
deep_orchestrator = DeepOrchestrator(
    llm_factory=AnthropicAugmentedLLM,
    available_agents=[researcher, analyst, synthesizer],
    policy_file="research_policy.md",  # Guardrails
    max_depth=5,
    knowledge_extraction=True,
)

result = await deep_orchestrator.research(
    query="Analyze the impact of sheaf theory on distributed systems",
    output_format="report"
)
```

## Links

- [mcp-agent GitHub](https://github.com/lastmile-ai/mcp-agent)
- [MCP Specification](https://modelcontextprotocol.io/)
- [Anthropic Agent Patterns](https://www.anthropic.com/engineering/building-effective-agents)
- [OpenAI Swarm](https://github.com/openai/swarm)

## Commands

```bash
just mcp-orchestrator-demo    # Basic orchestrator example
just mcp-swarm-handoff        # Swarm with handoffs
just mcp-eval-opt             # Evaluator-optimizer loop
just mcp-deep-research        # Long-horizon research
just mcp-gf3-balance          # Verify agent balance
```

---

*GF(3) Category: ZERO (Coordination) | Multi-agent orchestration patterns*