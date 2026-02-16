#!/usr/bin/env python3
"""
amp-continue Skill: Universal Cross-TUI Continuations

Cognitive-continuation skill that parses flexible natural language prompts
and routes execution across Claude Code, Codex, TOAD, AMP, and all supported TUI systems.

Usage:
  claude code --skill amp-continue --prompt "Start universal continuation: export threads"
  claude code --skill amp-continue --prompt "Fork threads to cq-ai, chromatic-walk, and skill-maker"
  claude code --skill amp-continue --prompt "Continue previous task with amp and shell"
"""

import sys
import json
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass
from datetime import datetime
import subprocess

# Add continuations module to path
CONTINUATIONS_PATH = Path.home() / "ies"
sys.path.insert(0, str(CONTINUATIONS_PATH))

try:
    from continuations_protocol import (
        Continuation, Decision, TUISystem, ContinuationAction,
        ContinuationRepository, ContinuationState
    )
except ImportError:
    print("Error: continuations_protocol module not found")
    print(f"Expected at: {CONTINUATIONS_PATH / 'continuations_protocol.py'}")
    sys.exit(1)


# ============================================================================
# Intent Recognition
# ============================================================================

@dataclass
class ParsedIntent:
    """Result of parsing a prompt into actionable intent"""
    action: str                    # export, analyze, fork, continue, compose
    primary_target: str            # Main target system
    secondary_targets: List[str]   # Additional targets
    decision: Decision             # GF(3) branching decision
    threads: List[str]            # Specific threads to operate on
    skills: List[str]             # Skills to invoke
    filters: Dict[str, Any]       # Filtering criteria
    confidence: float              # Confidence score (0-1)
    raw_prompt: str               # Original prompt


class IntentParser:
    """Parses natural language prompts into structured intents"""

    # Intent patterns
    EXPORT_KEYWORDS = {
        "export", "save", "dump", "extract", "output", "write",
        "backup", "archive", "serialize"
    }

    ANALYZE_KEYWORDS = {
        "analyze", "audit", "scan", "check", "review", "examine",
        "inspect", "evaluate", "assess", "diagnose"
    }

    FORK_KEYWORDS = {
        "fork", "parallel", "split", "branch", "diverge", "fan-out",
        "spawn", "launch", "start multiple", "execute in parallel"
    }

    CONTINUE_KEYWORDS = {
        "continue", "next", "proceed", "follow", "chain", "sequence",
        "then", "afterward", "subsequently", "next step"
    }

    REDUCE_KEYWORDS = {
        "reduce", "filter", "summarize", "compress", "consolidate",
        "aggregate", "synthesize", "distill", "extract summary"
    }

    COMPOSE_KEYWORDS = {
        "compose", "combine", "integrate", "orchestrate", "chain skills",
        "skill composition", "triadic"
    }

    # TUI system aliases
    TUI_ALIASES = {
        "claude": ("claude-code", TUISystem.CLAUDE_CODE),
        "code": ("claude-code", TUISystem.CLAUDE_CODE),
        "cc": ("claude-code", TUISystem.CLAUDE_CODE),
        "codex": ("codex", TUISystem.CODEX),
        "toad": ("toad", TUISystem.TOAD),
        "amp": ("amp", TUISystem.AMP),
        "shell": ("shell", TUISystem.SHELL),
        "bash": ("shell", TUISystem.SHELL),
        "vim": ("vim", TUISystem.VIM),
        "neovim": ("vim", TUISystem.VIM),
        "nvim": ("vim", TUISystem.VIM),
        "emacs": ("emacs", TUISystem.EMACS),
        "tmux": ("tmux", TUISystem.TMUX),
        "zellij": ("zellij", TUISystem.ZELLIJ),
    }

    @staticmethod
    def fuzzy_match(text: str, keywords: set) -> float:
        """
        Fuzzy match score for keyword set (0-1).
        Higher score = more keywords found in text.
        """
        text_lower = text.lower()
        matches = sum(1 for kw in keywords if kw in text_lower)
        return matches / len(keywords) if keywords else 0.0

    @staticmethod
    def extract_tui_systems(prompt: str) -> List[Tuple[str, TUISystem]]:
        """Extract TUI system mentions from prompt"""
        systems = []
        prompt_lower = prompt.lower()

        for alias, (name, system) in IntentParser.TUI_ALIASES.items():
            if alias in prompt_lower:
                systems.append((name, system))

        # Remove duplicates (by system)
        seen = set()
        unique = []
        for name, system in systems:
            if system not in seen:
                unique.append((name, system))
                seen.add(system)

        return unique

    @staticmethod
    def extract_thread_ids(prompt: str) -> List[str]:
        """Extract thread IDs from prompt (T-xxx-xxx format)"""
        # Match UUIDs in thread ID format
        pattern = r'T-[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}'
        return re.findall(pattern, prompt, re.IGNORECASE)

    @staticmethod
    def extract_skill_names(prompt: str) -> List[str]:
        """Extract skill names from prompt"""
        skills = []

        # Pattern 1: Quoted strings
        quoted = re.findall(r'"([^"]+)"', prompt)
        for item in quoted:
            if "-" in item or "_" in item:  # Looks like a skill name
                skills.append(item)

        # Pattern 2: Known skill-like names (word-word patterns after "to")
        # E.g., "to cq-ai, chromatic-walk, skill-maker"
        skill_pattern = r'(?:to|send to|run|execute|invoke|use)\s+([a-z][a-z0-9\-]*(?:\s*,\s*[a-z][a-z0-9\-]*)*)'
        matches = re.findall(skill_pattern, prompt, re.IGNORECASE)

        for match in matches:
            # Split by comma and clean up
            items = [s.strip() for s in match.split(',')]
            for item in items:
                if item and (item.count('-') >= 1 or item.count('_') >= 1 or len(item) > 5):
                    skills.append(item)

        # Remove duplicates
        return list(set(skills))

    @classmethod
    def parse(cls, prompt: str) -> ParsedIntent:
        """Parse prompt into structured intent"""
        # Detect action via fuzzy matching
        export_score = cls.fuzzy_match(prompt, cls.EXPORT_KEYWORDS)
        analyze_score = cls.fuzzy_match(prompt, cls.ANALYZE_KEYWORDS)
        fork_score = cls.fuzzy_match(prompt, cls.FORK_KEYWORDS)
        continue_score = cls.fuzzy_match(prompt, cls.CONTINUE_KEYWORDS)
        reduce_score = cls.fuzzy_match(prompt, cls.REDUCE_KEYWORDS)
        compose_score = cls.fuzzy_match(prompt, cls.COMPOSE_KEYWORDS)

        scores = {
            "export": export_score,
            "analyze": analyze_score,
            "fork": fork_score,
            "continue": continue_score,
            "reduce": reduce_score,
            "compose": compose_score
        }

        action = max(scores, key=scores.get)
        confidence = max(scores.values())

        # Determine GF(3) decision based on action AND context
        prompt_lower = prompt.lower()
        has_multiple_targets = prompt_lower.count("and") + prompt_lower.count(",") > 0
        is_parallel = any(kw in prompt_lower for kw in ["parallel", "fork", "simultaneous", "at once"])
        is_sequential = any(kw in prompt_lower for kw in ["then", "next", "sequence", "chain", "step"])

        if action == "fork" or (is_parallel and has_multiple_targets):
            decision = Decision.PLUS
        elif action == "reduce":
            decision = Decision.MINUS
        elif action == "continue" or is_sequential:
            decision = Decision.ZERO
        else:
            # If we have multiple targets and no explicit sequential indicator, fork
            if has_multiple_targets and not is_sequential:
                decision = Decision.PLUS
            else:
                decision = Decision.ZERO

        # Extract targets
        tui_systems = cls.extract_tui_systems(prompt)
        primary_target = TUISystem.TOAD  # Default gateway
        secondary_targets = []

        if tui_systems:
            primary_target = tui_systems[0][1]
            secondary_targets = [system for name, system in tui_systems[1:]]

        # Extract threads and skills
        threads = cls.extract_thread_ids(prompt)
        skills = cls.extract_skill_names(prompt)

        return ParsedIntent(
            action=action,
            primary_target=primary_target.value,
            secondary_targets=[s.value for s in secondary_targets],
            decision=decision,
            threads=threads,
            skills=skills,
            filters={},
            confidence=confidence,
            raw_prompt=prompt
        )


# ============================================================================
# Continuation Building
# ============================================================================

class ContinuationBuilder:
    """Builds continuation objects from parsed intents"""

    # Map detected actions to ContinuationAction values
    ACTION_MAPPING = {
        "export": ContinuationAction.EXPORT,
        "analyze": ContinuationAction.EXECUTE,
        "fork": ContinuationAction.EXECUTE,
        "continue": ContinuationAction.CONTINUE,
        "reduce": ContinuationAction.REDUCE,
        "compose": ContinuationAction.EXECUTE,
    }

    @staticmethod
    def from_intent(intent: ParsedIntent) -> List[Continuation]:
        """Create continuation(s) from parsed intent"""
        continuations = []

        # Determine source and target
        source = TUISystem.CLAUDE_CODE
        target = TUISystem.from_string(intent.primary_target)

        # Map detected action to ContinuationAction
        action = ContinuationBuilder.ACTION_MAPPING.get(
            intent.action,
            ContinuationAction.EXECUTE
        )

        # Create primary continuation
        primary = Continuation(
            source=source,
            target=target,
            decision=intent.decision,
            action=action,
            payload={
                "intent": intent.action,
                "threads": intent.threads,
                "skills": intent.skills,
                "prompt": intent.raw_prompt,
                "confidence": intent.confidence,
            },
            parallel=(intent.decision == Decision.PLUS),
            workers=len(intent.secondary_targets) or 1
        )
        continuations.append(primary)

        # Create secondary continuations for forks
        if intent.decision == Decision.PLUS and intent.secondary_targets:
            for secondary_target_str in intent.secondary_targets:
                secondary_target = TUISystem.from_string(secondary_target_str)
                secondary = Continuation(
                    source=target,
                    target=secondary_target,
                    decision=intent.decision,
                    action=ContinuationAction.EXECUTE,
                    payload=primary.payload.copy(),
                    parent_id=primary.id,
                    parallel=True,
                    workers=len(intent.secondary_targets)
                )
                continuations.append(secondary)

        return continuations


# ============================================================================
# Skill Interface
# ============================================================================

class AmpContinueSkill:
    """amp-continue skill: Universal cross-TUI continuations"""

    def __init__(self):
        self.parser = IntentParser()
        self.builder = ContinuationBuilder()
        self.repo = ContinuationRepository()

    def execute(self, prompt: str) -> Dict[str, Any]:
        """
        Execute the skill with a natural language prompt.

        Returns:
            Dictionary with continuations, routing plan, and execution results
        """
        # Parse intent from prompt
        intent = self.parser.parse(prompt)

        # Build continuations
        continuations = self.builder.from_intent(intent)

        # Save continuations
        continuation_ids = []
        for cont in continuations:
            self.repo.save(cont)
            continuation_ids.append(cont.id)

        # Build result
        result = {
            "status": "success",
            "timestamp": datetime.now().isoformat(),
            "input_prompt": prompt,
            "parsed_intent": {
                "action": intent.action,
                "primary_target": intent.primary_target,
                "secondary_targets": intent.secondary_targets,
                "decision": intent.decision.name,
                "confidence": intent.confidence,
                "threads": intent.threads,
                "skills": intent.skills,
            },
            "continuations": [c.to_dict() for c in continuations],
            "continuation_ids": continuation_ids,
            "routing_plan": self._build_routing_plan(intent, continuations),
            "next_step": self._suggest_next_step(intent, continuations),
        }

        return result

    def _build_routing_plan(self, intent: ParsedIntent, continuations: List[Continuation]) -> str:
        """Build human-readable routing plan"""
        if intent.decision == Decision.PLUS:
            targets = [intent.primary_target] + intent.secondary_targets
            return f"FORK (PLUS): Execute in parallel across {targets}"
        elif intent.decision == Decision.MINUS:
            return f"REDUCE (MINUS): Synthesize and filter results"
        else:
            if intent.secondary_targets:
                all_targets = [intent.primary_target] + intent.secondary_targets
                return f"CHAIN (ZERO): Execute sequentially {' → '.join(all_targets)}"
            else:
                return f"CONTINUE (ZERO): Execute in {intent.primary_target}"

    def _suggest_next_step(self, intent: ParsedIntent, continuations: List[Continuation]) -> str:
        """Suggest next action for user"""
        if intent.decision == Decision.PLUS:
            return (
                f"Continuations ready to fork to {intent.secondary_targets or 'multiple targets'}. "
                f"Use: codex route --parallel to execute in parallel."
            )
        elif intent.decision == Decision.MINUS:
            return (
                f"Results will be reduced/synthesized. "
                f"Use: codex apply --continuation {continuations[0].id} to execute."
            )
        else:
            return (
                f"Continuations chained sequentially. "
                f"Use: codex execute --continuation {continuations[0].id} to run."
            )


# ============================================================================
# Main Entry Point
# ============================================================================

def main():
    """Main skill entry point"""
    # Get prompt from stdin or argv
    if len(sys.argv) > 1:
        prompt = " ".join(sys.argv[1:])
    else:
        prompt = sys.stdin.read().strip()

    if not prompt:
        print(json.dumps({
            "error": "No prompt provided",
            "usage": "claude code --skill amp-continue --prompt 'your prompt here'"
        }, indent=2))
        return 1

    # Execute skill
    skill = AmpContinueSkill()
    result = skill.execute(prompt)

    # Output result
    print(json.dumps(result, indent=2, default=str))
    return 0


if __name__ == "__main__":
    sys.exit(main())
