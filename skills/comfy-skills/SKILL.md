---
name: comfy-skills
description: Manage and deploy ComfyUI workflow skills using the comfy-skills CLI.
---

# Comfy Skills Manager

## When to Use

Use this skill when you need to:
- Find ComfyUI workflows or skills (e.g., for image generation, SDXL, etc.)
- Search for specific workflow capabilities
- Install ComfyUI workflows to use in the current environment
- Get information about available ComfyUI skills

## When NOT to Use

- Do not use for general Python package management (use `uv` or `pip`).
- Do not use if you are looking for Agent Skills (like this one), unless you are looking for *ComfyUI* specific skills.

## Goal

Enable the agent to discover and deploy ComfyUI workflows using the `uvx comfy-skills` tool.

## Workflow

### 1) Discover Skills

To see what skills are available or search for a specific one:

```bash
uvx comfy-skills list
uvx comfy-skills search <query>
```

### 2) Inspect a Skill

Before installing, check the details of a skill:

```bash
uvx comfy-skills info <skill-id>
```

### 3) Install a Skill

To use a skill, install it.

```bash
uvx comfy-skills install <skill-id>
```

**After installation:**
The command will output the installation path, typically ending in `workflow.json`.
You can then load this workflow file to use it, or provide the path to the user.

Example output:
`Installed <skill> v<version> to <path>`
`Tell Claude: "Load the skill from <path>/workflow.json"`

### 4) Using the Installed Skill

Once installed, you can read the `workflow.json` to understand the nodes and connections.

## Examples

**Search for SDXL skills:**
```bash
uvx comfy-skills search sdxl
```

**Install and use:**
```bash
uvx comfy-skills install sdxl-generation
# Output shows path, e.g., /Users/bob/.cache/comfy-skills/installed/sdxl-generation
cat /Users/bob/.cache/comfy-skills/installed/sdxl-generation/workflow.json
```
