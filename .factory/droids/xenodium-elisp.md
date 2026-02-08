---
name: xenodium-elisp
description: "Xenodium's Emacs packages: chatgpt-shell, agent-shell, dwim-shell-command, and ACP integration for modern Emacs development."
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Xenodium Elisp Skill

> *"The best UI is no UI. The second best UI is Emacs."*

## Package Overview

| Package | Stars | Description |
|---------|-------|-------------|
| [chatgpt-shell](https://github.com/xenodium/chatgpt-shell) | 1180⭐ | Multi-LLM Emacs shell (ChatGPT, Claude, DeepSeek, Gemini, Ollama) |
| [agent-shell](https://github.com/xenodium/agent-shell) | 415⭐ | Native Emacs buffer for LLM agents via ACP |
| [dwim-shell-command](https://github.com/xenodium/dwim-shell-command) | 293⭐ | Save and apply shell commands with ease |
| [acp.el](https://github.com/xenodium/acp.el) | 109⭐ | Agent Client Protocol implementation |
| [ob-swiftui](https://github.com/xenodium/ob-swiftui) | 87⭐ | SwiftUI in Org Babel blocks |
| [sqlite-mode-extras](https://github.com/xenodium/sqlite-mode-extras) | 58⭐ | Enhanced sqlite-mode |

## chatgpt-shell: Multi-LLM Interface

```elisp
(use-package chatgpt-shell
  :custom
  (chatgpt-shell-model-version "gpt-4o")
  (chatgpt-shell-anthropic-key (getenv "ANTHROPIC_API_KEY"))
  (chatgpt-shell-openai-key (getenv "OPENAI_API_KEY"))
  :config
  ;; Switch between models
  (setq chatgpt-shell-model-versions
        '("gpt-4o" "gpt-4-turbo" "claude-3-5-sonnet" "gemini-pro")))

;; Key bindings
(global-set-key (kbd "C-c g") 'chatgpt-shell)
(global-set-key (kbd "C-c G") 'chatgpt-shell-send-region)
```

### Shell Commands

| Command | Description |
|---------|-------------|
| `chatgpt-shell` | Open interactive shell |
| `chatgpt-shell-send-region` | Send selected region |
| `chatgpt-shell-describe-code` | Explain code at point |
| `chatgpt-shell-refactor-code` | Refactor with AI |
| `chatgpt-shell-generate-unit-test` | Generate tests |

## agent-shell: ACP-Powered Agents

Agent Client Protocol enables structured agent workflows:

```elisp
(use-package agent-shell
  :after acp
  :config
  (setq agent-shell-default-agent "coding-assistant"))

;; Define custom agent
(acp-define-agent "music-topos-agent"
  :system-prompt "You are a categorical music 