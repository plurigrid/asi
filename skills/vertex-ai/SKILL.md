---
name: vertex-ai
description: Google Vertex AI via gcloud OAuth2. Call Gemini, Imagen, embeddings, and Model Garden models from the CLI. Use when users need generative AI, image generation, embeddings, or model inference.
version: 1.0.0
trit: 0
role: ERGODIC
tags: [vertex-ai, gemini, google-cloud, generative-ai, embeddings]
deployed: 2026-02-19
---

# Vertex AI Skill

Call Google Vertex AI models from the CLI using `gcloud` OAuth2 authentication.

## Prerequisites

- `gcloud` CLI installed (via `flox install google-cloud-sdk` or standalone)
- Authenticated: `gcloud auth login`
- Project set: `gcloud config set project PROJECT_ID`
- Vertex AI API enabled on the project

## Authentication

Vertex AI requires OAuth2, **not** API keys. Get a bearer token:

```bash
ACCESS_TOKEN=$(gcloud auth print-access-token)
```

Tokens expire after ~60 minutes. Re-run to refresh.

## Core Pattern

All Vertex AI calls follow this structure:

```bash
PROJECT=$(gcloud config get project)
REGION=us-central1
ACCESS_TOKEN=$(gcloud auth print-access-token)

curl -s "https://${REGION}-aiplatform.googleapis.com/v1/projects/${PROJECT}/locations/${REGION}/publishers/google/models/${MODEL}:${METHOD}" \
  -H "Authorization: Bearer $ACCESS_TOKEN" \
  -H "Content-Type: application/json" \
  -d "$PAYLOAD"
```

## Gemini — Text Generation

```bash
MODEL=gemini-2.0-flash
curl -s "https://${REGION}-aiplatform.googleapis.com/v1/projects/${PROJECT}/locations/${REGION}/publishers/google/models/${MODEL}:generateContent" \
  -H "Authorization: Bearer $ACCESS_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "contents": [{"role": "user", "parts": [{"text": "Your prompt here"}]}]
  }' | jq -r '.candidates[0].content.parts[0].text'
```

**CRITICAL**: Always include `"role": "user"` in contents — omitting it causes a 400 error.

### Available Gemini Models

| Model | Use Case |
|-------|----------|
| `gemini-2.0-flash` | Fast, general-purpose (recommended default) |
| `gemini-2.0-pro` | Complex reasoning, longer context |
| `gemini-1.5-pro` | 1M token context window |
| `gemini-1.5-flash` | Fast, cost-effective |

### Generation Config

```json
{
  "contents": [{"role": "user", "parts": [{"text": "prompt"}]}],
  "generationConfig": {
    "temperature": 0.7,
    "topP": 0.95,
    "topK": 40,
    "maxOutputTokens": 2048,
    "candidateCount": 1
  }
}
```

### System Instructions

```json
{
  "contents": [{"role": "user", "parts": [{"text": "prompt"}]}],
  "systemInstruction": {
    "parts": [{"text": "You are a helpful coding assistant."}]
  }
}
```

## Gemini — Multimodal (Image + Text)

```bash
# Base64 encode an image
IMG_B64=$(base64 -i image.png)

curl -s "https://${REGION}-aiplatform.googleapis.com/v1/projects/${PROJECT}/locations/${REGION}/publishers/google/models/gemini-2.0-flash:generateContent" \
  -H "Authorization: Bearer $ACCESS_TOKEN" \
  -H "Content-Type: application/json" \
  -d "{
    \"contents\": [{\"role\": \"user\", \"parts\": [
      {\"text\": \"Describe this image\"},
      {\"inlineData\": {\"mimeType\": \"image/png\", \"data\": \"$IMG_B64\"}}
    ]}]
  }" | jq -r '.candidates[0].content.parts[0].text'
```

## Embeddings

```bash
curl -s "https://${REGION}-aiplatform.googleapis.com/v1/projects/${PROJECT}/locations/${REGION}/publishers/google/models/text-embedding-005:predict" \
  -H "Authorization: Bearer $ACCESS_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "instances": [{"content": "Text to embed"}]
  }' | jq '.predictions[0].embeddings.values[:5]'
```

## Imagen — Image Generation

```bash
curl -s "https://${REGION}-aiplatform.googleapis.com/v1/projects/${PROJECT}/locations/${REGION}/publishers/google/models/imagen-3.0-generate-002:predict" \
  -H "Authorization: Bearer $ACCESS_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{
    "instances": [{"prompt": "A cat wearing a space helmet, digital art"}],
    "parameters": {"sampleCount": 1}
  }' | jq -r '.predictions[0].bytesBase64Encoded' | base64 -d > output.png
```

## Streaming

For streaming responses, use `streamGenerateContent`:

```bash
curl -s "https://${REGION}-aiplatform.googleapis.com/v1/projects/${PROJECT}/locations/${REGION}/publishers/google/models/gemini-2.0-flash:streamGenerateContent" \
  -H "Authorization: Bearer $ACCESS_TOKEN" \
  -H "Content-Type: application/json" \
  -d '{"contents": [{"role": "user", "parts": [{"text": "Write a haiku"}]}]}'
```

## Multi-turn Conversation

```json
{
  "contents": [
    {"role": "user", "parts": [{"text": "What is the capital of France?"}]},
    {"role": "model", "parts": [{"text": "Paris."}]},
    {"role": "user", "parts": [{"text": "What is its population?"}]}
  ]
}
```

## Helper Script

For quick single-prompt calls:

```bash
vertex() {
  local model="${2:-gemini-2.0-flash}"
  local token=$(gcloud auth print-access-token)
  local project=$(gcloud config get project 2>/dev/null)
  curl -s "https://us-central1-aiplatform.googleapis.com/v1/projects/${project}/locations/us-central1/publishers/google/models/${model}:generateContent" \
    -H "Authorization: Bearer $token" \
    -H "Content-Type: application/json" \
    -d "{\"contents\":[{\"role\":\"user\",\"parts\":[{\"text\":$(echo "$1" | jq -Rs .)}]}]}" \
    | jq -r '.candidates[0].content.parts[0].text'
}

# Usage: vertex "explain quantum computing" gemini-2.0-pro
```

## Error Reference

| Error | Cause | Fix |
|-------|-------|-----|
| 401 UNAUTHENTICATED | Token expired or API key used | `gcloud auth print-access-token` |
| 400 "valid role: user, model" | Missing `role` field in contents | Add `"role": "user"` |
| 403 PERMISSION_DENIED | API not enabled or no access | `gcloud services enable aiplatform.googleapis.com` |
| 429 RESOURCE_EXHAUSTED | Rate limit hit | Back off and retry |
| 404 NOT_FOUND | Wrong model name or region | Check model ID and use `us-central1` |

## 1Password Integration

Store and retrieve credentials securely:

```bash
# If using a service account key stored in 1Password:
export GOOGLE_APPLICATION_CREDENTIALS=$(op read "op://VaultName/GCP-SA-Key/credential" | base64 -d > /tmp/sa.json && echo /tmp/sa.json)
gcloud auth activate-service-account --key-file=$GOOGLE_APPLICATION_CREDENTIALS
```
