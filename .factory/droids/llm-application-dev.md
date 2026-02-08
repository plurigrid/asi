---
name: llm-application-dev
description: Building applications with Large Language Models - prompt engineering,
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# LLM Application Development

## Prompt Engineering

### Structured Prompts
```typescript
const systemPrompt = `You are a helpful assistant that answers questions about our product.

RULES:
- Only answer questions about our product
- If you don't know, say "I don't know"
- Keep responses concise (under 100 words)
- Never make up information

CONTEXT:
{context}`;

const userPrompt = `Question: {question}`;
```

### Few-Shot Examples
```typescript
const prompt = `Classify the sentiment of customer feedback.

Examples:
Input: "Love this product!"
Output: positive

Input: "Worst purchase ever"
Output: negative

Input: "It works fine"
Output: neutral

Input: "${customerFeedback}"
Output:`;
```

### Chain of Thought
```typescript
const prompt = `Solve this step by step:

Question: ${question}

Let's think through this:
1. First, identify the key information
2. Then, determine the approach
3. Finally, calculate the answer

Step-by-step solution:`;
```

## API Integration

### OpenAI Pattern
```typescript
import OpenAI from 'openai';

const openai = new OpenAI({ apiKey: process.env.OPENAI_API_KEY });

async function chat(messages: Message[]): Promise<string> {
  const response = await openai.chat.completions.create({
    model: 'gpt-4',
    messages,
    temperature: 0.7,
    max_tokens: 500,
  });

  return response.choices[0].message.content ?? '';
}
```

### Anthropic Pattern
```typescript
import Anthropic from '@anthropic-ai/sdk';

const anthropic = new Anthropic({ apiKey: process.env.ANTHROPIC_API_KEY });

async function chat(prompt: string): Promise<string> {
  const response = await anthropic.messages.create({
    model: 'claude-3-opus-20240229',
    max_tokens: 1024,
    messages: [{ role: 'user', content: prompt }],
  });

  return response.content[0].type === 'text'
    ? response.content[0].text
    : '';
}
```

### Streaming Responses
```typescript
async function* streamChat(prompt: string) {
  const stream = await openai.chat.completions.create({
    model: 'g