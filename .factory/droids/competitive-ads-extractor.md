---
name: competitive-ads-extractor
description: Extracts and analyzes competitors' ads from ad libraries (Facebook, LinkedIn,
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Competitive Ads Extractor

This skill extracts your competitors' ads from ad libraries and analyzes what's working—the problems they're highlighting, use cases they're targeting, and copy/creative that's resonating.

## When to Use This Skill

- Researching competitor ad strategies
- Finding inspiration for your own ads
- Understanding market positioning
- Identifying successful ad patterns
- Analyzing messaging that works
- Discovering new use cases or pain points
- Planning ad campaigns with proven concepts

## What This Skill Does

1. **Extracts Ads**: Scrapes ads from Facebook Ad Library, LinkedIn, etc.
2. **Captures Screenshots**: Saves visual copies of all ads
3. **Analyzes Messaging**: Identifies problems, use cases, and value props
4. **Categorizes Ads**: Groups by theme, audience, or format
5. **Identifies Patterns**: Finds common successful approaches
6. **Provides Insights**: Explains why certain ads likely perform well

## How to Use

### Basic Extraction

```
Extract all current ads from [Competitor Name] on Facebook Ad Library
```

```
Scrape ads from [Company] and analyze their messaging
```

### Specific Analysis

```
Get all ads from [Competitor] focusing on their messaging 
about [specific problem]. What pain points are they highlighting?
```

### Competitive Set

```
Extract ads from these 5 competitors: [list]. 
Compare their approaches and tell me what's working.
```

### Specific Platform

```
Get LinkedIn ads from [Competitor] and analyze their 
B2B positioning strategy
```

## Example

**User**: "Extract ads from Notion on Facebook Ad Library and tell me what messaging is working for them."

**Process**:
```
Accessing Facebook Ad Library...
Searching for: Notion
Found: 23 active ads

Extracting screenshots...
[████████████████████] 100%

Saved to: competitor-ads/notion/
- ad-001-collaboration.png
- ad-002-productivity.png
- ad-003-templates.png
...

Analyzing messaging...
```

**Output**:
```
# Notion Ad Analysis

## Overview
- Total Ads: 2