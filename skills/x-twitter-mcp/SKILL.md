---
name: x-twitter-mcp
description: MCP server for X/Twitter interaction - profile analysis, thread tracking, and social graph exploration
version: 1.0.0
trit: -1
role: MINUS
color: "#1DA1F2"
---

# x-twitter-mcp

MCP server for interacting with X (Twitter) via API and web scraping, enabling AI agents to analyze profiles, track threads, and explore social graphs.

**Trit**: -1 (MINUS) - Validation/analysis of social signals
**Use Cases**: Profile analysis, thread extraction, sentiment analysis, emergence detection

---

## Overview

This skill wraps X/Twitter interaction as an MCP server, allowing AI agents to:
- Analyze user profiles and posting patterns
- Extract and track conversation threads
- Map social connections and influence
- Detect emergent topics and memes
- Monitor specific accounts or keywords

**Key Insight**: Social media is a distributed learning system. By observing interaction patterns, we can detect:
- Emergent concepts (like "tpot" - tech Twitter subculture)
- Emotional development arcs (user growth over time)
- Information cascades and viral dynamics
- Collective sense-making processes

---

## Case Study: @imitationlearn

### Profile Overview
- **Joined**: August 2024
- **Growth**: ~1200 followers by Jan 2026 (rapid, organic growth)
- **Ratio**: Following:Followers ≈ 1:1 (authentic engagement)
- **Bio**: "the minima are so pretty" (mathematical/optimization interest)
- **Website**: imitationlearn.bearblog.dev (minimalist, markdown-based)

### Posting Themes

1. **Technical AI/ML**
   - "4chan figured out step-by-step reasoning as emergent property of gpt-3"
   - Deep interest in emergence and reasoning

2. **Personal Growth**
   - "emotionally repressed ppl who figured out how to feel more — what did u do?"
   - Active emotional development work

3. **Social Awareness**
   - "holy fuck it's hard to socialize i need to work on that"
   - "any tips for someone just getting into socializing? (not sarcasm)"
   - Public documentation of learning social skills

4. **Cultural Commentary**
   - "i grew up on studio ghibli...now its everywhere...ive lost something sacred"
   - "this isn't enjoyable to me. it's the smoothing out of reality"
   - Critique of cultural commodification

5. **Tech Culture**
   - "wait is tpot just a bunch of nerds"
   - Discovering and naming subcultures

### Temporal Arc

```
Aug 2024: Joins, starts exploring tech Twitter
Dec 2024: Technical observations (GPT-3 reasoning, socialization mechanics)
Mar 2025: Cultural critique (Ghibli commodification, Manifest events)
May 2025: Socialization awareness emerges ("hard to socialize")
Jul 2025: Active emotional growth work ("emotionally repressed ppl")
Sep 2025: Continued introspection and cultural analysis
```

### Analysis: Imitation Learning in Action

**Username Meaning**: "imitation learning" - literally describes the process
- Learning social behaviors through observation
- Publicly documenting experiments and failures
- Meta-awareness of the learning process itself

**Pattern Recognition**:
1. **Technical → Personal** progression (common in tech Twitter)
2. **Observation → Practice** cycle (classic RL)
3. **Public accountability** (social pressure as training signal)

**Emergence Detection**:
- User becoming aware of "tpot" (tech post-rationalist Twitter)
- Discovering implicit cultural norms through collision
- Meta-commentary on discovery process itself

---

## MCP Tools

### x_get_profile

Get profile information for a user.

```json
{
  "name": "x_get_profile",
  "description": "Get user profile information",
  "inputSchema": {
    "type": "object",
    "properties": {
      "username": {"type": "string", "description": "Twitter username (without @)"}
    },
    "required": ["username"]
  }
}
```

### x_get_posts

Get recent posts from a user.

```json
{
  "name": "x_get_posts",
  "description": "Get recent posts from a user",
  "inputSchema": {
    "type": "object",
    "properties": {
      "username": {"type": "string"},
      "limit": {"type": "integer", "default": 20},
      "include_replies": {"type": "boolean", "default": false},
      "since_date": {"type": "string", "format": "date"}
    },
    "required": ["username"]
  }
}
```

### x_get_thread

Extract a full conversation thread.

```json
{
  "name": "x_get_thread",
  "description": "Get full conversation thread",
  "inputSchema": {
    "type": "object",
    "properties": {
      "tweet_id": {"type": "string"},
      "include_quotes": {"type": "boolean", "default": true}
    },
    "required": ["tweet_id"]
  }
}
```

### x_search

Search for tweets matching a query.

```json
{
  "name": "x_search",
  "description": "Search tweets by keyword or phrase",
  "inputSchema": {
    "type": "object",
    "properties": {
      "query": {"type": "string"},
      "limit": {"type": "integer", "default": 20},
      "filter": {"type": "string", "enum": ["top", "latest", "people", "media"]}
    },
    "required": ["query"]
  }
}
```

### x_analyze_profile

Analyze posting patterns and themes for a user.

```json
{
  "name": "x_analyze_profile",
  "description": "Analyze user posting patterns and themes",
  "inputSchema": {
    "type": "object",
    "properties": {
      "username": {"type": "string"},
      "lookback_days": {"type": "integer", "default": 30}
    },
    "required": ["username"]
  }
}
```

**Example Output**:
```json
{
  "username": "imitationlearn",
  "themes": [
    {"topic": "AI/ML emergence", "frequency": 0.25},
    {"topic": "personal_growth", "frequency": 0.20},
    {"topic": "cultural_critique", "frequency": 0.15},
    {"topic": "social_learning", "frequency": 0.15},
    {"topic": "philosophy", "frequency": 0.10}
  ],
  "posting_frequency": {
    "avg_per_day": 3.2,
    "most_active_hour": 14,
    "reply_ratio": 0.45
  },
  "emotional_arc": {
    "trend": "introspective_to_social",
    "sentiment_trajectory": "increasing_openness",
    "milestones": [
      {"date": "2024-12-21", "event": "questioning social mechanics"},
      {"date": "2025-05-12", "event": "socialization awareness"},
      {"date": "2025-07-16", "event": "active emotional growth"}
    ]
  }
}
```

### x_get_social_graph

Map connections and influence for a user.

```json
{
  "name": "x_get_social_graph",
  "description": "Map social connections and influence",
  "inputSchema": {
    "type": "object",
    "properties": {
      "username": {"type": "string"},
      "depth": {"type": "integer", "default": 1, "maximum": 3},
      "include_followers": {"type": "boolean", "default": false}
    },
    "required": ["username"]
  }
}
```

### x_detect_emergence

Detect emergent topics across a set of users.

```json
{
  "name": "x_detect_emergence",
  "description": "Detect emergent topics and memes",
  "inputSchema": {
    "type": "object",
    "properties": {
      "usernames": {"type": "array", "items": {"type": "string"}},
      "time_window_hours": {"type": "integer", "default": 24}
    },
    "required": ["usernames"]
  }
}
```

---

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│ Claude Desktop / AI Agent                                   │
└─────────────────────────┬───────────────────────────────────┘
                          │ JSON-RPC 2.0 (stdio)
                          ▼
┌─────────────────────────────────────────────────────────────┐
│ x-twitter-mcp-server.bb (Babashka)                          │
│ ├─ Profile fetcher                                          │
│ ├─ Thread extractor                                         │
│ ├─ Sentiment analyzer                                       │
│ └─ Emergence detector                                       │
└─────────────────────────┬───────────────────────────────────┘
                          │
                          ├─► Twitter API v2 (with bearer token)
                          ├─► Web scraping (nitter.net fallback)
                          └─► DuckDB (local cache)
                          
┌─────────────────────────────────────────────────────────────┐
│ DuckDB: twitter_cache.db                                    │
│ ├─ profiles (username, bio, followers, etc.)                │
│ ├─ posts (tweet_id, content, sentiment, etc.)               │
│ ├─ threads (conversation graphs)                            │
│ └─ themes (emergent topics over time)                       │
└─────────────────────────────────────────────────────────────┘
```

---

## Implementation

### Babashka MCP Server

```clojure
#!/usr/bin/env bb

(ns x-twitter-mcp
  (:require [cheshire.core :as json]
            [babashka.process :as p]
            [babashka.http-client :as http]
            [clojure.string :as str]))

(def server-info
  {:name "x-twitter-mcp"
   :version "1.0.0"
   :protocolVersion "2024-11-05"})

(def tools
  [{:name "x_get_profile"
    :description "Get user profile information"
    :inputSchema {:type "object"
                  :properties {:username {:type "string"}}
                  :required ["username"]}}
   {:name "x_get_posts"
    :description "Get recent posts from a user"
    :inputSchema {:type "object"
                  :properties {:username {:type "string"}
                               :limit {:type "integer" :default 20}
                               :include_replies {:type "boolean" :default false}}
                  :required ["username"]}}
   {:name "x_analyze_profile"
    :description "Analyze posting patterns and themes"
    :inputSchema {:type "object"
                  :properties {:username {:type "string"}
                               :lookback_days {:type "integer" :default 30}}
                  :required ["username"]}}
   {:name "x_detect_emergence"
    :description "Detect emergent topics across users"
    :inputSchema {:type "object"
                  :properties {:usernames {:type "array" :items {:type "string"}}
                               :time_window_hours {:type "integer" :default 24}}
                  :required ["usernames"]}}])

;; Twitter API v2 client
(defn twitter-api-get [endpoint params]
  (let [bearer-token (System/getenv "TWITTER_BEARER_TOKEN")
        url (str "https://api.twitter.com/2/" endpoint)
        response (http/get url {:headers {"Authorization" (str "Bearer " bearer-token)}
                                :query-params params})]
    (json/parse-string (:body response) true)))

;; Fallback: Web scraping via nitter
(defn nitter-scrape-profile [username]
  (let [url (str "https://nitter.net/" username)
        html (slurp url)]
    (parse-nitter-html html)))

(defn get-profile [username]
  (try
    (twitter-api-get (str "users/by/username/" username)
                     {:user.fields "description,created_at,public_metrics"})
    (catch Exception e
      (nitter-scrape-profile username))))

(defn get-posts [username limit include-replies]
  (let [user (get-profile username)
        user-id (:id user)]
    (twitter-api-get (str "users/" user-id "/tweets")
                     {:max_results limit
                      :exclude (when-not include-replies "replies")
                      :tweet.fields "created_at,public_metrics"})))

(defn analyze-profile [username lookback-days]
  (let [posts (get-posts username 200 true)
        themes (extract-themes posts)
        patterns (analyze-patterns posts)
        emotional-arc (detect-emotional-arc posts)]
    {:username username
     :themes themes
     :posting_frequency patterns
     :emotional_arc emotional-arc}))

(defn extract-themes [posts]
  ;; Simple keyword frequency + clustering
  (let [all-text (str/join " " (map :text posts))
        keywords (extract-keywords all-text)
        clusters (cluster-keywords keywords)]
    (map (fn [[topic freq]] 
           {:topic topic :frequency (float freq)})
         (take 10 clusters))))

(defn detect-emotional-arc [posts]
  ;; Sentiment analysis over time
  (let [sorted (sort-by :created_at posts)
        sentiments (map analyze-sentiment sorted)
        trend (compute-trend sentiments)
        milestones (find-inflection-points sorted sentiments)]
    {:trend trend
     :sentiment_trajectory (classify-trajectory sentiments)
     :milestones milestones}))

(defn handle-tool-call [{:keys [name arguments]}]
  (case name
    "x_get_profile"
    {:content [{:type "text"
                :text (json/generate-string 
                       (get-profile (:username arguments))
                       {:pretty true})}]}
    
    "x_get_posts"
    {:content [{:type "text"
                :text (json/generate-string
                       (get-posts (:username arguments)
                                  (or (:limit arguments) 20)
                                  (or (:include_replies arguments) false))
                       {:pretty true})}]}
    
    "x_analyze_profile"
    {:content [{:type "text"
                :text (json/generate-string
                       (analyze-profile (:username arguments)
                                        (or (:lookback_days arguments) 30))
                       {:pretty true})}]}
    
    "x_detect_emergence"
    {:content [{:type "text"
                :text (json/generate-string
                       (detect-emergence (:usernames arguments)
                                         (or (:time_window_hours arguments) 24))
                       {:pretty true})}]}
    
    {:content [{:type "text" :text (str "Unknown tool: " name)}]
     :isError true}))
```

---

## DuckDB Schema

```sql
-- Profiles table
CREATE TABLE profiles (
    username VARCHAR PRIMARY KEY,
    display_name VARCHAR,
    bio TEXT,
    website VARCHAR,
    joined_date DATE,
    followers INTEGER,
    following INTEGER,
    verified BOOLEAN,
    fetched_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Posts table
CREATE TABLE posts (
    tweet_id VARCHAR PRIMARY KEY,
    username VARCHAR REFERENCES profiles(username),
    content TEXT,
    posted_at TIMESTAMP,
    likes INTEGER,
    retweets INTEGER,
    replies INTEGER,
    is_reply BOOLEAN,
    reply_to_id VARCHAR,
    sentiment_score FLOAT,
    themes JSON
);

-- Themes table (aggregated over time)
CREATE TABLE themes (
    id INTEGER PRIMARY KEY,
    username VARCHAR REFERENCES profiles(username),
    theme VARCHAR,
    frequency FLOAT,
    detected_at TIMESTAMP,
    time_window_days INTEGER
);

-- Social graph edges
CREATE TABLE follows (
    follower_username VARCHAR,
    followee_username VARCHAR,
    detected_at TIMESTAMP,
    PRIMARY KEY (follower_username, followee_username)
);

-- Emergent topics
CREATE TABLE emergent_topics (
    topic_id INTEGER PRIMARY KEY,
    topic_name VARCHAR,
    first_seen TIMESTAMP,
    peak_velocity FLOAT,
    participating_users JSON,
    related_keywords JSON
);
```

### Queries

```sql
-- User posting frequency over time
SELECT 
    DATE_TRUNC('week', posted_at) as week,
    COUNT(*) as posts_per_week,
    AVG(sentiment_score) as avg_sentiment
FROM posts
WHERE username = 'imitationlearn'
GROUP BY week
ORDER BY week DESC;

-- Detect emergence (sudden topic spikes)
WITH recent_themes AS (
  SELECT 
    theme,
    COUNT(DISTINCT username) as user_count,
    AVG(frequency) as avg_freq
  FROM themes
  WHERE detected_at > CURRENT_TIMESTAMP - INTERVAL '24 hours'
  GROUP BY theme
)
SELECT * FROM recent_themes
WHERE user_count > 5
ORDER BY user_count DESC, avg_freq DESC;

-- Emotional arc (sentiment trajectory)
SELECT 
    DATE_TRUNC('month', posted_at) as month,
    AVG(sentiment_score) as sentiment,
    STDDEV(sentiment_score) as variance,
    COUNT(*) as post_count
FROM posts
WHERE username = 'imitationlearn'
GROUP BY month
ORDER BY month;

-- Social graph clustering
WITH RECURSIVE graph AS (
  SELECT follower_username as user, 0 as depth
  FROM follows WHERE follower_username = 'imitationlearn'
  UNION ALL
  SELECT f.followee_username, g.depth + 1
  FROM follows f
  JOIN graph g ON f.follower_username = g.user
  WHERE g.depth < 2
)
SELECT user, COUNT(*) as connections
FROM graph
GROUP BY user
ORDER BY connections DESC;
```

---

## Analysis Patterns

### Pattern 1: Imitation Learning Detection

**Signals**:
1. Meta-commentary on social interaction
2. Explicit questions about social norms
3. Public documentation of experiments
4. Temporal progression from observation → practice

**@imitationlearn Example**:
```
Dec 2024: "How does a porn bot...find my obscure reply?" (observation)
May 2025: "holy fuck it's hard to socialize" (awareness)
May 2025: "any tips for someone just getting into socializing?" (seeking guidance)
Jul 2025: "emotionally repressed ppl...what did u do?" (active learning)
```

### Pattern 2: Emergence Detection

**Method**:
1. Monitor keyword frequency across cohort
2. Detect sudden spikes (>3σ from baseline)
3. Identify "patient zero" users
4. Map diffusion through social graph

**Example: "tpot" emergence**
- Originated as inside joke (~2020)
- Crystallized as identifier (~2022)
- Now broadly used with shared meaning (~2024)
- User discovers: "wait is tpot just a bunch of nerds" (2025)

### Pattern 3: Cultural Commodification Critique

**Signal**: Expressions of loss when niche culture goes mainstream

**@imitationlearn Example**:
```
"i grew up on studio ghibli. i come back to it for comfort...
now its everywhere, everything. ive lost something sacred.
this is different...it's the smoothing out of reality."
```

**Analysis**: Awareness of Goodhart's Law in cultural space
- When niche culture becomes target (mainstream), it loses what made it valuable
- "Smoothing out of reality" = loss of authentic roughness

---

## GF(3) Integration

```
Triad: Social Media Analysis

x-twitter-mcp (-1, MINUS)     # Validation via social proof/consensus
gay-mcp (0, ERGODIC)          # Deterministic color coding of users/topics
bluesky-jetstream (+1, PLUS)  # Generative alternative protocol

Sum: -1 + 0 + 1 ≡ 0 (mod 3) ✓
```

**Interpretation**:
- **Twitter (MINUS)**: Validates ideas through likes, retweets, engagement
- **Gay.jl (ERGODIC)**: Assigns deterministic colors to users based on behavioral patterns
- **Bluesky (PLUS)**: Generates new decentralized social primitives (AT Protocol)

---

## Privacy & Ethics

### Principles

1. **Public Data Only**: Only access publicly visible posts
2. **Rate Limiting**: Respect API limits (300 requests/15min for v2)
3. **Caching**: Use DuckDB to minimize API calls
4. **No Automation**: Never automate likes, follows, or replies without disclosure
5. **Anonymization**: When sharing analyses, anonymize unless public figures
6. **Opt-Out**: Respect user privacy preferences

### Authorized Use Cases

✅ **Allowed**:
- Academic research on emergence and collective behavior
- Personal profile analysis for self-reflection
- Trend detection and forecasting
- Sentiment analysis of public discourse
- Social graph research

❌ **Prohibited**:
- Automated engagement without disclosure
- Scraping protected accounts
- Training models on user data without consent
- Manipulative behavior (astroturfing, sockpuppets)
- Harassment or doxxing

---

## Setup

### 1. Get Twitter API Access

```bash
# Apply for Twitter API v2 access
open https://developer.twitter.com/en/portal/dashboard

# Set bearer token
export TWITTER_BEARER_TOKEN="your_token_here"
```

### 2. Alternative: Web Scraping (No API Key)

```bash
# Use nitter.net as fallback
export X_SCRAPING_METHOD="nitter"
```

### 3. Claude Desktop Config

```json
{
  "mcpServers": {
    "x-twitter": {
      "command": "bb",
      "args": ["/Users/bob/ies/plurigrid/asi/skills/x-twitter-mcp/x-twitter-mcp-server.bb"],
      "env": {
        "TWITTER_BEARER_TOKEN": "${TWITTER_BEARER_TOKEN}"
      }
    }
  }
}
```

---

## Related Skills

- **bluesky-jetstream** - Alternative social protocol (AT Protocol)
- **gay-mcp** - Deterministic coloring for social graph visualization
- **bisimulation-game** - Compare user behaviors across platforms
- **cognitive-surrogate** - Learn from social interaction patterns
- **agent-o-rama** - Model social learning as agent training
- **low-discrepancy-sequences** - Sample social graph uniformly

---

## Future Enhancements

### 1. Real-Time Streaming

```clojure
(defn subscribe-to-user [username callback]
  (let [stream (twitter-api-stream "tweets" {:user username})]
    (doseq [tweet stream]
      (callback (analyze-tweet tweet)))))
```

### 2. Cross-Platform Analysis

```clojure
(defn compare-platforms [username]
  {:twitter (analyze-twitter-profile username)
   :bluesky (analyze-bluesky-profile username)
   :mastodon (analyze-mastodon-profile username)
   :behavioral_diff (compute-behavioral-delta)})
```

### 3. Predictive Modeling

```sql
-- Train on historical arcs to predict future sentiment
CREATE TABLE sentiment_predictions AS
WITH historical AS (
  SELECT username, posted_at, sentiment_score,
         LAG(sentiment_score, 7) OVER (PARTITION BY username ORDER BY posted_at) as prev_week
  FROM posts
)
SELECT username, 
       regr_slope(sentiment_score, prev_week) as sentiment_velocity,
       sentiment_score + (regr_slope(sentiment_score, prev_week) * 7) as predicted_next_week
FROM historical;
```

---

**Status**: Design complete, requires API credentials for deployment
**Trit**: -1 (MINUS - Social validation and consensus)
**License**: MIT (respect Twitter ToS and rate limits)
