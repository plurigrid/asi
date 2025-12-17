# SkillCreator Ranking Algorithm

## The Problem

Smithery: 18,306 skills
SkillsMP: 26,161 skills
Most of it: Noise.

## The Solution

**Stars = Community Validation = Quality Signal**

We scrape GitHub, track stars, and rank accordingly. Simple. Effective.

---

## Discovery: Finding Skills on GitHub

### Method 1: File Search (Primary)
```
Search: "filename:SKILL.md"
Filter: Has frontmatter with name/description
Result: All repos with SKILL.md files
```

### Method 2: Topic Search
```
Topics: "claude-skills", "claude-skill", "anthropic-skills"
Result: Repos tagged as skills
```

### Method 3: Code Search
```
Search: "---\nname:" in:file filename:SKILL.md
Result: Properly formatted skills only
```

### Method 4: Crawl Known Sources
```
Sources:
- github.com/anthropics/skills
- github.com/obra/superpowers
- github.com/ComposioHQ/awesome-claude-skills
- github.com/VoltAgent/awesome-claude-skills
- Links from awesome lists
```

---

## Data Model

```typescript
interface Skill {
  // Identity
  id: string;                    // UUID
  name: string;                  // From SKILL.md frontmatter
  slug: string;                  // URL-safe name

  // Content
  description: string;           // From SKILL.md frontmatter
  content: string;               // Full SKILL.md content

  // Source
  github_url: string;            // Full repo URL
  github_path: string;           // Path to SKILL.md
  author: string;                // GitHub username/org

  // Ranking Signals
  stars: number;                 // GitHub stars (PRIMARY)
  forks: number;                 // GitHub forks
  watchers: number;              // GitHub watchers

  // Freshness
  last_commit: Date;             // Last commit to skill
  created_at: Date;              // When we discovered it
  updated_at: Date;              // Last scrape update

  // Classification
  category: string;              // development, document, etc.
  tags: string[];                // Additional tags

  // Quality
  has_install_script: boolean;   // Has install.sh
  has_examples: boolean;         // Has usage examples
  is_verified: boolean;          // Manually verified by us

  // Computed
  score: number;                 // Ranking score
}
```

---

## Ranking Formula

### Base Score
```
base_score = stars
```

### Recency Boost
```
days_since_update = (now - last_commit) / (1000 * 60 * 60 * 24)

if days_since_update < 7:
  recency_boost = 1.5
elif days_since_update < 30:
  recency_boost = 1.2
elif days_since_update < 90:
  recency_boost = 1.0
elif days_since_update < 365:
  recency_boost = 0.8
else:
  recency_boost = 0.5
```

### Quality Multiplier
```
quality_multiplier = 1.0

if has_install_script:
  quality_multiplier += 0.1
if has_examples:
  quality_multiplier += 0.1
if is_verified:
  quality_multiplier += 0.3
if author == "anthropics":
  quality_multiplier += 0.5  // Official skills boost
```

### Final Score
```
score = base_score * recency_boost * quality_multiplier
```

### Example Calculations
```
Skill: frontend-design (anthropics)
- stars: 46,100
- last_commit: 2 days ago
- has_install: true, has_examples: true, is_verified: true

score = 46100 * 1.5 * (1 + 0.1 + 0.1 + 0.3 + 0.5)
      = 46100 * 1.5 * 2.0
      = 138,300

---

Skill: random-community-skill
- stars: 15
- last_commit: 200 days ago
- has_install: false, has_examples: false, is_verified: false

score = 15 * 0.5 * 1.0
      = 7.5
```

---

## Scraping Architecture

### GitHub API Approach
```
Endpoint: api.github.com
Auth: Personal Access Token
Rate Limit: 5,000 requests/hour

Process:
1. Search for SKILL.md files
2. For each result, get repo metadata (stars, forks, etc.)
3. Fetch SKILL.md content
4. Parse frontmatter
5. Store in database
```

### Rate Limit Strategy
```
5,000 requests/hour = ~83 requests/minute

Budget per skill:
- 1 request: Search result (batched, 100 per request)
- 1 request: Repo metadata
- 1 request: File content

Per 100 skills = ~102 requests
Full scan of 1000 skills = ~1,020 requests (~15 min)
```

### Cron Schedule
```
Daily: Full refresh of star counts
Weekly: Full re-scrape for new skills
On-demand: When user submits new skill
```

---

## Implementation

### Tech Stack
```
- Supabase: Database + Edge Functions
- GitHub API: Data source
- Vercel Cron: Scheduled jobs
- Redis (Upstash): Rate limit tracking
```

### Edge Function: Scraper
```typescript
// /api/scrape-github

import { Octokit } from "@octokit/rest";
import { createClient } from "@supabase/supabase-js";

const octokit = new Octokit({ auth: process.env.GITHUB_TOKEN });
const supabase = createClient(SUPABASE_URL, SUPABASE_KEY);

async function scrapeSkills() {
  // 1. Search for SKILL.md files
  const results = await octokit.search.code({
    q: "filename:SKILL.md",
    per_page: 100
  });

  for (const item of results.data.items) {
    // 2. Get repo metadata
    const repo = await octokit.repos.get({
      owner: item.repository.owner.login,
      repo: item.repository.name
    });

    // 3. Get file content
    const file = await octokit.repos.getContent({
      owner: item.repository.owner.login,
      repo: item.repository.name,
      path: item.path
    });

    // 4. Parse and store
    const content = Buffer.from(file.data.content, 'base64').toString();
    const { name, description } = parseFrontmatter(content);

    await supabase.from('shared_skills').upsert({
      id: generateId(item.repository.full_name, item.path),
      name,
      description,
      content,
      github_url: item.repository.html_url,
      github_path: item.path,
      author: item.repository.owner.login,
      stars: repo.data.stargazers_count,
      forks: repo.data.forks_count,
      last_commit: repo.data.pushed_at,
      score: calculateScore(repo.data)
    });
  }
}
```

### Cron Job: Daily Star Update
```typescript
// /api/cron/update-stars

async function updateStars() {
  const skills = await supabase
    .from('shared_skills')
    .select('id, github_url, author')
    .order('score', { ascending: false })
    .limit(500);  // Top 500 only

  for (const skill of skills.data) {
    const [owner, repo] = parseGithubUrl(skill.github_url);

    const repoData = await octokit.repos.get({ owner, repo });

    await supabase
      .from('shared_skills')
      .update({
        stars: repoData.data.stargazers_count,
        score: calculateScore(repoData.data),
        updated_at: new Date()
      })
      .eq('id', skill.id);
  }
}
```

---

## Database Schema Update

```sql
-- Add columns to shared_skills
ALTER TABLE shared_skills ADD COLUMN IF NOT EXISTS
  github_url TEXT,
  github_path TEXT,
  stars INTEGER DEFAULT 0,
  forks INTEGER DEFAULT 0,
  last_commit TIMESTAMPTZ,
  score FLOAT DEFAULT 0,
  category TEXT,
  tags TEXT[],
  has_install_script BOOLEAN DEFAULT FALSE,
  has_examples BOOLEAN DEFAULT FALSE,
  is_verified BOOLEAN DEFAULT FALSE;

-- Index for ranking queries
CREATE INDEX idx_skills_score ON shared_skills(score DESC);
CREATE INDEX idx_skills_category ON shared_skills(category);
CREATE INDEX idx_skills_stars ON shared_skills(stars DESC);
```

---

## API Endpoints

### GET /api/skills
```typescript
// Query params:
// - category: filter by category
// - sort: "stars" | "score" | "recent"
// - limit: number of results
// - offset: pagination

const { data } = await supabase
  .from('shared_skills')
  .select('*')
  .eq('category', category)
  .order('score', { ascending: false })
  .range(offset, offset + limit);
```

### GET /api/skills/[slug]
```typescript
const { data } = await supabase
  .from('shared_skills')
  .select('*')
  .eq('slug', slug)
  .single();
```

### POST /api/skills/submit
```typescript
// User submits a new skill
// We fetch from GitHub and add to queue
const { github_url } = req.body;
await queueSkillForReview(github_url);
```

---

## Display on Frontend

### Skills Directory Page
```
/discover

[Search Bar]

[Category Tabs: All | Development | Document | ...]

[Sort: Stars | Score | Recent]

[Skill Cards Grid]
  - Name
  - Description
  - Stars badge
  - Category tag
  - Install button
```

### Skill Card Component
```jsx
<SkillCard>
  <StarsBadge>{skill.stars.toLocaleString()}</StarsBadge>
  <Title>{skill.name}</Title>
  <Description>{skill.description}</Description>
  <Author>by {skill.author}</Author>
  <Category>{skill.category}</Category>
  <InstallButton onClick={() => copyInstallCommand(skill)} />
</SkillCard>
```

---

## Competitive Advantage

| Feature | Smithery/SkillsMP | SkillCreator |
|---------|-------------------|--------------|
| Total Skills | 26,000+ | 100+ curated |
| Ranking | Basic stars | Score algorithm |
| Quality | No filter | 2+ stars minimum |
| Install | Manual | One-click |
| Create | No | 30-second generator |
| Verification | No | Manual review |

---

## Phase 1: MVP (Dec 20 Launch)

1. [x] Create repo structure
2. [ ] Import 100 curated skills manually
3. [ ] Add star counts from GitHub
4. [ ] Sort by stars on /discover page
5. [ ] Basic install flow

## Phase 2: Automation (Jan 2025)

1. [ ] GitHub API integration
2. [ ] Daily star updates via cron
3. [ ] Weekly new skill discovery
4. [ ] User skill submission
5. [ ] Auto-categorization

## Phase 3: Scale (Feb 2025)

1. [ ] Expand to 500+ curated skills
2. [ ] Advanced search
3. [ ] Skill recommendations
4. [ ] Creator profiles
5. [ ] Skill analytics
