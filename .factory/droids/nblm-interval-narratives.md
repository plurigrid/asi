---
name: nblm-interval-narratives
description: NotebookLM Enterprise API for narrative knowledge synthesis. Creates notebooks as sheaves on interval posets - sources are local sections, audio overviews are global sections via cosheaf pushforward. Integrates Bumpus-Fairbanks-Karvonen compositional temporal reasoning with Gay.jl deterministic coloring. Use when creating, managing, or synthesizing NotebookLM notebooks, adding sources, generating audio overviews, or applying interval-theoretic narrative structures to knowledge bases.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute", "WebSearch", "Create"]
---

# NBLM Interval Narratives

> **Trit**: +1 (PLUS) - Generative synthesis of knowledge into narrative form

NotebookLM Enterprise API operations structured as sheaves on interval posets.
Notebooks = functors from time categories to knowledge categories.

## API Reference (Discovery Engine v1alpha)

Base URL: `https://discoveryengine.googleapis.com/v1alpha`
Project: `projects/{PROJECT_NUMBER}/locations/us`
Auth: `gcloud auth print-access-token`

### Notebooks (NotebookService)

```bash
# List recent notebooks
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  "https://discoveryengine.googleapis.com/v1alpha/projects/${PROJECT_NUMBER}/locations/us/notebookLmApps:recentNotebooks" \
  -X POST -H "Content-Type: application/json" -d '{}'

# Create notebook
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  "https://discoveryengine.googleapis.com/v1alpha/projects/${PROJECT_NUMBER}/locations/us/notebookLmApps" \
  -X POST -H "Content-Type: application/json" \
  -d '{"displayName": "TITLE"}'

# Delete notebooks (batch)
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  "https://discoveryengine.googleapis.com/v1alpha/projects/${PROJECT_NUMBER}/locations/us/notebookLmApps:batchDelete" \
  -X POST -H "Content-Type: application/json" \
  -d '{"names": ["projects/PROJECT_NUM/locations/us/notebookLmApps/NOTEBOOK_ID"]}'
```

### Sources (local sections of the narrative sheaf)

```bash
# Add web source
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  "https://discoveryengine.googleapis.com/v1alpha/projects/${PROJECT_NUMBER}/locations/us/notebookLmApps/${NOTEBOOK_ID}/notebookLmSources" \
  -X POST -H "Content-Type: application/json" \
  -d '{"webUri": "https://example.com/page"}'

# Add inline text source
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  "https://discoveryengine.googleapis.com/v1alpha/projects/${PROJECT_NUMBER}/locations/us/notebookLmApps/${NOTEBOOK_ID}/notebookLmSources" \
  -X POST -H "Content-Type: application/json" \
  -d '{"inlineSource": {"title": "TITLE", "content": "TEXT CONTENT"}}'

# Add YouTube source
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  "https://discoveryengine.googleapis.com/v1alpha/projects/${PROJECT_NUMBER}/locations/us/notebookLmApps/${NOTEBOOK_ID}/notebookLmSources" \
  -X POST -H "Content-Type: application/json" \
  -d '{"youtubeUri": "https://www.youtube.com/watch?v=VIDEO_ID"}'

# Upload file source (PDF, txt, etc.)
nblm sources upload <notebook_id> <file_path>

# Get source details
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  "https://discoveryengine.googleapis.com/v1alpha/projects/${PROJECT_NUMBER}/locations/us/notebookLmApps/${NOTEBOOK_ID}/notebookLmSources/${SOURCE_ID}"

# Delete source
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  "https://discoveryengine.googleapis.com/v1alpha/projects/${PROJECT_NUMBER}/locations/us/notebookLmApps/${NOTEBOOK_ID}/notebookLmSources/${SOURCE_ID}" \
  -X DELETE
```

### Audio Overviews (global section via cosheaf pushforward)

```bash
# Create audio overview (the narrative's global section)
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  "https://discoveryengine.googleapis.com/v1alpha/projects/${PROJECT_NUMBER}/locations/us/notebookLmApps/${NOTEBOOK_ID}/audioOverviews:create" \
  -X POST -H "Content-Type: application/json" \
  -d '{}'

# Create with custom instructions
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  "https://discoveryengine.googleapis.com/v1alpha/projects/${PROJECT_NUMBER}/locations/us/notebookLmApps/${NOTEBOOK_ID}/audioOverviews:create" \
  -X POST -H "Content-Type: application/json" \
  -d '{"instructions": "Focus on the mathematical structure and category theory connections."}'

# Delete audio overview
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  "https://discoveryengine.googleapis.com/v1alpha/projects/${PROJECT_NUMBER}/locations/us/notebookLmApps/${NOTEBOOK_ID}/audioOverviews" \
  -X DELETE
```

### Sharing

Note: The share API endpoint path varies by API version. The nblm CLI uses
`locations/global/notebooks/{id}:share` while the Discovery Engine API uses
`locations/us/notebookLmApps/{id}:share`. Check current API docs for the
correct payload format. Known working example from previous session used HTTP 200:

```bash
# Share notebook (Discovery Engine path)
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  "https://discoveryengine.googleapis.com/v1alpha/projects/${PROJECT_NUMBER}/locations/us/notebookLmApps/${NOTEBOOK_ID}:share" \
  -X POST -H "Content-Type: application/json" \
  -d '{"projectRoleAssignment": {"email": "user@example.com", "role": "PROJECT_ROLE_WRITER"}}'
```

### nblm CLI (Rust)

```bash
# Install
cargo install nblm-cli

# Set project
export NBLM_PROJECT_NUMBER=302712368086

# Notebook operations
nblm notebooks create "Title"
nblm notebooks recent
nblm notebooks delete <id>

# Source operations
nblm sources add <notebook_id> --web "https://url"
nblm sources add <notebook_id> --text "content" --title "Title"
nblm sources add <notebook_id> --youtube "https://youtube.com/watch?v=..."
nblm sources upload <notebook_id> file.pdf
nblm sources get <notebook_id> <source_id>
nblm sources delete <notebook_id> <source_id>

# Audio operations
nblm audio create <notebook_id>
nblm audio create <notebook_id> --instructions "Focus on X"
nblm audio delete <notebook_id>
```

## Interval Narrative Theory (Bumpus-Fairbanks-Karvonen)

### Notebooks as Sheaves on Interval Posets

A notebook N with sources {S_1, ..., S_k} is a **sheaf** F: I_N -> D where:
- I_N = poset of time intervals [a,b] (knowledge provenance windows)
- D = category of text/knowledge spaces
- Sources S_i = local sections F([t_i, t_i]) at points
- Audio overview = global section Gamma(F) via colimit

The **sheaf condition** ensures coherence:
```
F([a,b]) = F([a,p]) x_{F([p,p])} F([p,b])
```
Sources that overlap in topic must agree on shared content.

### Persistent vs Cumulative Narratives

From Bumpus-Fairbanks-Karvonen unified framework:

| Type | Functor | Direction | NotebookLM Analogue |
|------|---------|-----------|---------------------|
| **Persistent** | Restriction (sheaf) | Backward | Source retrieval: zoom into specific section |
| **Cumulative** | Pushforward (cosheaf) | Forward | Audio overview: synthesize all sources into narrative |
| **Decay** | Endofunctor D: I -> I | Temporal | Source staleness, knowledge half-life |

### Ternary Modalities (HYST Semantics)

Each source gets a temporal modality:
- **-1 (MINUS)**: Decaying/historical - source may be outdated
- **0 (ERGODIC)**: Stable/canonical - source is timeless reference
- **+1 (PLUS)**: Accumulating/growing - source is actively updated

```
trit(source) = classify(last_modified, topic_velocity, citation_half_life)
```

### Decay Functors

Knowledge decay on interval [a,b]:
```
D_lambda([a,b]) = [a + lambda*(b-a), b]  -- shrink from left
```
Applied to sources: older sources get smaller effective intervals.

## Gay.jl Integration

### Color-Coded Notebooks

Each notebook gets a deterministic color from its ID:
```bash
# Notebook color = gay_color(NBLM_SEED ^ hash(notebook_id))
gay color_at --seed $(echo "nblm" | shasum | cut -c1-8) --index $NOTEBOOK_INDEX
```

### Source Coloring by Trit

Sources inherit colors from their temporal modality:
- Warm hues (red/orange) = PLUS (+1, accumulating)
- Neutral hues (green/blue) = ERGODIC (0, stable)
- Cool hues (violet/indigo) = MINUS (-1, decaying)

### Audio Overview as Colimit

The audio overview is the **colimit** of the source diagram:
```
colim(F) = coequalizer of all source overlaps
```
Its color = the balanced blend of all source colors (GF(3) sum mod 3).

## Workflow: Interval Game Notebook

Create a notebook capturing the Interval Game narrative theory:

```bash
export PROJECT_NUMBER=302712368086

# 1. Create notebook
NOTEBOOK_ID=$(nblm notebooks create "Interval Game: Narratives on Interval Posets" | jq -r '.name' | rev | cut -d/ -f1 | rev)

# 2. Add sources (local sections)
# Bumpus unified framework paper
nblm sources add $NOTEBOOK_ID --web "https://arxiv.org/abs/2402.00206"

# Fairbanks-Karvonen structured decompositions
nblm sources add $NOTEBOOK_ID --web "https://arxiv.org/abs/2207.06091"

# Inline narrative theory synthesis
nblm sources add $NOTEBOOK_ID --text "$(cat << 'EOF'
Narratives as Sheaves on Interval Posets

The Bumpus-Fairbanks-Karvonen framework unifies persistent and cumulative
data structures through sheaves and cosheaves on interval categories.

Key insight: A narrative is a sheaf F: I_N -> D where I_N is the poset
of intervals [a,b] with a <= b. The sheaf condition ensures that
overlapping narrative segments agree on their intersection.

Persistent narratives use restriction maps (backward): zooming into a
sub-interval preserves information. This models knowledge retrieval.

Cumulative narratives use pushforward maps (forward): combining intervals
synthesizes new information. This models audio overview generation.

The decay endofunctor D: I -> I models knowledge staleness, where
D_lambda([a,b]) = [a + lambda*(b-a), b] shrinks intervals from the left.

HYST semantics add hysteresis: once a source crosses a threshold of
relevance, it remains relevant even as it decays slightly below threshold.

Ternary classification (-1/0/+1) maps naturally to GF(3) trit algebra:
- Decaying sources (-1) need refresh
- Stable sources (0) are canonical references
- Growing sources (+1) are actively contributing
EOF
)" --title "Narrative Theory Synthesis"

# 3. Generate audio overview (global section / cosheaf pushforward)
nblm audio create $NOTEBOOK_ID --instructions "Explain how narratives can be modeled as sheaves on interval posets, connecting persistent and cumulative data structures. Discuss the practical applications to knowledge management and NotebookLM itself."

# 4. Share with collaborator
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  "https://discoveryengine.googleapis.com/v1alpha/projects/${PROJECT_NUMBER}/locations/us/notebookLmApps/${NOTEBOOK_ID}:share" \
  -X POST -H "Content-Type: application/json" \
  -d '{"projectRoleAssignment": {"email": "freemorphism@gmail.com", "role": "PROJECT_ROLE_WRITER"}}'
```

## Triadic Composition

```
bumpus-narratives (0, ERGODIC) -- temporal reasoning framework
  |
  v
nblm-interval-narratives (+1, PLUS) -- generative notebook synthesis
  |
  v
gay-mcp (+1, PLUS) -- deterministic coloring
```

Balancing skill needed: trit -1 (MINUS) for verification.
Candidates: sheaf-cohomology, persistent-homology, skill-validation-gf3

## NSFT: New San Francisco Times Dissemination Factory

Three-channel dissemination pipeline mapped to GF(3) trits:

### Channel -1: AM Radio / Podcast (Audio)
1. Generate English audio overview: `nblm audio create --notebook-id $NB`
2. Translate source text: Google Cloud Translation API (195 languages)
3. Re-synthesize in target language: Google Cloud TTS (63 languages, 2066 voices)

### Channel 0: TV / Video (Visual)
1. Generate diagrams with DisCoPy/tikz-cd colored by Gay.jl
2. Narrate in target language via TTS
3. Compose via Veo/Imagen APIs

### Channel +1: Print / Tabloid (Text)
1. Write as inline text source in NotebookLM
2. Translate via Translation API
3. Generate companion audio overview

### TTS Languages (63 language codes, 2066 voices)

| Language | Code | Voices |
|----------|------|--------|
| Afrikaans | af-ZA | 1 |
| Amharic | am-ET | 4 |
| Arabic | ar-XA | 38 |
| Bengali | bn-IN | 38 |
| Bulgarian | bg-BG | 31 |
| Cantonese | yue-HK | 34 |
| Catalan | ca-ES | 1 |
| Chinese (Mandarin) | cmn-CN | 38 |
| Chinese (Taiwan) | cmn-TW | 6 |
| Czech | cs-CZ | 32 |
| Danish | da-DK | 35 |
| Dutch | nl-NL | 34 |
| Dutch (Belgium) | nl-BE | 34 |
| English (US) | en-US | 99 |
| English (GB) | en-GB | 63 |
| English (AU) | en-AU | 49 |
| English (IN) | en-IN | 49 |
| Estonian | et-EE | 31 |
| Basque | eu-ES | 1 |
| Filipino | fil-PH | 10 |
| Finnish | fi-FI | 32 |
| French | fr-FR | 42 |
| French (Canada) | fr-CA | 45 |
| Galician | gl-ES | 1 |
| German | de-DE | 42 |
| Greek | el-GR | 32 |
| Gujarati | gu-IN | 38 |
| Hebrew | he-IL | 38 |
| Hindi | hi-IN | 46 |
| Croatian | hr-HR | 30 |
| Hungarian | hu-HU | 32 |
| Icelandic | is-IS | 1 |
| Indonesian | id-ID | 38 |
| Italian | it-IT | 40 |
| Japanese | ja-JP | 41 |
| Kannada | kn-IN | 38 |
| Korean | ko-KR | 41 |
| Latvian | lv-LV | 31 |
| Lithuanian | lt-LT | 31 |
| Malay | ms-MY | 8 |
| Malayalam | ml-IN | 38 |
| Marathi | mr-IN | 36 |
| Norwegian | nb-NO | 34 |
| Polish | pl-PL | 34 |
| Portuguese (Brazil) | pt-BR | 43 |
| Portuguese (Portugal) | pt-PT | 4 |
| Punjabi | pa-IN | 38 |
| Romanian | ro-RO | 32 |
| Russian | ru-RU | 18 |
| Serbian | sr-RS | 31 |
| Slovak | sk-SK | 32 |
| Slovenian | sl-SI | 30 |
| Spanish (Spain) | es-ES | 49 |
| Spanish (US) | es-US | 48 |
| Swahili | sw-KE | 30 |
| Swedish | sv-SE | 44 |
| Tamil | ta-IN | 38 |
| Telugu | te-IN | 34 |
| Thai | th-TH | 32 |
| Turkish | tr-TR | 40 |
| Ukrainian | uk-UA | 32 |
| Urdu | ur-IN | 34 |
| Vietnamese | vi-VN | 40 |

### Translation Languages (195 total)

Full text translation available for: Abkhaz, Acehnese, Acholi, Afrikaans, Albanian,
Alur, Amharic, Arabic, Armenian, Assamese, Awadhi, Aymara, Azerbaijani, Balinese,
Bambara, Bashkir, Basque, Batak Karo/Simalungun/Toba, Belarusian, Bemba, Bengali,
Betawi, Bhojpuri, Bikol, Bosnian, Breton, Bulgarian, Buryat, Cantonese, Catalan,
Cebuano, Chichewa, Chinese (Simplified/Traditional), Chuvash, Corsican, Crimean Tatar,
Croatian, Czech, Danish, Dhivehi, Dinka, Dogri, Dombe, Dutch, Dzongkha, English,
Esperanto, Estonian, Ewe, Fijian, Filipino, Finnish, French (FR/CA), Frisian, Fulani,
Ga, Galician, Georgian, German, Greek, Guarani, Gujarati, Haitian Creole, Hakha Chin,
Hausa, Hawaiian, Hebrew, Hiligaynon, Hindi, Hmong, Hungarian, Hunsrik, Icelandic,
Igbo, Ilocano, Indonesian, Irish, Italian, Japanese, Javanese, Kannada, Kapampangan,
Kazakh, Khmer, Kiga, Kinyarwanda, Kituba, Konkani, Korean, Krio, Kurdish (Kurmanji/Sorani),
Kyrgyz, Lao, Latgalian, Latin, Latvian, Ligurian, Limburgish, Lingala, Lithuanian,
Lombard, Luganda, Luo, Luxembourgish, Macedonian, Maithili, Makassar, Malagasy,
Malay (Latin/Jawi), Malayalam, Maltese, Maori, Marathi, Meadow Mari, Meiteilon,
Minang, Mizo, Mongolian, Myanmar, Ndebele, Nepalbhasa, Nepali, Norwegian, Nuer,
Occitan, Odia, Oromo, Pangasinan, Papiamento, Pashto, Persian, Polish, Portuguese
(BR/PT), Punjabi (Gurmukhi/Shahmukhi), Quechua, Romani, Romanian, Rundi, Russian,
Samoan, Sango, Sanskrit, Scots Gaelic, Sepedi, Serbian, Sesotho, Seychellois Creole,
Shan, Shona, Sicilian, Silesian, Sindhi, Sinhala, Slovak, Slovenian, Somali, Spanish,
Sundanese, Swahili, Swati, Swedish, Tajik, Tamil, Tatar, Telugu, Tetum, Thai, Tigrinya,
Tsonga, Tswana, Turkish, Turkmen, Twi, Ukrainian, Urdu, Uyghur, Uzbek, Vietnamese,
Welsh, Xhosa, Yiddish, Yoruba, Yucatec Maya, Zulu

### Multilingual TTS Pipeline

```bash
# Step 1: Translate article text to target language
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  -H "x-goog-user-project: merovingians" \
  "https://translation.googleapis.com/language/translate/v2" \
  -X POST -H "Content-Type: application/json" \
  -d '{"q": "SOURCE_TEXT", "target": "TARGET_LANG_CODE", "source": "en"}'

# Step 2: Synthesize speech in target language
curl -s -H "Authorization: Bearer $(gcloud auth print-access-token)" \
  -H "x-goog-user-project: merovingians" \
  "https://texttospeech.googleapis.com/v1/text:synthesize" \
  -X POST -H "Content-Type: application/json" \
  -d '{
    "input": {"text": "TRANSLATED_TEXT"},
    "voice": {"languageCode": "TARGET_LANG_CODE", "ssmlGender": "NEUTRAL"},
    "audioConfig": {"audioEncoding": "MP3"}
  }'
# Response contains base64-encoded audio in audioContent field
```

## Limitations

- Max 50 sources per notebook
- No direct content query API (read-only metadata)
- Audio overview generation is async (may take minutes)
- Audio overview language is English only (use TTS pipeline for multilingual)
- Sharing requires Google Workspace / Cloud Identity accounts
- No programmatic access to notebook chat/Q&A
- YouTube sources limited to public videos with captions
- No custom voice/persona selection for audio overviews
