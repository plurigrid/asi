# Music Topos Framework REST API Documentation

## Overview

The Music Topos Framework provides a REST API for analyzing music through eight integrated music theory categories simultaneously. All endpoints return JSON and support CORS for cross-origin requests.

**Base URL**: `http://localhost:4567` (or deployed server URL)
**API Version**: 1.0.0
**Framework Version**: 1.0.0

---

## Quick Start

### Running the Server

```bash
ruby api/music_topos_server.rb
```

The server will start on `http://localhost:4567` and print available endpoints.

### Simple Test Request

```bash
curl -X POST http://localhost:4567/analyze/progression \
  -H "Content-Type: application/json" \
  -d '{
    "progressions": [
      ["C", "E", "G"],
      ["F", "A", "C"],
      ["G", "B", "D"],
      ["C", "E", "G"]
    ],
    "key": "C"
  }'
```

This analyzes the classic I-IV-V-I progression through all 8 categories.

---

## Authentication

Currently, the API requires no authentication. All endpoints are publicly accessible. Future versions may support API keys or OAuth.

---

## Status Endpoints

### Health Check

**Endpoint**: `GET /health`

**Description**: Check if the API service is running and healthy.

**Response**:
```json
{
  "status": "ok",
  "service": "Music Topos Framework API",
  "version": "1.0.0",
  "categories": [4, 5, 6, 7, 8, 9, 10, 11]
}
```

**Status Code**: 200

---

### Framework Status

**Endpoint**: `GET /status`

**Description**: Get detailed framework status and metadata.

**Response**:
```json
{
  "framework": "Music Topos Framework v1.0.0 (8 categories)",
  "metadata": {
    "name": "Music Topos Framework",
    "version": "1.0.0",
    "created": "2025-12-25T00:00:00Z",
    "categories": 8,
    "test_coverage": "27/27 (100%)"
  },
  "worlds_loaded": 8,
  "categories": [4, 5, 6, 7, 8, 9, 10, 11],
  "test_coverage": "27/27 (100%)",
  "status": "Production Ready"
}
```

**Status Code**: 200

---

## Analysis Endpoints

### Analyze Single Chord

**Endpoint**: `POST /analyze/chord`

**Description**: Analyze a single chord through all 8 categories simultaneously.

**Request Body**:
```json
{
  "notes": ["C", "E", "G"]
}
```

**Parameters**:
- `notes` (required): Array of note names (C, D, E, F, G, A, B, C#, D#, F#, G#, A#, Db, Eb, Gb, Ab, Bb)

**Response**:
```json
{
  "success": true,
  "chord": ["C", "E", "G"],
  "analyses": {
    "4": {
      "category": "Group Theory",
      "permutations": 1,
      "composition_valid": true
    },
    "5": {
      "category": "Harmonic Function",
      "functions": ["tonic"],
      "valid_progression": true,
      "cadence": null
    },
    "6": {
      "category": "Modulation",
      "modulation_paths": 0,
      "circle_of_fifths_movement": true
    },
    "7": {
      "category": "Voice Leading",
      "chord_count": 1,
      "voice_motion_analysis": "ready"
    },
    "8": {
      "category": "Progressions",
      "progression_length": 1,
      "harmonic_closure": "verified"
    },
    "9": {
      "category": "Structure",
      "phrase_structure": "analyzed"
    },
    "10": {
      "category": "Form",
      "structural_role": "determined"
    },
    "11": {
      "category": "Spectral",
      "total_harmonics": 3
    }
  }
}
```

**Status Codes**:
- 200: Success
- 400: Invalid input

---

### Analyze Chord Progression

**Endpoint**: `POST /analyze/progression`

**Description**: Analyze a chord progression through all 8 categories simultaneously.

**Request Body**:
```json
{
  "progressions": [
    ["C", "E", "G"],
    ["F", "A", "C"],
    ["G", "B", "D"],
    ["C", "E", "G"]
  ],
  "key": "C",
  "is_minor": false
}
```

**Parameters**:
- `progressions` (required): Array of chords, where each chord is an array of note names
- `key` (optional): Key context (default: "C")
- `is_minor` (optional): Is the key minor? (default: false)

**Response** (abbreviated):
```json
{
  "success": true,
  "progression": [
    ["C", "E", "G"],
    ["F", "A", "C"],
    ["G", "B", "D"],
    ["C", "E", "G"]
  ],
  "key": "C",
  "is_minor": false,
  "analyses_by_category": {
    "4": {
      "analysis": {
        "category": "Group Theory",
        "permutations": 4,
        "composition_valid": true
      }
    },
    "5": {
      "analysis": {
        "category": "Harmonic Function",
        "functions": ["tonic", "subdominant", "dominant", "tonic"],
        "valid_progression": true,
        "cadence": "authentic"
      }
    },
    ...
  }
}
```

**Status Codes**:
- 200: Success
- 400: Invalid input

**Example**: Authentic Cadence (V-I)

```bash
curl -X POST http://localhost:4567/analyze/progression \
  -H "Content-Type: application/json" \
  -d '{
    "progressions": [
      ["G", "B", "D"],
      ["C", "E", "G"]
    ],
    "key": "C"
  }'
```

**Example**: Bach Chorale (I-vi-IV-V)

```bash
curl -X POST http://localhost:4567/analyze/progression \
  -H "Content-Type: application/json" \
  -d '{
    "progressions": [
      ["C", "E", "G"],
      ["A", "C", "E"],
      ["F", "A", "C"],
      ["G", "B", "D"]
    ],
    "key": "C"
  }'
```

---

### Analyze Specific Category

**Endpoint**: `POST /analyze/category/:category_num`

**Description**: Analyze a chord progression through a specific category only.

**Parameters**:
- `category_num` (path parameter): Category number (4-11)
- `progressions` (required, body): Array of chords
- `key` (optional, body): Key context (default: "C")
- `is_minor` (optional, body): Is minor key? (default: false)

**Response**:
```json
{
  "success": true,
  "category": 5,
  "progression": [["C", "E", "G"], ["G", "B", "D"]],
  "analysis": {
    "analysis": {
      "category": "Harmonic Function",
      "functions": ["tonic", "dominant"],
      "valid_progression": true,
      "cadence": "authentic"
    }
  }
}
```

**Example**: Harmonic Function Analysis Only

```bash
curl -X POST http://localhost:4567/analyze/category/5 \
  -H "Content-Type: application/json" \
  -d '{
    "progressions": [
      ["C", "E", "G"],
      ["G", "B", "D"],
      ["C", "E", "G"]
    ],
    "key": "C"
  }'
```

**Example**: Voice Leading Analysis Only

```bash
curl -X POST http://localhost:4567/analyze/category/7 \
  -H "Content-Type: application/json" \
  -d '{
    "progressions": [
      ["C", "E", "G"],
      ["F", "A", "C"]
    ],
    "key": "C"
  }'
```

---

### Validate Cross-Category Coherence

**Endpoint**: `POST /validate/coherence`

**Description**: Check that analyses are consistent across all 8 categories.

**Request Body**:
```json
{
  "progressions": [
    ["C", "E", "G"],
    ["F", "A", "C"],
    ["G", "B", "D"],
    ["C", "E", "G"]
  ],
  "key": "C"
}
```

**Response**:
```json
{
  "success": true,
  "coherent": true,
  "validations": {
    "all_categories_present": true,
    "progression_length_consistent": true,
    "harmonic_and_structure_agree": true
  },
  "progression": [
    ["C", "E", "G"],
    ["F", "A", "C"],
    ["G", "B", "D"],
    ["C", "E", "G"]
  ]
}
```

**Status Codes**:
- 200: Success
- 400: Invalid input

---

## Category Endpoints

### List All Categories

**Endpoint**: `GET /categories`

**Description**: Get information about all 8 music theory categories.

**Response**:
```json
{
  "total_categories": 8,
  "categories": {
    "4": {
      "name": "Group Theory",
      "description": "Permutations and symmetries in pitch space (S₁₂)",
      "tests": 8
    },
    "5": {
      "name": "Harmonic Function",
      "description": "Functional harmony and cadences (T/S/D cycle)",
      "tests": 6
    },
    "6": {
      "name": "Modulation",
      "description": "Key changes and transposition",
      "tests": 7
    },
    "7": {
      "name": "Voice Leading",
      "description": "Polyphonic voice leading (SATB)",
      "tests": 6
    },
    "8": {
      "name": "Progressions",
      "description": "Harmony and chord progressions",
      "tests": 4
    },
    "9": {
      "name": "Structure",
      "description": "Structural tonality and cadences",
      "tests": 3
    },
    "10": {
      "name": "Form",
      "description": "Musical forms and large-scale structure",
      "tests": 3
    },
    "11": {
      "name": "Spectral Analysis",
      "description": "Harmonic content and timbre",
      "tests": 3
    }
  }
}
```

**Status Code**: 200

---

### Get Category Details

**Endpoint**: `GET /categories/:num`

**Description**: Get detailed information about a specific category.

**Parameters**:
- `num` (path parameter): Category number (4-11)

**Response**:
```json
{
  "success": true,
  "category": 5,
  "name": "Harmonic Function",
  "metadata": {
    "name": "Harmonic Function World",
    "objects_count": 3,
    "metric_type": "functional_distance"
  }
}
```

**Status Codes**:
- 200: Success
- 404: Category not found

---

## Example Endpoints

### Get Example Progressions

**Endpoint**: `GET /examples`

**Description**: Get pre-built example progressions for testing.

**Response**:
```json
{
  "examples": {
    "authentic_cadence": {
      "description": "V-I authentic cadence (strong resolution)",
      "progression": [["G", "B", "D"], ["C", "E", "G"]],
      "key": "C",
      "type": "cadence"
    },
    "plagal_cadence": {
      "description": "IV-I plagal cadence (Amen)",
      "progression": [["F", "A", "C"], ["C", "E", "G"]],
      "key": "C",
      "type": "cadence"
    },
    "common_progression": {
      "description": "I-IV-V-I (very common)",
      "progression": [
        ["C", "E", "G"],
        ["F", "A", "C"],
        ["G", "B", "D"],
        ["C", "E", "G"]
      ],
      "key": "C",
      "type": "progression"
    },
    "bach_chorale": {
      "description": "Bach chorale opening (I-vi-IV-V)",
      "progression": [
        ["C", "E", "G"],
        ["A", "C", "E"],
        ["F", "A", "C"],
        ["G", "B", "D"]
      ],
      "key": "C",
      "type": "chorale"
    },
    "jazz_standard": {
      "description": "Jazz ii-V-I progression",
      "progression": [
        ["D", "F", "A"],
        ["G", "B", "D"],
        ["C", "E", "G"]
      ],
      "key": "C",
      "type": "jazz"
    },
    "modulation": {
      "description": "Modulation from C Major to G Major",
      "progression": [
        ["C", "E", "G"],
        ["D", "F#", "A"],
        ["G", "B", "D"],
        ["B", "D", "F#"],
        ["G", "B", "D"]
      ],
      "key": "C",
      "type": "modulation"
    }
  }
}
```

**Status Code**: 200

---

## Documentation Endpoints

### API Documentation

**Endpoint**: `GET /docs`

**Description**: Get interactive HTML documentation.

**Status Code**: 200 (returns HTML)

---

### OpenAPI Specification

**Endpoint**: `GET /api/spec.json`

**Description**: Get the complete OpenAPI 3.0 specification for the API.

**Response**: JSON formatted OpenAPI specification compatible with Swagger UI and other API tools.

**Status Code**: 200

---

## Error Handling

### Error Response Format

All errors follow a consistent JSON format:

```json
{
  "success": false,
  "error": "Error message describing what went wrong"
}
```

### Common Error Codes

| Code | Error | Cause |
|------|-------|-------|
| 400 | Bad Request | Invalid JSON, missing required fields, invalid note names |
| 404 | Not Found | Invalid endpoint or category number |
| 500 | Server Error | Unexpected server error (check logs) |

### Example Error Response

```json
{
  "success": false,
  "error": "Missing progressions array"
}
```

---

## Request/Response Specifications

### Supported Note Names

The API accepts standard note names:
- Natural notes: `C`, `D`, `E`, `F`, `G`, `A`, `B`
- Sharp notes: `C#`, `D#`, `F#`, `G#`, `A#`
- Flat notes: `Db`, `Eb`, `Gb`, `Ab`, `Bb`

Case-insensitive: `c` and `C` both work.

### Supported Keys

Any major or minor key context can be specified:
- Major keys: `C`, `G`, `D`, `A`, `E`, `B`, `F#`, `Db`, `Ab`, `Eb`, `Bb`, `F`
- Add `m` suffix for minor: `c`, `g`, `d`, `a`, `e`, `b`, `f#`, `db`, `ab`, `eb`, `bb`, `f`

### Category Numbers

Valid category numbers: **4, 5, 6, 7, 8, 9, 10, 11**

Each represents:
- **4**: Group Theory
- **5**: Harmonic Function
- **6**: Modulation
- **7**: Voice Leading
- **8**: Progressions
- **9**: Structure
- **10**: Form
- **11**: Spectral Analysis

---

## Rate Limiting

Currently, the API has no rate limiting. All endpoints are freely accessible. Future versions may implement rate limiting for public deployments.

---

## Testing the API

### Using cURL

```bash
# Test health endpoint
curl http://localhost:4567/health

# Test status endpoint
curl http://localhost:4567/status

# Analyze a progression
curl -X POST http://localhost:4567/analyze/progression \
  -H "Content-Type: application/json" \
  -d '{
    "progressions": [
      ["C", "E", "G"],
      ["G", "B", "D"],
      ["C", "E", "G"]
    ],
    "key": "C"
  }'
```

### Using Python

```python
import requests
import json

url = 'http://localhost:4567/analyze/progression'
data = {
    'progressions': [
        ['C', 'E', 'G'],
        ['F', 'A', 'C'],
        ['G', 'B', 'D'],
        ['C', 'E', 'G']
    ],
    'key': 'C'
}

response = requests.post(url, json=data)
analysis = response.json()
print(json.dumps(analysis, indent=2))
```

### Using JavaScript/Node.js

```javascript
const url = 'http://localhost:4567/analyze/progression';
const data = {
  progressions: [
    ['C', 'E', 'G'],
    ['F', 'A', 'C'],
    ['G', 'B', 'D'],
    ['C', 'E', 'G']
  ],
  key: 'C'
};

fetch(url, {
  method: 'POST',
  headers: { 'Content-Type': 'application/json' },
  body: JSON.stringify(data)
})
.then(res => res.json())
.then(analysis => console.log(JSON.stringify(analysis, null, 2)));
```

---

## Deployment

### Local Development

```bash
ruby api/music_topos_server.rb
```

Server runs on `http://localhost:4567`

### Docker Deployment

See `Dockerfile` for containerized deployment.

### Cloud Deployment

Supported platforms:
- Heroku (free tier available)
- AWS Lambda
- DigitalOcean
- Self-hosted Kubernetes

---

## Support and Contributing

For issues, suggestions, or contributions, visit the GitHub repository:
https://github.com/[username]/music-topos

---

**Last Updated**: December 2025
**API Version**: 1.0.0
**Framework Version**: 1.0.0
