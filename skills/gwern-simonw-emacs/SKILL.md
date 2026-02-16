# gwern-simonw-emacs

> Self-operating Gwern via Simon Willison's LLM CLI toolkit, generating s-expressions through NuShell structured data reflow with CQ analysis.

## Trit: +1 (PLUS - generative)

## The Synthesis

```
┌─────────────────────────────────────────────────────────────────┐
│                  SELF-OPERATING GWERN                           │
│                                                                 │
│    Gwern's Essays ────▶ LLM (simonw) ────▶ S-expressions       │
│         │                    │                    │             │
│         ▼                    ▼                    ▼             │
│    gwern_worlds/        llm CLI              Emacs/Hy          │
│    (JSON manifests)     (tool support)       (eval loop)       │
│         │                    │                    │             │
│         └──────────┬─────────┴────────────────────┘             │
│                    ▼                                            │
│              NuShell Structured Data                            │
│              (typed tables, records)                            │
│                    │                                            │
│                    ▼                                            │
│               CQ Analysis                                       │
│         (content-addressed queries)                             │
└─────────────────────────────────────────────────────────────────┘
```

## Simon Willison Exposure

### Into Hy (H)
```python
# simonw/llm → Hy s-expression generation
(import llm)
(setv model (llm.get-model "claude-sonnet-4-20250514"))

(defn gwern->sexp [essay-url]
  "Transform Gwern essay to s-expression via LLM"
  (let [response (.chain model 
                   f"Convert {essay-url} to Lisp s-expressions preserving structure"
                   :tools [scraper])]
    (hy.read-str (.text response))))
```

### Into Y (Emacs Lisp / General Lisp)
```elisp
;; gwern-simonw.el - Self-operating Gwern in Emacs
(require 'llm)  ;; xenodium's llm.el or similar

(defun gwern-to-sexp (url)
  "Fetch Gwern essay and convert to s-expression."
  (let ((result (shell-command-to-string
                  (format "llm --tool 'scrape(\"%s\")' 'Convert to sexp' -m claude-sonnet" url))))
    (read result)))

(defun gwern-self-operate ()
  "Gwern operates on himself - recursive essay analysis."
  (interactive)
  (let* ((essays '("scaling" "bitter-lesson" "spaced-repetition"))
         (sexps (mapcar (lambda (e)
                          (gwern-to-sexp (format "https://gwern.net/%s" e)))
                        essays)))
    (apply #'append sexps)))
```

## CQ Analysis → NuShell Reflow

### Content-Addressed Queries (CQ)
```nu
# CQ: content-addressed query over Gwern corpus
def cq [query: string] {
  # 1. Hash the query for content-addressing
  let query_hash = ($query | hash sha256 | str substring 0..8)
  
  # 2. Query gwern_worlds via structured data
  ls gwern_worlds/*.json 
  | each { |f| open $f.name | insert source $f.name }
  | flatten
  | where content =~ $query
  | insert query_hash $query_hash
}

# Reflow: transform CQ results through NuShell tables
def reflow [data: table] {
  $data 
  | group-by source
  | transpose key value
  | each { |row|
      {
        source: $row.key
        count: ($row.value | length)
        sexp: (to-sexp $row.value)
      }
    }
}

# Convert NuShell record to s-expression
def to-sexp [record] {
  let keys = ($record | columns)
  let pairs = ($keys | each { |k| $"(:($k) \"($record | get $k)\")" })
  $"'(($pairs | str join ' '))"
}
```

### Full Pipeline
```nu
# gwern_simonw_pipeline.nu

# 1. Ingest Gwern essays
def ingest-gwern [essays: list] {
  $essays | each { |e|
    let url = $"https://gwern.net/($e)"
    let content = (http get $url | str substring 0..10000)
    {name: $e, url: $url, content: $content}
  }
}

# 2. LLM transform via simonw's llm CLI
def llm-sexp [content: string] {
  llm -m claude-sonnet $"Convert to s-expression: ($content | str substring 0..2000)"
  | str trim
}

# 3. CQ analysis with content-addressing  
def analyze-cq [corpus: table, query: string] {
  let hash = ($query | hash sha256 | str substring 0..8)
  
  $corpus 
  | where content =~ $query
  | insert cq_hash $hash
  | insert sexp { |row| (llm-sexp $row.content) }
}

# 4. Full reflow
def gwern-reflow [] {
  let essays = [scaling bitter-lesson spaced-repetition tool-ai]
  let corpus = (ingest-gwern $essays)
  
  # Multiple CQ queries
  let queries = ["scaling hypothesis" "bitter lesson" "spaced repetition"]
  
  $queries | each { |q|
    analyze-cq $corpus $q
  } | flatten
}
```

## Integration with Gay.jl SPI

```nu
# Extend gay_spi.nu with s-expression generation

# Reference values generate s-expression colors
def gay-sexp [index: int] {
  let val = $REFERENCE_VALUES | get $index
  let hue = (($val mod 360) | math abs)
  let trit = (($val mod 3) | into int)
  
  $"'(:color (:hue ($hue) :sat 0.7 :lit 0.5) :trit ($trit) :index ($index))"
}

# Generate palette as s-expression
def gay-palette-sexp [n: int] {
  0..<$n | each { |i| gay-sexp $i } | str join "\n"
}
```

## Emacs Package Structure

```
gwern-simonw/
├── gwern-simonw.el       # Main package
├── gwern-cq.el           # CQ query interface
├── gwern-nushell.el      # NuShell integration
├── gwern-sexp.el         # S-expression generation
└── gwern-llm.el          # simonw/llm CLI bridge
```

### gwern-simonw.el Core
```elisp
;;; gwern-simonw.el --- Self-operating Gwern via LLM  -*- lexical-binding: t; -*-

(require 'json)
(require 'subr-x)

(defgroup gwern-simonw nil
  "Self-operating Gwern with simonw LLM tools."
  :group 'applications)

(defcustom gwern-simonw-model "claude-sonnet"
  "Default LLM model for Gwern processing."
  :type 'string)

(defvar gwern-simonw--cache (make-hash-table :test 'equal)
  "Content-addressed cache for CQ results.")

(defun gwern-simonw-cq (query)
  "Execute content-addressed query on Gwern corpus."
  (let* ((hash (secure-hash 'sha256 query))
         (cached (gethash hash gwern-simonw--cache)))
    (or cached
        (let ((result (gwern-simonw--execute-cq query)))
          (puthash hash result gwern-simonw--cache)
          result))))

(defun gwern-simonw--execute-cq (query)
  "Run CQ via NuShell."
  (shell-command-to-string
    (format "nu -c 'source gwern_simonw_pipeline.nu; cq \"%s\"'" query)))

(defun gwern-simonw-generate-sexp (topic)
  "Generate s-expression from Gwern topic."
  (interactive "sTopic: ")
  (let ((result (shell-command-to-string
                  (format "llm -m %s 'Generate Lisp s-expression about %s from Gwern perspective'"
                          gwern-simonw-model topic))))
    (with-current-buffer (get-buffer-create "*Gwern S-exp*")
      (erase-buffer)
      (insert result)
      (lisp-mode)
      (pop-to-buffer (current-buffer)))))

(provide 'gwern-simonw)
;;; gwern-simonw.el ends here
```

## NuShell Data Structures

```nu
# Typed records for Gwern analysis

# Essay record
record Essay {
  name: string
  url: string  
  content: string
  word_count: int
  cq_hashes: list<string>
}

# CQ Result
record CQResult {
  query: string
  hash: string
  matches: list<Essay>
  sexp: string
}

# Reflow State
record ReflowState {
  input: table
  transforms: list<string>
  output: table
  gf3_trit: int
}
```

## GF(3) Conservation

```
gwern-simonw-emacs (+1) ⊗ nushell-cq (0) ⊗ leapity-frog (-1) = 0 ✓
simonw-llm (+1) ⊗ gay-spi (0) ⊗ gwern-corpus (-1) = 0 ✓
```

## Usage

```bash
# Install simonw's llm
pip install llm
llm install llm-claude-3

# Run NuShell pipeline
nu gwern_simonw_pipeline.nu

# In Emacs
M-x gwern-simonw-generate-sexp RET "scaling laws" RET
```

## References

- [simonw/llm](https://github.com/simonw/llm) - LLM CLI with tool support
- [llm-tools-datasette](https://github.com/simonw/llm-tools-datasette) - Datasette integration
- [gwern.net](https://gwern.net) - Gwern's essay corpus
- [gay_spi.nu](file:///Users/bob/ies/gay_spi.nu) - NuShell SPI implementation
- [gwern_worlds/](file:///Users/bob/ies/gwern_worlds) - Gwern world manifests


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
