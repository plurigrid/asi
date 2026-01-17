# StringZilla Operations: 'strings' Skill for Plurigrid ASI

**Status**: 🌳 Production Ready (upstream in StringZilla v3+)
**Type**: High-Performance String Operations / SIMD-Accelerated Text Processing
**Principle**: Zero-copy views, SIMD/SWAR acceleration, deterministic hashing
**Frame**: Cross-language interoperability (C, C++, Python, Rust, Go, Swift, JS)
**Performance**: 10-100x faster than standard libraries

---

## Core Discovery

**StringZilla exposes a unified API for string operations across 7 language bindings**, leveraging SIMD (Single Instruction Multiple Data) and SWAR (SIMD Within A Register) for massive performance gains. All operations maintain **deterministic behavior** and support **zero-copy views** for memory efficiency.

### Why This Matters for Plurigrid ASI

String processing is fundamental to:
- **Document parsing**: CommonCrawl, RedPajama, LAION datasets
- **Bioinformatics**: Edit distances for protein/DNA sequences
- **Search engines**: Fuzzy matching, similarity scoring
- **Database operations**: LIKE, ORDER BY, GROUP BY optimizations
- **Cryptographic verification**: SHA-256 checksums, HMAC
- **Text embeddings**: Rolling fingerprints (MinHashing)

---

## Operation Taxonomy

### 1. Substring Search (Forward & Reverse)

**Maturity**: 🌳 Production
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ✅ | JS ✅ | Swift ✅ | Go ✅

#### Core Operations

```c
// C API
sz_cptr_t sz_find(sz_cptr_t haystack, sz_size_t h_len, sz_cptr_t needle, sz_size_t n_len);
sz_cptr_t sz_rfind(sz_cptr_t haystack, sz_size_t h_len, sz_cptr_t needle, sz_size_t n_len);
sz_bool_t sz_contains(sz_cptr_t haystack, sz_size_t h_len, sz_cptr_t needle, sz_size_t n_len);
sz_size_t sz_count(sz_cptr_t haystack, sz_size_t h_len, sz_cptr_t needle, sz_size_t n_len, sz_bool_t allowoverlap);
```

```cpp
// C++ API
auto offset = haystack.find(needle, start, end);
auto offset = haystack.rfind(needle, start, end);
bool has_it = haystack.contains(needle);
size_t n = haystack.count(needle, allowoverlap);
```

```python
# Python API
x: int = text.find('substring', start=0, end=sys.maxsize)
x: int = text.rfind('substring', start=0, end=sys.maxsize)
x: bool = 'substring' in text
x: int = text.count('substring', allowoverlap=False)
```

```rust
// Rust API
use stringzilla::StringZilla;
let offset = my_string.sz_find("world");
let offset = my_string.sz_rfind("world");
```

**Performance**: 10.6 GB/s (x86) vs 7.4 GB/s (LibC strstr) for ~5 byte words

---

### 2. Character Set Search

**Maturity**: 🌳 Production
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ✅ | JS ✅ | Swift ✅ | Go ✅

#### Operations

```c
// Find first/last occurrence of ANY character in set
sz_cptr_t sz_find_byteset(sz_cptr_t h, sz_size_t h_len, sz_byteset_t set);
sz_cptr_t sz_rfind_byteset(sz_cptr_t h, sz_size_t h_len, sz_byteset_t set);

// Find first/last character NOT in set
sz_cptr_t sz_find_byte_not_from(sz_cptr_t h, sz_size_t h_len, sz_cptr_t set, sz_size_t set_len);
sz_cptr_t sz_rfind_byte_not_from(sz_cptr_t h, sz_size_t h_len, sz_cptr_t set, sz_size_t set_len);

// Single byte search (memchr/memrchr replacement)
sz_cptr_t sz_find_byte(sz_cptr_t h, sz_size_t h_len, sz_cptr_t byte);
sz_cptr_t sz_rfind_byte(sz_cptr_t h, sz_size_t h_len, sz_cptr_t byte);
```

```python
# Python API
x: int = text.find_first_of('chars', start=0, end=sys.maxsize)
x: int = text.find_last_of('chars', start=0, end=sys.maxsize)
x: int = text.find_first_not_of('chars', start=0, end=sys.maxsize)
x: int = text.find_last_not_of('chars', start=0, end=sys.maxsize)
```

**Use Case**: Splitting CSV, parsing whitespace, validating character classes

**Performance**: 4.08 GB/s (x86) for byteset operations vs 5.42 GB/s (strcspn) but with reverse support

---

### 3. String Splitting & Iteration

**Maturity**: 🌳 Production
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ✅ | JS ⚪ | Swift ⚪ | Go ⚪

#### Operations

```python
# Python: Eager evaluation (allocates Strs collection)
x: Strs = text.split(separator=' ', maxsplit=sys.maxsize, keepseparator=False)
x: Strs = text.rsplit(separator=' ', maxsplit=sys.maxsize, keepseparator=False)
x: Strs = text.splitlines(keeplinebreaks=False, maxsplit=sys.maxsize)
x: Strs = text.split_byteset(separator='chars', maxsplit=sys.maxsize, keepseparator=False)

# Python: Lazy evaluation (zero-copy iterators)
x: SplitIterator = text.split_iter(separator=' ', keepseparator=False)
x: SplitIterator = text.rsplit_iter(separator=' ', keepseparator=False)
x: SplitIterator = text.split_byteset_iter(separator='chars', keepseparator=False)
```

```cpp
// C++: Lazy ranges
for (auto line : haystack.split("\r\n"))
    for (auto word : line.split(sz::byteset(" \w\t.,;:!?")))
        std::cout << word << std::endl;
```

**Memory Efficiency**: 10x less memory than Python's `str.split()` with lazy iterators

**Use Case**: Processing multi-GB files like CommonCrawl without full materialization

---

### 4. Hashing (Non-Cryptographic)

**Maturity**: 🌳 Production
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ✅ | JS ✅ | Swift ✅ | Go ✅

#### Operations

```c
// One-shot hash (64-bit output, stable across platforms)
sz_u64_t sz_hash(sz_cptr_t data, sz_size_t len, sz_u64_t seed);

// Incremental hashing
sz_hash_state_t state;
sz_hash_state_init(&state, seed);
sz_hash_state_update(&state, chunk1, len1);
sz_hash_state_update(&state, chunk2, len2);
sz_u64_t digest = sz_hash_state_digest(&state);
```

```python
# Python API
one_shot = sz.hash(b"Hello, world!", seed=42)

hasher = sz.Hasher(seed=42)
hasher.update(b"Hello, ").update(b"world!")
streamed = hasher.digest()  # or hexdigest()
```

```rust
// Rust: Compatible with std::collections
use std::collections::HashMap;
let map: HashMap<&str, i32, sz::BuildSzHasher> = 
    HashMap::with_hasher(sz::BuildSzHasher::with_seed(42));
```

**Determinism**: Same input + same seed = same hash (unlike std::hash in some STL implementations)

**Use Case**: Fast hash tables, deduplication, fingerprinting

---

### 5. SHA-256 Cryptographic Hashing

**Maturity**: 🌳 Production
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ✅ | JS ✅ | Swift ✅ | Go ✅

#### Operations

```c
// One-shot SHA-256
sz_u8_t digest[32];
sz_sha256(sz_cptr_t data, sz_size_t len, sz_u8_t digest[32]);

// Incremental SHA-256
sz_sha256_state_t state;
sz_sha256_state_init(&state);
sz_sha256_state_update(&state, chunk, len);
sz_sha256_state_digest(&state, digest);

// HMAC-SHA256
sz_hmac_sha256(sz_cptr_t key, sz_size_t key_len, sz_cptr_t msg, sz_size_t msg_len, sz_u8_t mac[32]);
```

```python
# Python API
digest_bytes = sz.sha256(b"Hello, world!")  # 32 bytes
hasher = sz.Sha256()
hasher.update(b"Hello, ").update(b"world!")
digest_hex = hasher.hexdigest()  # 64-char lowercase hex

# HMAC for message authentication
mac = sz.hmac_sha256(key=b"secret", message=b"Hello, world!")
```

**Performance**: 3x faster than OpenSSL-backed hashlib for large files (memory-mapped I/O advantage)

**Use Case**: Content verification, checksums, authenticated encryption

---

### 6. Unicode Case-Folding

**Maturity**: 🧐 Beta (expanding coverage)
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ⚪ | JS ⚪ | Swift ⚪ | Go ⚪

#### Operations

```c
// Case-fold UTF-8 (output buffer must be 3x input size)
sz_size_t sz_utf8_case_fold(sz_cptr_t source, sz_size_t src_len, sz_ptr_t dest);
```

```python
# Python API
sz.utf8_case_fold('HELLO')      # b'hello'
sz.utf8_case_fold('Straße')     # b'strasse' — ß expands to "ss"
sz.utf8_case_fold('eﬃcient')    # b'efficient' — ﬃ ligature → "ffi"
```

**Coverage**: 1M+ Unicode codepoints (vs ASCII-only for most libraries)

**Character Expansions**:
- German ß → ss (1 char → 2 chars)
- Ligature ﬃ → ffi (1 char → 3 chars)
- Georgian letters with complex expansions

**Use Case**: Case-insensitive search, text normalization for NLP

---

### 7. Case-Insensitive UTF-8 Search

**Maturity**: 🚧 Active Development
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ⚪ | JS ⚪ | Swift ⚪ | Go ⚪

#### Operations

```c
// Case-insensitive search with metadata caching
sz_utf8_case_insensitive_needle_metadata_t metadata = {};
sz_size_t match_length;
sz_cptr_t match = sz_utf8_case_insensitive_find(
    haystack, h_len, needle, n_len, &metadata, &match_length
);
```

```python
# Python: Single search
offset = sz.utf8_case_insensitive_find('Der große Hund', 'GROSSE')  # 4

# Python: Iterator for all matches
for match in sz.utf8_case_insensitive_find_iter('Straße STRASSE strasse', 'strasse'):
    print(match, match.offset_within(haystack))
    
# With overlapping matches
list(sz.utf8_case_insensitive_find_iter('aaaa', 'aa', include_overlapping=True))  # 3 matches
```

```cpp
// C++: Pre-compiled pattern for repeated searches
sz::utf8_case_insensitive_needle pattern("hello");
for (auto const& haystack : haystacks) {
    auto match = haystack.utf8_case_insensitive_find(pattern);
}
```

**Performance**: 3.0 GB/s (x86) vs 0.02 GB/s (ICU StringSearch) — 150x faster

**Use Case**: Search engines, fuzzy matching, multilingual text processing

---

### 8. Sorting & Sequence Operations

**Maturity**: 🌳 Production
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ✅ | JS ⚪ | Swift ⚪ | Go ⚪

#### Operations

```c
// Sort strings and return permutation order
sz_sequence_t array = {handle, count, get_start_fn, get_length_fn};
sz_sorted_idx_t order[count];
sz_sequence_argsort(&array, allocator, order);
```

```python
# Python API
lines: Strs = text.split('\n')
order: tuple = lines.argsort()  # like numpy.argsort
lines_sorted: Strs = lines.sorted()
lines_shuffled: Strs = lines.shuffled(seed=42)
batch: Strs = lines.sample(seed=42)  # 10x faster than random.choices
```

```cpp
// C++ API
std::vector<std::string> data({"c", "b", "a"});
std::vector<std::size_t> order = sz::argsort(data);
```

**Performance**: 1.91s vs 2.79s (std::sort) vs 7.58s (numpy.argsort) for 8M English words

**Use Case**: Database ORDER BY, ranked search results, dataset shuffling

---

### 9. Random String Generation

**Maturity**: 🌳 Production
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ✅ | JS ⚪ | Swift ⚪ | Go ⚪

#### Operations

```c
// Fill buffer with random bytes from alphabet
void sz_fill_random(sz_ptr_t buffer, sz_size_t len, sz_cptr_t alphabet, sz_size_t alphabet_size, sz_u64_t seed);
sz_string_t sz_random(sz_size_t len, sz_cptr_t alphabet, sz_size_t alphabet_size, sz_u64_t seed);
```

```python
# Python API
protein = sz.string.random(300, "ARNDCQEGHILKMFPSTWYV")
dna = sz.string.random(3_000_000_000, "ACGT")

dna.fill_random("ACGT")  # Pre-allocated, noexcept
dna.fill_random(std::mt19937, "ACGT")  # Custom RNG

# Overwrite any buffer
uuid = bytearray(36)
sz.fill_random(uuid, "0123456789abcdef-")
```

**Performance**: 56.2 MB/s (x86) vs 47.2 MB/s (uniform_int_distribution) vs 18.0 MB/s (rand)

**Use Case**: Testing, synthetic data generation, simulation

---

### 10. Bulk Replacements & Lookup Tables

**Maturity**: 🌳 Production
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ⚪ | JS ⚪ | Swift ⚪ | Go ⚪

#### Operations

```python
# Replace all occurrences
text.replace_all(needle_string, replacement_string)
text.replace_all(sz.byteset("chars"), replacement_string)

# Lookup table transforms (256-byte LUT)
look_up_table = bytes(range(256))  # Identity LUT
image_bytes = open("/image.jpeg", "rb").read()
sz.translate(image_bytes, look_up_table, inplace=True)

# Character mapping
text.translate('chars', {mapping_dict}, inplace=False)
```

**Performance**: 21.2 GB/s (x86) vs 3.81 GB/s (std::transform) vs 260 MB/s (str.translate)

**Use Case**: Image processing, binary data transformation, bioinformatics (codon translation)

---

### 11. Memory Operations (Copy, Move, Fill)

**Maturity**: 🌳 Production
**Bindings**: C ✅ | C++ ✅ | Python ⚪ | Rust ⚪ | JS ⚪ | Swift ⚪ | Go ⚪

#### Operations

```c
// High-performance memory operations
void sz_copy(sz_ptr_t dest, sz_cptr_t src, sz_size_t len);
void sz_move(sz_ptr_t dest, sz_cptr_t src, sz_size_t len);
void sz_fill(sz_ptr_t dest, sz_size_t len, sz_u8_t value);
```

**LibC Mapping**:
- `sz_copy` ↔ `memcpy`
- `sz_move` ↔ `memmove`
- `sz_fill` ↔ `memset`

**Advantage**: SIMD-accelerated, NULL-safe (unlike LibC's undefined behavior for `memcpy(NULL, NULL, 0)`)

---

### 12. Levenshtein Edit Distance

**Maturity**: 🌳 Production (parallel CPU/GPU backends via StringZillas)
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ✅ | JS ⚪ | Swift ⚪ | Go ⚪

#### Operations

```python
# Python API (StringZillas module)
import stringzillas as szs

strings_a = sz.Strs(["kitten", "flaw"])
strings_b = sz.Strs(["sitting", "lawn"])

cpu_scope = szs.DeviceScope(cpu_cores=4)
gpu_scope = szs.DeviceScope(gpu_device=0)

engine = szs.LevenshteinDistances(
    match=0, mismatch=2,
    open=3, extend=1,
    capabilities=("serial",)
)
distances = engine(strings_a, strings_b, device=cpu_scope)
```

```cpp
// C++ API
#include <stringzillas/similarities.hpp>

sz::arrow_strings_tape<char, sz::size_t> tape_a, tape_b;
tape_a.try_assign(left.begin(), left.end());

using levenshtein_t = szs::levenshtein_distances<char, szs::linear_gap_costs_t>;
levenshtein_t engine{szs::uniform_substitution_costs_t{0,1}, szs::linear_gap_costs_t{1}};
std::size_t distances[count];
engine(tape_a, tape_b, distances);
```

**Performance**: 3.4B CUPS (x86) vs 1.6B CUPS (NLTK) vs 6.5B CUPS (CuDF GPU baseline) vs **93.7B CUPS (StringZilla GPU)**

**Use Case**: Spell-checking, DNA alignment, fuzzy matching

---

### 13. Needleman-Wunsch Alignment Scores

**Maturity**: 🌳 Production (parallel CPU/GPU backends via StringZillas)
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ✅ | JS ⚪ | Swift ⚪ | Go ⚪

#### Operations

```python
# Python API with substitution matrix
import numpy as np
substitution_matrix = np.zeros((256, 256), dtype=np.int8)
substitution_matrix.fill(-1)  # mismatch
np.fill_diagonal(substitution_matrix, 0)  # match

engine = szs.NeedlemanWunsch(
    substitution_matrix=substitution_matrix,
    open=1, extend=1
)
scores = engine(strings_a, strings_b, device=cpu_scope)
```

**BioPython Compatibility**: Load BLOSUM62 matrix and convert to 256×256 format

**Performance**: 453M CUPS (x86) vs 576M CUPS (BioPython C implementation) — competitive with domain-specific tools

**Use Case**: Protein sequence alignment, homology detection, structural biology

---

### 14. Rolling Fingerprints (MinHashing)

**Maturity**: 🌳 Production (parallel CPU/GPU backends via StringZillas)
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ✅ | JS ⚪ | Swift ⚪ | Go ⚪

#### Operations

```python
# Python API
import numpy as np
texts = sz.Strs([
    "quick brown fox jumps over the lazy dog",
    "quick brown fox jumped over a very lazy dog",
])

cpu = szs.DeviceScope(cpu_cores=4)
ndim = 1024
window_widths = np.array([4, 6, 8, 10], dtype=np.uint64)

engine = szs.Fingerprints(
    ndim=ndim,
    window_widths=window_widths,
    alphabet_size=256,
    capabilities=("serial",)
)

hashes, counts = engine(texts, device=cpu)
assert hashes.shape == (len(texts), ndim)
```

```cpp
// C++ API
#include <stringzillas/fingerprints.hpp>

constexpr std::size_t dimensions_k = 256;
constexpr std::size_t window_width_k = 7;
using fingerprinter_t = szs::floating_rolling_hashers<sz_cap_serial_k, dimensions_k>;

fingerprinter_t engine;
engine.try_extend(window_width_k, dimensions_k);
engine(tape, hashes, counts, thread_pool);
```

**Use Case**: Document similarity, plagiarism detection, fuzzy deduplication, LSH (Locality-Sensitive Hashing)

---

### 15. Small String Optimization (SSO)

**Maturity**: 🧐 Beta
**Bindings**: C ✅ | C++ ✅ | Python ❌ | Rust ⚪ | JS ❌ | Swift ❌ | Go ❌

#### Operations

```c
// C API for owning string
sz_string_t string;
sz_string_init(&string);
sz_string_is_on_stack(&string);  // sz_true_k for strings ≤22 bytes

sz_string_grow(&string, 100, &allocator);
sz_string_expand(&string, 0, "_Hello_", 7, &allocator);
sz_string_expand(&string, SZ_SIZE_MAX, "world", 5, &allocator);
sz_string_erase(&string, 0, 1);

sz_ptr_t start;
sz_size_t length, space;
sz_bool_t is_external;
sz_string_unpack(string, &start, &length, &space, &is_external);

sz_string_free(&string, &allocator);
```

```cpp
// C++ API
sz::string text;  // 32 bytes total, 22-byte internal capacity
text.push_back('x');
text.push_back('x', sz::string::unchecked);  // No bounds check
bool success = text.try_push_back('x');  // Returns false on failure
```

**Comparison**:
| Library | sizeof | Inner Capacity |
|---------|--------|----------------|
| libstdc++ (GCC 13) | 32 | 15 |
| libc++ (Clang 17) | 24 | 22 |
| StringZilla | 32 | **22** |

**Use Case**: High-frequency string allocations, latency-sensitive applications

---

### 16. Lazy Ranges & Zero-Copy Views

**Maturity**: 🌳 Production
**Bindings**: C ❌ | C++ ✅ | Python ✅ | Rust ✅ | JS ❌ | Swift ⚪ | Go ⚪

#### Operations

```cpp
// C++ ranges
haystack[::3]        // every third line
haystack[1::1]       // every odd line
haystack[:-100:-1]   // last 100 lines in reverse

range.size();        // O(1)
range.empty();       // O(1)
range.template to<std::set<std::string>>();
range.template to<std::vector<std::string_view>>();
```

```python
# Python ranges
lines: Strs = text.split('\n')  # 4 bytes per line overhead for <4GB text
batch: Strs = lines.sample(seed=42)
lines[::3]   # every third line
lines[1::1]  # every odd line
```

**Memory Overhead**: 4 bytes per chunk (vs full string copies in standard libraries)

**Use Case**: Processing 20B document RedPajama dataset with 160GB RAM instead of terabytes

---

### 17. String Trimming & Partitioning

**Maturity**: 🌳 Production
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ⚪ | JS ⚪ | Swift ⚪ | Go ⚪

#### Operations

```python
# Python API (inspired by Python str)
text.lstrip('chars')  # Strip leading
text.rstrip('chars')  # Strip trailing
text.strip('chars')   # Strip both ends

# Partitioning (returns 3-tuple)
before, match, after = haystack.partition(':')
before, match, after = haystack.partition(sz.byteset(":;"))
before, match, after = haystack.partition(" : ")
before, match, after = haystack.rpartition(sz.whitespaces_set())
```

```cpp
// C++ API
auto parts = haystack.partition(':');
auto [before, match, after] = haystack.partition(':');  // Structured binding
```

**Use Case**: CSV parsing, HTTP header parsing, configuration files

---

### 18. Content Validation

**Maturity**: 🌳 Production
**Bindings**: C ✅ | C++ ✅ | Python ✅ | Rust ⚪ | JS ⚪ | Swift ⚪ | Go ⚪

#### Operations

```python
# Python API
text.isalnum()
text.isalpha()
text.isascii()
text.isdigit()
text.islower()
text.isspace()
text.isupper()

# Membership checks
text.contains_only(" \w\t")
text.contains(sz.whitespaces_set())
```

```cpp
// C++ API
text.contains_only(" \\w\\t");
text.contains(sz::whitespaces_set());
```

**Use Case**: Input validation, data cleaning, format verification

---

### 19. TR29 Word Boundary Detection

**Maturity**: 🚧 Active Development
**Bindings**: C ✅ | C++ ✅ | Python ⚪ | Rust ⚪ | JS ⚪ | Swift ⚪ | Go ⚪

**Standard**: Unicode UAX #29 (Text Segmentation)

**Use Case**: Tokenization for NLP, word counting, text indexing

---

### 20. CUDA GPU Acceleration

**Maturity**: 🌳 Production (StringZillas module)
**Bindings**: CUDA C++ ✅ | Python ✅ (via StringZillas)

#### Operations

```cpp
// CUDA API
#include <stringzillas/similarities.cuh>
#include <stringzillas/fingerprints.cuh>

// Query GPU capabilities
szs::gpu_specs_t specs;
szs::gpu_specs_fetch(device_id, specs);

// Use unified memory allocator
auto data = szs::unified_alloc<char>(size);
szs::unified_free(data);
```

**Performance Gains**:
- Levenshtein: 93.7B CUPS vs 6.5B CUPS (CuDF baseline) — **14x faster**
- Needleman-Wunsch: 9.0B CUPS for proteins
- Load balancing for both many small strings and few large strings

**Use Case**: Bioinformatics at scale, document similarity for billion-scale corpora

---

## Cross-Language Operation Matrix

| Operation | C | C++ | Python | Rust | JS | Swift | Go |
|-----------|:-:|:---:|:------:|:----:|:--:|:-----:|:--:|
| **Search** |
| Substring find/rfind | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Character set search | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Splitting** |
| Split/rsplit | ✅ | ✅ | ✅ | ✅ | ⚪ | ⚪ | ⚪ |
| Lazy split iterators | ❌ | ✅ | ✅ | ✅ | ❌ | ⚪ | ⚪ |
| **Hashing** |
| Non-cryptographic | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| SHA-256 | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Unicode** |
| Case-folding | ✅ | ✅ | ✅ | ⚪ | ⚪ | ⚪ | ⚪ |
| Case-insensitive search | ✅ | ✅ | ✅ | ⚪ | ⚪ | ⚪ | ⚪ |
| **Collection Ops** |
| Sorting & argsort | ✅ | ✅ | ✅ | ✅ | ⚪ | ⚪ | ⚪ |
| Random generation | ✅ | ✅ | ✅ | ✅ | ⚪ | ⚪ | ⚪ |
| **Similarity** |
| Levenshtein | ✅ | ✅ | ✅ | ✅ | ⚪ | ⚪ | ⚪ |
| Needleman-Wunsch | ✅ | ✅ | ✅ | ✅ | ⚪ | ⚪ | ⚪ |
| Rolling fingerprints | ✅ | ✅ | ✅ | ✅ | ⚪ | ⚪ | ⚪ |
| **Memory** |
| Small String Opt | ✅ | ✅ | ❌ | ⚪ | ❌ | ❌ | ❌ |
| Zero-copy views | ✅ | ✅ | ✅ | ✅ | ⚪ | ⚪ | ⚪ |

**Legend**: ✅ Implemented | ⚪ Considered | ❌ Not intended

---

## Performance Benchmarks

### CPU Operations (x86 Sapphire Rapids, 1GB English corpus)

| Operation | LibC/STL | StringZilla | Speedup |
|-----------|----------|-------------|---------|
| Substring find (~5 bytes) | 7.4 GB/s | **10.6 GB/s** | 1.4x |
| Reverse find | 0.5 GB/s | **10.8 GB/s** | 21.6x |
| Character set search | 5.42 GB/s | **4.08 GB/s** | 0.75x* |
| Random generation | 47.2 MB/s | **56.2 MB/s** | 1.2x |
| Lookup table transform | 3.81 GB/s | **21.2 GB/s** | 5.6x |
| Sorting (8M words) | 2.79s | **1.91s** | 1.5x |

*Trade-off: StringZilla provides reverse operations not available in LibC

### GPU Operations (Nvidia H100)

| Operation | Baseline | StringZilla | Speedup |
|-----------|----------|-------------|---------|
| Levenshtein (100 pairs, ~100 bytes) | 6.5B CUPS | **93.7B CUPS** | 14.4x |
| Needleman-Wunsch (proteins ~1K AA) | 0.58B CUPS | **9.0B CUPS** | 15.5x |

### Unicode Operations (x86)

| Operation | Standard | StringZilla | Speedup |
|-----------|----------|-------------|---------|
| Case-folding | 0.4 GB/s | **1.3 GB/s** | 3.25x |
| Case-insensitive search | 0.02 GB/s | **3.0 GB/s** | 150x |

---

## Hardware Backend Support

### CPU Architectures

**x86_64**:
- SSE2 (baseline, 2001+)
- Westmere (2010+)
- Haswell AVX2 (2013+)
- Skylake AVX-512 (2017+)
- Ice Lake (2019+)

**ARM**:
- NEON (ARMv7+)
- NEON with AES/SHA extensions
- SVE (Scalable Vector Extension)
- SVE2

**Platform Support**:
- Little-endian ✅
- Big-endian ✅
- 32-bit ✅
- 64-bit ✅

### GPU Architectures

**NVIDIA CUDA**:
- Kepler (compute capability 3.5+)
- Maxwell, Pascal, Volta, Turing
- Ampere
- Hopper (H100)

**Features**:
- Dynamic dispatch (runtime CPU/GPU detection)
- Unified memory support
- Mixed-precision computation (bf16, f16, f32, f64, i8)

---

## Integration Patterns

### 1. Drop-In Replacement (Python)

```python
# Before
text = "hello world"
if "world" in text:
    pos = text.find("world")
    
# After (transparent acceleration)
from stringzilla import Str
text = Str("hello world")
if "world" in text:  # 10x faster
    pos = text.find("world")
```

### 2. Explicit Acceleration (C++)

```cpp
// Before
#include <string>
std::string text = "hello world";
auto pos = text.find("world");

// After
#include <stringzilla/stringzilla.hpp>
namespace sz = ashvardanian::stringzilla;
sz::string text = "hello world";
auto pos = text.find("world");  // SIMD-accelerated
```

### 3. Hybrid Approach (Rust)

```rust
// Use StringZilla traits on existing types
use stringzilla::StringZilla;

let my_string = String::from("Hello, world!");
assert_eq!(my_string.sz_find("world"), Some(7));  // Accelerated

// Or use with standard collections
use std::collections::HashMap;
let map: HashMap<&str, i32, sz::BuildSzHasher> = 
    HashMap::with_hasher(sz::BuildSzHasher::with_seed(42));
```

### 4. Memory-Mapped Files

```python
from stringzilla import Str, File

# Zero-copy memory mapping
mapped = Str(File('large_dataset.txt'))  # No RAM copy
for line in mapped.split('\n'):
    process(line)  # Lazy evaluation
```

### 5. Parallel Processing (Python)

```python
import stringzillas as szs

# Multi-CPU backend
cpu_scope = szs.DeviceScope(cpu_cores=16)

# Or GPU backend
gpu_scope = szs.DeviceScope(gpu_device=0)

# Batch operations
engine = szs.LevenshteinDistances()
distances = engine(strings_a, strings_b, device=cpu_scope)
```

---

## Design Principles

### 1. Zero-Copy Philosophy

**Views over Copies**: Operations return `string_view` equivalents, not allocated copies

```cpp
sz::string_view front = text.front(10);  // No allocation
sz::string_view back = text.back(10);    // No allocation
sz::string_view middle = text.sub(5, -5); // Python-like slicing
```

**Memory-Mapped I/O**: Direct file mapping without intermediate buffers

### 2. Deterministic Hashing

**Stable Across Platforms**: Same input + seed → same hash on all architectures

```python
# Python (64-bit little-endian ARM)
hash1 = sz.hash(b"test", seed=42)

# C++ (64-bit big-endian x86)  
hash2 = sz::hash("test", 42);

assert hash1 == hash2  # Always true
```

### 3. Lazy Evaluation

**Iterators over Collections**: Avoid materializing intermediate results

```python
# Memory-efficient pipeline
for word in text.split_iter('\n').filter(lambda x: len(x) > 5):
    process(word)  # No intermediate list allocation
```

### 4. Safety by Design

**Bounds Checking**: Configurable via `SZ_DEBUG` flag

```cpp
text.front(10, sz::string::cap);  // Clamp to string bounds
text.back(10, sz::string::cap);   // Never throws, always safe
```

**NULL Safety**: Unlike LibC, `sz_copy(NULL, NULL, 0)` is well-defined

### 5. Composability

**Orthogonal Operations**: Mix and match without conflicts

```cpp
auto email = sz::concatenate(name, "@", domain, ".", tld);  // 0 allocations
auto email_lazy = name | "@" | domain | "." | tld;          // Lazy pipeline
sz::string email_eager = name | "@" | domain | "." | tld;   // 1 allocation
```

---

## Compilation Flags

### Performance Tuning

- `SZ_USE_MISALIGNED_LOADS`: Enable word-sized loads on x86 (default: platform-dependent)
- `SZ_DYNAMIC_DISPATCH`: Runtime CPU feature detection (default: header-only)
- `SZ_ENFORCE_SVE_OVER_NEON`: Force SVE on ARM even when slower (default: off)

### Backend Selection

- `SZ_USE_AVX512`, `SZ_USE_AVX2`, `SZ_USE_NEON`, `SZ_USE_SVE`: Explicit SIMD control
- `SZ_USE_CUDA`, `SZ_USE_HOPPER`: GPU backend control

### Safety vs Performance

- `SZ_DEBUG`: Enable aggressive bounds checking (default: inferred from build type)
- `SZ_SAFETY_OVER_COMPATIBILITY`: Disable error-prone STL overloads (default: off)

### Dependency Control

- `SZ_AVOID_LIBC`: Disable LibC dependencies (default: off)
- `SZ_OVERRIDE_LIBC`: Replace LibC symbols with StringZilla (default: off)
- `SZ_AVOID_STL`: Disable std::string interop (default: off)

---

## Use Cases for Plurigrid ASI

### 1. Document Processing Pipelines

**Problem**: Processing CommonCrawl (petabytes) or RedPajama (20B documents)

**Solution**:
```python
from stringzilla import Str, File

corpus = Str(File('/data/commoncrawl/segment.txt'))  # Memory-mapped
for doc in corpus.split('\n\n'):  # Lazy iteration
    for sentence in doc.split_byteset('.!?'):
        tokens = sentence.split()  # 10x less memory than str.split()
        yield tokens
```

**Benefit**: 160 GB RAM instead of terabytes for 20B documents

### 2. Bioinformatics Workflows

**Problem**: Aligning millions of protein sequences

**Solution**:
```python
import stringzillas as szs

proteins_a = load_fasta('query.fa')
proteins_b = load_fasta('database.fa')

engine = szs.NeedlemanWunsch(substitution_matrix=BLOSUM62, open=1, extend=1)
scores = engine(proteins_a, proteins_b, device=szs.DeviceScope(gpu_device=0))
```

**Benefit**: 15x faster than BioPython, 7.8s vs 25.8s for 100 proteins (~10K AA each)

### 3. Search Engine Indexing

**Problem**: Case-insensitive multilingual search across 1M+ Unicode codepoints

**Solution**:
```python
import stringzilla as sz

# Pre-compile pattern once
pattern = sz.utf8_case_insensitive_needle("CAFÉ")

# Search across documents
for doc in corpus:
    for match in doc.utf8_case_insensitive_find_iter(pattern):
        index.add(doc.id, match.offset)
```

**Benefit**: 150x faster than ICU StringSearch (3.0 GB/s vs 0.02 GB/s)

### 4. Cryptographic Verification

**Problem**: Checksumming large files without Python I/O overhead

**Solution**:
```python
from stringzilla import Sha256, File

mapped_file = File("dataset.csv")
checksum = Sha256().update(mapped_file).hexdigest()
```

**Benefit**: 3x faster than OpenSSL-backed hashlib (4.0s vs 12.6s for 1GB file)

### 5. Document Similarity at Scale

**Problem**: Near-duplicate detection across billion-document corpus

**Solution**:
```python
import stringzillas as szs

engine = szs.Fingerprints(ndim=1024, window_widths=[4,6,8,10])
hashes, counts = engine(documents, device=szs.DeviceScope(cpu_cores=64))

# Jaccard similarity via MinHash
similarity_matrix = compute_jaccard(hashes)
```

**Benefit**: Parallel CPU/GPU backends, O(D·L) → O(D·log(L)) via rolling hashes

### 6. Database String Operations

**Problem**: Accelerating LIKE, ORDER BY, GROUP BY in analytical databases

**Solution**: Integrate StringZilla into query engine
- DuckDB VSS already uses SimSIMD (from same author)
- Replace LibC string functions with `sz_*` equivalents
- Enable SIMD-accelerated string columns

**Benefit**: 2-10x speedup on string-heavy queries

---

## Plurigrid ASI Skill Interface

### Skill Metadata

```json
{
  "skill_name": "strings",
  "version": "4.6.0",
  "author": "Ash Vardanian (Unum Cloud)",
  "upstream": "https://github.com/ashvardanian/StringZilla",
  "license": "Apache-2.0",
  "maturity": "production",
  "backends": ["cpu_serial", "cpu_simd", "cpu_parallel", "gpu_cuda"],
  "language_bindings": ["c", "cpp", "python", "rust", "javascript", "swift", "go"]
}
```

### Capability Declaration

```python
import stringzilla as sz

capabilities = sz.__capabilities__
# Returns: {'avx2': True, 'avx512': True, 'neon': False, 'sve': False, ...}

backend = sz.get_backend()
# Returns: 'avx512' | 'avx2' | 'neon' | 'sve' | 'serial'
```

### Operation Categories

```python
OPERATIONS = {
    "search": ["find", "rfind", "contains", "count"],
    "charset": ["find_byte", "find_byteset", "find_first_of", "find_last_not_of"],
    "split": ["split", "rsplit", "splitlines", "split_byteset"],
    "hash": ["hash", "sha256", "hmac_sha256"],
    "unicode": ["utf8_case_fold", "utf8_case_insensitive_find"],
    "similarity": ["levenshtein", "needleman_wunsch", "smith_waterman"],
    "fingerprint": ["minhash", "rolling_hash"],
    "sort": ["argsort", "sorted", "shuffled"],
    "random": ["random", "fill_random"],
    "transform": ["replace_all", "translate", "lookup"],
    "memory": ["copy", "move", "fill"],
}
```

### GF(3) Trit Assignment

Using the skill trit assignment methodology from Gay MCP:

**Trit Semantics**:
- **MINUS (-1)**: Verification, analysis, validation (similarity scoring, checksums)
- **ERGODIC (0)**: Infrastructure, utilities (memory ops, hashing, case-folding)
- **PLUS (+1)**: Generation, construction (random strings, concatenation, transforms)

**Assignment**:
```python
skill_trit_assignment = {
    "strings": 0,  # ERGODIC - fundamental infrastructure
}
```

**Rationale**: String operations are foundational utilities that enable both construction (splitting, transforming) and analysis (search, similarity). They form the **ergodic baseline** that other skills compose with.

---

## Integration with Existing ASI Skills

### 1. ACSets (Attributed C-Sets)

**Connection**: Strings as morphism labels in category-theoretic databases

```julia
# Use StringZilla for fast string matching in acset queries
acset_query = @acset_query(schema, {
    morphism_label: find_all_matches("pattern", strings_column)
})
```

### 2. SIMD Operations

**Connection**: StringZilla's SIMD backend composes with other SIMD skills

- Share CPU capability detection (`avx2`, `avx512`, `neon`)
- Unified memory allocators for GPU backends
- Compatible SIMD width (128/256/512-bit lanes)

### 3. Bioinformatics Skills

**Connection**: Edit distances for sequence alignment

- DNA/RNA sequence search (ACGT alphabet)
- Protein alignment (20 amino acid alphabet)
- Codon translation via lookup tables

### 4. Cryptographic Skills

**Connection**: SHA-256 for content-addressed storage

- Deterministic hashing (seed=0 for cryptographic use)
- HMAC for authenticated messages
- Integrate with Merkle tree / IPFS skills

### 5. Document Processing Skills

**Connection**: Memory-mapped files, lazy iteration

- Compatible with Arrow/Parquet columnar formats
- PyArrow buffer interop (`foreign_buffer`)
- Zero-copy views into memory-mapped regions

---

## Installation & Quick Start

### Python

```bash
pip install stringzilla          # Serial algorithms
pip install stringzillas-cpus    # Parallel CPU backends
pip install stringzillas-cuda    # Parallel GPU backend

# Verify installation
python -c "import stringzilla; print(stringzilla.__version__)"
python -c "import stringzilla; print(stringzilla.__capabilities__)"
```

### Rust

```toml
[dependencies]
stringzilla = ">=3"
stringzilla = { version = ">=3", features = ["cpus"] }
stringzilla = { version = ">=3", features = ["cuda"] }
```

### C/C++ (Header-Only)

```bash
git submodule add https://github.com/ashvardanian/StringZilla.git external/stringzilla
```

```cpp
#include <stringzilla/stringzilla.h>   // C API
#include <stringzilla/stringzilla.hpp> // C++ API
```

### JavaScript

```bash
npm install stringzilla
```

```javascript
const sz = require('stringzilla');
const pos = sz.find("hello world", "world");
```

---

## References

**Upstream Repository**: https://github.com/ashvardanian/StringZilla  
**Documentation**: https://ashvardanian.com/posts/stringzilla/  
**Python Package**: https://pypi.org/project/stringzilla/  
**Rust Crate**: https://crates.io/crates/stringzilla  
**NPM Package**: https://www.npmjs.com/package/stringzilla  

**Related Projects**:
- SimSIMD: https://github.com/ashvardanian/SimSIMD (vector math)
- USearch: https://github.com/unum-cloud/usearch (vector search)
- DuckDB VSS: https://github.com/duckdb/duckdb (database integration)

**Benchmarks**:
- StringWars: https://github.com/ashvardanian/StringWars (comparisons)
- HashEvals: https://github.com/ashvardanian/HashEvals (collision resistance)

---

## Status Summary

**Maturity Levels**:
- 🌳 Production Ready: Core operations battle-tested in production
- 🧐 Beta: Stable API, expanding coverage (Unicode operations)
- 🚧 Active Development: Evolving (TR29 word boundaries)

**Cross-Language Parity**: 
- C/C++/Python: 95%+ feature parity
- Rust: 80% (similarity ops available, iterators in progress)
- Go/Swift/JS: 60% (core search/hash operations only)

**Hardware Coverage**:
- x86 CPUs: Full (SSE2 → AVX-512)
- ARM CPUs: Full (NEON → SVE2)
- NVIDIA GPUs: Full (Kepler → Hopper)
- AMD GPUs: Planned (ROCm backend)

**Integration Status**:
- ✅ DuckDB (via SimSIMD)
- ✅ PyArrow (buffer interop)
- ✅ NumPy (array interop)
- ⚪ Julia (planned ACSets integration)

---

**Skill Name**: strings  
**Type**: High-Performance String Operations  
**Upstream**: StringZilla v4.6.0+  
**License**: Apache-2.0  
**GF(3) Trit**: 0 (ERGODIC - infrastructure)  
**Backends**: CPU (serial/SIMD/parallel) + GPU (CUDA)  
**Language Bindings**: 7 (C, C++, Python, Rust, JS, Swift, Go)  
**Status**: ✅ Production ready, SIMD-accelerated, cross-platform

---

★ Insight ─────────────────────────────────────
**StringZilla achieves 10-100x speedups through three key innovations:**

1. **SIMD/SWAR Exploitation**: Where LibC uses scalar loops, StringZilla processes 16-64 bytes per instruction using AVX-512 or ARM NEON. Even the SWAR baseline (no SIMD) outperforms LibC on misaligned-load-friendly architectures.

2. **Zero-Copy Architecture**: Memory-mapped files + lazy iterators eliminate allocation overhead. Processing 20B documents requires 160GB RAM (4 bytes/string overhead) instead of terabytes for full materialization.

3. **Asymmetric Completeness**: LibC provides `memchr` but not `memrchr` (reverse search). StringZilla provides both forward/reverse variants for every operation, enabling algorithms that were previously impossible without copying data.

**Why This Matters for ASI**: String processing is the **ergodic baseline** (GF(3) trit=0) that enables both construction (tokenization, parsing) and analysis (search, similarity). By accelerating this foundational layer 10-100x, all downstream NLP, bioinformatics, and search operations inherit the speedup.
─────────────────────────────────────────────────
