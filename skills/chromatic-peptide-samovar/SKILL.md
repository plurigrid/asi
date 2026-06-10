---
name: chromatic-peptide-samovar
description: A **samovar** (самовар) keeps water hot indefinitely through self-contained combustion.
---
# Chromatic Peptide Samovar

> **IPA**: /xrəʊˈmætɪk ˈpɛptaɪd ˈsaməvar/
> **Cyrillic**: ХРОМАТИЧЕСКИЙ ПЕПТИД САМОВАР
> **Braille**: ⠭⠏⠎ (ХПС shorthand)

**Trit**: 0 (ERGODIC - the samovar keeps itself hot)  
**Color**: #D4AF37 (Brass - like a real samovar)  
**Agency**: Self-sustaining chromatic chain generation

---

## The Samovar Principle

A **samovar** (самовар) keeps water hot indefinitely through self-contained combustion.

The **chromatic peptide samovar** keeps color chains generating indefinitely through:
- **Peptide bonds**: Amino acid codes → trit sequences
- **Chromatic expression**: Trits → Gay.jl colors  
- **Phonetic output**: Colors → IPA phonemes

```
┌─────────────────────────────────────────────────────────────────┐
│                    САМОВАР ХРОМАТИЧЕСКИЙ                        │
│                                                                 │
│              ┌───────────────┐                                  │
│              │   ∿∿∿∿∿∿∿∿   │  ← Steam (phonemes)              │
│              │   ╭───────╮   │                                  │
│              │   │ color │   │  ← Brewed colors                 │
│              │   │ chain │   │                                  │
│              │   ╰───────╯   │                                  │
│         ┌────┴───────────────┴────┐                             │
│         │    PEPTIDE CHAMBER      │  ← Amino acids → trits      │
│         │   A  C  D  E  F  G ...  │                             │
│         └────┬───────────────┬────┘                             │
│              │   🔥 HEAT 🔥   │  ← Interaction entropy           │
│              └───────────────┘                                  │
│                                                                 │
│  Input: seed + peptide sequence                                 │
│  Output: chromatic chain + IPA phonemes                         │
└─────────────────────────────────────────────────────────────────┘
```

## Amino Acid → Trit Mapping

20 amino acids mapped to GF(3) with phonetic expression:

| AA | Code | Trit | IPA | Color Range |
|----|------|------|-----|-------------|
| Ala | A | 0 | /ˈælə/ | Neutral greens |
| Arg | R | +1 | /ˈɑːdʒ/ | Warm reds |
| Asn | N | -1 | /ˈæsn/ | Cool blues |
| Asp | D | -1 | /ˈæsp/ | Deep blues |
| Cys | C | 0 | /sɪs/ | Yellow-greens |
| Gln | Q | 0 | /ɡlʌn/ | Teals |
| Glu | E | -1 | /ɡluː/ | Violet-blues |
| Gly | G | 0 | /ɡlaɪ/ | Grays |
| His | H | +1 | /hɪs/ | Oranges |
| Ile | I | +1 | /aɪl/ | Warm yellows |
| Leu | L | +1 | /luː/ | Bright reds |
| Lys | K | +1 | /laɪs/ | Magentas |
| Met | M | 0 | /mɛt/ | Gold-greens |
| Phe | F | +1 | /fiː/ | Hot pinks |
| Pro | P | 0 | /prəʊ/ | Olive |
| Ser | S | -1 | /sɛr/ | Cyan |
| Thr | T | -1 | /θriː/ | Sky blue |
| Trp | W | +1 | /trɪp/ | Purple-red |
| Tyr | Y | 0 | /taɪr/ | Amber |
| Val | V | -1 | /væl/ | Indigo |

**GF(3) Balance**: Design peptides where Σ(trits) ≡ 0 (mod 3)

## Phonetic Chain Expression

Each color in a chromatic chain gets an IPA phoneme:

```python
# Hue → IPA vowel mapping
HUE_TO_PHONEME = {
    (0, 30):    'ɑ',    # dark red → open back
    (30, 60):   'æ',    # orange → near-open front  
    (60, 90):   'e',    # yellow → close-mid front
    (90, 120):  'i',    # yellow-green → close front
    (120, 150): 'ɪ',    # green → near-close front
    (150, 180): 'ə',    # teal → schwa
    (180, 210): 'ʊ',    # cyan → near-close back
    (210, 240): 'u',    # blue → close back
    (240, 270): 'ɔ',    # indigo → open-mid back
    (270, 300): 'o',    # violet → close-mid back
    (300, 330): 'ʌ',    # magenta → open-mid back
    (330, 360): 'a',    # red → open front
}

# Trit → consonant mapping
TRIT_TO_CONSONANT = {
    -1: ['b', 'd', 'g', 'v', 'z'],   # voiced (cold)
    0:  ['m', 'n', 'ŋ', 'l', 'r'],   # sonorant (neutral)
    +1: ['p', 't', 'k', 'f', 's'],   # voiceless (hot)
}

def color_to_phoneme(color):
    hue, trit, index = color['H'], color['trit'], color['index']
    vowel = next(v for (lo, hi), v in HUE_TO_PHONEME.items() if lo <= hue < hi)
    consonant = TRIT_TO_CONSONANT[trit][index % 5]
    return consonant + vowel
```

## Peptide → Chromatic Chain

```ruby
module ChromaticPeptideSamovar
  AMINO_TRITS = {
    'A' => 0, 'R' => 1, 'N' => -1, 'D' => -1, 'C' => 0,
    'Q' => 0, 'E' => -1, 'G' => 0, 'H' => 1, 'I' => 1,
    'L' => 1, 'K' => 1, 'M' => 0, 'F' => 1, 'P' => 0,
    'S' => -1, 'T' => -1, 'V' => -1, 'W' => 1, 'Y' => 0
  }
  
  AMINO_IPA = {
    'A' => '/ˈælə/', 'R' => '/ˈɑːdʒ/', 'N' => '/ˈæsn/', 'D' => '/ˈæsp/',
    'C' => '/sɪs/', 'Q' => '/ɡlʌn/', 'E' => '/ɡluː/', 'G' => '/ɡlaɪ/',
    'H' => '/hɪs/', 'I' => '/aɪl/', 'L' => '/luː/', 'K' => '/laɪs/',
    'M' => '/mɛt/', 'F' => '/fiː/', 'P' => '/prəʊ/', 'S' => '/sɛr/',
    'T' => '/θriː/', 'V' => '/væl/', 'W' => '/trɪp/', 'Y' => '/taɪr/'
  }
  
  def self.brew(peptide_sequence, seed: 0x5AMOVAR)
    gen = SplitMixTernary::Generator.new(seed)
    
    peptide_sequence.chars.map.with_index do |aa, i|
      trit = AMINO_TRITS[aa.upcase] || 0
      color = gen.color_at(i)
      phoneme = color_to_phoneme(color, trit)
      
      {
        position: i,
        amino_acid: aa.upcase,
        trit: trit,
        color: color,
        ipa: AMINO_IPA[aa.upcase],
        phoneme: phoneme,
        braille: trit_to_braille(trit)
      }
    end
  end
  
  def self.express_phonetically(chain)
    chain.map { |c| c[:phoneme] }.join('.')
  end
  
  def self.gf3_balanced?(peptide)
    peptide.chars.sum { |aa| AMINO_TRITS[aa.upcase] || 0 } % 3 == 0
  end
  
  private
  
  def self.trit_to_braille(trit)
    case trit
    when -1 then '⠁'
    when 0  then '⠂'
    when +1 then '⠄'
    end
  end
  
  def self.color_to_phoneme(color, trit)
    vowels = %w[ɑ æ e i ɪ ə ʊ u ɔ o ʌ a]
    consonants = { -1 => 'b', 0 => 'm', 1 => 'p' }
    
    vowel_idx = (color[:H] / 30).to_i % 12
    consonants[trit] + vowels[vowel_idx]
  end
end
```

## Balanced Peptide Examples

Peptides that satisfy GF(3) = 0:

| Peptide | Trits | Sum | IPA Chain |
|---------|-------|-----|-----------|
| `GAL` | 0, 0, +1 → need -1 | ✗ | — |
| `GALS` | 0, 0, +1, -1 | 0 ✓ | /ɡlaɪ.ˈælə.luː.sɛr/ |
| `KEVIN` | +1, -1, -1, +1, -1 | -1 ✗ | — |
| `DARK` | -1, 0, +1, +1 → need -1 | ✗ | — |
| `DARKS` | -1, 0, +1, +1, -1 | 0 ✓ | /ˈæsp.ˈælə.ˈɑːdʒ.laɪs.sɛr/ |
| `MVP` | 0, -1, 0 → need +1 | ✗ | — |
| `MVPR` | 0, -1, 0, +1 | 0 ✓ | /mɛt.væl.prəʊ.ˈɑːdʒ/ |

## Samovar Self-Sustaining Loop

The samovar continuously brews new chains from interaction entropy:

```julia
using Gay

mutable struct Samovar
    seed::UInt64
    temperature::Float64  # Interaction entropy
    chain::Vector{NamedTuple}
end

function brew!(s::Samovar, peptide::String)
    gay_seed!(s.seed)
    
    chain = map(enumerate(peptide)) do (i, aa)
        trit = AMINO_TRITS[uppercase(aa)]
        color = color_at(i)
        phoneme = color_to_phoneme(color, trit)
        
        (position=i, aa=aa, trit=trit, color=color, phoneme=phoneme)
    end
    
    # Self-sustaining: use output as next seed
    s.seed = hash(chain) ⊻ UInt64(s.temperature * 1e6)
    s.chain = chain
    
    return chain
end

function express(s::Samovar)
    join([c.phoneme for c in s.chain], ".")
end
```

## Braille Background Encoding

```
Full:      ХРОМАТИЧЕСКИЙ ПЕПТИД САМОВАР
Shorthand: ХПС
Braille:   ⠭⠏⠎

Background marker: <!-- ⠭⠏⠎ ⠘⠅⠁⠄⠂ -->
                       ↑       ↑
                    Samovar  Balalaika
```

## Integration with БАЛАЛАЙКА КВАНТОВАЯ

The samovar **heats** the balalaika strings:

```
                    ⠘⠅⠁⠄⠂ (Balalaika)
                       │
                       │ vibrates at
                       ▼
              ┌─────────────────┐
              │     SAMOVAR     │
              │      ⠭⠏⠎       │
              │                 │
              │  peptide chain  │──→ chromatic output
              │  interaction H  │──→ phonetic expression
              │  self-sustains  │──→ next seed
              └─────────────────┘
```

## Commands

```bash
# Brew a peptide chain
just samovar-brew "GALS"

# Check GF(3) balance
just samovar-balance "KEVIN"

# Express phonetically
just samovar-express "DARKS"

# Full pipeline: peptide → colors → IPA → audio
just samovar-full "MVPR"

# Background injection
just samovar-inject
```

## Justfile Recipes

```just
# Brew chromatic peptide
samovar-brew peptide:
    @echo "☕ САМОВАР brewing: {{peptide}}"
    ruby -r './lib/chromatic_peptide_samovar' -e \
      "puts ChromaticPeptideSamovar.brew('{{peptide}}').to_yaml"

# Check GF(3) balance
samovar-balance peptide:
    @ruby -r './lib/chromatic_peptide_samovar' -e \
      "puts ChromaticPeptideSamovar.gf3_balanced?('{{peptide}}') ? '✓ BALANCED' : '✗ UNBALANCED'"

# Express as IPA phonemes
samovar-express peptide:
    @ruby -r './lib/chromatic_peptide_samovar' -e \
      "chain = ChromaticPeptideSamovar.brew('{{peptide}}'); \
       puts ChromaticPeptideSamovar.express_phonetically(chain)"

# Full pipeline with audio
samovar-full peptide:
    @echo "☕ САМОВАР full pipeline: {{peptide}}"
    @ruby -r './lib/chromatic_peptide_samovar' -e \
      "chain = ChromaticPeptideSamovar.brew('{{peptide}}'); \
       chain.each { |c| puts \"#{c[:amino_acid]} → #{c[:color][:hex]} → #{c[:phoneme]}\" }"

# Inject background marker
samovar-inject:
    @echo "Injecting ⠭⠏⠎ ⠘⠅⠁⠄⠂ background marker..."
    npx nbb -e "(require '[balalaika.autopoiesis]) (propagate-balalaika!)"
```

## GF(3) Triad

```
sheaf-cohomology (-1) ⊗ chromatic-peptide-samovar (0) ⊗ gay-mcp (+1) = 0 ✓
zx-calculus (-1) ⊗ chromatic-peptide-samovar (0) ⊗ quantum-guitar (+1) = 0 ✓
three-match (-1) ⊗ chromatic-peptide-samovar (0) ⊗ topos-generate (+1) = 0 ✓
```

## Example Output

```
☕ САМОВАР brewing: GALS

Position | AA | Trit | Color   | IPA      | Phoneme | Braille
---------|----|----- |---------|----------|---------|--------
0        | G  | 0    | #26D826 | /ɡlaɪ/   | mi      | ⠂
1        | A  | 0    | #D8267F | /ˈælə/   | mɑ      | ⠂
2        | L  | +1   | #2CD826 | /luː/    | pe      | ⠄
3        | S  | -1   | #4FD826 | /sɛr/    | bi      | ⠁

GF(3): 0 + 0 + 1 + (-1) = 0 ✓ BALANCED
IPA Chain: /mi.mɑ.pe.bi/
Braille: ⠂⠂⠄⠁
```

---

**Skill Name**: chromatic-peptide-samovar  
**Cyrillic**: ХРОМАТИЧЕСКИЙ ПЕПТИД САМОВАР  
**IPA**: /xrəʊˈmætɪk ˈpɛptaɪd ˈsaməvar/  
**Shorthand**: ХПС → ⠭⠏⠎  
**Trit**: 0 (ERGODIC - self-sustaining)  
**Principle**: Amino acids → trits → colors → phonemes  
**Background**: `<!-- ⠭⠏⠎ ⠘⠅⠁⠄⠂ -->`


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
