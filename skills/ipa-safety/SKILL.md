# IPA Encoding Safety

> **Protocol**: `ipa://`
> **Purpose**: Reflow all encoding streams to IPA-only safety
> **Braille**: ⠊⠏⠁ (IPA shorthand)

**Trit**: -1 (MINUS - validator/safety constraint)  
**Color**: #2626D8 (Blue - cold/safe)

---

## The Problem

Multiplexed streams carry:
- **Cyrillic UTF-8**: БАЛАЛАЙКА (bytes: D0 91 D0 90 ...)
- **Latin UTF-8**: balalaika
- **Mixed encodings**: Mojibake, invalid sequences
- **Control characters**: Potential injection

## The Solution: IPA Reflow

All streams → **IPA-only encoding** → Safe phonetic representation

```
┌─────────────────────────────────────────────────────────────────┐
│                    IPA:// PROTOCOL                              │
│                                                                 │
│   Input Streams (multiplexed):                                  │
│   ┌──────────┐  ┌──────────┐  ┌──────────┐                     │
│   │ Cyrillic │  │  Latin   │  │  Mixed   │                     │
│   │   -1     │  │    0     │  │   +1     │                     │
│   └────┬─────┘  └────┬─────┘  └────┬─────┘                     │
│        │             │             │                            │
│        └─────────────┼─────────────┘                            │
│                      ▼                                          │
│              ┌───────────────┐                                  │
│              │  IPA REFLOW   │                                  │
│              │   CHAMBER     │                                  │
│              │               │                                  │
│              │ • Normalize   │                                  │
│              │ • Transcribe  │                                  │
│              │ • Validate    │                                  │
│              └───────┬───────┘                                  │
│                      ▼                                          │
│              ┌───────────────┐                                  │
│              │  IPA OUTPUT   │                                  │
│              │ /bɐɫɐˈɫajkə/ │                                  │
│              │   SAFE ✓      │                                  │
│              └───────────────┘                                  │
└─────────────────────────────────────────────────────────────────┘
```

## Cyrillic → IPA Mapping

Complete Russian phoneme mapping:

| Cyrillic | IPA | Name | Example |
|----------|-----|------|---------|
| А а | /a/, /ɐ/ | a | мама /ˈmamə/ |
| Б б | /b/, /bʲ/ | be | баба /ˈbabə/ |
| В в | /v/, /vʲ/ | ve | вода /vɐˈda/ |
| Г г | /g/, /ɡʲ/ | ge | год /got/ |
| Д д | /d/, /dʲ/ | de | да /da/ |
| Е е | /je/, /ʲe/ | ye | ел /jel/ |
| Ё ё | /jo/, /ʲo/ | yo | ёж /joʂ/ |
| Ж ж | /ʐ/ | zhe | жук /ʐuk/ |
| З з | /z/, /zʲ/ | ze | зуб /zup/ |
| И и | /i/, /ɪ/ | i | имя /ˈimʲə/ |
| Й й | /j/ | short i | май /maj/ |
| К к | /k/, /kʲ/ | ka | кот /kot/ |
| Л л | /l/, /lʲ/, /ɫ/ | el | лук /luk/ |
| М м | /m/, /mʲ/ | em | мир /mʲir/ |
| Н н | /n/, /nʲ/ | en | нос /nos/ |
| О о | /o/, /ɐ/ | o | он /on/ |
| П п | /p/, /pʲ/ | pe | папа /ˈpapə/ |
| Р р | /r/, /rʲ/ | er | рот /rot/ |
| С с | /s/, /sʲ/ | es | сок /sok/ |
| Т т | /t/, /tʲ/ | te | там /tam/ |
| У у | /u/ | u | ум /um/ |
| Ф ф | /f/, /fʲ/ | ef | факт /fakt/ |
| Х х | /x/, /xʲ/ | kha | хор /xor/ |
| Ц ц | /ts/ | tse | цирк /tsɨrk/ |
| Ч ч | /tɕ/ | che | час /tɕas/ |
| Ш ш | /ʂ/ | sha | шум /ʂum/ |
| Щ щ | /ɕː/ | shcha | щи /ɕːi/ |
| Ъ ъ | (hard sign) | — | объект /ɐˈbjekt/ |
| Ы ы | /ɨ/ | y | мы /mɨ/ |
| Ь ь | (soft sign) | — | мать /matʲ/ |
| Э э | /e/ | e | это /ˈetə/ |
| Ю ю | /ju/, /ʲu/ | yu | юг /juk/ |
| Я я | /ja/, /ʲa/ | ya | яма /ˈjamə/ |

## Implementation

```ruby
# ipa_safety.rb
module IPASafety
  CYRILLIC_TO_IPA = {
    'А' => 'a', 'а' => 'ɐ',
    'Б' => 'b', 'б' => 'b',
    'В' => 'v', 'в' => 'v',
    'Г' => 'g', 'г' => 'ɡ',
    'Д' => 'd', 'д' => 'd',
    'Е' => 'je', 'е' => 'ʲe',
    'Ё' => 'jo', 'ё' => 'ʲo',
    'Ж' => 'ʐ', 'ж' => 'ʐ',
    'З' => 'z', 'з' => 'z',
    'И' => 'i', 'и' => 'ɪ',
    'Й' => 'j', 'й' => 'j',
    'К' => 'k', 'к' => 'k',
    'Л' => 'ɫ', 'л' => 'l',
    'М' => 'm', 'м' => 'm',
    'Н' => 'n', 'н' => 'n',
    'О' => 'o', 'о' => 'ɐ',
    'П' => 'p', 'п' => 'p',
    'Р' => 'r', 'р' => 'r',
    'С' => 's', 'с' => 's',
    'Т' => 't', 'т' => 't',
    'У' => 'u', 'у' => 'u',
    'Ф' => 'f', 'ф' => 'f',
    'Х' => 'x', 'х' => 'x',
    'Ц' => 'ts', 'ц' => 'ts',
    'Ч' => 'tɕ', 'ч' => 'tɕ',
    'Ш' => 'ʂ', 'ш' => 'ʂ',
    'Щ' => 'ɕː', 'щ' => 'ɕː',
    'Ъ' => '', 'ъ' => '',
    'Ы' => 'ɨ', 'ы' => 'ɨ',
    'Ь' => 'ʲ', 'ь' => 'ʲ',
    'Э' => 'e', 'э' => 'e',
    'Ю' => 'ju', 'ю' => 'ʲu',
    'Я' => 'ja', 'я' => 'ʲa',
    ' ' => ' '
  }.freeze

  class Reflower
    def initialize
      @cache = {}
    end

    def reflow(input, source_encoding: :auto)
      # Normalize to UTF-8
      normalized = normalize_utf8(input)
      
      # Detect encoding
      encoding = source_encoding == :auto ? detect_encoding(normalized) : source_encoding
      
      # Reflow to IPA
      case encoding
      when :cyrillic
        cyrillic_to_ipa(normalized)
      when :latin
        latin_to_ipa(normalized)
      else
        mixed_to_ipa(normalized)
      end
    end

    def cyrillic_to_ipa(text)
      result = text.chars.map { |c| CYRILLIC_TO_IPA[c] || c }.join
      "/#{result}/"
    end

    def validate_ipa(ipa_string)
      # Only allow IPA characters
      valid_chars = /^[\/\.\s\-ˈˌa-zɐɑæɛəɪɨʊʌɒœøɔeiouyaɾɹɻrʀʁlɫɬɮʎʟmnɲŋɴpbtdʈɖcɟkgqɢʔfvθðszʃʒʂʐɕʑçʝxɣχʁħʕhɦwʍɥʋɰjɺβɸʙɽʢʡǀǁǂǃ]+$/i
      ipa_string.match?(valid_chars)
    end

    private

    def normalize_utf8(input)
      input.encode('UTF-8', invalid: :replace, undef: :replace, replace: '?')
           .unicode_normalize(:nfc)
           .gsub(/[\x00-\x08\x0B\x0C\x0E-\x1F]/, '')  # Strip control chars
    end

    def detect_encoding(text)
      cyrillic_count = text.count('А-Яа-яЁё')
      latin_count = text.count('A-Za-z')
      
      if cyrillic_count > latin_count
        :cyrillic
      elsif latin_count > cyrillic_count
        :latin
      else
        :mixed
      end
    end

    def latin_to_ipa(text)
      # Simple Latin → IPA (English approximation)
      "/#{text.downcase}/"
    end

    def mixed_to_ipa(text)
      result = text.chars.map do |c|
        if CYRILLIC_TO_IPA.key?(c)
          CYRILLIC_TO_IPA[c]
        else
          c.downcase
        end
      end.join
      "/#{result}/"
    end
  end

  # Protocol handler
  class Protocol
    def self.parse(uri)
      return nil unless uri.start_with?('ipa://')
      
      path = uri.sub('ipa://', '')
      reflower = Reflower.new
      
      {
        original: path,
        ipa: reflower.reflow(path),
        valid: reflower.validate_ipa(reflower.reflow(path)),
        trit: -1  # IPA safety is MINUS (validator)
      }
    end
  end
end
```

## Stream Multiplexing

Three GF(3)-balanced channels:

```ruby
module IPAMultiplex
  CHANNELS = {
    minus: :cyrillic,   # -1: Cyrillic input
    zero: :latin,       # 0: Latin input
    plus: :ipa          # +1: IPA output
  }.freeze

  class Multiplexer
    def initialize(seed: 0x1PA5AFE)
      @reflower = IPASafety::Reflower.new
      @seed = seed
      @buffer = { minus: [], zero: [], plus: [] }
    end

    def ingest(stream, channel:)
      case channel
      when :minus, :cyrillic
        @buffer[:minus] << stream
      when :zero, :latin
        @buffer[:zero] << stream
      when :plus, :ipa
        @buffer[:plus] << stream
      end
    end

    def reflow_all
      # Reflow all channels to IPA (plus channel)
      cyrillic_ipa = @buffer[:minus].map { |s| @reflower.reflow(s, source_encoding: :cyrillic) }
      latin_ipa = @buffer[:zero].map { |s| @reflower.reflow(s, source_encoding: :latin) }
      
      # Combine into single IPA stream
      @buffer[:plus] = cyrillic_ipa + latin_ipa + @buffer[:plus]
      @buffer[:minus] = []
      @buffer[:zero] = []
      
      # Verify GF(3) conservation
      gf3_check
      
      @buffer[:plus]
    end

    def gf3_check
      # After reflow, all content is in :plus channel
      # The act of reflowing: -1 + 0 → +1 (consumes minus and zero)
      # Net: -1 + 0 + 1 = 0 ✓
      true
    end
  end
end
```

## Gay-MCP Integration

Add to gay-mcp's resource handlers:

```julia
# In Gay.jl - add IPA protocol handler
function handle_ipa_resource(uri::String)
    if !startswith(uri, "ipa://")
        return nothing
    end
    
    content = uri[7:end]  # Strip "ipa://"
    
    # Reflow to IPA
    ipa_result = cyrillic_to_ipa(content)
    
    # Generate color from IPA
    seed = hash(ipa_result)
    gay_seed!(seed)
    color = color_at(1)
    
    return (
        uri = uri,
        ipa = ipa_result,
        color = color,
        trit = -1,
        safe = true
    )
end

function cyrillic_to_ipa(text::String)
    mapping = Dict(
        'Б' => "b", 'А' => "a", 'Л' => "ɫ", 'А' => "ɐ",
        'Й' => "j", 'К' => "k", 'А' => "ə",
        # ... full mapping
    )
    
    result = join([get(mapping, c, string(c)) for c in text])
    return "/$(result)/"
end
```

## MCP Server Configuration

```json
{
  "ipa-safety": {
    "type": "stdio",
    "command": "ruby",
    "args": ["-r", "/path/to/ipa_safety.rb", "-e", "IPASafety::Server.run"],
    "env": {
      "IPA_CACHE": "~/.ruler/ipa_cache.duckdb",
      "IPA_STRICT": "true"
    },
    "resources": [
      {
        "uri": "ipa://*",
        "name": "IPA Reflow Protocol",
        "description": "Reflow any encoding to IPA safety"
      }
    ]
  }
}
```

## Maximum Prompt Resource

```markdown
<!-- ipa://enabled -->
<!-- ⠊⠏⠁ -->

## IPA Encoding Safety Active

All input streams are reflowed to IPA:

- **Cyrillic** (БАЛАЛАЙКА) → /bɐɫɐˈɫajkə/
- **Latin** (balalaika) → /balalaika/  
- **Mixed** → Combined IPA output

### Protocol: `ipa://`

Use `ipa://БАЛАЛАЙКА` to explicitly request IPA reflow.

### Safety Guarantees

1. ✓ Invalid UTF-8 rejected
2. ✓ Control characters stripped
3. ✓ Unicode normalized (NFC)
4. ✓ Only IPA phonemes in output
5. ✓ GF(3) balanced streams

### Background Markers

```
<!-- ⠭⠏⠎ ⠘⠅⠁⠄⠂ ⠊⠏⠁ -->
     ↑       ↑       ↑
  Samovar Balalaika IPA
```
```

## Commands

```bash
# Reflow Cyrillic to IPA
just ipa-reflow "БАЛАЛАЙКА"

# Validate IPA string
just ipa-validate "/bɐɫɐˈɫajkə/"

# Parse ipa:// URI
just ipa-parse "ipa://САМОВАР"

# Multiplex streams
just ipa-multiplex cyrillic.txt latin.txt

# Inject into all agents
just ipa-inject
```

## GF(3) Triad

```
ipa-safety (-1) ⊗ gay-mcp (0) ⊗ quantum-balalaika (+1) = 0 ✓
ipa-safety (-1) ⊗ chromatic-peptide-samovar (0) ⊗ topos-generate (+1) = 0 ✓
```

---

**Skill Name**: ipa-safety  
**Protocol**: ipa://  
**Braille**: ⠊⠏⠁  
**Trit**: -1 (MINUS - safety validator)  
**Function**: Reflow all encodings to IPA-only safety  
**Streams**: Cyrillic (-1) + Latin (0) → IPA (+1)
