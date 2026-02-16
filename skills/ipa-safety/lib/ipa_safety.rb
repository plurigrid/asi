# IPA Encoding Safety
# Protocol: ipa://
# Braille: ⠊⠏⠁
# Trit: -1 (MINUS - safety validator)

require 'json'
require 'digest'

module IPASafety
  VERSION = '1.0.0'
  BRAILLE = '⠊⠏⠁'
  TRIT = -1

  # Complete Cyrillic → IPA mapping (Russian)
  CYRILLIC_TO_IPA = {
    # Uppercase
    'А' => 'a', 'Б' => 'b', 'В' => 'v', 'Г' => 'g', 'Д' => 'd',
    'Е' => 'je', 'Ё' => 'jo', 'Ж' => 'ʐ', 'З' => 'z', 'И' => 'i',
    'Й' => 'j', 'К' => 'k', 'Л' => 'ɫ', 'М' => 'm', 'Н' => 'n',
    'О' => 'o', 'П' => 'p', 'Р' => 'r', 'С' => 's', 'Т' => 't',
    'У' => 'u', 'Ф' => 'f', 'Х' => 'x', 'Ц' => 'ts', 'Ч' => 'tɕ',
    'Ш' => 'ʂ', 'Щ' => 'ɕː', 'Ъ' => '', 'Ы' => 'ɨ', 'Ь' => 'ʲ',
    'Э' => 'e', 'Ю' => 'ju', 'Я' => 'ja',
    # Lowercase
    'а' => 'ɐ', 'б' => 'b', 'в' => 'v', 'г' => 'ɡ', 'д' => 'd',
    'е' => 'ʲe', 'ё' => 'ʲo', 'ж' => 'ʐ', 'з' => 'z', 'и' => 'ɪ',
    'й' => 'j', 'к' => 'k', 'л' => 'l', 'м' => 'm', 'н' => 'n',
    'о' => 'ɐ', 'п' => 'p', 'р' => 'r', 'с' => 's', 'т' => 't',
    'у' => 'u', 'ф' => 'f', 'х' => 'x', 'ц' => 'ts', 'ч' => 'tɕ',
    'ш' => 'ʂ', 'щ' => 'ɕː', 'ъ' => '', 'ы' => 'ɨ', 'ь' => 'ʲ',
    'э' => 'e', 'ю' => 'ʲu', 'я' => 'ʲa',
    # Common
    ' ' => '.', '-' => '-', '\'' => 'ˈ'
  }.freeze

  # Valid IPA characters
  IPA_CHARS = /^[\/\.\s\-ˈˌːʲʷa-zɐɑæɛəɪɨʊʌɒœøɔeiouyɾɹɻrʀʁlɫɬɮʎʟmnɲŋɴpbtdʈɖcɟkgqɢʔfvθðszʃʒʂʐɕʑçʝxɣχħʕhɦwʍɥʋɰjɺβɸʙɽʢʡǀǁǂǃ]+$/i

  # Maximum allowed Unicode codepoint (below emoji)
  MAX_CODEPOINT = 0x1F000

  class Reflower
    def initialize(strict: true)
      @strict = strict
      @cache = {}
    end

    def reflow(input, source_encoding: :auto)
      cache_key = "#{input}:#{source_encoding}"
      return @cache[cache_key] if @cache.key?(cache_key)

      # Step 1: Normalize UTF-8
      normalized = normalize_utf8(input)

      # Step 2: Safety checks
      if @strict
        validate_codepoints!(normalized)
        strip_control_chars!(normalized)
      end

      # Step 3: Detect encoding if auto
      encoding = source_encoding == :auto ? detect_encoding(normalized) : source_encoding

      # Step 4: Reflow to IPA
      result = case encoding
               when :cyrillic then cyrillic_to_ipa(normalized)
               when :latin then latin_to_ipa(normalized)
               else mixed_to_ipa(normalized)
               end

      @cache[cache_key] = result
      result
    end

    def cyrillic_to_ipa(text)
      phonemes = text.chars.map { |c| CYRILLIC_TO_IPA[c] || c }
      "/#{phonemes.join}/"
    end

    def latin_to_ipa(text)
      # Basic Latin → IPA (English approximation)
      "/#{text.downcase.gsub(/\s+/, '.')}/"
    end

    def mixed_to_ipa(text)
      phonemes = text.chars.map do |c|
        CYRILLIC_TO_IPA[c] || c.downcase
      end
      "/#{phonemes.join}/"
    end

    def validate(ipa_string)
      {
        input: ipa_string,
        valid: ipa_string.match?(IPA_CHARS),
        length: ipa_string.length,
        phonemes: ipa_string.gsub(/[\/\.\s]/, '').length
      }
    end

    private

    def normalize_utf8(input)
      input.to_s
           .encode('UTF-8', invalid: :replace, undef: :replace, replace: '?')
           .unicode_normalize(:nfc)
    end

    def validate_codepoints!(text)
      text.each_codepoint do |cp|
        if cp > MAX_CODEPOINT
          raise EncodingError, "Codepoint U+#{cp.to_s(16).upcase} exceeds maximum"
        end
      end
    end

    def strip_control_chars!(text)
      text.gsub!(/[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]/, '')
    end

    def detect_encoding(text)
      cyrillic_count = text.scan(/[А-Яа-яЁё]/).size
      latin_count = text.scan(/[A-Za-z]/).size

      if cyrillic_count > latin_count * 2
        :cyrillic
      elsif latin_count > cyrillic_count * 2
        :latin
      else
        :mixed
      end
    end
  end

  # GF(3) Multiplexer
  class Multiplexer
    CHANNELS = { minus: -1, zero: 0, plus: 1 }.freeze

    def initialize
      @reflower = Reflower.new
      @buffers = { minus: [], zero: [], plus: [] }
    end

    def ingest(content, channel:)
      ch = normalize_channel(channel)
      @buffers[ch] << content
    end

    def reflow_all
      # Reflow cyrillic (minus) and latin (zero) to IPA (plus)
      cyrillic_ipa = @buffers[:minus].map { |s| @reflower.reflow(s, source_encoding: :cyrillic) }
      latin_ipa = @buffers[:zero].map { |s| @reflower.reflow(s, source_encoding: :latin) }

      # All output goes to plus channel
      output = cyrillic_ipa + latin_ipa + @buffers[:plus]

      # Clear input channels
      @buffers[:minus] = []
      @buffers[:zero] = []
      @buffers[:plus] = output

      # Verify GF(3): -1 + 0 + 1 = 0
      gf3_sum = CHANNELS.values.sum
      raise "GF(3) violation: sum=#{gf3_sum}" unless gf3_sum == 0

      output
    end

    private

    def normalize_channel(ch)
      case ch.to_s.downcase.to_sym
      when :minus, :cyrillic, :"-1" then :minus
      when :zero, :latin, :"0" then :zero
      when :plus, :ipa, :"1", :"+1" then :plus
      else :zero
      end
    end
  end

  # Protocol handler for ipa:// URIs
  class Protocol
    def self.parse(uri)
      return nil unless uri.to_s.start_with?('ipa://')

      path = URI.decode_www_form_component(uri.to_s.sub('ipa://', ''))
      reflower = Reflower.new

      ipa = reflower.reflow(path)
      validation = reflower.validate(ipa)

      {
        uri: uri,
        original: path,
        ipa: ipa,
        valid: validation[:valid],
        trit: TRIT,
        braille: BRAILLE,
        seed: Digest::SHA256.hexdigest(ipa)[0..15].to_i(16)
      }
    end
  end

  # MCP Server
  class MCPServer
    def self.run
      server = new
      server.start
    end

    def initialize
      @reflower = Reflower.new
      @multiplexer = Multiplexer.new
    end

    def start
      loop do
        line = $stdin.gets
        break if line.nil?

        request = JSON.parse(line)
        response = handle_request(request)
        $stdout.puts JSON.generate(response)
        $stdout.flush
      end
    end

    private

    def handle_request(request)
      case request['method']
      when 'tools/call'
        handle_tool(request['params'])
      when 'resources/read'
        handle_resource(request['params'])
      else
        { error: "Unknown method: #{request['method']}" }
      end
    end

    def handle_tool(params)
      case params['name']
      when 'ipa_reflow'
        text = params['arguments']['text']
        encoding = params['arguments']['source_encoding'] || 'auto'
        ipa = @reflower.reflow(text, source_encoding: encoding.to_sym)
        { content: [{ type: 'text', text: ipa }] }

      when 'ipa_validate'
        ipa = params['arguments']['ipa']
        result = @reflower.validate(ipa)
        { content: [{ type: 'text', text: JSON.generate(result) }] }

      when 'ipa_multiplex'
        streams = params['arguments']['streams']
        streams.each { |s| @multiplexer.ingest(s['content'], channel: s['channel']) }
        output = @multiplexer.reflow_all
        { content: [{ type: 'text', text: output.join("\n") }] }

      else
        { error: "Unknown tool: #{params['name']}" }
      end
    end

    def handle_resource(params)
      uri = params['uri']
      result = Protocol.parse(uri)

      if result
        { contents: [{ uri: uri, mimeType: 'text/plain', text: result[:ipa] }] }
      else
        { error: "Invalid IPA URI: #{uri}" }
      end
    end
  end
end

# CLI
if __FILE__ == $PROGRAM_NAME
  if ARGV[0] == 'serve'
    IPASafety::MCPServer.run
  elsif ARGV[0]
    input = ARGV.join(' ')
    reflower = IPASafety::Reflower.new
    puts reflower.reflow(input)
  else
    puts "Usage: ruby ipa_safety.rb <text>  OR  ruby ipa_safety.rb serve"
  end
end
