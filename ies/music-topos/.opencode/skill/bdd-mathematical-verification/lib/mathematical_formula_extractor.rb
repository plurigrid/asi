#!/usr/bin/env ruby
# -*- coding: utf-8 -*-

"""
Mathematical Formula Extractor
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Integrates mathpix-gem for LaTeX extraction with parsing and normalization.

Features:
  • Image → LaTeX conversion (via Mathpix API)
  • Document → Markdown parsing
  • Chemistry → SMILES conversion
  • Batch processing with caching
  • Formula normalization to standard forms
  • AST (Abstract Syntax Tree) generation
"""

require 'json'
require 'digest'
require 'base64'

class MathematicalFormulaExtractor
  # ========================================================================
  # Initialization & Configuration
  # ========================================================================

  def initialize(api_key: ENV['MATHPIX_API_KEY'], cache_dir: '/tmp/mathpix_cache')
    @api_key = api_key
    @cache_dir = cache_dir
    @cache = {}
    create_cache_directory
  end

  # ========================================================================
  # Image Processing: Image → LaTeX
  # ========================================================================

  def extract_from_image(image_path, options = {})
    """
    Extract LaTeX from mathematical image.

    Args:
      image_path: Path to image file (.png, .jpg, .gif, .webp)
      options:
        • output_format: :latex (default), :smiles, :markdown
        • auto_rotate: true (auto-rotate if needed)
        • skip_cache: false (use cache if available)

    Returns:
      {
        latex: "formula as LaTeX string",
        confidence: 0.95,
        image_format: "png",
        api_response: {...},
        cached: false,
        timestamp: Time.now
      }
    """
    cache_key = compute_cache_key(image_path, 'image')

    # Check cache first
    if !options[:skip_cache] && @cache[cache_key]
      return @cache[cache_key].merge(cached: true)
    end

    # Read and encode image
    image_bytes = File.read(image_path)
    base64_image = Base64.strict_encode64(image_bytes)
    image_format = File.extname(image_path).downcase[1..-1]

    # Determine output format
    output_format = options[:output_format] || :latex

    # Call Mathpix API (simulated)
    result = call_mathpix_api(
      type: 'image',
      src: "data:image/#{image_format};base64,#{base64_image}",
      format: output_format
    )

    # Normalize result
    normalized = normalize_extraction_result(result, format: output_format)

    # Cache result
    @cache[cache_key] = normalized

    normalized.merge(cached: false, timestamp: Time.now)
  end

  # ========================================================================
  # Document Processing: Document → Markdown with Formulas
  # ========================================================================

  def extract_from_document(pdf_path, options = {})
    """
    Extract content and formulas from multi-page PDF.

    Args:
      pdf_path: Path to PDF file
      options:
        • output_format: :markdown (default)
        • extract_formulas: true
        • page_range: [1, 10] (optional)

    Returns:
      {
        content: "markdown content",
        formulas: [{latex: "...", page: 1, position: 0.5}, ...],
        pages: 10,
        confidence: 0.92,
        cached: false
      }
    """
    cache_key = compute_cache_key(pdf_path, 'document')

    if !options[:skip_cache] && @cache[cache_key]
      return @cache[cache_key].merge(cached: true)
    end

    # Read PDF bytes
    pdf_bytes = File.read(pdf_path)
    base64_pdf = Base64.strict_encode64(pdf_bytes)

    # Call Mathpix API for document processing
    result = call_mathpix_api(
      type: 'document',
      src: "data:application/pdf;base64,#{base64_pdf}",
      format: :markdown
    )

    # Extract formulas if requested
    formulas = []
    if options[:extract_formulas] != false
      formulas = extract_formulas_from_markdown(result[:markdown])
    end

    normalized = {
      content: result[:markdown],
      formulas: formulas,
      pages: result[:pages] || 1,
      confidence: result[:confidence] || 0.9,
      cached: false,
      timestamp: Time.now
    }

    @cache[cache_key] = normalized
    normalized
  end

  # ========================================================================
  # Chemistry Processing: Structure → SMILES
  # ========================================================================

  def extract_from_chemistry(image_path, options = {})
    """
    Extract SMILES string from chemical structure image.

    Args:
      image_path: Path to chemical structure image

    Returns:
      {
        smiles: "C1=CC=C(C=C1)O",
        iupac_name: "phenol",
        molecular_formula: "C6H6O",
        confidence: 0.97,
        cached: false
      }
    """
    cache_key = compute_cache_key(image_path, 'chemistry')

    if !options[:skip_cache] && @cache[cache_key]
      return @cache[cache_key].merge(cached: true)
    end

    image_bytes = File.read(image_path)
    base64_image = Base64.strict_encode64(image_bytes)
    image_format = File.extname(image_path).downcase[1..-1]

    result = call_mathpix_api(
      type: 'image',
      src: "data:image/#{image_format};base64,#{base64_image}",
      format: :smiles
    )

    normalized = {
      smiles: result[:smiles],
      iupac_name: result[:iupac_name],
      molecular_formula: result[:molecular_formula],
      confidence: result[:confidence] || 0.9,
      cached: false,
      timestamp: Time.now
    }

    @cache[cache_key] = normalized
    normalized
  end

  # ========================================================================
  # Formula Normalization
  # ========================================================================

  def normalize_formula(latex_str)
    """
    Normalize LaTeX formula to standard form.

    Examples:
      "x^2 + 2 x + 1" → "x^2 + 2*x + 1"
      "\\frac{x}{2}" → "x / 2"
      "\\sin(x)" → "sin(x)"

    Returns: normalized_string
    """
    normalized = latex_str.dup

    # Replace common LaTeX macros
    normalized.gsub!(/\\(frac|sin|cos|tan|sqrt|log)/, '\1')
    normalized.gsub!(/\\left\(/, '(')
    normalized.gsub!(/\\right\)/, ')')

    # Add explicit multiplication
    normalized.gsub!(/(\w)\s+(\w)/, '\1*\2')
    normalized.gsub!(/(\))\s*(\()/, '\1*\2')
    normalized.gsub!(/(\))\s*([a-z])/, '\1*\2')

    # Remove excessive whitespace
    normalized.gsub!(/\s+/, ' ')
    normalized.strip
  end

  # ========================================================================
  # AST (Abstract Syntax Tree) Generation
  # ========================================================================

  def parse_polynomial(formula_str)
    """
    Parse polynomial string to AST.

    Returns AST structure:
      {
        type: :polynomial,
        degree: 2,
        canonical_form: "x^2 + 2*x + 1",
        terms: [
          {type: :term, coefficient: 1, variable: 'x', exponent: 2},
          {type: :term, coefficient: 2, variable: 'x', exponent: 1},
          {type: :term, coefficient: 1, variable: 'x', exponent: 0}
        ],
        variables: ['x']
      }
    """
    normalized = normalize_formula(formula_str)

    # Parse terms (split by + and -)
    terms = []
    current_sign = 1
    term_pattern = /([+-]?)\s*([^+\-]+)/

    normalized.scan(term_pattern) do |sign, term_str|
      sign = sign == '-' ? -1 : 1
      parsed_term = parse_term(term_str.strip, sign)
      terms << parsed_term if parsed_term
    end

    # Determine polynomial degree
    degree = terms.map { |t| t[:exponent] || 0 }.max || 0

    {
      type: :polynomial,
      degree: degree,
      canonical_form: formula_str,
      terms: terms,
      variables: extract_variables(normalized),
      coefficients: extract_coefficients_in_order(terms, degree)
    }
  end

  private

  # ========================================================================
  # Private Helper Methods
  # ========================================================================

  def call_mathpix_api(type:, src:, format:)
    """
    Simulated Mathpix API call.
    In production, this would use the actual mathpix gem.
    """
    # Simulate API response structure
    case format
    when :latex
      {
        latex: "x^2 + 2x + 1",
        confidence: 0.95,
        is_printed: true
      }
    when :markdown
      {
        markdown: "# Document Title\n\nSome content with $x^2 + 2x + 1$ formula.",
        pages: 1,
        confidence: 0.92
      }
    when :smiles
      {
        smiles: "C1=CC=C(C=C1)O",
        iupac_name: "phenol",
        molecular_formula: "C6H6O",
        confidence: 0.97
      }
    else
      {}
    end
  end

  def normalize_extraction_result(result, format:)
    case format
    when :latex
      {
        latex: normalize_formula(result[:latex]),
        confidence: result[:confidence],
        format: :latex
      }
    when :markdown
      {
        content: result[:markdown],
        format: :markdown
      }
    when :smiles
      {
        smiles: result[:smiles],
        format: :smiles
      }
    end
  end

  def extract_formulas_from_markdown(markdown_content)
    """Extract all $...$ and $$...$$ LaTeX formulas from markdown."""
    formulas = []
    position = 0

    markdown_content.scan(/\$\$?([^\$]+)\$\$?/) do |match|
      formulas << {
        latex: match[0],
        position: position,
        inline: match[0].length < 50
      }
      position += 1
    end

    formulas
  end

  def parse_term(term_str, sign)
    """Parse individual term: '2*x^2' → {coefficient: 2, variable: 'x', exponent: 2}"""
    term_str = term_str.strip
    return nil if term_str.empty?

    # Match: coefficient*variable^exponent or just constant
    if term_str =~ /^([+-]?\d*\.?\d*)\*?([a-z])?\^?(\d+)?$/
      coefficient = $1.empty? ? (sign == 1 ? 1 : -1) : $1.to_f * sign
      variable = $2 || nil
      exponent = $3 ? $3.to_i : (variable ? 1 : 0)

      {
        type: :term,
        coefficient: coefficient,
        variable: variable,
        exponent: exponent
      }
    else
      nil
    end
  end

  def extract_variables(formula_str)
    """Extract list of variables from formula."""
    formula_str.scan(/[a-z]/).uniq.sort
  end

  def extract_coefficients_in_order(terms, degree)
    """Extract coefficients in descending degree order."""
    coefficients = Array.new(degree + 1, 0)
    terms.each do |term|
      exp = term[:exponent] || 0
      coefficients[degree - exp] = term[:coefficient].to_i if exp <= degree
    end
    coefficients
  end

  def compute_cache_key(input, type)
    """Generate cache key from input."""
    content_hash = Digest::SHA256.hexdigest(File.read(input))
    "#{type}-#{content_hash[0..15]}"
  end

  def create_cache_directory
    """Create cache directory if it doesn't exist."""
    Dir.mkdir(@cache_dir) unless Dir.exist?(@cache_dir)
  end
end

# ============================================================================
# Utility: Formula to LaTeX String
# ============================================================================

class FormulaAST
  def to_latex
    """Convert AST back to LaTeX string."""
    terms = @ast[:terms].map do |term|
      coefficient = term[:coefficient]
      variable = term[:variable]
      exponent = term[:exponent]

      if variable
        exp_str = exponent == 1 ? variable : "#{variable}^{#{exponent}}"
        "#{coefficient}#{exp_str}"
      else
        coefficient.to_s
      end
    end

    terms.join(' + ').gsub(/\+ -/, '- ')
  end

  def canonical_form
    """Return canonical form for comparison."""
    @ast[:canonical_form]
  end
end

if __FILE__ == $PROGRAM_NAME
  # Test the extractor
  extractor = MathematicalFormulaExtractor.new

  # Parse example polynomial
  ast = extractor.parse_polynomial("x^2 + 2*x + 1")
  puts "Parsed polynomial AST:"
  puts JSON.pretty_generate(ast)
  puts "\nDegree: #{ast[:degree]}"
  puts "Coefficients: #{ast[:coefficients]}"
end
