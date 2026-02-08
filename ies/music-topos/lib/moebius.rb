# lib/moebius.rb
#
# Möbius Inversion on computational lattices
#
# Classical: f(n) = Σ_{d|n} g(d)  ⟹  g(n) = Σ_{d|n} μ(n/d)f(d)
#
# Generalized to prefix-free program lattice:
# - Programs ordered by prefix relation (≤ₚ)
# - Möbius function μ(p,q) on interval [p,q]
# - Inversion recovers "atomic" program contributions

module Moebius
  # Classical Möbius function μ(n)
  # μ(1) = 1
  # μ(n) = 0 if n has squared prime factor
  # μ(n) = (-1)^k if n is product of k distinct primes
  def self.mu(n)
    return 1 if n == 1
    return 0 if n <= 0

    # Factor n
    factors = prime_factors(n)
    return 0 if factors.any? { |_, exp| exp > 1 }  # squared factor

    (-1) ** factors.size
  end

  def self.prime_factors(n)
    factors = {}
    d = 2
    while d * d <= n
      while (n % d).zero?
        factors[d] = (factors[d] || 0) + 1
        n /= d
      end
      d += 1
    end
    factors[n] = (factors[n] || 0) + 1 if n > 1
    factors
  end

  # Divisors of n
  def self.divisors(n)
    (1..Math.sqrt(n).to_i).select { |d| (n % d).zero? }
                          .flat_map { |d| [d, n / d] }
                          .uniq.sort
  end

  # Classical Möbius inversion
  # Given f(n) = Σ_{d|n} g(d), recover g(n)
  def self.invert(f_values, n)
    divisors(n).sum { |d| mu(n / d) * (f_values[d] || 0) }
  end

  # Möbius transform: g(n) → f(n) = Σ_{d|n} g(d)
  def self.transform(g_values, max_n)
    (1..max_n).to_h { |n| [n, divisors(n).sum { |d| g_values[d] || 0 }] }
  end

  # Prefix Lattice for Programs
  # p ≤ q iff p is a prefix of q (in ternary encoding)
  class PrefixLattice
    attr_reader :programs

    def initialize
      @programs = {}  # encoding → program
      @cache = {}     # memoization for μ
    end

    def add(encoding, program)
      @programs[encoding] = program
      @cache.clear
    end

    def prefix?(p, q)
      p.length <= q.length && q.start_with?(p)
    end

    def interval(p, q)
      return [] unless prefix?(p, q)
      @programs.keys.select { |r| prefix?(p, r) && prefix?(r, q) }
    end

    # Möbius function on prefix lattice
    # μ(p,p) = 1
    # μ(p,q) = -Σ_{p≤r<q} μ(p,r) for p < q
    def mu_lattice(p, q)
      return 0 unless prefix?(p, q)
      return 1 if p == q

      key = [p, q]
      return @cache[key] if @cache.key?(key)

      # Sum over strict subinterval
      result = -interval(p, q).reject { |r| r == q }
                              .sum { |r| mu_lattice(p, r) }
      @cache[key] = result
    end

    # Inversion on prefix lattice
    # If F(q) = Σ_{p≤q} f(p), then f(q) = Σ_{p≤q} μ(p,q)F(p)
    def invert_prefix(f_values, q)
      @programs.keys.select { |p| prefix?(p, q) }
                    .sum { |p| mu_lattice(p, q) * (f_values[p] || 0) }
    end
  end

  # Ternary Möbius encoding
  # Maps integers to prefix-free ternary codes
  class TernaryEncoder
    # Elias-like prefix-free code in ternary
    # Length prefix: unary in ternary, then payload
    def self.encode(n)
      return "0" if n == 0
      
      # Convert to balanced ternary
      trits = []
      temp = n.abs
      while temp > 0
        rem = temp % 3
        temp /= 3
        if rem == 2
          rem = -1
          temp += 1
        end
        trits << rem
      end
      
      # Prefix: length in unary (1s followed by 0)
      len = trits.size
      prefix = "1" * len + "0"
      
      # Payload: balanced ternary
      payload = trits.reverse.map { |t| t == -1 ? 'T' : t.to_s }.join
      
      prefix + payload
    end

    def self.decode(code)
      # Find prefix (count 1s until 0)
      len = code.index('0')
      return 0 if len.nil? || len == 0
      
      payload = code[(len + 1)..(len + len)]
      return 0 if payload.nil?
      
      # Decode balanced ternary
      payload.chars.reduce(0) do |acc, c|
        val = c == 'T' ? -1 : c.to_i
        acc * 3 + val
      end
    end

    # Generate all prefix-free codes up to length n
    def self.all_codes(max_length)
      (0..(3 ** (max_length / 2))).map { |i| encode(i) }
                                   .select { |c| c.length <= max_length }
    end
  end
end
