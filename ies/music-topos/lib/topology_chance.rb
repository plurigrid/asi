# Topological Reconstruction Logic
# "2-torus to 1-torus back to the SAME EXACT 2-torus only by chance"

class Z12
  attr_reader :value
  
  def initialize(value)
    @value = value % 12
  end

  def ==(other)
    other.is_a?(Z12) && @value == other.value
  end

  def to_s
    "Z12(#{@value})"
  end
end

class Torus2
  attr_reader :x, :y

  def initialize(x, y)
    @x = Z12.new(x)
    @y = Z12.new(y)
  end

  def ==(other)
    other.is_a?(Torus2) && @x == other.x && @y == other.y
  end

  def to_s
    "T2(#{@x.value}, #{@y.value})"
  end

  # Projection to 1-Torus (forget y)
  # T^2 -> T^1
  def project
    Torus1.new(@x.value)
  end
end

class Torus1
  attr_reader :x

  def initialize(x)
    @x = Z12.new(x)
  end

  def ==(other)
    other.is_a?(Torus1) && @x == other.x
  end

  def to_s
    "T1(#{@x.value})"
  end

  # Lift back to 2-Torus
  # T^1 -> T^2
  # Since information is lost, we must guess 'y'.
  # This represents the "chance" element.
  def lift_random
    y_guess = rand(12)
    Torus2.new(@x.value, y_guess)
  end
end

# Simulation
def run_simulation(trials = 1000)
  puts "Running Topological Reconstruction Simulation..."
  puts "Domain: Discrete Torus (Z12 x Z12)"
  puts "Mapping: (x,y) -> x -> (x, y_random)"
  
  successes = 0
  
  trials.times do |i|
    # 1. Start with a specific point on the 2-torus
    original = Torus2.new(rand(12), rand(12))
    
    # 2. Project to 1-torus (Lossy)
    projected = original.project
    
    # 3. Attempt to reconstruct (Lift)
    reconstructed = projected.lift_random
    
    # 4. Check if we got the SAME EXACT 2-torus point
    if original == reconstructed
      successes += 1
    end
  end
  
  probability = successes.to_f / trials
  puts "Trials: #{trials}"
  puts "Successes: #{successes}"
  puts "Probability: #{probability}"
  puts "Theoretical Probability (1/12): #{1.0/12}"
  
  if (probability - (1.0/12)).abs < 0.05
    puts "Result: Confirmed 'Only by chance' (Random guessing matches theoretical probability)"
  else
    puts "Result: Deviation detected (Check RNG)"
  end
end

if __FILE__ == $0
  run_simulation
end
