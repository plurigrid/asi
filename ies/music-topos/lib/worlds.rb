# lib/worlds.rb
require 'set'
require_relative 'pitch_class'
require_relative 'chord'

module MusicalWorlds
  class World
    attr_reader :objects, :metric, :name

    def initialize(name, metric_fn)
      @name = name
      @metric = metric_fn
      @objects = Set.new
    end

    def add_object(obj)
      @objects.add(obj)
    end

    def appearance(obj)
      exists = @objects.include?(obj)
      total_dist = 0
      relations_count = 0
      
      if exists
        @objects.each do |other|
          if obj != other
            total_dist += distance(obj, other)
            relations_count += 1
          end
        end
      end
      
      intensity = relations_count > 0 ? 1.0 : 0.0 # Simplification
      
      {
        exists: exists,
        intensity: intensity,
        relations_count: relations_count,
        total_distance: total_dist
      }
    end

    def distance(obj1, obj2)
      # Check triangle inequality here if we had all shortest paths, 
      # but for now we just compute the metric.
      # The real enforcement happens when we validate the metric space.
      @metric.call(obj1, obj2)
    end

    def validate_metric_space
      errors = []
      objects_arr = @objects.to_a
      
      # Positivity & Symmetry
      objects_arr.each do |o1|
        objects_arr.each do |o2|
          d = distance(o1, o2)
          if d < 0
            errors << "Positivity violation: d(#{o1}, #{o2}) = #{d}"
          end
          d_sym = distance(o2, o1)
          if d != d_sym
            errors << "Symmetry violation: d(#{o1},#{o2})=#{d} != d(#{o2},#{o1})=#{d_sym}"
          end
        end
      end
      
      # Triangle Inequality
      objects_arr.each do |a|
        objects_arr.each do |b|
          objects_arr.each do |c|
            d_ab = distance(a, b)
            d_bc = distance(b, c)
            d_ac = distance(a, c)
            
            if d_ac > d_ab + d_bc + 1e-10 # allow floating point slop
               errors << "Triangle inequality violation: #{d_ac} > #{d_ab} + #{d_bc} for #{a},#{b},#{c}"
            end
          end
        end
      end
      
      {
        valid: errors.empty?,
        errors: errors,
        objects_count: @objects.size
      }
    end

    # Reachability: Can we find a path of morphisms to another world?
    def reachable?(other_world, depth = 3)
      # In a connected Topos, every world is eventually reachable 
      # through compositions of functors and natural transformations.
      # For now, we stub this as true if they share a common object type.
      return true if self.name == other_world.name
      
      # Objects in pitch space can reach chord space via the 'from_pitch_classes' functor
      if self.name == "PitchSpace" && other_world.name == "ChordSpace"
        return true
      end
      
      false
    end
  end

  class HarmonicWorld < World
    FUNCTIONS = {T: 0, S: 1, D: 2}

    def self.functional_metric
      lambda do |f1, f2|
        return 0 if f1 == f2
        # T-S-D distance logic
        # T <-> S : 1
        # S <-> D : 1
        # T <-> D : 2 (via S, usually) - or direct if we consider them connected?
        # The prompt says: "T↔S: 1, S↔D: 1, D↔T: 1, T↔D: 2" - wait, D-T is resolution (1).
        # Let's assume standard functional map: T-S-D-T
        
        v1 = f1.is_a?(Symbol) ? FUNCTIONS[f1] : f1
        v2 = f2.is_a?(Symbol) ? FUNCTIONS[f2] : f2
        
        return (v1 - v2).abs
      end
    end

    def self.world
      new("HarmonicWorld", functional_metric)
    end
  end

  class TransformationWorld < World
    ELEMENTS = [:id, :P, :R, :L, :PR, :RL]
    
    def self.group_metric
      lambda { |g1, g2| cayley_distance(g1, g2) }
    end
    
    def self.cayley_distance(g1, g2)
       # Simplified stub: real impl would use BFS on Cayley graph
       return 0 if g1 == g2
       1 
    end

    def self.world
      new("TransformationWorld", group_metric)
    end
  end

  def self.pitch_space_world
    World.new("PitchSpace", lambda { |p1, p2| p1.distance(p2) })
  end

  def self.chord_space_world
    World.new("ChordSpace", lambda { |c1, c2| c1.voice_leading_distance(c2) })
  end
end
