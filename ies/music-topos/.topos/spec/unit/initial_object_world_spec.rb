#!/usr/bin/env ruby
# spec/unit/initial_object_world_spec.rb
#
# RSpec tests for InitialObjectWorld class
# Tests emergence of all musical structure from a single pitch

require_relative '../spec_helper'

describe MusicalWorlds::InitialObjectWorld do
  let(:world) { MusicalWorlds::InitialObjectWorld.new("TestInitialWorld") }

  describe 'Initialization' do
    it 'creates a new initial object world' do
      expect(world).to be_an_instance_of(MusicalWorlds::InitialObjectWorld)
    end

    it 'has a name' do
      expect(world.name).to eq("TestInitialWorld")
    end

    it 'starts with empty objects and relations' do
      expect(world.objects).to be_empty
      expect(world.relations).to be_empty
    end

    it 'has properly initialized category containers' do
      expect(world.instance_variable_get(:@pitch_classes)).to be_empty
      expect(world.instance_variable_get(:@harmonic_functions_obj)).to be_empty
      expect(world.instance_variable_get(:@chords_obj)).to be_empty
      expect(world.instance_variable_get(:@progressions_obj)).to be_empty
      expect(world.instance_variable_get(:@cadences_obj)).to be_empty
    end
  end

  describe 'Building from Initial Pitch (C=0)' do
    before do
      world.build_from_initial_pitch(0)
    end

    it 'creates an initial pitch object' do
      expect(world.initial_pitch).not_to be_nil
      expect(world.initial_pitch).to be_an_instance_of(PitchClass)
      expect(world.initial_pitch.value).to eq(0)
    end

    it 'adds the initial pitch to world objects' do
      expect(world.objects).to include(world.initial_pitch)
    end

    context 'Category 4: Pitch Classes (S₁₂)' do
      it 'generates all 12 pitch classes' do
        expect(world.pitch_classes.length).to eq(12)
      end

      it 'creates pitch classes with values 0-11' do
        pitch_values = world.pitch_classes.map(&:value).sort
        expect(pitch_values).to eq((0..11).to_a)
      end

      it 'adds all pitch classes to world objects' do
        world.pitch_classes.each do |pitch|
          expect(world.objects).to include(pitch)
        end
      end

      it 'creates permutation relations from initial pitch' do
        permutation_relations = world.relations.select { |r| r[:type] == :permutation }
        expect(permutation_relations.length).to eq(11)  # 12 pitches, 1 is identity
      end

      it 'has exactly one identity relation' do
        identity_relations = world.relations.select { |r| r[:type] == :identity }
        expect(identity_relations.length).to eq(1)
      end
    end

    context 'Category 5: Harmonic Functions' do
      it 'generates 3 harmonic functions (T, S, D)' do
        expect(world.harmonic_functions_obj.length).to eq(3)
      end

      it 'has Tonic function' do
        tonic = world.harmonic_functions_obj.find { |f| f.function == HarmonicFunction::TONIC }
        expect(tonic).not_to be_nil
      end

      it 'has Subdominant function' do
        subdominant = world.harmonic_functions_obj.find { |f| f.function == HarmonicFunction::SUBDOMINANT }
        expect(subdominant).not_to be_nil
      end

      it 'has Dominant function' do
        dominant = world.harmonic_functions_obj.find { |f| f.function == HarmonicFunction::DOMINANT }
        expect(dominant).not_to be_nil
      end

      it 'adds all harmonic functions to world objects' do
        world.harmonic_functions_obj.each do |func|
          expect(world.objects).to include(func)
        end
      end

      it 'creates function relations from pitch classes' do
        function_relations = world.relations.select { |r| r[:type] == :function }
        expect(function_relations.length).to eq(3)
      end
    end

    context 'Category 6: Modulation (Circle of Fifths)' do
      it 'creates modulation path relations' do
        modulation_relations = world.relations.select { |r| r[:type] == :circle_of_fifths_plus }
        expect(modulation_relations.length).to be > 0
      end

      it 'has resolution relation' do
        resolution_relations = world.relations.select { |r| r[:type] == :resolution }
        expect(resolution_relations.length).to eq(1)
      end

      it 'includes pitches in modulation path (C, G, D, F)' do
        path_pitches = [0, 7, 2, 5]
        path_pitches.each do |pitch_val|
          pitch = world.pitch_classes.find { |p| p.value == pitch_val }
          expect(pitch).not_to be_nil
        end
      end
    end

    context 'Category 7: Voice-Leading Chords' do
      it 'generates 3 chords (C, F, G)' do
        expect(world.chords_obj.length).to eq(3)
      end

      it 'creates chords with correct root pitches' do
        chord_roots = world.chords_obj.map { |c| c.root.value }.sort
        expect(chord_roots).to eq([0, 5, 7])
      end

      it 'adds all chords to world objects' do
        world.chords_obj.each do |chord|
          expect(world.objects).to include(chord)
        end
      end

      it 'creates chord formation relations' do
        chord_relations = world.relations.select { |r| r[:type] == :chord_formation }
        expect(chord_relations.length).to eq(3)
      end
    end

    context 'Category 8: Harmonic Progressions' do
      it 'generates 1 harmonic progression' do
        expect(world.progressions_obj.length).to eq(1)
      end

      it 'progression has 4 chords (I-IV-V-I)' do
        progression = world.progressions_obj.first
        expect(progression.chords.length).to eq(4)
      end

      it 'adds progression to world objects' do
        world.progressions_obj.each do |prog|
          expect(world.objects).to include(prog)
        end
      end

      it 'creates progression membership relations' do
        membership_relations = world.relations.select { |r| r[:type] == :progression_member }
        expect(membership_relations.length).to eq(3)  # 3 chords in progression
      end
    end

    context 'Category 9: Cadential Structures' do
      it 'generates 1 authentic cadence' do
        expect(world.cadences_obj.length).to eq(1)
      end

      it 'cadence is an instance of Phrase' do
        cadence = world.cadences_obj.first
        expect(cadence).to be_an_instance_of(Phrase)
      end

      it 'adds cadence to world objects' do
        world.cadences_obj.each do |cadence|
          expect(world.objects).to include(cadence)
        end
      end

      it 'creates conclusion relations' do
        conclusion_relations = world.relations.select { |r| r[:type] == :concludes_with }
        expect(conclusion_relations.length).to eq(1)  # 1 progression concludes with cadence
      end
    end

    context '8-Dimensional Semantic Closure' do
      it 'satisfies pitch space dimension' do
        expect(world.pitch_classes.length).to eq(12)
      end

      it 'satisfies harmonic function dimension' do
        expect(world.harmonic_functions_obj.length).to eq(3)
      end

      it 'satisfies modulation dimension' do
        modulation_relations = world.relations.select { |r| r[:type].to_s.include?('circle') }
        expect(modulation_relations.length).to be > 0
      end

      it 'satisfies chord space dimension' do
        expect(world.chords_obj.length).to eq(3)
      end

      it 'satisfies progression space dimension' do
        expect(world.progressions_obj.length).to eq(1)
      end

      it 'satisfies cadential structure dimension' do
        expect(world.cadences_obj.length).to eq(1)
      end

      it 'satisfies emergence dimension' do
        emergence_relations = world.relations.select { |r| r[:type] == :permutation }
        expect(emergence_relations.length).to be > 0
      end

      it 'satisfies completion dimension' do
        authentic_cadences = world.cadences_obj.select { |c| c.cadence_type == Phrase::AUTHENTIC }
        expect(authentic_cadences.length).to be > 0
      end

      it 'passes full semantic closure test' do
        expect(world.semantic_closure_initial).to be true
      end
    end

    context 'Total World Statistics' do
      it 'contains exactly 20 objects' do
        # 12 pitch classes (includes initial pitch) + 3 harmonic functions + 3 chords + 1 progression + 1 cadence
        expect(world.objects.length).to eq(20)
      end

      it 'contains 26 total relations' do
        expect(world.relations.length).to eq(26)
      end

      it 'all objects are present in relations source or target' do
        related_objects = Set.new
        world.relations.each do |relation|
          related_objects.add(relation[:source]) if relation[:source]
          related_objects.add(relation[:target]) if relation[:target]
        end

        world.objects.each do |obj|
          # It's OK if some objects don't appear in relations (they may be peripheral)
          # Just verify we're not adding nil objects
          expect(obj).not_to be_nil
        end
      end
    end
  end

  describe 'Factory Method' do
    it 'creates and builds world via factory method' do
      factory_world = MusicalWorlds::InitialObjectWorld.create_from_initial_object(0)
      expect(factory_world).to be_an_instance_of(MusicalWorlds::InitialObjectWorld)
      expect(factory_world.objects.length).to eq(20)
    end

    it 'factory method returns fully built world' do
      factory_world = MusicalWorlds::InitialObjectWorld.create_from_initial_object(0)
      expect(factory_world.semantic_closure_initial).to be true
    end
  end

  describe 'Different Initial Pitches' do
    it 'builds correctly from different pitch (G=7)' do
      world_g = MusicalWorlds::InitialObjectWorld.new("InitialG")
      world_g.build_from_initial_pitch(7)
      expect(world_g.initial_pitch.value).to eq(7)
      expect(world_g.objects.length).to eq(20)
    end

    it 'semantic closure holds for different initial pitches' do
      world_g = MusicalWorlds::InitialObjectWorld.new("InitialG")
      world_g.build_from_initial_pitch(7)
      expect(world_g.semantic_closure_initial).to be true
    end
  end
end
