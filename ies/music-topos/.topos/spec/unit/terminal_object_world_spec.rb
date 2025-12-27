#!/usr/bin/env ruby
# spec/unit/terminal_object_world_spec.rb
#
# RSpec tests for TerminalObjectWorld class
# Tests resolution of all musical fragments into sonata form

require_relative '../spec_helper'

describe MusicalWorlds::TerminalObjectWorld do
  let(:world) { MusicalWorlds::TerminalObjectWorld.new("TestTerminalWorld") }

  describe 'Initialization' do
    it 'creates a new terminal object world' do
      expect(world).to be_an_instance_of(MusicalWorlds::TerminalObjectWorld)
    end

    it 'has a name' do
      expect(world.name).to eq("TestTerminalWorld")
    end

    it 'starts with empty objects and relations' do
      expect(world.objects).to be_empty
      expect(world.relations).to be_empty
    end

    it 'has properly initialized sonata sections' do
      expect(world.instance_variable_get(:@exposition)).to be_nil
      expect(world.instance_variable_get(:@development)).to be_nil
      expect(world.instance_variable_get(:@recapitulation)).to be_nil
      expect(world.instance_variable_get(:@coda)).to be_nil
    end

    it 'has properly initialized fragment categories' do
      expect(world.instance_variable_get(:@category_4_fragments)).to be_empty
      expect(world.instance_variable_get(:@category_5_fragments)).to be_empty
      expect(world.instance_variable_get(:@category_6_fragments)).to be_empty
      expect(world.instance_variable_get(:@category_7_fragments)).to be_empty
      expect(world.instance_variable_get(:@category_8_fragments)).to be_empty
      expect(world.instance_variable_get(:@category_9_fragments)).to be_empty
    end
  end

  describe 'Building from Terminal Object (Sonata Form)' do
    before do
      world.build_from_terminal_object
    end

    context 'Terminal Object Creation' do
      it 'creates the sonata movement' do
        expect(world.sonata_movement).not_to be_nil
        expect(world.sonata_movement).to be_an_instance_of(Movement)
      end

      it 'adds sonata movement to world objects' do
        expect(world.objects).to include(world.sonata_movement)
      end

      it 'creates exposition section' do
        expect(world.exposition).not_to be_nil
        expect(world.exposition).to be_an_instance_of(Section)
      end

      it 'creates development section' do
        expect(world.development).not_to be_nil
        expect(world.development).to be_an_instance_of(Section)
      end

      it 'creates recapitulation section' do
        expect(world.recapitulation).not_to be_nil
        expect(world.recapitulation).to be_an_instance_of(Section)
      end

      it 'creates coda section' do
        expect(world.coda).not_to be_nil
        expect(world.coda).to be_an_instance_of(Section)
      end

      it 'sonata contains all four sections' do
        expect(world.sonata_movement.sections.length).to eq(4)
        expect(world.sonata_movement.sections).to include(world.exposition)
        expect(world.sonata_movement.sections).to include(world.development)
        expect(world.sonata_movement.sections).to include(world.recapitulation)
        expect(world.sonata_movement.sections).to include(world.coda)
      end
    end

    context 'Category 4 Fragments: Pitch Classes' do
      it 'generates 12 pitch class fragments' do
        expect(world.category_4_fragments.length).to eq(12)
      end

      it 'adds all pitch class fragments to world objects' do
        world.category_4_fragments.each do |fragment|
          expect(world.objects).to include(fragment)
        end
      end

      it 'creates embedding relations for all pitch classes' do
        exposition_embeddings = world.relations.select do |r|
          r[:type] == :embeds_in_exposition && world.category_4_fragments.include?(r[:source])
        end
        expect(exposition_embeddings.length).to eq(12)
      end
    end

    context 'Category 5 Fragments: Harmonic Functions' do
      it 'generates 3 harmonic function fragments' do
        expect(world.category_5_fragments.length).to eq(3)
      end

      it 'adds all harmonic function fragments to world objects' do
        world.category_5_fragments.each do |fragment|
          expect(world.objects).to include(fragment)
        end
      end

      it 'creates tonic function embedding in exposition and recapitulation' do
        tonic_relations = world.relations.select do |r|
          r[:type].to_s.include?('tonic') && world.category_5_fragments.include?(r[:source])
        end
        expect(tonic_relations.length).to be > 0
      end

      it 'creates dominant function embedding in exposition' do
        dominant_relations = world.relations.select do |r|
          r[:type] == :secondary_theme && world.category_5_fragments.include?(r[:source])
        end
        expect(dominant_relations.length).to eq(1)
      end
    end

    context 'Category 6 Fragments: Modulation Paths' do
      it 'generates 4 modulation key fragments' do
        expect(world.category_6_fragments.length).to eq(4)
      end

      it 'adds all modulation fragments to world objects' do
        world.category_6_fragments.each do |fragment|
          expect(world.objects).to include(fragment)
        end
      end

      it 'creates embedding relations for keys in sections' do
        key_embeddings = world.relations.select do |r|
          (r[:type] == :exposition_key || r[:type] == :development_exploration ||
           r[:type] == :recapitulation_key) &&
          world.category_6_fragments.include?(r[:source])
        end
        expect(key_embeddings.length).to eq(4)
      end
    end

    context 'Category 7 Fragments: Voice-Leading Chords' do
      it 'generates 3 chord fragments' do
        expect(world.category_7_fragments.length).to eq(3)
      end

      it 'adds all chord fragments to world objects' do
        world.category_7_fragments.each do |fragment|
          expect(world.objects).to include(fragment)
        end
      end

      it 'creates embedding relations for chords into sections' do
        chord_embeddings = world.relations.select do |r|
          (r[:type] == :exposition_chord || r[:type] == :development_chord ||
           r[:type] == :recapitulation_chord || r[:type] == :final_chord) &&
          world.category_7_fragments.include?(r[:source])
        end
        expect(chord_embeddings.length).to be > 0
      end
    end

    context 'Category 8 Fragments: Harmonic Progressions' do
      it 'generates 1 progression fragment' do
        expect(world.category_8_fragments.length).to eq(1)
      end

      it 'adds progression fragment to world objects' do
        world.category_8_fragments.each do |fragment|
          expect(world.objects).to include(fragment)
        end
      end

      it 'creates embedding relations for progression across sections' do
        progression_embeddings = world.relations.select do |r|
          (r[:type] == :exposition_progression || r[:type] == :development_transformation ||
           r[:type] == :recapitulation_resolution) &&
          world.category_8_fragments.include?(r[:source])
        end
        expect(progression_embeddings.length).to eq(3)
      end
    end

    context 'Category 9 Fragments: Cadential Structures' do
      it 'generates 4 cadence fragments' do
        expect(world.category_9_fragments.length).to eq(4)
      end

      it 'adds all cadence fragments to world objects' do
        world.category_9_fragments.each do |fragment|
          expect(world.objects).to include(fragment)
        end
      end

      it 'creates embedding relations for cadences into sections' do
        cadence_embeddings = world.relations.select do |r|
          (r[:type] == :resolves_into_recapitulation || r[:type] == :concludes_in_coda) &&
          world.category_9_fragments.include?(r[:source])
        end
        expect(cadence_embeddings.length).to be > 0
      end
    end

    context 'Universal Embedding Relations' do
      it 'creates embedded_in_sonata relation for all fragments' do
        all_fragments = world.category_4_fragments + world.category_5_fragments +
                       world.category_6_fragments + world.category_7_fragments +
                       world.category_8_fragments + world.category_9_fragments

        embedding_count = world.relations.count { |r| r[:type] == :embedded_in_sonata }
        expect(embedding_count).to eq(all_fragments.length)
      end

      it 'every fragment maps uniquely into the sonata' do
        all_fragments = world.category_4_fragments + world.category_5_fragments +
                       world.category_6_fragments + world.category_7_fragments +
                       world.category_8_fragments + world.category_9_fragments

        all_fragments.each do |fragment|
          sonata_embeddings = world.relations.count do |r|
            r[:source] == fragment && r[:target] == world.sonata_movement
          end
          expect(sonata_embeddings).to be > 0
        end
      end
    end

    context '8-Dimensional Semantic Closure' do
      it 'satisfies pitch space dimension' do
        expect(world.category_4_fragments.length).to eq(12)
      end

      it 'satisfies harmonic function dimension' do
        expect(world.category_5_fragments.length).to eq(3)
      end

      it 'satisfies modulation dimension' do
        expect(world.category_6_fragments.length).to eq(4)
      end

      it 'satisfies chord space dimension' do
        expect(world.category_7_fragments.length).to eq(3)
      end

      it 'satisfies progression space dimension' do
        expect(world.category_8_fragments.length).to eq(1)
      end

      it 'satisfies cadential structure dimension' do
        expect(world.category_9_fragments.length).to eq(4)
      end

      it 'satisfies embedding dimension' do
        embedding_relations = world.relations.select { |r| r[:type] == :embedded_in_sonata }
        expect(embedding_relations.length).to be > 0
      end

      it 'satisfies completion dimension' do
        expect(world.sonata_movement.formally_closed?).to be true
      end

      it 'passes full semantic closure test' do
        expect(world.semantic_closure_terminal).to be true
      end
    end

    context 'Total World Statistics' do
      it 'contains exactly 26 objects' do
        # 1 movement + 4 sections + 12 pitch classes + 3 functions + 4 keys + 3 chords + 1 progression + 4 cadences
        expect(world.objects.length).to eq(26)
      end

      it 'contains many embedding relations (>60)' do
        expect(world.relations.length).to be > 60
      end

      it 'all fragments have paths into sonata' do
        all_fragments = world.category_4_fragments + world.category_5_fragments +
                       world.category_6_fragments + world.category_7_fragments +
                       world.category_8_fragments + world.category_9_fragments

        all_fragments.each do |fragment|
          embedded = world.relations.any? { |r| r[:source] == fragment && r[:target] == world.sonata_movement }
          expect(embedded).to be true
        end
      end
    end
  end

  describe 'Factory Method' do
    it 'creates and builds world via factory method' do
      factory_world = MusicalWorlds::TerminalObjectWorld.create_terminal_sonata_world
      expect(factory_world).to be_an_instance_of(MusicalWorlds::TerminalObjectWorld)
      expect(factory_world.sonata_movement).not_to be_nil
    end

    it 'factory method returns fully built world' do
      factory_world = MusicalWorlds::TerminalObjectWorld.create_terminal_sonata_world
      expect(factory_world.semantic_closure_terminal).to be true
    end
  end

  describe 'Bidirectional Structure Verification' do
    it 'terminal object world has more relations than initial world' do
      initial_world = MusicalWorlds::InitialObjectWorld.create_from_initial_object(0)
      terminal_world = MusicalWorlds::TerminalObjectWorld.create_terminal_sonata_world

      # Terminal world has convergence relations, so more relations
      expect(terminal_world.relations.length).to be > initial_world.relations.length
    end

    it 'both worlds contain same fundamental musical categories (4-9)' do
      initial_world = MusicalWorlds::InitialObjectWorld.create_from_initial_object(0)
      terminal_world = MusicalWorlds::TerminalObjectWorld.create_terminal_sonata_world

      # Both have pitch classes
      expect(initial_world.pitch_classes.length).to eq(terminal_world.category_4_fragments.length)

      # Both have harmonic functions
      expect(initial_world.harmonic_functions_obj.length).to eq(terminal_world.category_5_fragments.length)

      # Both have chords
      expect(initial_world.chords_obj.length).to eq(terminal_world.category_7_fragments.length)
    end
  end
end
