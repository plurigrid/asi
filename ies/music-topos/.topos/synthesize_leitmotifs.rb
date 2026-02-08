#!/usr/bin/env ruby

# bin/synthesize_leitmotifs.rb
#
# Render the four consequential leitmotifs as actual sound
# Mathematical theorems converted to audible frequencies

require_relative '../lib/pitch_class'
require_relative '../lib/chord'
require_relative '../lib/neo_riemannian'
require_relative '../lib/audio_synthesis'

LeitmotifSynthesis.render_all
