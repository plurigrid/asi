#!/usr/bin/env julia
"""
ElevenLabsACSet.jl - Voice Synthesis as Categorical Database

Deterministic conversion of ElevenLabs API to ACSet schema.
Integrates with Gay.jl for color-coded voice identities.
"""

module ElevenLabsACSetModule

using Catlab
using Catlab.Present
using Catlab.CSetDataStructures

export SchElevenLabsACSet, ElevenLabsACSet
export create_elevenlabs_acset, add_voice!, add_model!, add_tts_request!
export persist_to_duckdb!, load_from_duckdb

# ============================================================================
# SCHEMA DEFINITION
# ============================================================================

@present SchElevenLabsACSet(FreeSchema) begin
    # Objects (API Resources)
    Voice::Ob
    Model::Ob
    TTSRequest::Ob
    HistoryItem::Ob
    SoundEffect::Ob
    
    # Morphisms (Relationships)
    voice_for_request::Hom(TTSRequest, Voice)
    model_for_request::Hom(TTSRequest, Model)
    history_of_request::Hom(HistoryItem, TTSRequest)
    
    # Attribute Types
    VoiceId::AttrType
    VoiceName::AttrType
    ModelId::AttrType
    ModelName::AttrType
    Text::AttrType
    AudioPath::AttrType
    Timestamp::AttrType
    CharCount::AttrType
    GayColor::AttrType
    Trit::AttrType
    
    # Voice Attributes
    voice_id::Attr(Voice, VoiceId)
    voice_name::Attr(Voice, VoiceName)
    voice_color::Attr(Voice, GayColor)
    
    # Model Attributes
    model_id::Attr(Model, ModelId)
    model_name::Attr(Model, ModelName)
    
    # TTS Request Attributes
    request_text::Attr(TTSRequest, Text)
    request_timestamp::Attr(TTSRequest, Timestamp)
    request_trit::Attr(TTSRequest, Trit)
    
    # History Attributes
    history_audio_path::Attr(HistoryItem, AudioPath)
    history_timestamp::Attr(HistoryItem, Timestamp)
    history_char_count::Attr(HistoryItem, CharCount)
    
    # Sound Effect Attributes
    effect_prompt::Attr(SoundEffect, Text)
    effect_audio_path::Attr(SoundEffect, AudioPath)
end

# Concrete ACSet type
const ElevenLabsACSet = @acset_type ElevenLabsACSetType(SchElevenLabsACSet,
    index=[:voice_for_request, :model_for_request])

# ============================================================================
# GAY.JL COLOR INTEGRATION
# ============================================================================

"""
Generate deterministic color for voice based on voice_id hash.
Uses Gay.jl golden angle spiral for maximum perceptual dispersion.
"""
function voice_to_color(voice_id::String)::String
    # Hash voice_id to seed
    seed = hash(voice_id) % UInt64
    
    # Golden angle in degrees
    φ = (1 + sqrt(5)) / 2
    golden_angle = 360.0 / (φ^2)
    
    # Generate hue from seed
    hue = (seed * golden_angle) % 360
    
    # Convert HSL to hex (fixed saturation/lightness)
    h = hue / 360
    s = 0.7
    l = 0.55
    
    # HSL to RGB conversion
    function hue_to_rgb(p, q, t)
        t < 0 && (t += 1)
        t > 1 && (t -= 1)
        t < 1/6 && return p + (q - p) * 6 * t
        t < 1/2 && return q
        t < 2/3 && return p + (q - p) * (2/3 - t) * 6
        return p
    end
    
    q = l < 0.5 ? l * (1 + s) : l + s - l * s
    p = 2 * l - q
    r = round(Int, hue_to_rgb(p, q, h + 1/3) * 255)
    g = round(Int, hue_to_rgb(p, q, h) * 255)
    b = round(Int, hue_to_rgb(p, q, h - 1/3) * 255)
    
    return "#" * string(r, base=16, pad=2) * 
                 string(g, base=16, pad=2) * 
                 string(b, base=16, pad=2)
end

"""
Derive GF(3) trit from voice_id.
"""
function voice_to_trit(voice_id::String)::Int
    seed = hash(voice_id) % UInt64
    return Int(seed % 3) - 1  # Returns -1, 0, or 1
end

# ============================================================================
# ACSet OPERATIONS
# ============================================================================

"""Create empty ElevenLabs ACSet."""
function create_elevenlabs_acset()::ElevenLabsACSet
    return ElevenLabsACSet()
end

"""Add voice to ACSet, returns voice index."""
function add_voice!(acset::ElevenLabsACSet, voice_id::String, name::String)::Int
    color = voice_to_color(voice_id)
    return add_part!(acset, :Voice; 
        voice_id=voice_id, 
        voice_name=name,
        voice_color=color)
end

"""Add model to ACSet, returns model index."""
function add_model!(acset::ElevenLabsACSet, model_id::String, name::String="")::Int
    model_name = isempty(name) ? model_id : name
    return add_part!(acset, :Model; model_id=model_id, model_name=model_name)
end

"""Add TTS request to ACSet, returns request index."""
function add_tts_request!(acset::ElevenLabsACSet, 
                          voice_idx::Int, 
                          model_idx::Int, 
                          text::String)::Int
    timestamp = string(now())
    trit = -1  # TTS requests are always MINUS (consumption)
    
    return add_part!(acset, :TTSRequest;
        voice_for_request=voice_idx,
        model_for_request=model_idx,
        request_text=text,
        request_timestamp=timestamp,
        request_trit=trit)
end

"""Add history item for completed TTS."""
function add_history!(acset::ElevenLabsACSet,
                      request_idx::Int,
                      audio_path::String,
                      char_count::Int)::Int
    timestamp = string(now())
    
    return add_part!(acset, :HistoryItem;
        history_of_request=request_idx,
        history_audio_path=audio_path,
        history_timestamp=timestamp,
        history_char_count=char_count)
end

# ============================================================================
# DUCKDB PERSISTENCE
# ============================================================================

"""Persist ACSet to DuckDB."""
function persist_to_duckdb!(acset::ElevenLabsACSet, db_path::String)
    # Lazy load DuckDB
    @eval using DuckDB
    
    db = DuckDB.DB(db_path)
    
    # Create tables if not exist
    DuckDB.execute(db, """
        CREATE TABLE IF NOT EXISTS voices (
            id INTEGER PRIMARY KEY,
            voice_id VARCHAR,
            voice_name VARCHAR,
            voice_color VARCHAR,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )
    """)
    
    DuckDB.execute(db, """
        CREATE TABLE IF NOT EXISTS models (
            id INTEGER PRIMARY KEY,
            model_id VARCHAR,
            model_name VARCHAR
        )
    """)
    
    DuckDB.execute(db, """
        CREATE TABLE IF NOT EXISTS tts_requests (
            id INTEGER PRIMARY KEY,
            voice_id INTEGER REFERENCES voices(id),
            model_id INTEGER REFERENCES models(id),
            request_text TEXT,
            request_timestamp TIMESTAMP,
            request_trit INTEGER
        )
    """)
    
    DuckDB.execute(db, """
        CREATE TABLE IF NOT EXISTS history_items (
            id INTEGER PRIMARY KEY,
            request_id INTEGER REFERENCES tts_requests(id),
            audio_path VARCHAR,
            timestamp TIMESTAMP,
            char_count INTEGER
        )
    """)
    
    # Insert data
    for i in parts(acset, :Voice)
        DuckDB.execute(db, """
            INSERT OR REPLACE INTO voices (id, voice_id, voice_name, voice_color)
            VALUES (?, ?, ?, ?)
        """, (i, acset[:voice_id][i], acset[:voice_name][i], acset[:voice_color][i]))
    end
    
    for i in parts(acset, :Model)
        DuckDB.execute(db, """
            INSERT OR REPLACE INTO models (id, model_id, model_name)
            VALUES (?, ?, ?)
        """, (i, acset[:model_id][i], acset[:model_name][i]))
    end
    
    for i in parts(acset, :TTSRequest)
        DuckDB.execute(db, """
            INSERT OR REPLACE INTO tts_requests 
            (id, voice_id, model_id, request_text, request_timestamp, request_trit)
            VALUES (?, ?, ?, ?, ?, ?)
        """, (i, acset[:voice_for_request][i], acset[:model_for_request][i],
              acset[:request_text][i], acset[:request_timestamp][i], acset[:request_trit][i]))
    end
    
    DuckDB.close(db)
    println("✅ Persisted to $db_path")
end

"""Load ACSet from DuckDB."""
function load_from_duckdb(db_path::String)::ElevenLabsACSet
    @eval using DuckDB
    
    acset = create_elevenlabs_acset()
    db = DuckDB.DB(db_path)
    
    # Load voices
    result = DuckDB.execute(db, "SELECT * FROM voices ORDER BY id")
    for row in result
        add_part!(acset, :Voice;
            voice_id=row.voice_id,
            voice_name=row.voice_name,
            voice_color=row.voice_color)
    end
    
    # Load models
    result = DuckDB.execute(db, "SELECT * FROM models ORDER BY id")
    for row in result
        add_part!(acset, :Model;
            model_id=row.model_id,
            model_name=row.model_name)
    end
    
    # Load requests
    result = DuckDB.execute(db, "SELECT * FROM tts_requests ORDER BY id")
    for row in result
        add_part!(acset, :TTSRequest;
            voice_for_request=row.voice_id,
            model_for_request=row.model_id,
            request_text=row.request_text,
            request_timestamp=row.request_timestamp,
            request_trit=row.request_trit)
    end
    
    DuckDB.close(db)
    return acset
end

# ============================================================================
# PHONE AGENT CONFIG
# ============================================================================

"""
Phone agent configuration for +14156960069.
Returns config dict for the special agent.
"""
function phone_agent_config()::Dict{String, Any}
    return Dict(
        "agent_id" => "monaduck69-voice",
        "phone" => "+14156960069",
        "voice_settings" => Dict(
            "voice_id" => "cgSgspJ2msm6clMCkdW9",
            "model_id" => "eleven_multilingual_v2",
            "stability" => 0.5,
            "similarity_boost" => 0.75,
            "style" => 0.4,
            "speed" => 1.0
        ),
        "media_sources" => Dict(
            "soundcloud" => "rickroderick",
            "bandcamp" => "monaduck69",
            "poe" => "bmorphism"
        ),
        "capabilities" => [
            "text_to_speech",
            "voice_cloning", 
            "audio_isolation",
            "sound_effects"
        ],
        "trit" => -1,
        "color" => "#0243d2"
    )
end

end # module
