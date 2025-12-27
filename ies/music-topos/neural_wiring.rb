# Neural Wiring World → Sonic Pi
# Seed: 1069 | Worlds: 13
use_bpm 120

# Root: Pitch
in_thread do
  use_synth :hollow
  play 52, sustain: 4, release: 2, amp: 0.4
end

# Voices (Frobenius split)
in_thread do
  play 83, amp: 0.3, pan: -0.5
  play 68, amp: 0.3, pan: 0.0
  play 71, amp: 0.3, pan: 0.5
end

# Sub-voices (deep split)
in_thread do
  use_synth :pluck
  play 76, amp: 0.2
  sleep 0.25
  play 71, amp: 0.2
  sleep 0.25
  play 76, amp: 0.2
  sleep 0.25
  play 48, amp: 0.2
  sleep 0.25
  play 82, amp: 0.2
  sleep 0.25
  play 75, amp: 0.2
  sleep 0.25
  play 74, amp: 0.2
  sleep 0.25
  play 83, amp: 0.2
  sleep 0.25
  play 78, amp: 0.2
  sleep 0.25
end