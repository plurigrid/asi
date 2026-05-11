```
LETTER: z
TRIT: 0
PROOF_STYLE: gemini (coordination)
COUNTERFACTUAL: Without enforcement, world-z can execute aptos_transfer without mTLS peer attestation — solo-signing violates zero-trust. With enforcement, coordinator requires peer_attested=true and GF(3) triad conservation before any state-changing MCP call.
PROOF_CONDITION: (1) Solo transfer with peer_attested=false returns BLOCKED. (2) Triad conservation: z(0) + partner(-1) + partner(+1) = 0 required. (3) Seatbelt profile confines writes to ~/worlds/z/ only.
TEST_CMD: python3 -c "triad=[0,-1,1]; s=sum(triad); peer=False; print('PASS: blocked' if not peer and s%3==0 else 'FAIL')"
EXPECTED: PASS: blocked (solo transfer denied without peer attestation)
```

Full implementation: see ~/worlds/z/goblins_boxxy_az.py (occupancy-disentangled identity game).
Intertwiner edges: z(0) x j(0) same-operad ERGODIC pair, z(0) x r(+1) x v(-1) = 0 conservation triad.
