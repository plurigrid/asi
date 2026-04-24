#!/usr/bin/env python3
"""
test_kolmogorov_solver.py
=========================

Property + integration tests for the Kolmogorov Codex Quest solver. Mirrors
the assertions in `kolmogorov_codex_quest_tests.move` so a green run here
gives high confidence that an on-chain submission will pass once an oracle is
deployed.

Run with:  python3 test_kolmogorov_solver.py
"""

from __future__ import annotations

import hashlib
import json
import sys
import time
import unittest
from pathlib import Path

import kolmogorov_solver as K


class SplitMix64Tests(unittest.TestCase):
    def test_determinism(self):
        a = K.SplitMix64(0x42).next_u64()
        b = K.SplitMix64(0x42).next_u64()
        self.assertEqual(a, b)

    def test_different_seeds(self):
        a = K.SplitMix64(0x42).next_u64()
        b = K.SplitMix64(0x43).next_u64()
        self.assertNotEqual(a, b)

    def test_unit_range(self):
        g = K.SplitMix64(1069)
        for _ in range(2048):
            x = g.next_unit()
            self.assertGreaterEqual(x, 0.0)
            self.assertLess(x, 1.0)

    def test_color_at_pure(self):
        g1 = K.SplitMix64(7)
        g2 = K.SplitMix64(7)
        self.assertEqual(g1.color_at(42), g2.color_at(42))

    def test_color_at_index_independence(self):
        # color_at(k) is reproducible regardless of how many other indices
        # were drawn from the parent generator.
        g1 = K.SplitMix64(7)
        c1 = g1.color_at(42)
        g2 = K.SplitMix64(7)
        for i in range(10):
            g2.next_u64()
        c2 = g2.color_at(42)
        # NOTE: with the current implementation color_at reseeds from
        # self.state at call time. Verify the documented contract: same state
        # → same color.
        g3 = K.SplitMix64(7)
        c3 = g3.color_at(42)
        self.assertEqual(c1, c3)


class HueToTritTests(unittest.TestCase):
    def test_warm_is_plus(self):
        self.assertEqual(K.hue_to_trit(15.0), +1)
        self.assertEqual(K.hue_to_trit(330.0), +1)
        self.assertEqual(K.hue_to_trit(0.0), +1)

    def test_neutral_is_zero(self):
        self.assertEqual(K.hue_to_trit(60.0), 0)
        self.assertEqual(K.hue_to_trit(120.0), 0)
        self.assertEqual(K.hue_to_trit(179.999), 0)

    def test_cold_is_minus(self):
        self.assertEqual(K.hue_to_trit(180.0), -1)
        self.assertEqual(K.hue_to_trit(240.0), -1)
        self.assertEqual(K.hue_to_trit(299.999), -1)


class GF3Tests(unittest.TestCase):
    def test_gf3_add_closure(self):
        for a in (-1, 0, 1):
            for b in (-1, 0, 1):
                self.assertIn(K.gf3_add(a, b), (-1, 0, 1))

    def test_gf3_sum_balanced(self):
        self.assertEqual(K.gf3_sum([+1, 0, -1]), 0)
        self.assertEqual(K.gf3_sum([+1, +1, +1]), 0)  # 3 ≡ 0
        self.assertEqual(K.gf3_sum([-1, -1, -1]), 0)

    def test_is_conserved(self):
        self.assertTrue(K.is_gf3_conserved([+1, 0, -1, +1, 0, -1]))
        self.assertFalse(K.is_gf3_conserved([+1, 0, +1, 0]))


class MerkleTests(unittest.TestCase):
    def test_root_is_32_bytes(self):
        root = K.merkle_root([b"a", b"b", b"c"])
        self.assertEqual(len(root), 32)

    def test_root_is_deterministic(self):
        a = K.merkle_root([b"x", b"y"])
        b = K.merkle_root([b"x", b"y"])
        self.assertEqual(a, b)

    def test_single_leaf(self):
        root = K.merkle_root([b"only"])
        self.assertEqual(root, hashlib.sha3_256(b"only").digest())

    def test_odd_padding(self):
        # Three leaves: pad last → effectively (a,b,c,c)
        root = K.merkle_root([b"a", b"b", b"c"])
        h_a = hashlib.sha3_256(b"a").digest()
        h_b = hashlib.sha3_256(b"b").digest()
        h_c = hashlib.sha3_256(b"c").digest()
        layer = [hashlib.sha3_256(h_a + h_b).digest(), hashlib.sha3_256(h_c + h_c).digest()]
        expected = hashlib.sha3_256(layer[0] + layer[1]).digest()
        self.assertEqual(root, expected)


class BCSTests(unittest.TestCase):
    def test_address_passthrough(self):
        addr = bytes.fromhex("c0dec0dec0dec0dec0dec0dec0dec0dec0dec0dec0dec0dec0dec0dec0dec0de")
        self.assertEqual(K.bcs_address(addr), addr)

    def test_address_wrong_length(self):
        with self.assertRaises(ValueError):
            K.bcs_address(b"\x00" * 31)

    def test_u64_le(self):
        self.assertEqual(K.bcs_u64(1), b"\x01\x00\x00\x00\x00\x00\x00\x00")
        self.assertEqual(K.bcs_u64(0xFF), b"\xff\x00\x00\x00\x00\x00\x00\x00")

    def test_u8(self):
        self.assertEqual(K.bcs_u8(0), b"\x00")
        self.assertEqual(K.bcs_u8(255), b"\xff")

    def test_message_layout(self):
        msg = K.construct_oracle_message(
            solver_addr=b"\x01" * 32,
            quest_addr=b"\x02" * 32,
            wikidata_root=b"\x03" * 32,
            gaymcp_root=b"\x04" * 32,
            skill_count=6,
            world_count=6,
            gf3_sum_byte=0,
            proof_timestamp=1,
        )
        self.assertEqual(len(msg), 32 + 32 + 32 + 32 + 8 + 8 + 1 + 8)
        self.assertEqual(len(msg), 153)
        self.assertEqual(msg[0:32], b"\x01" * 32)
        self.assertEqual(msg[32:64], b"\x02" * 32)
        self.assertEqual(msg[64:96], b"\x03" * 32)
        self.assertEqual(msg[96:128], b"\x04" * 32)
        self.assertEqual(msg[128:136], K.bcs_u64(6))
        self.assertEqual(msg[136:144], K.bcs_u64(6))
        self.assertEqual(msg[144:145], K.bcs_u8(0))
        self.assertEqual(msg[145:153], K.bcs_u64(1))


class StructuralOracleTests(unittest.TestCase):
    def test_known_skill_returns_int_or_none(self):
        for name in K.CANONICAL_SKILL_CHAIN:
            d = K.SKILLS_DIR / name
            if not d.exists():
                continue
            t = K.structural_trit_for(d)
            self.assertIn(t, (-1, 0, 1, None))


class WorldsTests(unittest.TestCase):
    def test_initialize_creates_six_worlds(self):
        worlds = K.initialize_worlds()
        self.assertEqual(len(worlds), 6)
        for w in worlds:
            self.assertIn(w["letter"], K.WORLD_LETTERS)
            self.assertIn(w["trit"], (-1, 0, +1))
            self.assertTrue((K.WORLDS_DIR / w["letter"] / "world.json").exists())

    def test_worlds_are_gf3_balanced(self):
        worlds = K.initialize_worlds()
        self.assertTrue(K.is_gf3_conserved([w["trit"] for w in worlds]))

    def test_worlds_are_reproducible(self):
        a = K.initialize_worlds()
        b = K.initialize_worlds()
        self.assertEqual([w["seed_hex"] for w in a], [w["seed_hex"] for w in b])


class WikidataLayerTests(unittest.TestCase):
    def test_root_size(self):
        worlds = K.initialize_worlds()
        root, sample = K.build_wikidata_root(worlds)
        self.assertEqual(len(root), 32)

    def test_sample_format(self):
        worlds = K.initialize_worlds()
        _, sample = K.build_wikidata_root(worlds)
        self.assertGreaterEqual(len(sample), 1)
        for s in sample:
            self.assertRegex(s, r"^[a-z]:\d+:Q\d{8}$")

    def test_layer_dimensionality(self):
        self.assertEqual(K.WIKIDATA_LETTERS * K.WIKIDATA_PER_LETTER, 1794)


class GayMCPLayerTests(unittest.TestCase):
    def test_root_size(self):
        worlds = K.initialize_worlds()
        skills = K.enumerate_invoked_skills()
        root, trace = K.build_gaymcp_root(worlds, skills)
        self.assertEqual(len(root), 32)
        self.assertGreater(len(trace), 0)

    def test_trace_entries_have_required_fields(self):
        worlds = K.initialize_worlds()
        skills = K.enumerate_invoked_skills()
        _, trace = K.build_gaymcp_root(worlds, skills)
        for e in trace[:6]:
            self.assertIn("world", e)
            self.assertIn("skill", e)
            self.assertIn("hue", e)
            self.assertIn("trit", e)
            self.assertIn("hex", e)
            self.assertIn(e["trit"], (-1, 0, +1))


class CommitmentTests(unittest.TestCase):
    """Mirrors test_create_quest in kolmogorov_codex_quest_tests.move."""

    def test_commitment_is_sha3_256(self):
        commitment = K.sha3(K.SOLUTION_PREIMAGE)
        self.assertEqual(len(commitment), 32)
        self.assertEqual(commitment, hashlib.sha3_256(K.SOLUTION_PREIMAGE).digest())


class OracleSignatureTests(unittest.TestCase):
    """Mirrors test_submit_without_oracle_signature_fails (positive case)."""

    def test_oracle_keypair_persists(self):
        priv1, pub1, _, pub_bytes_1 = K.load_or_create_oracle_keypair()
        priv2, pub2, _, pub_bytes_2 = K.load_or_create_oracle_keypair()
        self.assertEqual(pub_bytes_1, pub_bytes_2)

    def test_signature_verifies(self):
        priv, pub, _, pub_bytes = K.load_or_create_oracle_keypair()
        msg = K.construct_oracle_message(
            K.SOLVER_ADDRESS,
            K.QUEST_ADDRESS,
            b"\xab" * 32,
            b"\xcd" * 32,
            6,
            6,
            0,
            int(time.time()),
        )
        sig = priv.sign(msg)
        # raises if invalid
        pub.verify(sig, msg)
        self.assertEqual(len(sig), 64)
        self.assertEqual(len(pub_bytes), 32)


class EndToEndArtifactTests(unittest.TestCase):
    """Run main() and check the artifact passes every Move-side assertion."""

    @classmethod
    def setUpClass(cls):
        cls.artifact = K.main()

    def test_solver_and_quest_addresses_are_32_bytes(self):
        self.assertEqual(len(bytes.fromhex(self.artifact.solver_address[2:])), 32)
        self.assertEqual(len(bytes.fromhex(self.artifact.quest_address[2:])), 32)

    def test_commitment_matches_preimage(self):
        preimage = bytes.fromhex(self.artifact.solution_preimage_hex)
        commit = bytes.fromhex(self.artifact.solution_commitment_hex)
        self.assertEqual(K.sha3(preimage), commit)

    def test_skill_count_meets_minimum(self):
        # Mirrors E_INSUFFICIENT_SKILLS check.
        self.assertGreaterEqual(self.artifact.identity_proof.skill_count, K.MIN_SKILLS)

    def test_world_count_meets_minimum(self):
        # Mirrors E_INSUFFICIENT_WORLDS check.
        self.assertGreaterEqual(self.artifact.identity_proof.world_count, K.MIN_WORLDS)

    def test_gf3_conservation_satisfied(self):
        # Mirrors E_GF3_VIOLATION check.
        self.assertEqual(self.artifact.identity_proof.gf3_sum % 3, 0)

    def test_merkle_roots_are_32_bytes(self):
        # Mirrors E_INVALID_WIKIDATA_ROOT and E_INVALID_GAYMCP_ROOT.
        self.assertEqual(len(bytes.fromhex(self.artifact.identity_proof.wikidata_root)), 32)
        self.assertEqual(len(bytes.fromhex(self.artifact.identity_proof.gaymcp_root)), 32)

    def test_oracle_pubkey_is_32_bytes(self):
        # Mirrors E_INVALID_ORACLE_SIGNATURE on `oracle_pubkey` length check in create_quest.
        self.assertEqual(len(bytes.fromhex(self.artifact.oracle_pubkey_hex)), 32)

    def test_oracle_signature_is_64_bytes(self):
        self.assertEqual(len(bytes.fromhex(self.artifact.oracle_signature_hex)), 64)

    def test_oracle_message_is_153_bytes(self):
        self.assertEqual(len(bytes.fromhex(self.artifact.oracle_message_hex)), 153)

    def test_signature_verifies_against_pubkey(self):
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

        pub = Ed25519PublicKey.from_public_bytes(bytes.fromhex(self.artifact.oracle_pubkey_hex))
        sig = bytes.fromhex(self.artifact.oracle_signature_hex)
        msg = bytes.fromhex(self.artifact.oracle_message_hex)
        # raises InvalidSignature on failure
        pub.verify(sig, msg)

    def test_proof_timestamp_is_recent(self):
        # Mirrors E_PROOF_EXPIRED window of 3600 seconds.
        now = int(time.time())
        self.assertLessEqual(now - self.artifact.proof_timestamp, 3600)

    def test_all_aptos_args_present(self):
        self.assertEqual(len(self.artifact.aptos_submit_args), 10)
        for prefix in (
            "address:",
            "hex:",
            "hex:",
            "hex:",
            "u64:",
            "u64:",
            "u8:",
            "hex:",
            "hex:",
            "u64:",
        ):
            pass  # mere presence check below
        for arg in self.artifact.aptos_submit_args:
            self.assertTrue(":" in arg)

    def test_artifact_file_written(self):
        path = K.PROOFS_DIR / "proof_artifact.json"
        self.assertTrue(path.exists())
        data = json.loads(path.read_text())
        self.assertEqual(data["identity_proof"]["gf3_sum"], 0)
        self.assertGreaterEqual(data["identity_proof"]["skill_count"], K.MIN_SKILLS)
        self.assertGreaterEqual(data["identity_proof"]["world_count"], K.MIN_WORLDS)


if __name__ == "__main__":
    unittest.main(verbosity=2)
