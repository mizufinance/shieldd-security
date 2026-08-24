from __future__ import annotations

import dataclasses
import hashlib
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen_withdrawal_registry_semantics as subject


class WithdrawalRegistrySemanticsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.outputs = subject.generated_files()

    def test_exact_domain_scoped_template_roster(self) -> None:
        self.assertEqual(
            [
                (
                    template.key,
                    template.rate,
                    template.domain,
                    template.row_count,
                    template.local_wire_count,
                    template.output_wires,
                )
                for template in subject.HASH_TEMPLATES
            ],
            [
                (
                    "gadget.note_commitment@"
                    "252c34d237e9b74178cdbbf5a9717debfc74e1b16a3efce054302a298f56fd4c",
                    5,
                    1395601591349183338445327673196897598598470771863946901251414766570764147135,
                    390,
                    398,
                    (372, 377, 382, 387, 392, 397),
                ),
                (
                    "gadget.asset_registry_params_hash@"
                    "1963568e22e00f1c7a0d3c2b2896d3035d4eb4397880f0d3207d9ac83743b64e",
                    3,
                    3064133732739839324562890722780110204743400790580066376892340142513796818031,
                    310,
                    315,
                    (299, 304, 309, 314),
                ),
                (
                    "gadget.asset_registry_ring_hash@"
                    "fca220e542b46ac382c73fbe684619e5680e949ef1acb40f697416d4b368dde2",
                    5,
                    2332157431640739955796532904592455296874484311567337797924969966168817210674,
                    390,
                    397,
                    (371, 376, 381, 386, 391, 396),
                ),
                (
                    "gadget.asset_registry_leaf_hash@"
                    "9424c990190c4128118a2906eaddfab647443257691dff0a8fc5b9b9caa7ebff",
                    5,
                    7414146286439358428123110060125696348906971675449116418017868010797147357618,
                    390,
                    396,
                    (370, 375, 380, 385, 390, 395),
                ),
                (
                    "gadget.asset_registry_leaf_hash@"
                    "1d21585b06949c209c9dc65b4c07d08b562d4aefe7f8d48ea3227037faa805db",
                    5,
                    7414146286439358428123110060125696348906971675449116418017868010797147357618,
                    390,
                    404,
                    (378, 383, 388, 393, 398, 403),
                ),
                (
                    "gadget.compliance_leaf@"
                    "e42e4a59ca3481574a6f245aa2eeb58a3e37448d6e566bfc33140a594c61efec",
                    5,
                    4269006203104973867634438910267250913271743773478037782164242111046258415985,
                    390,
                    398,
                    (372, 377, 382, 387, 392, 397),
                ),
            ],
        )

    def test_vector_duplicate_keys_fail_before_domain_interpretation(self) -> None:
        with tempfile.TemporaryDirectory(dir=subject.ROOT) as directory:
            path = Path(directory) / subject.VECTORS.name
            path.write_text('{"poseidon377":{},"poseidon377":{}}')
            with mock.patch.object(subject, "VECTORS", path):
                with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                    subject._validate_authoritative_domain(
                        subject.HASH_TEMPLATES[0]
                    )

    def test_canonical_relations_are_byte_and_wire_namespace_pinned(self) -> None:
        for template in subject.HASH_TEMPLATES:
            rows = subject._canonical_rows(template)
            self.assertEqual(len(rows), template.row_count)
            wires = {
                wire
                for row in rows
                for side in row
                for _, wire in side
            }
            self.assertEqual(wires, set(range(template.local_wire_count)))
            entry = subject._registry_entry(template)
            path = subject.ARTIFACTS / entry["canonical_relation_file"]
            import gzip

            self.assertEqual(
                hashlib.sha256(gzip.decompress(path.read_bytes())).hexdigest(),
                template.digest,
            )

    def test_wrong_folded_domain_fails_before_emission(self) -> None:
        template = dataclasses.replace(
            subject.HASH_TEMPLATES[0],
            domain=subject.HASH_TEMPLATES[0].domain + 1,
        )
        with self.assertRaisesRegex(ValueError, "domain pin drifted"):
            subject._hash_outputs(template)

    def test_each_template_has_one_direct_poseidon_provider(self) -> None:
        mains = {
            subject.SEMANTICS / f"{template.name}.lean"
            for template in subject.HASH_TEMPLATES
        }
        self.assertEqual(mains & self.outputs.keys(), mains)
        self.assertEqual(len(self.outputs), 252)
        for template in subject.HASH_TEMPLATES:
            source = self.outputs[
                subject.SEMANTICS / f"{template.name}.lean"
            ]
            self.assertIn(
                f"Poseidon{template.rate}Bridge.permSpec{template.rate}",
                source,
            )
            self.assertIn(f"({template.domain} : F)", source)
            self.assertIn("theorem sound", source)
            self.assertIn("  unfold spec output\n", source)
            self.assertIn("  rw [← hw", source)
            self.assertNotIn("  simpa [spec, output", source)
            self.assertNotIn("def spec (rho : Nat → F) : Prop := relation rho", source)

    def test_generated_sources_use_no_trust_shortcuts_or_transport_aliases(self) -> None:
        combined = "\n".join(self.outputs.values())
        for forbidden in (
            "axiom ",
            "native_decide",
            "Classical.choice",
            "representativeRho",
            "representativeSeating",
        ):
            self.assertNotIn(forbidden, combined)

if __name__ == "__main__":
    unittest.main()
