"""Expected-construction checks; these are not an actual-runtime certificate."""
import copy
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "circuits"))
import poseidon_graph as pg


def synthetic_source(graph):
    source, refs = {}, []
    for i, node in enumerate(graph["nodes"]):
        kind = node["kind"]
        name = ("c" if kind == "constant" else "w" if kind == "input" else "n") + str(i)
        refs.append(name)
        if kind == "input":
            source[name] = {"kind": "witness"}
        elif kind == "constant":
            source[name] = dict(node)
        else:
            source[name] = {"kind": kind, "left": refs[node["left"]], "right": refs[node["right"]]}
    return source, [refs[i] for i in graph["inputs"]], refs[graph["output"]]


class ExpectedGraphTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Deterministic NONCRYPTOGRAPHIC parameters keep these structural tests
        # independent of an ignored runtime checkout or downloaded artifact.
        cls.parameters = {"width": 6, "ark": [[round * 6 + col + 1 for col in range(6)] for round in range(65)],
                          "mds": [[1 + row * 6 + col for col in range(6)] for row in range(6)]}
        cls.graph = pg.expected(cls.parameters, 7, 3)
        cls.source, cls.inputs, cls.output = synthetic_source(cls.graph)

    def test_topological_match_and_constant_change(self):
        matched = pg.match_source(self.graph, self.source, self.inputs, self.output)
        self.assertTrue(matched)
        changed = copy.deepcopy(self.source)
        constant = next(actual for _, actual in matched if actual.startswith("c"))
        changed[constant]["value"] = (changed[constant]["value"] + 1) % pg.P
        with self.assertRaisesRegex(ValueError, "constant mismatch"):
            pg.match_source(self.graph, changed, self.inputs, self.output)

    def test_permutation_checks_every_lane_and_native_initial_state(self):
        graph = pg.permutation(self.parameters, [2321, None, None, None, None, None])
        source, inputs, _ = synthetic_source(graph)
        refs = [("c" if node["kind"] == "constant" else "w" if node["kind"] == "input" else "n") + str(i)
                for i, node in enumerate(graph["nodes"])]
        outputs = [refs[i] for i in graph["outputs"]]
        self.assertTrue(pg.match_permutation(graph, source, inputs, outputs))
        changed = list(outputs)
        changed[0] = outputs[1]
        with self.assertRaises(ValueError):
            pg.match_permutation(graph, source, inputs, changed)
        wrong = pg.permutation(self.parameters, [2322, None, None, None, None, None])
        with self.assertRaisesRegex(ValueError, "constant mismatch"):
            pg.match_permutation(wrong, source, inputs, outputs)
        for before in ([0] * 5, [True] + [None] * 5, [pg.P] + [None] * 5):
            with self.assertRaises(ValueError):
                pg.permutation(self.parameters, before)

    def test_wrong_slot_and_hidden_witness(self):
        with self.assertRaisesRegex(ValueError, "input/slot mismatch"):
            pg.match_source(self.graph, self.source, self.inputs[::-1], self.output)
        changed = copy.deepcopy(self.source)
        changed["w999999"] = {"kind": "witness"}
        changed[self.output]["right"] = "w999999"
        with self.assertRaisesRegex(ValueError, "undeclared witness mismatch"):
            pg.match_source(self.graph, changed, self.inputs, self.output)

    def test_forward_edge_and_operation_substitution(self):
        changed = copy.deepcopy(self.source)
        changed[self.output]["left"] = self.output
        with self.assertRaisesRegex(ValueError, "forward source reference"):
            pg.match_source(self.graph, changed, self.inputs, self.output)
        changed = copy.deepcopy(self.source)
        changed[self.output]["kind"] = "mul"
        with self.assertRaisesRegex(ValueError, "operation"):
            pg.match_source(self.graph, changed, self.inputs, self.output)

    def test_framing_and_unsupported_aliases(self):
        other = pg.expected(self.parameters, 8, 3)
        with self.assertRaisesRegex(ValueError, "constant mismatch"):
            pg.match_source(other, self.source, self.inputs, self.output)
        with self.assertRaisesRegex(ValueError, "alias unsupported"):
            pg.match_source(self.graph, self.source, [self.inputs[0]] * 3, self.output)
        with self.assertRaisesRegex(ValueError, "IV overflow"):
            pg.expected(self.parameters, 7, 1 << 64)
        with self.assertRaisesRegex(ValueError, "wrong width"):
            pg.expected(self.parameters, 7, 2)

    def test_round_order_and_unapproved_zero_padding_operation(self):
        parameters = copy.deepcopy(self.parameters)
        parameters["ark"][0], parameters["ark"][1] = parameters["ark"][1], parameters["ark"][0]
        reordered = pg.expected(parameters, 7, 3)
        source, inputs, output = synthetic_source(reordered)
        with self.assertRaisesRegex(ValueError, "constant mismatch"):
            pg.match_source(self.graph, source, inputs, output)
        # A final add-zero preserves every evaluated output. Exact construction
        # matching must still reject the unqualified padding/round-shape change.
        source = copy.deepcopy(self.source)
        source["c999999"] = {"kind": "constant", "value": 0}
        source["n999999"] = {"kind": "add", "left": "c999999", "right": self.output}
        with self.assertRaises(ValueError):
            pg.match_source(self.graph, source, self.inputs, "n999999")

    def test_duplicate_json_members_rejected(self):
        with self.assertRaisesRegex(ValueError, "duplicate JSON member"):
            pg.decode_json('{"ark": [], "ark": []}')
        with self.assertRaisesRegex(ValueError, "duplicate JSON member"):
            pg.decode_json('{"n0": {"kind": "add", "kind": "mul"}}')

    def test_computed_boundary_is_explicit_and_not_a_hidden_input(self):
        source = copy.deepcopy(self.source)
        # Rename one declared witness into an actual computed source handle.
        # Its dependencies belong to a prior certified component, not this cone.
        prior = self.inputs[0]
        replacement = "n0"
        source.pop(prior)
        source[replacement] = {"kind": "add", "left": "w999999", "right": "c999999"}
        for node in source.values():
            for side in ("left", "right"):
                if node.get(side) == prior:
                    node[side] = replacement
        inputs = [replacement] + self.inputs[1:]
        self.assertTrue(pg.match_source(self.graph, source, inputs, self.output))
        with self.assertRaisesRegex(ValueError, "missing/forward source reference"):
            pg.match_source(self.graph, source, self.inputs, self.output)
        source[replacement]["left"] = replacement
        with self.assertRaisesRegex(ValueError, "forward source reference"):
            pg.match_source(self.graph, source, inputs, self.output)

    def test_ownership_handle_joins_reject_wrong_caller_bindings(self):
        roles = {"authorization.effective_nk": "w0", "action.ak.x": "w1", "action.ak.y": "w2",
                 "action.randomizer": "w3", "action.computed_rk.x": "n0", "action.computed_rk.y": "n1",
                 "action.rk.x": "w4", "action.rk.y": "w5", "statement.rk.x": "w4", "statement.rk.y": "w5",
                 "spend0.position": "w6", "spend1.position": "w7",
                 "spend0.real_nullifier": "n4", "spend1.real_nullifier": "n5"}
        calls = [{"inputs": ["w8", "w1", "w2"]},
                 {"inputs": ["w9", "w10", "w11", "w12", "w13", "w14", "w15", "w16", "w17"]},
                 {"inputs": ["n6"]}]
        notes = []
        for slot in range(2):
            notes.extend([
                {"slot": slot, "role": "commitment", "domain": 15,
                 "inputs": [f"w{18+slot}", f"w{20+slot}", "w15", "w11", "w12", "w13", "w14", f"w{22+slot}"],
                 "output": f"n{2+slot}"},
                {"slot": slot, "role": "nullifier", "domain": 7,
                 "inputs": ["w0", f"n{2+slot}", f"w{6+slot}"], "output": f"n{4+slot}"}])
        export = {"ownership": roles, "note_hashes": notes, "touching_source_assertions": [
            {"index": 0, "left": "n0", "right": "w4"}, {"index": 1, "left": "n1", "right": "w5"}]}
        observed = {f"w{i}": {} for i in range(24)} | {f"n{i}": {} for i in range(6)}
        pg.check_ownership_handles(export, calls, observed)
        mutations = [
            lambda x: x["ownership"].__setitem__("statement.rk.x", "w1"),
            lambda x: x["ownership"].__setitem__("action.ak.x", "w4"),
            lambda x: x["touching_source_assertions"].pop(),
            lambda x: x["note_hashes"][2]["inputs"].__setitem__(2, "w16"),
            lambda x: x["note_hashes"][3]["inputs"].__setitem__(0, "w8"),
            lambda x: x["note_hashes"][3]["inputs"].__setitem__(1, "n2"),
            lambda x: x["note_hashes"][3]["inputs"].__setitem__(2, "w6"),
            lambda x: x["note_hashes"][3].__setitem__("output", "n4"),
        ]
        for mutate in mutations:
            bad = copy.deepcopy(export)
            mutate(bad)
            with self.assertRaises(ValueError):
                pg.check_ownership_handles(bad, calls, observed)
        expanded = calls + [{"role": f'spend{item["slot"]}.{item["role"]}',
                             "inputs": item["inputs"][:], "output": item["output"]}
                            for item in notes]
        pg.check_ownership_handles(export, expanded, observed)
        for index in range(3, 7):
            for field, value in (("role", "spend0.wrong"), ("inputs", ["w0"]), ("output", "w0")):
                bad = copy.deepcopy(expanded)
                bad[index][field] = value
                with self.assertRaisesRegex(ValueError, "cone/caller descriptor mismatch"):
                    pg.check_ownership_handles(export, bad, observed)

    def test_declared_hash_scope_rejects_unknown_or_incomplete_calls(self):
        basic = {"subject": "actual Transfer authorization hash dependency cones",
                 "scalar_encoding": "canonical-big-endian-32", "modulus_minus_one": f"{pg.P-1:064x}",
                 "calls": []}
        for scope in ("unknown", None, []):
            with self.assertRaisesRegex(ValueError, "unexpected hash export/field"):
                pg.match_export(basic | {"hash_scope": scope}, Path("unused"))
        for scope, subject in (("authorization", basic["subject"]),
                               ("authorization-and-input-notes", "actual Transfer authorization and input-note hash dependency cones")):
            with self.assertRaisesRegex(ValueError, "missing/extra declared hash call"):
                pg.match_export(basic | {"hash_scope": scope, "subject": subject}, Path("unused"))


if __name__ == "__main__":
    unittest.main()
