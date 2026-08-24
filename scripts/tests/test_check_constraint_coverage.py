import os
import subprocess
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CHECK = ROOT / "scripts/check-constraint-coverage.sh"


def bridge_import_function() -> str:
    lines = CHECK.read_text().splitlines()
    start = lines.index("bridge_import_for_theorem() {")
    end = next(i for i in range(start + 1, len(lines)) if lines[i] == "}")
    return "\n".join(lines[start : end + 1])


def shell_function(name: str) -> str:
    lines = CHECK.read_text().splitlines()
    start = lines.index(f"{name}() {{")
    end = next(i for i in range(start + 1, len(lines)) if lines[i] == "}")
    return "\n".join(lines[start : end + 1])


class BridgeImportTests(unittest.TestCase):
    def mapped_import(self, theorem: str) -> str:
        script = bridge_import_function() + '\nbridge_import_for_theorem "$1"'
        shell = ["bash"]
        if os.name == "nt":
            shell = ["wsl.exe", "-e", "bash"]
        result = subprocess.run(
            [*shell, "-c", script, "bridge-import-test", theorem],
            check=True,
            capture_output=True,
            text=True,
        )
        return result.stdout.strip()

    def test_split_semantic_bridge_modules_resolve(self) -> None:
        self.assertEqual(
            self.mapped_import(
                "Shieldd.GnarkFormal.Deployed.DecafAssertOnCurve.circuit_sound"
            ),
            "ShielddGnarkFormal.Deployed.DecafAssertOnCurveBridge",
        )
        self.assertEqual(
            self.mapped_import(
                "Shieldd.GnarkFormal.DtkBridge."
                "decaf377_diversifiedTransmissionKey_sound"
            ),
            "ShielddGnarkFormal.DtkBridge.Semantics",
        )
        self.assertEqual(
            self.mapped_import(
                "Shieldd.GnarkFormal.isZeroExtracted_implies_is_zero"
            ),
            "ShielddGnarkFormal.ExtractedProofs",
        )

    def test_generic_namespace_mapping_remains_available(self) -> None:
        self.assertEqual(
            self.mapped_import("Shieldd.GnarkFormal.Poseidon3Bridge.circuit_sound"),
            "ShielddGnarkFormal.Poseidon3Bridge",
        )


class SemanticGenerationTests(unittest.TestCase):
    def test_shared_generator_runs_once_after_backend_discovery(self) -> None:
        source = CHECK.read_text()
        command = '"$ROOT/tools/gnark/lean/gen/gen_note_reshape_template_semantics.py"'
        self.assertEqual(source.count(command), 1)
        self.assertLess(
            source.index('done <<< "$generation_backends"'),
            source.index(command),
        )

    def test_atomic_validation_can_reuse_fresh_semantics(self) -> None:
        source = CHECK.read_text()
        self.assertIn('${FV_SEMANTICS_CURRENT:-0}', source)


class TemplateMergeTests(unittest.TestCase):
    def run_shell(self, body: str) -> subprocess.CompletedProcess[str]:
        shell = ["bash"]
        if os.name == "nt":
            shell = ["wsl.exe", "-e", "bash"]
        fail = "fail() { printf '%s\\n' \"$*\" >&2; exit 1; }"
        script = "\n".join(
            (fail, shell_function("merge_generated_templates"), body)
        )
        return subprocess.run(
            [*shell, "-c", script],
            capture_output=True,
            text=True,
        )

    def test_templates_from_each_circuit_are_unioned(self) -> None:
        result = self.run_shell(
            """
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
for source in first second; do
  mkdir -p "$work/$source/Generated" "$work/$source/Relations"
done
printf first > "$work/first/Generated/First.lean"
printf first > "$work/first/Relations/First.lean"
printf second > "$work/second/Generated/Second.lean"
printf second > "$work/second/Relations/Second.lean"
merge_generated_templates "$work/first" "$work/all" first
merge_generated_templates "$work/second" "$work/all" second
test "$(find "$work/all" -type f | wc -l)" -eq 4
"""
        )
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_conflicting_template_content_fails_closed(self) -> None:
        result = self.run_shell(
            """
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
for source in first second; do
  mkdir -p "$work/$source/Generated" "$work/$source/Relations"
done
printf first > "$work/first/Generated/Same.lean"
printf relation > "$work/first/Relations/Same.lean"
printf second > "$work/second/Generated/Same.lean"
printf relation > "$work/second/Relations/Same.lean"
merge_generated_templates "$work/first" "$work/all" first
merge_generated_templates "$work/second" "$work/all" second
"""
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("normalized template collision", result.stderr)


class CircuitIterationTests(unittest.TestCase):
    def test_circuit_list_is_not_exposed_as_child_stdin(self) -> None:
        source = CHECK.read_text()
        self.assertIn(
            'mapfile -t selected_circuit_list <<< "$selected_circuits"',
            source,
        )
        self.assertIn(
            'for circuit in "${selected_circuit_list[@]}"; do',
            source,
        )
        self.assertNotIn(
            'done < <(printf \'%s\\n\' "$selected_circuits")',
            source,
        )


if __name__ == "__main__":
    unittest.main()
