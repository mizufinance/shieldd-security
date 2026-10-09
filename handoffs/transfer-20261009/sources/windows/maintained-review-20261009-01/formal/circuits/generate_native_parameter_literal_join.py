"""Exact raw parameter literals -> typed canonical codec strings.

This is a closed source-data producer, not a JSON/Rust refinement, row replay,
or cryptographic qualification. Kernel proofs compare literal values with the
proved concrete codec, and symbolic consumers keep the row/column order.
"""
from dataclasses import dataclass
from pathlib import Path
import re

from .generate_native_poseidon_parameters import _checked, _table
from .poseidon_graph import P


@dataclass
class Token:
    kind: str
    value: object
    begin: int
    end: int


class SourceParser:
    """Bounded plain-ASCII subset of both exact artifacts, retaining positions."""

    def __init__(self, raw):
        if not isinstance(raw, bytes) or len(raw) > 128 * 1024 or any(b >= 128 for b in raw):
            raise ValueError("bounded ASCII parameter source required")
        self.raw, self.pos, self.count = raw, 0, 0

    def space(self):
        while self.pos < len(self.raw) and self.raw[self.pos] in b" \t\r\n":
            self.pos += 1

    def parse(self, depth=0):
        self.space()
        self.count += 1
        if depth > 32 or self.count > 10000 or self.pos >= len(self.raw):
            raise ValueError("bounded parameter structure required")
        start, ch = self.pos, self.raw[self.pos]
        if ch == 34:
            self.pos += 1
            begin = self.pos
            while self.pos < len(self.raw) and self.raw[self.pos] != 34:
                if self.raw[self.pos] < 32 or self.raw[self.pos] == 92:
                    raise ValueError("plain source string required")
                self.pos += 1
            if self.pos == len(self.raw):
                raise ValueError("unterminated source string")
            value = self.raw[begin:self.pos].decode("ascii")
            self.pos += 1
            return Token("string", value, start, self.pos)
        if ch in (91, 123):
            close = 93 if ch == 91 else 125
            self.pos += 1
            self.space()
            values, keys = [], set()
            if self.pos < len(self.raw) and self.raw[self.pos] == close:
                self.pos += 1
                return Token("array" if ch == 91 else "object", values, start, self.pos)
            while True:
                if ch == 123:
                    key = self.parse(depth + 1)
                    if key.kind != "string" or key.value in keys:
                        raise ValueError("unique string member required")
                    keys.add(key.value)
                    self.space()
                    if self.pos >= len(self.raw) or self.raw[self.pos] != 58:
                        raise ValueError("source colon required")
                    self.pos += 1
                    values.append((key, self.parse(depth + 1)))
                else:
                    values.append(self.parse(depth + 1))
                self.space()
                if self.pos >= len(self.raw):
                    raise ValueError("unterminated source container")
                punct = self.raw[self.pos]
                self.pos += 1
                if punct == close:
                    break
                if punct != 44:
                    raise ValueError("source separator required")
            return Token("array" if ch == 91 else "object", values, start, self.pos)
        for literal, value in ((b"true", True), (b"false", False), (b"null", None)):
            if self.raw.startswith(literal, self.pos):
                self.pos += len(literal)
                return Token("other", value, start, self.pos)
        match = re.match(rb"-?(?:0|[1-9][0-9]*)", self.raw[self.pos:])
        if not match:
            raise ValueError("source integer required")
        self.pos += len(match[0])
        return Token("integer", int(match[0]), start, self.pos)

    def document(self):
        token = self.parse()
        self.space()
        if self.pos != len(self.raw):
            raise ValueError("complete source EOF required")
        return token


def _matrix_tokens(root, kind, height, width):
    if root.kind != "object":
        raise ValueError("actual object artifact required")
    fields = {key.value: value for key, value in root.value}
    if kind not in fields:
        raise ValueError("coefficient matrix member absent")
    node = fields[kind]
    if node.kind != "array" or len(node.value) != height:
        raise ValueError("exact matrix height required")
    rows = []
    for row in node.value:
        if row.kind != "array" or len(row.value) != width:
            raise ValueError("exact matrix width required")
        if any(value.kind != "string" for value in row.value):
            raise ValueError("coefficient strings required")
        rows.append(row.value)
    return rows


def _canonical_section(source, name, params):
    expected = _table(name, params, "Nat")
    marker = f"def {name} : Poseidon.Parameters Nat {params['width']} where\n"
    begin = source.find(marker)
    if source.count(marker) != 1 or source[begin:begin + len(expected)] != expected:
        raise ValueError("qualified canonical definition differs")


RECORD_KEYS = {"bytes_be", "canonical_integer", "canonical_namespace", "column", "file",
               "lf_content_begin", "literal", "raw_closing_quote", "raw_content_begin",
               "raw_next_cursor", "row", "serde_plain_branch", "table"}


def checked(parameter_root, canonical_source, retained_literals):
    """Reparse source positions and coefficient meaning; never accept a digest alone."""
    if not isinstance(canonical_source, str) or len(canonical_source) > 512 * 1024:
        raise ValueError("bounded canonical module source required")
    if not isinstance(retained_literals, list) or len(retained_literals) != 630:
        raise ValueError("all630 retained literal records required")
    expected_records, tables = [], []
    for file, label, width in (("poseidon381.json", "small", 3), ("poseidon381-wide.json", "wide", 6)):
        path = Path(parameter_root) / file
        raw = path.read_bytes()
        root = SourceParser(raw).document()
        params = _checked(path, width)
        _canonical_section(canonical_source, label + "Canonical", params)
        for kind, height in (("ark", 65), ("mds", width)):
            rows = _matrix_tokens(root, kind, height, width)
            literals = []
            for row_index, row in enumerate(rows):
                literal_row = []
                for column, token in enumerate(row):
                    literal = token.value
                    if not re.fullmatch(r"[0-9a-f]{64}", literal):
                        raise ValueError("exact lowercase64 source literal required")
                    integer = int(literal, 16)
                    if not 0 <= integer < P or params[kind][row_index][column] != integer:
                        raise ValueError("canonical coefficient differs")
                    byte_values = [(integer // (256 ** (31 - i))) % 256 for i in range(32)]
                    rebuilt = "".join("0123456789abcdef"[byte // 16] + "0123456789abcdef"[byte % 16]
                                      for byte in byte_values)
                    begin, end = token.begin + 1, token.end - 1
                    if rebuilt != literal or raw[begin:end] != literal.encode("ascii") or end - begin != 64:
                        raise ValueError("literal byte/codec reconstruction differs")
                    expected_records.append(dict(file=file, table=kind, row=row_index, column=column,
                        raw_content_begin=begin, raw_closing_quote=end, raw_next_cursor=end + 1,
                        lf_content_begin=len(raw[:begin].replace(b"\r\n", b"\n")), literal=literal,
                        canonical_integer=str(integer), bytes_be=byte_values,
                        canonical_namespace="RuntimeNativePoseidonParameters." + label + "Canonical",
                        serde_plain_branch=True))
                    literal_row.append(literal)
                literals.append(literal_row)
            tables.append(dict(label=label, kind=kind, width=width, height=height, literals=literals))
    for actual, expected in zip(retained_literals, expected_records, strict=True):
        if not isinstance(actual, dict) or set(actual) != RECORD_KEYS:
            raise ValueError("closed retained literal record required")
        for key in ("row", "column", "raw_content_begin", "raw_closing_quote", "raw_next_cursor", "lf_content_begin"):
            if type(actual[key]) is not int:
                raise ValueError("literal indices must be exact integers")
        if (type(actual["serde_plain_branch"]) is not bool
                or not isinstance(actual["bytes_be"], list)
                or any(type(byte) is not int for byte in actual["bytes_be"])):
            raise ValueError("literal byte/branch types differ")
        if actual != expected:
            raise ValueError("retained literal source/position/meaning differs")
    return tables


def _module(table):
    label, kind, width, height = (table[key] for key in ("label", "kind", "width", "height"))
    name = "RuntimeNativeParameterLiteral" + label.title() + kind.title()
    source = "import ShielddSecurity.ShielddHexTypedString\nimport ShielddSecurity.RuntimeNativePoseidonParameters\nimport Mathlib.Tactic.FinCases\n"
    source += "set_option maxHeartbeats 1000000\nset_option maxRecDepth 4096\nnamespace ShielddSecurity." + name + "\n"
    source += "local instance finiteLiteralDecidable {n : Nat} (predicate : Fin n → Prop)\n"
    source += "    [DecidablePred predicate] : Decidable (∀ i, predicate i) := Fintype.decidableForallFintype\n"
    source += f"def rawLiteral (row : Fin {height}) (column : Fin {width}) : String :=\n  match row.val with\n"
    for row_index, literals in enumerate(table["literals"]):
        source += f"  | {row_index} => match column.val with\n"
        for column, literal in enumerate(literals):
            source += f'    | {column} => "{literal}"\n'
        source += '    | _ => ""\n'
    source += '  | _ => ""\n'
    selector = "row.val" if kind == "ark" else "row"
    canonical = f"RuntimeNativePoseidonParameters.{label}Canonical.{kind} {selector} column"
    # Keep evaluation local to one small row. A whole-table `decide` retains
    # all 64-character codec computations in a single interpreter reduction.
    for row_index in range(height):
        row = f"(⟨{row_index}, by decide⟩ : Fin {height})"
        selected_row = str(row_index) if kind == "ark" else row
        if width > 3:
            for column_index in range(width):
                column = f"(⟨{column_index}, by decide⟩ : Fin {width})"
                source += f"private theorem raw_codec_cell_{row_index:03d}_{column_index} :\n"
                source += f"    rawLiteral {row} {column} = ShielddHexTypedString.codec.render\n"
                source += f"      (RuntimeNativePoseidonParameters.{label}Canonical.{kind} {selected_row} {column}) := by decide\n"
        source += f"private theorem raw_codec_row_{row_index:03d} (column : Fin {width}) :\n"
        source += f"    rawLiteral {row} column = ShielddHexTypedString.codec.render\n"
        source += f"      (RuntimeNativePoseidonParameters.{label}Canonical.{kind} {selected_row} column) := by\n"
        if width > 3:
            source += "  fin_cases column\n"
            for column_index in range(width):
                source += f"  · exact raw_codec_cell_{row_index:03d}_{column_index}\n"
        else:
            source += "  fin_cases column <;> decide\n"
    source += f"theorem raw_codec_entries : ∀ (row : Fin {height}) (column : Fin {width}),\n"
    source += f"    rawLiteral row column = ShielddHexTypedString.codec.render ({canonical}) := by\n"
    source += "  intro row column\n  fin_cases row\n"
    for row_index in range(height):
        source += f"  · exact raw_codec_row_{row_index:03d} column\n"
    source += f"def rows : List (List String) := List.ofFn (fun row : Fin {height} => List.ofFn (rawLiteral row))\n"
    source += "theorem ordered_rows_render : rows =\n"
    source += f"    List.ofFn (fun row : Fin {height} => List.ofFn (fun column : Fin {width} =>\n"
    source += f"      ShielddHexTypedString.codec.render ({canonical}))) := by\n"
    source += "  apply congrArg List.ofFn\n  funext row\n  apply congrArg List.ofFn\n  funext column\n"
    source += "  exact raw_codec_entries row column\n"
    for audit in ("raw_codec_entries", "ordered_rows_render"):
        source += f"set_option pp.all true in\n#check @{audit}\n#print axioms {audit}\n"
    source += "end ShielddSecurity." + name + "\n"
    return name, source


def _artifact_module():
    """Symbolic composition; no 65-round unfolding or selected decoded result."""
    name = "RuntimeNativeParameterLiteralArtifact"
    source = "import ShielddSecurity.ShielddHexArtifactLoader\n"
    for label, kind in (("Small", "Ark"), ("Small", "Mds"), ("Wide", "Ark"), ("Wide", "Mds")):
        source += f"import ShielddSecurity.RuntimeNativeParameterLiteral{label}{kind}\n"
    source += "set_option maxHeartbeats 200000\nnamespace ShielddSecurity." + name + "\n"
    for label, width, block in (("small", 3, 2), ("wide", 6, 0)):
        source += f'''def {label}Artifact : ShielddJsonArtifactDispatch.Artifact :=
  {{ schema := "shieldd.poseidon381.v1", modulus := "{P}", alpha := 5,
    fullRounds := 8, partialRounds := 57, skipMatrices := 0,
    ark := RuntimeNativeParameterLiteral{label.title()}Ark.rows,
    mds := RuntimeNativeParameterLiteral{label.title()}Mds.rows }}

theorem {label}_source_artifact : {label}Artifact =
    ShielddHexArtifactLoader.sourceArtifact
      (fun row => RuntimeNativePoseidonParameters.{label}Canonical.ark row.val)
      RuntimeNativePoseidonParameters.{label}Canonical.mds := by
  unfold {label}Artifact ShielddHexArtifactLoader.sourceArtifact
  rw [RuntimeNativeParameterLiteral{label.title()}Ark.ordered_rows_render,
    RuntimeNativeParameterLiteral{label.title()}Mds.ordered_rows_render]
  simp only [ShielddNativeLoadedPermutation.sourceHeader,
    ShielddHexArtifactLoader.renderRow, List.map_ofFn, Function.comp_def]

theorem {label}_literal_load {{F Q : Type}} [Field F] [CharP F Scalar.modulus]
    (fq : GroupNativeSdk.FqBytes Q)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (canonical : TransferReduction.CanonicalField F) :
    ShielddHexArtifactLoader.loadArtifact {width} fq {label}Artifact =
      some (ShielddNativeLoadedPermutation.expectedNative fq arithmetic canonical
        {{ ark := fun row column => (RuntimeHashBlock_authorization_rnk_permutation{block}_0.parameters.ark row column : F), mds := fun row column => (RuntimeHashBlock_authorization_rnk_permutation{block}_0.parameters.mds row column : F) }}) := by
  rw [{label}_source_artifact]
  exact ShielddHexArtifactLoader.{label}_source_object fq arithmetic canonical

'''
    audits = ["small_source_artifact", "small_literal_load", "wide_source_artifact", "wide_literal_load"]
    for audit in audits:
        source += f"set_option pp.all true in\n#check @{audit}\n#print axioms {audit}\n"
    source += "end ShielddSecurity." + name + "\n"
    return name, source, audits


def generate(parameter_root, canonical_source, retained_literals):
    tables = checked(parameter_root, canonical_source, retained_literals)
    modules = dict(_module(table) for table in tables)
    audits = {name: ["raw_codec_entries", "ordered_rows_render"] for name in modules}
    name, source, artifact_audits = _artifact_module()
    modules[name], audits[name] = source, artifact_audits
    return dict(modules=modules, audits=audits,
        literal_count=630, qualification=False, certification=False, evidence=[],
        scope="Actual unescaped raw literal values to proved typed codec and qualified canonical tables; ordered row equality only, not JSON/Rust parser refinement or Transfer qualification")
