"""Exact detection/core ciphertext assertions and four seed operand aliases.

Address packing, DH, hash results, and native/caller correspondence are separate
obligations. This module retains only nine rows while inspecting the ordinary
relation, rather than accumulating unrelated assertions.
"""
from . import transfer_arithmetic as arithmetic
from . import transfer_relation as relation
from . import transfer_remaining_pages as pages
from .transfer_balance_rows import canonical, combine


def plan(checked):
    pages.require(checked["metadata"]["scope"] == "encryption", "cipher source scope")
    records = checked["records"]
    published = records["encryption", "published44", 0]
    shared = records["encryption", "shared", 0]
    calls = [call for call in checked["metadata"]["calls"] if call["scope"] == "encryption"]
    pages.require(len(calls) == 24, "cipher exact encryption call roster")

    def value(ref):
        kind, item = pages.reference(ref)
        return canonical([(0, item)]) if kind == "native" else checked["observed"][item]

    def inputs(index, expected):
        pages.require(calls[index]["inputs"] == expected, "cipher exact hash operand order")

    def integer(n):
        return {"native": f"{n:064x}"}

    for index in range(5):
        inputs(index, [shared[1], integer(index)])
    pages.require(calls[5]["inputs"][2:] == published[4:6], "detection exact tier-zero EPK")
    for index in range(4):
        inputs(6 + index, [calls[5]["output"], integer(index)])

    assertions = []
    plaintext = [value(shared[2]), value(calls[0]["output"]), value(shared[0]), ()]
    for index in range(4):
        assertions.append((f"detection{index}", value(published[index]),
                           combine(plaintext[index], value(calls[6 + index]["output"]))))

    seeds = []
    # Published.fields orders each core as EPK x/y, c2, confirmation, ciphertext.
    for tier, secret, seed_call, core, salt in [(0, 10, 11, 4, 1), (2, 13, 14, 9, 3)]:
        seed = value(calls[seed_call]["inputs"][0])
        expected = combine(value(published[core + 2]), value(calls[secret]["output"]), -1)
        pages.require(seed == expected, "core exact c2 minus secret LC")
        inputs(seed_call, [calls[seed_call]["inputs"][0], *published[core:core + 2],
                           calls[salt]["output"]])
        inputs(seed_call + 1, [calls[seed_call]["inputs"][0], integer(0)])
        seeds.append((f"seed{tier}", seed, value(published[core + 2]),
                      value(calls[secret]["output"])))
        assertions.extend([
            (f"core{tier}_confirmation", value(published[core + 3]),
             value(calls[seed_call]["output"])),
            (f"core{tier}_amount", value(published[core + 4]),
             combine(value(shared[3]), value(calls[seed_call + 1]["output"]))),
        ])
    for tier, secret, start, c2 in [(1, 16, 17, 16), (3, 20, 21, 22)]:
        seed_ref = calls[start]["inputs"][0]
        seed = value(seed_ref)
        expected = combine(value(published[c2]), value(calls[secret]["output"]), -1)
        pages.require(seed == expected, "extended exact c2 minus secret LC")
        for index in range(3):
            inputs(start + index, [seed_ref, integer(index)])
        seeds.append((f"seed{tier}", seed, value(published[c2]), value(calls[secret]["output"])))
    pages.require(len(assertions) == 8 and len(seeds) == 4, "closed cipher obligation roster")
    return dict(assertions=assertions, seeds=seeds)


def extract(checked, stream):
    derived = plan(checked)
    metadata = checked["metadata"]
    copy = metadata["constant_copy"]
    outline = lambda lc: canonical((copy if c == 0 else c, v) for c, v in lc)
    required = {canonical([(0, 1), (copy, -1)]): "constant-copy"}
    for name, left, right in derived["assertions"]:
        delta = outline(combine(left, right, -1))
        pages.require(bool(delta) and delta not in required, "distinct nontrivial cipher assertion")
        required[delta] = name
    matched = {}
    selected = {}

    def observe(row):
        if row["b"]:
            return
        a = tuple((c, int(v, 16)) for c, v in row["a"])
        key = a if a in required else canonical((c, -v) for c, v in a)
        if key in required and key not in matched:
            matched[key] = row["row"]
            selected[row["row"]] = row

    identity = relation.inspect(stream, expected_relation=metadata["relation_digest"], row_observer=observe)
    pages.require(identity["domain_size"] == metadata["domain_size"]
                  and identity["stored_rows"] == metadata["full_rows"], "cipher ordinary shape")
    pages.require(set(matched) == set(required), "all eight actual cipher assertions and copy row")
    return dict(identity=identity, selected_rows=[selected[i] for i in sorted(selected)],
                templates=[dict(row=matched[key], roles=[role]) for key, role in required.items()],
                products=[], metadata_sha256=checked["metadata_sha256"],
                scope="Eight detection/core physical equality rows; four c2-secret seed aliases; address/DH/native/full Transfer open")


def generate(checked, extracted):
    from .generate_hash_round import linear
    derived = plan(checked)
    raw, normalized = arithmetic.normalize_selection(
        extracted, checked["metadata"], checked["metadata_sha256"])
    copy = checked["metadata"]["constant_copy"]
    pages.require(len(raw) == 9, "exact cipher nine-row retention")
    source = ("import ShielddSecurity.Compiler\nset_option maxHeartbeats 400000\n"
              "namespace ShielddSecurity.RuntimeEncryptionCipherRows\n"
              f"def modulus : Nat := {relation.MODULUS}\n"
              "def rawRows : List Row := [\n" + ",\n".join(
                  "⟨" + linear(a) + "," + linear(b) + "⟩" for a, b in raw.values()) + "]\n"
              f"def rows : List Row := Compiler.unoutlineRows {copy} rawRows\n"
              f"theorem constant_link : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide\n")
    names = ["constant_link"]
    for name, seed, c2, secret in derived["seeds"]:
        source += f"""theorem {name} {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F) :
    eval rho {linear(seed)} = eval rho {linear(c2)} - eval rho {linear(secret)} := by
  have same := Compiler.canonical_equal rho {linear(seed)}
    (Compiler.subtract {linear(c2)} {linear(secret)}) (by decide)
  simpa only [Compiler.eval_subtract] using same
"""
        names.append(name)
    used = set()
    for name, left, right in derived["assertions"]:
        delta = combine(left, right, -1)
        matches = [i for i, row in normalized.items() if row in
                   ((delta, ()), (canonical((c, -v) for c, v in delta), ()))]
        pages.require(len(matches) == 1, "exact retained cipher equality")
        used.update(matches)
        direct = normalized[matches[0]][0] == delta
        first, second = (left, right) if direct else (right, left)
        proof = (f"Compiler.checked_assertion_sound rho rows {linear(first)} {linear(second)} "
                 "normalized (by decide)")
        if not direct:
            proof = "(" + proof + ").symm"
        source += f"""theorem {name} {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho {linear(left)} = eval rho {linear(right)} := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constant_link
  exact {proof}
"""
        names.append(name)
    pages.require(len(used) == 8, "all eight distinct retained cipher assertions used")
    for name in names:
        source += f"set_option pp.all true in\n#check @{name}\n#print axioms {name}\n"
    source += "end ShielddSecurity.RuntimeEncryptionCipherRows\n"
    return source, names
