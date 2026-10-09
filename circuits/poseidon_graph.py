"""Expected Poseidon arithmetic and a closed actual-source-cone matcher.

This checks source operation shape, not the Pari row equations: Compiler.lean
certificates must separately relate each matched source node to emitted rows.
There is no hash-injectivity or cryptographic-security conclusion here.
"""
import json
from pathlib import Path

P = 52435875175126190479447740508185965837690552500527637822603658699938581184513


def decode_json(text: str) -> dict:
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON member: {key}")
            result[key] = value
        return result
    return json.loads(text, object_pairs_hook=unique)


def parameters(path: Path, width: int) -> dict:
    obj = decode_json(path.read_text(encoding="utf-8"))
    required = {"schema", "modulus", "alpha", "full_rounds", "partial_rounds",
                "skip_matrices", "ark", "mds", "vectors"}
    if set(obj) != required or width not in (3, 6):
        raise ValueError("unsupported parameter artifact")
    if (obj["schema"], obj["modulus"], obj["alpha"], obj["full_rounds"],
        obj["partial_rounds"], obj["skip_matrices"]) != (
            "shieldd.poseidon381.v1", str(P), 5, 8, 57, 0):
        raise ValueError("unexpected Poseidon recipe")

    def matrix(rows, height):
        if len(rows) != height or any(len(row) != width for row in rows):
            raise ValueError("parameter dimensions")
        result = []
        for row in rows:
            values = []
            for encoded in row:
                if not isinstance(encoded, str) or len(encoded) != 64:
                    raise ValueError("parameter encoding")
                raw = bytes.fromhex(encoded)
                value = int.from_bytes(raw, "big")
                if len(raw) != 32 or value >= P:
                    raise ValueError("noncanonical field parameter")
                values.append(value)
            result.append(values)
        return result

    return {"width": width, "ark": matrix(obj["ark"], 65),
            "mds": matrix(obj["mds"], width), "vectors": obj["vectors"]}


def expected(params: dict, domain: int, arity: int) -> dict:
    """Finite DAG, retaining sharing rather than expanding a round expression.

    Native-only constant folding and constant-left ordering match Var's two
    arithmetic construction rules. Their meaning is ordinary field arithmetic;
    neither compiler witness values nor observed output values are consulted.
    """
    if type(domain) is not int or not 0 <= domain < 256:
        raise ValueError("domain is not u8")
    if type(arity) is not int or not 0 <= arity <= ((1 << 64) - 1 - domain) // 256:
        raise ValueError("arity IV overflow")
    width = 3 if arity <= 2 else 6
    if params["width"] != width:
        raise ValueError("wrong width for input arity")
    nodes, segments = [], []

    def append(node):
        nodes.append(node)
        return len(nodes) - 1

    def constant(value):
        return append({"kind": "constant", "value": value % P})

    def binary(kind, left, right):
        lc, rc = nodes[left]["kind"] == "constant", nodes[right]["kind"] == "constant"
        if lc and rc:
            a, b = nodes[left]["value"], nodes[right]["value"]
            return constant(a + b if kind == "add" else a * b)
        if rc:
            left, right = right, left
        return append({"kind": kind, "left": left, "right": right})

    inputs = [append({"kind": "input", "slot": i}) for i in range(arity)]
    state = [constant(arity * 256 + domain)] + [constant(0) for _ in range(width - 1)]
    chunks = [inputs[i:i + width - 1] for i in range(0, arity, width - 1)] or [[]]
    for chunk_index, chunk in enumerate(chunks):
        before_absorb = list(state)
        for i, item in enumerate(chunk):
            state[i + 1] = binary("add", state[i + 1], item)
        segments.append({"kind": "absorb", "chunk": chunk_index,
                         "before": before_absorb, "inputs": list(chunk), "after": list(state)})
        for round_index in range(65):
            before = list(state)
            state = [binary("add", item, constant(params["ark"][round_index][i]))
                     for i, item in enumerate(state)]
            shifted, powers = list(state), {}
            for i, item in enumerate(state):
                if round_index < 4 or round_index >= 61 or i == 0:
                    square = binary("mul", item, item)
                    fourth = binary("mul", square, square)
                    state[i] = binary("mul", fourth, item)
                    powers[i] = {"square": square, "fourth": fourth, "fifth": state[i]}
            transformed = list(state)
            mixed = []
            for row in params["mds"]:
                total = constant(0)
                for coefficient, item in zip(row, state):
                    total = binary("add", total, binary("mul", constant(coefficient), item))
                mixed.append(total)
            state = mixed
            segments.append({"kind": "round", "chunk": chunk_index, "round": round_index,
                             "before": before, "shifted": shifted, "powers": powers,
                             "transformed": transformed, "after": list(state)})
    return {"domain": domain, "arity": arity, "width": width,
            "nodes": nodes, "inputs": inputs, "output": state[1], "segments": segments}


def permutation(params: dict, before: list[int | None]) -> dict:
    """One permutation from independently typed native/source state coordinates.

    None denotes a source boundary; an integer is an existing native constant.
    Absorption and sponge adjacency are separate checks, not implied here.
    """
    width=params['width']
    if width not in (3,6) or not isinstance(before,list) or len(before)!=width:
        raise ValueError('invalid permutation state width')
    if any(value is not None and (type(value) is not int or not 0<=value<P) for value in before):
        raise ValueError('noncanonical native permutation state')
    nodes=[];segments=[];inputs=[]
    def append(node):nodes.append(node);return len(nodes)-1
    def constant(value):return append({'kind':'constant','value':value%P})
    def binary(kind,left,right):
        lc,rc=nodes[left]['kind']=='constant',nodes[right]['kind']=='constant'
        if lc and rc:
            a,b=nodes[left]['value'],nodes[right]['value']
            return constant(a+b if kind=='add' else a*b)
        if rc:left,right=right,left
        return append({'kind':kind,'left':left,'right':right})
    state=[]
    for value in before:
        if value is None:
            item=append({'kind':'input','slot':len(inputs)});inputs.append(item)
        else:item=constant(value)
        state.append(item)
    initial=list(state)
    for round_index in range(65):
        previous=list(state)
        state=[binary('add',item,constant(params['ark'][round_index][i])) for i,item in enumerate(state)]
        shifted=list(state);powers={}
        for i,item in enumerate(state):
            if round_index<4 or round_index>=61 or i==0:
                square=binary('mul',item,item);fourth=binary('mul',square,square)
                state[i]=binary('mul',fourth,item)
                powers[i]={'square':square,'fourth':fourth,'fifth':state[i]}
        transformed=list(state);mixed=[]
        for row in params['mds']:
            total=constant(0)
            for coefficient,item in zip(row,state):
                total=binary('add',total,binary('mul',constant(coefficient),item))
            mixed.append(total)
        state=mixed
        segments.append({'kind':'round','chunk':0,'round':round_index,'before':previous,
                         'shifted':shifted,'powers':powers,'transformed':transformed,'after':list(state)})
    return {'mode':'permutation','arity':len(inputs),'width':width,'nodes':nodes,
            'inputs':inputs,'initial':initial,'outputs':list(state),'output':state[1],'segments':segments}


def match_permutation(graph: dict, source: dict, input_refs: list[str], output_refs: list[str]) -> list:
    """Match every output lane; lane-one agreement alone is insufficient."""
    if graph.get('mode')!='permutation' or len(output_refs)!=graph['width']:
        raise ValueError('permutation output width mismatch')
    matched=set()
    for expected_output,actual_output in zip(graph['outputs'],output_refs):
        lane={**graph,'output':expected_output}
        matched.update(match_source(lane,source,input_refs,actual_output))
    return sorted(matched)


def evaluate(graph: dict, inputs: list[int]) -> int:
    if len(inputs) != graph["arity"] or any(type(x) is not int or not 0 <= x < P for x in inputs):
        raise ValueError("noncanonical input tuple")
    values = []
    for node in graph["nodes"]:
        kind = node["kind"]
        if kind == "constant":
            value = node["value"]
        elif kind == "input":
            value = inputs[node["slot"]]
        elif kind == "add":
            value = values[node["left"]] + values[node["right"]]
        elif kind == "mul":
            value = values[node["left"]] * values[node["right"]]
        else:
            raise ValueError("unsupported operation")
        values.append(value % P)
    return values[graph["output"]]


def match_source(graph: dict, source: dict, input_refs: list[str], output_ref: str) -> list:
    """Match a complete exported Add/Mul cone against independently built data.

    Source references are original `cN`, `wN`, `nN` identities. Only named hash
    inputs may stop traversal. A hidden witness, wrong slot, unsupported source
    operation or forward edge fails. Exporter provenance/full-relation membership
    and the semantic roles of the input/output handles remain explicit joins.
    Source JSON ingress must use decode_json, never last-key-wins decoding.
    Returns expected-node/source-index pairs for subsequent row certificates;
    the pairs are not a bijection because shared/equal subexpressions can occur
    at different source identities. Each returned pair needs its own binding.
    """
    if len(input_refs) != graph["arity"] or len(set(input_refs)) != len(input_refs):
        raise ValueError("input arity/alias unsupported")

    def ref(value):
        if (not isinstance(value, str) or len(value) < 2 or value[0] not in "cwn"
                or not value[1:].isascii() or not value[1:].isdigit()
                or str(int(value[1:])) != value[1:]):
            raise ValueError("invalid source reference")
        return value[0], int(value[1:])

    for name, node in source.items():
        role, index = ref(name)
        if role == "c":
            if set(node) != {"kind", "value"} or node["kind"] != "constant" or type(node["value"]) is not int or not 0 <= node["value"] < P:
                raise ValueError("invalid source constant")
        elif role == "w":
            if node != {"kind": "witness"}:
                raise ValueError("invalid source witness")
        else:
            if set(node) != {"kind", "left", "right"} or node["kind"] not in ("add", "mul"):
                raise ValueError("unsupported source node")
            for child in (node["left"], node["right"]):
                child_role, child_index = ref(child)
                if ((child not in source and name not in input_refs)
                        or (child_role == "n" and child_index >= index)):
                    raise ValueError("missing/forward source reference")
    if any(name not in source for name in input_refs + [output_ref]):
        raise ValueError("missing declared source handle")
    boundary = {name: i for i, name in enumerate(input_refs)}
    work = [(graph["output"], output_ref)]
    matched = set()
    while work:
        expected_id, actual_id = work.pop()
        if (expected_id, actual_id) in matched:
            continue
        wanted, actual = graph["nodes"][expected_id], source[actual_id]
        if wanted["kind"] == "input":
            if boundary.get(actual_id) != wanted["slot"]:
                raise ValueError("source hash input/slot mismatch")
        elif actual_id in boundary:
            raise ValueError("undeclared computation at input boundary")
        elif wanted["kind"] == "constant":
            if actual != wanted:
                raise ValueError("source constant mismatch")
        else:
            if actual["kind"] != wanted["kind"]:
                raise ValueError("source operation or undeclared witness mismatch")
            work.extend((wanted[side], actual[side]) for side in ("left", "right"))
        matched.add((expected_id, actual_id))
    return sorted(matched)


def match_export(export: dict, parameter_root: Path) -> list[dict]:
    """Check the three actual authorization call cones; not their row proofs.

    Each declared input is an exact retained constructor handle. A computed
    input boundary may omit its earlier children from this call's cone. Its
    operation/ref shape remains checked, and proving that boundary's value is
    deliberately a separate prior-stage obligation.
    """
    scope = export.get("hash_scope", "authorization")
    subjects = {
        "authorization": "actual Transfer authorization hash dependency cones",
        "transfer-ivk-only": "actual Transfer IVK hash dependency cone",
        "authorization-and-input-notes": "actual Transfer authorization and input-note hash dependency cones",
    }
    if (not isinstance(scope, str) or scope not in subjects or export.get("subject") != subjects[scope]
            or export.get("scalar_encoding") != "canonical-big-endian-32"
            or export.get("modulus_minus_one") != f"{P-1:064x}"):
        raise ValueError("unexpected hash export/field")
    expected_calls = [("authorization.ivk", 16, 3),
                      ("authorization.rnk", 17, 9),
                      ("authorization.rnk_commitment", 18, 1)]
    if scope == "transfer-ivk-only":
        handles = export.get("input_source_handles")
        if (export.get("input_role_provenance") != "formal input renaming; original captured handles retained"
                or not isinstance(handles,list) or len(handles) != 3
                or any(not isinstance(h,list) or len(h) != 2
                    or type(h[0]) is not int or h[0] not in (1,2)
                    or type(h[1]) is not int or not 0 <= h[1] < 2**32 for h in handles)
                or len({tuple(h) for h in handles}) != 3):
            raise ValueError("missing exact IVK formal-boundary source mapping")
        expected_calls = expected_calls[:1]
    if scope == "authorization-and-input-notes":
        expected_calls.extend((f"spend{slot}.{kind}", domain, arity)
                              for slot in range(2)
                              for kind, domain, arity in (("commitment", 15, 8), ("nullifier", 7, 3)))
    calls = export.get("calls")
    if not isinstance(calls, list) or len(calls) != len(expected_calls):
        raise ValueError("missing/extra declared hash call")
    expressions = export.get("expressions")
    if not isinstance(expressions, list):
        raise ValueError("missing compiled source observations")
    observed = {}
    for expression in expressions:
        if set(expression) != {"source", "kind", "terms"} or expression["kind"] not in ("linear", "square"):
            raise ValueError("unsupported compiled observation")
        source = expression["source"]
        if source in observed:
            raise ValueError("duplicate compiled source observation")
        observed[source] = expression
    result, shared_source = [], {}
    for call, (role, domain, arity) in zip(calls, expected_calls):
        if (set(call) != {"role", "domain", "inputs", "output", "source"}
                or call["role"] != role or type(call["domain"]) is not int
                or call["domain"] != domain or len(call["inputs"]) != arity):
            raise ValueError("wrong authorization hash role/domain/arity")
        source = {}
        for identity, item in call["source"].items():
            value = dict(item)
            if value.get("kind") == "constant":
                encoded = value.get("value")
                if (not isinstance(encoded, str) or len(encoded) != 64
                        or any(c not in "0123456789abcdef" for c in encoded)
                        or int(encoded, 16) >= P):
                    raise ValueError("noncanonical source constant")
                value["value"] = int(encoded, 16)
            source[identity] = value
            if identity in shared_source and shared_source[identity] != value:
                raise ValueError("contradictory shared source identity")
            shared_source[identity] = value
        if scope == "transfer-ivk-only":
            if call["inputs"] != ["w0","w1","w2"]:
                raise ValueError("IVK formal input order changed")
            for formal, handle in zip(call["inputs"], export["input_source_handles"]):
                expression = observed.get(formal)
                if expression is None or expression["kind"] != "linear":
                    raise ValueError("missing IVK formal boundary expression")
                if handle[0] == 1 and expression["terms"] != [[3+handle[1],f"{1:064x}"]]:
                    raise ValueError("IVK original witness handle/LC mapping changed")
        if any(identity not in observed for identity in source):
            raise ValueError("source node lacks compiled observation")
        width = 3 if arity <= 2 else 6
        filename = "poseidon381.json" if width == 3 else "poseidon381-wide.json"
        graph = expected(parameters(parameter_root / filename, width), domain, arity)
        pairs = match_source(graph, source, call["inputs"], call["output"])
        result.append({"role": role, "graph": graph, "source": source, "pairs": pairs,
                       "inputs": call["inputs"], "output": call["output"]})
    if scope == "transfer-ivk-only":
        return result
    if result[2]["inputs"] != [result[1]["output"]]:
        raise ValueError("RNK commitment does not consume the actual RNK output")
    check_ownership_handles(export, result, observed)
    return result


def check_ownership_handles(export: dict, calls: list[dict], observed: dict) -> None:
    """Check same-constructor handle joins, not group/hash/signature semantics.

    Source assertions here remain extraction evidence. Their mathematical
    consequences must separately be derived from actual compiled rows.
    """
    roles = export.get("ownership")
    if len(calls) not in (3, 7):
        raise ValueError("unsupported caller-role hash scope")
    expected_roles = {"authorization.effective_nk", "action.ak.x", "action.ak.y",
                      "action.randomizer", "action.computed_rk.x", "action.computed_rk.y",
                      "action.rk.x", "action.rk.y", "statement.rk.x", "statement.rk.y"}
    expected_roles.update(f"spend{slot}.{role}" for slot in range(2)
                          for role in ("position", "real_nullifier"))
    if not isinstance(roles, dict) or set(roles) != expected_roles:
        raise ValueError("missing/extra ownership role")
    if any(not isinstance(value, str) or value not in observed for value in roles.values()):
        raise ValueError("unobserved ownership handle")
    if [roles["action.ak.x"], roles["action.ak.y"]] != calls[0]["inputs"][1:]:
        raise ValueError("IVK does not use the action authorization key")
    assertions = export.get("touching_source_assertions")
    if not isinstance(assertions, list):
        raise ValueError("missing source assertion evidence")
    pairs, indices = set(), set()
    for item in assertions:
        if (not isinstance(item, dict) or set(item) != {"index", "left", "right"}
                or type(item["index"]) is not int or item["index"] < 0
                or item["index"] in indices
                or not all(isinstance(item[side], str) for side in ("left", "right"))):
            raise ValueError("invalid source assertion evidence")
        indices.add(item["index"])
        pairs.add((item["left"], item["right"]))
    for axis in ("x", "y"):
        if roles[f"action.rk.{axis}"] != roles[f"statement.rk.{axis}"]:
            raise ValueError("statement/action authorization key mismatch")
        pair = (roles[f"action.computed_rk.{axis}"], roles[f"action.rk.{axis}"])
        if pair not in pairs and pair[::-1] not in pairs:
            raise ValueError("missing computed/action authorization assertion")
    notes = export.get("note_hashes")
    if not isinstance(notes, list) or len(notes) != 4:
        raise ValueError("missing/extra input note hash roles")
    for slot in range(2):
        commitment, nullifier = notes[2 * slot:2 * slot + 2]
        for item, role, domain, arity in ((commitment, "commitment", 15, 8),
                                          (nullifier, "nullifier", 7, 3)):
            if (not isinstance(item, dict) or set(item) != {"slot", "role", "domain", "inputs", "output"}
                    or type(item["slot"]) is not int or item["slot"] != slot
                    or item["role"] != role or type(item["domain"]) is not int or item["domain"] != domain
                    or not isinstance(item["inputs"], list) or len(item["inputs"]) != arity
                    or any(not isinstance(ref, str) or ref not in observed
                           for ref in item["inputs"] + [item["output"]])):
                raise ValueError("invalid input note hash role/domain/handles")
        rnk_inputs = calls[1]["inputs"]
        if commitment["inputs"][2] != rnk_inputs[6] or commitment["inputs"][3:7] != rnk_inputs[2:6]:
            raise ValueError("note does not use shared authorized asset/address")
        if nullifier["inputs"] != [roles["authorization.effective_nk"], commitment["output"], roles[f"spend{slot}.position"]]:
            raise ValueError("note nullifier key/commitment/position mismatch")
        if nullifier["output"] != roles[f"spend{slot}.real_nullifier"]:
            raise ValueError("note nullifier output/spend mismatch")
        if len(calls) == 7:
            for offset, descriptor in enumerate((commitment, nullifier)):
                actual = calls[3 + 2 * slot + offset]
                if (actual["role"] != f'spend{slot}.{descriptor["role"]}'
                        or actual["inputs"] != descriptor["inputs"]
                        or actual["output"] != descriptor["output"]):
                    raise ValueError("note dependency cone/caller descriptor mismatch")
