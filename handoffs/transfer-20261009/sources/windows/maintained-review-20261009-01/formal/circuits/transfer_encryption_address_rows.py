"""Infer address packing operands from exact physical ciphertext assertions.

The 248/248/16 coefficient sequences identify the word operands. Their point
coordinate reconstructions, Boolean rows, and full canonical comparisons are
then independently checked against the same original relation. No native byte
value, guessed source handle, or desired ciphertext is used as a premise.
"""
from . import transfer_relation as relation
from . import transfer_routing_rows as physical
from . import transfer_encryption_cipher_rows as cipher
from .transfer_balance_rows import canonical, combine

SCHEMA = "shieldd-transfer-encrypted-address-rows-v1"
MAX_POOL_ROWS = 150000
MAX_POOL_TERMS = 900000


def _columns(weighted, width, occupied):
    if len(weighted) != width:
        return None
    powers = {1 << i: i for i in range(width)}
    columns = [None] * width
    for column, coefficient in weighted:
        if column in occupied or coefficient not in powers:
            return None
        index = powers[coefficient]
        if columns[index] is not None:
            return None
        columns[index] = column
    if any(column is None for column in columns) or len(set(columns)) != width:
        return None
    return tuple(columns)


def extract(checked, stream):
    # Validate all seed/counter/EPK/confirmation identities before row inference.
    cipher.plan(checked)
    metadata = checked["metadata"]
    copy = metadata["constant_copy"]
    shared = checked["records"]["encryption", "shared", 0]
    published = checked["records"]["encryption", "published44", 0]
    calls = [c for c in metadata["calls"] if c["scope"] == "encryption"]

    def value(ref):
        kind, handle = physical.pages.reference(ref)
        return canonical([(0, handle)]) if kind == "native" else checked["observed"][handle]

    targets = []
    for owner, address, start, output in [("Receiver", 15, 17, 17), ("Sender", 11, 21, 23)]:
        coordinates = [value(ref) for ref in shared[address:address + 4]]
        words = [(value(published[output + i]), value(calls[start + i]["output"])) for i in range(3)]
        targets.append(dict(owner=owner, coordinates=coordinates, words=words))
    touched = {c for target in targets for lc in target["coordinates"] +
               [lc for pair in target["words"] for lc in pair] for c, _ in lc}
    raw, normalized = {}, {}
    term_count = 0

    def observe(row):
        nonlocal term_count
        a, b = (tuple((c, int(v, 16)) for c, v in row[key]) for key in ("a", "b"))
        if not (len(a) <= 6 and len(b) <= 6 or any(c in touched for c, _ in a)):
            return
        term_count += len(a) + len(b)
        if len(raw) >= MAX_POOL_ROWS or term_count > MAX_POOL_TERMS:
            raise relation.RelationError("bounded encrypted-address row pool exceeded")
        raw[row["row"]] = a, b
        normalized[row["row"]] = tuple(canonical((0 if c == copy else c, v) for c, v in lc)
                                        for lc in (a, b))

    identity = relation.inspect(stream, expected_relation=metadata["relation_digest"], row_observer=observe)
    physical.pages.require(identity["domain_size"] == metadata["domain_size"] and
                           identity["stored_rows"] == metadata["full_rows"], "address ordinary shape")
    links = [i for i, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ())]
    physical.pages.require(len(links) == 1, "address exact constant-copy row")
    table = physical._Rows(raw, normalized, copy)
    used = {links[0]}
    addresses = []
    decompositions = []
    for target in targets:
        owner = target["owner"]
        word_plans = []
        occupied = {0, copy} | {c for lc in target["coordinates"] for c, _ in lc}
        for ordinal, (output, stream_value) in enumerate(target["words"]):
            width = 248 if ordinal < 2 else 16
            output_column = physical._unit(output, "address ciphertext witness")
            candidates = []
            base = combine(output, stream_value, -1)
            for index, (a, b) in normalized.items():
                if b or not any(c == output_column for c, _ in a):
                    continue
                for orientation in (1, -1):
                    word = combine(base, a, orientation)
                    columns = _columns(word, width, occupied | {output_column})
                    if columns is not None:
                        candidates.append((index, word, columns))
            physical.pages.require(len(candidates) == 1, "unique exact packed address ciphertext assertion")
            index, word, columns = candidates[0]
            used.add(index)
            word_plans.append(dict(ordinal=ordinal, output=output, stream=stream_value,
                                   word=word, columns=list(columns), assertion_row=index))
        first, second, third = [plan["columns"] for plan in word_plans]
        # point_bits is canonical-y[0..254], then canonical-x parity. Its two
        # 256-bit points are split at 248 and 496 by address_words.
        y0 = first + second[:7]
        y1 = second[8:] + third[:15]
        physical.pages.require(len(y0) == len(y1) == 255 and len(set(y0 + y1)) == 510,
                               "distinct canonical address y-bit operands")
        selectors = [second[7], y0[0], third[15], y1[0]]
        coordinate_plans = []
        for suffix, coordinate, low in zip(["GeneratorX", "GeneratorY", "TransmissionX", "TransmissionY"],
                                           target["coordinates"], selectors):
            plan, part = physical._permutation(dict(swapped=((low, 1),), output=coordinate), table)
            if suffix == "GeneratorY":
                physical.pages.require(plan["columns"] == y0, "generator y exact packed bit order")
            if suffix == "TransmissionY":
                physical.pages.require(plan["columns"] == y1, "transmission y exact packed bit order")
            used.update(part)
            role = owner + suffix
            decompositions.append(dict(role=role, plan=plan))
            coordinate_plans.append(role)
        addresses.append(dict(owner=owner, coordinates=target["coordinates"], words=word_plans,
                              coordinate_roles=coordinate_plans))
    physical.pages.require(len(decompositions) == 8 and len(addresses) == 2,
                           "closed encrypted-address coordinate roster")
    rows = [dict(row=i, a=[[c, f"{v:064x}"] for c, v in raw[i][0]],
                 b=[[c, f"{v:064x}"] for c, v in raw[i][1]]) for i in sorted(used)]
    physical.pages.require(len(rows) <= 8192, "bounded retained address rows")
    return dict(schema=SCHEMA, identity=identity, metadata_sha256=checked["metadata_sha256"],
                selected_rows=rows, plan=dict(constant_link=links[0], addresses=addresses,
                                              decompositions=decompositions),
                candidate_rows=len(raw), candidate_terms=term_count,
                scope="Six packed address cipher assertions and eight canonical point-coordinate decompositions; kernel/native/caller/full Transfer remain separate")
