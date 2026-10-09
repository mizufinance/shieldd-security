"""Bounded row transport into the already proved owned126-window RNK loop.

The genuine ownership/RNK and DH captures remain independently typed. Every
reused Lean block is checked against actual selected rows under one complete
LC substitution. No endpoint equality or honest witness is a soundness premise.
Rendering is source only; ordinary qualification and kernel receipts are needed.
"""
import re
from . import transfer_encryption_dh_substitution as matcher
from . import transfer_linear_substitution as substitution, transfer_relation as relation
from .transfer_balance_rows import canonical
from .generate_hash_round import linear, _signature_audits


def _terms(text):
    if not text.startswith('[') or not text.endswith(']'):
        raise relation.RelationError('DH transport literal template LC required')
    pattern = r'\((\d+),\s*\((-?\d+)\s*:\s*Int\)\)'
    body = text[1:-1]
    matches = list(re.finditer(pattern, body))
    if re.sub(pattern, '', body).strip(', \n\r\t') or len(matches) > 4096:
        raise relation.RelationError('DH transport bounded literal template LC')
    terms = tuple((int(item[1]), int(item[2])) for item in matches)
    if any(column >= 2**32 or abs(value) >= relation.MODULUS for column, value in terms):
        raise relation.RelationError('DH transport template LC range')
    return terms


def template_blocks(text, start):
    """Parse only finite literal arithmetic/Boolean blocks; kernel checks them.

    The parser selects physical target rows. Generated theorems refer to the
    actual imported definitions, so the parsed text cannot replace kernel truth.
    """
    if type(start) is not int or start not in range(0, 126, 16) or not isinstance(text, str) or len(text) > 2 * 1024 * 1024:
        raise relation.RelationError('DH transport bounded template source')
    name = f'RuntimeRnkTrace{start:03d}'
    if not re.search(r'^namespace ShielddSecurity\.' + name + r'\s*$', text, re.M):
        raise relation.RelationError('DH transport exact reused template namespace')
    found = re.findall(r'^def blocks : List \(List Row\) := \[([^\]\n]+)\]\s*$', text, re.M)
    if len(found) != 1 or not re.search(r'^def rawRows : List Row := blocks\.flatten\s*$', text, re.M):
        raise relation.RelationError('DH transport exact finite block composition')
    names = [item.strip() for item in found[0].split(',')]
    count = min(16, 126 - start)
    if names[:-1] != [f'rows{index}' for index in range(count)] or names[-1] not in ('bitRows', f'rows{count}'):
        raise relation.RelationError('DH transport exact window and Boolean block coverage')
    result = []
    row_pattern = r'\u27e8(\[.*?\])\s*,\s*(\[.*?\])\u27e9'
    for block in names:
        declaration = re.findall(r'^def ' + block + r' : List Row := (.*?)(?=\n(?:def |theorem |private |noncomputable |set_option ))', text, re.M | re.S)
        if len(declaration) != 1:
            raise relation.RelationError('DH transport unique literal block definition')
        body = declaration[0].strip()
        rows = list(re.finditer(row_pattern, body, re.S))
        if not body.startswith('[') or not body.endswith(']') or not 0 < len(rows) <= 128 or re.sub(row_pattern, '', body, flags=re.S).strip('[], \n\r\t'):
            raise relation.RelationError('DH transport bounded literal row block')
        result.append((block, [(_terms(row[1]), _terms(row[2])) for row in rows]))
    return result


def _balanced(entries, leaf):
    if not entries:
        return 'MapTree.empty'
    if len(entries) == 1:
        column, value = entries[0]
        return f'(MapTree.leaf {column} {leaf(value)})'
    middle = len(entries) // 2
    return f'(MapTree.branch {entries[middle][0]} {_balanced(entries[:middle], leaf)} {_balanced(entries[middle:], leaf)})'


def map_source(role, entries):
    if type(role) is not int or not 0 <= role < 5 or not isinstance(entries, list) or not 0 < len(entries) <= 65536:
        raise relation.RelationError('DH transport finite map role/support')
    if entries != sorted(entries) or len(entries) != len(dict(entries)) or dict(entries).get(0) != ((0, 1),):
        raise relation.RelationError('DH transport exact sorted map/constant binding')
    total = 0
    for column, terms in entries:
        if type(column) is not int or not 0 <= column < 2**32 or terms != canonical(terms) or len(terms) > 4096:
            raise relation.RelationError('DH transport canonical map image')
        total += len(terms)
        if total > 262144:
            raise relation.RelationError('DH transport finite map term budget')
    name = f'RuntimeTransferEncryptionDh{role}Map'
    output = ['import ShielddSecurity.RowLinearSubstitution\n',
              f'namespace ShielddSecurity.{name}\nset_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n']
    output.append('''inductive MapTree where
  | empty
  | leaf (key : Nat) (value : Linear)
  | branch (pivot : Nat) (left right : MapTree)
def lookup : MapTree → Nat → Linear
  | .empty, _ => []
  | .leaf key value, column => if column = key then value else []
  | .branch pivot left right, column =>
      if column < pivot then lookup left column else lookup right column
''')
    pages = []
    for ordinal, start in enumerate(range(0, len(entries), 128)):
        page = entries[start:start + 128]
        part = f'part{ordinal}'
        output.append(f'def {part} : MapTree := {_balanced(page, linear)}\n')
        pages.append((page[0][0], part))
    # Store bounded balanced data pages instead of compiling thousands of
    # distinct conditional functions. One recursive lookup checks every key;
    # balanced page dispatch keeps an empty image outside the exact support.
    def dispatch(items):
        if len(items) == 1:
            return 'lookup ' + items[0][1] + ' column'
        middle = len(items) // 2
        return f'(if column < {items[middle][0]} then {dispatch(items[:middle])} else {dispatch(items[middle:])})'
    output.append('def columns (column : Nat) : Linear := ' + dispatch(pages) + '\n')
    output.append('theorem columns_zero : columns 0 = [(0, 1)] := by decide\n#print axioms columns_zero\n')
    output.append(f'end ShielddSecurity.{name}\n')
    return name, _signature_audits(''.join(output))


def row_source(role, start, ordinal, block, template_rows, columns, actual_rows, *, actual_copy=None):
    if type(role) is not int or not 0 <= role < 5 or start not in range(0, 126, 16) or type(ordinal) is not int or not 0 <= ordinal < 17:
        raise relation.RelationError('DH transport exact row block role')
    if not re.fullmatch(r'rows\d+|bitRows', block) or not 0 < len(template_rows) <= 128 or not 0 < len(actual_rows) <= 8192:
        raise relation.RelationError('DH transport bounded row block')
    index = {}
    for physical, row in sorted(actual_rows.items()):
        normalized = tuple(canonical(terms) if actual_copy is None else matcher.unoutline(terms, actual_copy)
                           for terms in row)
        if type(physical) is not int or not 0 <= physical < 2**32:
            raise relation.RelationError('DH transport physical row index')
        index.setdefault(normalized, physical)
    selected = []
    for row in template_rows:
        renamed = tuple(substitution.linear(terms, columns) for terms in row)
        reverse = (canonical((column, -factor) for column, factor in renamed[0]), renamed[1])
        candidates = [index[value] for value in (renamed, reverse) if value in index]
        if not candidates:
            raise relation.RelationError('DH transport reused kernel block has no exact actual row')
        selected.append(min(candidates))
    if actual_copy is not None:
        if type(actual_copy) is not int or not 3 <= actual_copy < 2**32:
            raise relation.RelationError('DH transport actual copy column')
        link = (canonical([(0, 1), (actual_copy, -1)]), ())
        links = [physical for physical, row in actual_rows.items()
                 if tuple(canonical(side) for side in row) == link]
        if len(links) != 1:
            raise relation.RelationError('DH transport exact physical copy assertion required')
        selected.extend(links)
    selected = sorted(set(selected))
    name = f'RuntimeTransferEncryptionDh{role}Rows{start:03d}Part{ordinal:02d}'
    source = f'RuntimeRnkTrace{start:03d}'
    mapping = f'RuntimeTransferEncryptionDh{role}Map.columns'
    checked_rows = 'rawRows' if actual_copy is None else f'(Compiler.unoutlineRows {actual_copy} rawRows)'
    satisfaction = 'satisfied' if actual_copy is None else 'normalized'
    normalize_proof = '' if actual_copy is None else f'''
  have link : Compiler.checkRow {source}.modulus rawRows ⟨[(0,1),({actual_copy},-1)],[]⟩ = true := by decide
  have normalized := Compiler.unoutline_rows_sound rho {actual_copy} rawRows satisfied link
'''
    output = f'''import ShielddSecurity.RowLinearSubstitutionSoundness
import ShielddSecurity.{source}
import ShielddSecurity.RuntimeTransferEncryptionDh{role}Map
namespace ShielddSecurity.{name}
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
def originalRows : List Nat := {selected}
def rawRows : List Row := [''' + ',\n'.join('⟨' + linear(actual_rows[row][0]) + ',' + linear(actual_rows[row][1]) + '⟩' for row in selected) + f''']
def mappedRows : List Row := {source}.{block}.map (RowLinearSubstitution.row {mapping})
theorem rows_checked : mappedRows.all (fun row =>
    Compiler.checkRow {source}.modulus {checked_rows} row ||
    Compiler.checkRow {source}.modulus {checked_rows} ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide
theorem source_satisfied {{F : Type}} [Field F] [CharP F {source}.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies (fun column => eval rho ({mapping} column)) {source}.{block} := by
{normalize_proof}  exact RowLinearSubstitutionSoundness.checked_rows rho {mapping} {source}.{block} {checked_rows} rows_checked {satisfaction}
#print axioms rows_checked
#print axioms source_satisfied
end ShielddSecurity.{name}
'''
    return name, _signature_audits(output)


def generate_rows(template_chunks, template_rows, target_chunks, target_rows, template_sources):
    """Generate map and134 bounded reused-row checks, without kernel credit.

    Exact source/compiler/import identities and ordinary ordered-row provenance
    must be recorded by the source driver and subsequent kernel guards. Whole
    loop/point/bit/scalar/caller composition is a later generated module.
    """
    checked = matcher.full_substitution(template_chunks, template_rows, target_chunks, target_rows)
    if not isinstance(template_sources, dict) or set(template_sources) != set(range(0, 126, 16)):
        raise relation.RelationError('DH transport exact eight reused source modules')
    role, columns = checked['role'], dict(checked['loop_columns'])
    if checked.get('unoutlined') is not True:
        raise relation.RelationError('DH transport checked copy normalization required')
    modules = [map_source(role, checked['loop_columns'])]
    for ordinal, start in enumerate(range(0, 126, 16)):
        blocks = template_blocks(template_sources[start], start)
        actual_rows = checked['chunks'][ordinal]['actual_rows']
        modules.extend(row_source(role, start, part, block, rows, columns, actual_rows,
                                  actual_copy=checked['actual_copy'])
                       for part, (block, rows) in enumerate(blocks))
    if len(modules) != 135:
        raise relation.RelationError('DH transport exact map/126 windows/eight bit block count')
    return modules, checked


def chunk_source(role, start, blocks):
    """Assemble bounded local checks, retaining one shared substitution."""
    count = min(16, 126 - start)
    if type(role) is not int or not 0 <= role < 5 or start not in range(0, 126, 16) or len(blocks) != count + 1:
        raise relation.RelationError('DH transport exact chunk assembly')
    if blocks[:-1] != [f'rows{index}' for index in range(count)] or blocks[-1] not in ('bitRows', f'rows{count}'):
        raise relation.RelationError('DH transport exact imported chunk definitions')
    source = f'RuntimeRnkTrace{start:03d}'
    mapping = f'RuntimeTransferEncryptionDh{role}Map.columns'
    names = [f'RuntimeTransferEncryptionDh{role}Rows{start:03d}Part{index:02d}' for index in range(len(blocks))]
    name = f'RuntimeTransferEncryptionDh{role}Chunk{start:03d}'
    output = ''.join(f'import ShielddSecurity.{leaf}\n' for leaf in names)
    output += f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
def actualBlocks : List (List Row) := [{', '.join(leaf + '.rawRows' for leaf in names)}]
def rawRows : List Row := actualBlocks.flatten
theorem actual_block_satisfied {{F : Type}} [Field F]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows)
    (block : List Row) (member : block ∈ actualBlocks) : Satisfies rho block := by
  intro item present
  exact satisfied item (List.mem_flatten.mpr ⟨block, member, present⟩)
theorem source_satisfied {{F : Type}} [Field F] [CharP F {source}.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies (fun column => eval rho ({mapping} column)) {source}.rawRows := by
  intro item member
  obtain ⟨block, member, present⟩ := List.mem_flatten.mp member
  simp only [{source}.blocks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with ''' + ' | '.join('rfl' for _ in blocks) + '\n'
    for leaf in names:
        output += f'  · exact {leaf}.source_satisfied rho (actual_block_satisfied rho satisfied {leaf}.rawRows (by simp only [actualBlocks, List.mem_cons, List.not_mem_nil, or_false]; tauto)) item present\n'
    output += f'''#print axioms actual_block_satisfied
#print axioms source_satisfied
end ShielddSecurity.{name}
'''
    return name, _signature_audits(output)


def loop_source(checked, block_names):
    """Derive the actual endpoint; source row and role checks are explicit."""
    if checked.get('qualified') is not True or checked.get('windows') != 126 or set(block_names) != set(range(0, 126, 16)):
        raise relation.RelationError('DH transport complete checked loop assembly')
    role = checked['role']
    if type(role) is not int or not 0 <= role < 5:
        raise relation.RelationError('DH transport complete loop role')
    for start, names in block_names.items():
        count = min(16, 126 - start)
        if len(names) != count + 1 or names[:-1] != [f'rows{index}' for index in range(count)] or names[-1] not in ('bitRows', f'rows{count}'):
            raise relation.RelationError('DH transport complete imported block coverage')
    roles = checked['loop_roles']
    if (len(roles['base']['source']) != 2 or len(roles['base']['actual']) != 2 or
            len(roles['output']['source']) != 2 or len(roles['output']['actual']) != 2 or
            len(roles['bits']['source']) != 252 or len(roles['bits']['actual']) != 252):
        raise relation.RelationError('DH transport complete point/252-bit roles')
    mapping = f'RuntimeTransferEncryptionDh{role}Map'
    loop = 'RuntimeTransferRnkLoop'
    chunks = [f'RuntimeTransferEncryptionDh{role}Chunk{start:03d}' for start in range(0, 126, 16)]
    name = f'RuntimeTransferEncryptionDh{role}Loop'
    output = 'import ShielddSecurity.RuntimeTransferRnkLoop\n'
    output += ''.join(f'import ShielddSecurity.{chunk}\n' for chunk in chunks)
    output += f'''namespace ShielddSecurity.{name}
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
def actualBlocks : List (List Row) := [{', '.join(chunk + '.rawRows' for chunk in chunks)}]
def rawRows : List Row := actualBlocks.flatten
theorem actual_chunk_satisfied {{F : Type}} [Field F]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows)
    (block : List Row) (member : block ∈ actualBlocks) : Satisfies rho block := by
  intro item present
  exact satisfied item (List.mem_flatten.mpr ⟨block, member, present⟩)
'''
    # Scalar bits run low to high, whereas loop chunks consume windows from
    # the high end. Each source block remains its imported exact definition.
    bit_sources = [f'RuntimeRnkTrace{start:03d}.{block_names[start][-1]}' for start in reversed(range(0, 126, 16))]
    output += 'def sourceBitBlocks : List (List Row) := [' + ', '.join(bit_sources) + ']\n'
    output += f'theorem bits_covered : {loop}.bitRows = sourceBitBlocks.flatten := by decide\n'
    output += f'''theorem source_satisfied {{F : Type}} [Field F] [CharP F {loop}.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    Satisfies (fun column => eval rho ({mapping}.columns column)) {loop}.rawRows := by
  intro item member
  rcases List.mem_append.mp member with inChunks | inBits
  · obtain ⟨block, member, present⟩ := List.mem_flatten.mp inChunks
    simp only [{loop}.chunkRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with ''' + ' | '.join('rfl' for _ in chunks) + '\n'
    for chunk in chunks:
        output += f'    · exact {chunk}.source_satisfied rho (actual_chunk_satisfied rho satisfied {chunk}.rawRows (by simp only [actualBlocks, List.mem_cons, List.not_mem_nil, or_false]; tauto)) item present\n'
    output += '''  · rw [bits_covered] at inBits
    obtain ⟨block, member, present⟩ := List.mem_flatten.mp inBits
    simp only [sourceBitBlocks, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with ''' + ' | '.join('rfl' for _ in chunks) + '\n'
    for start in reversed(range(0, 126, 16)):
        chunk = f'RuntimeTransferEncryptionDh{role}Chunk{start:03d}'
        leaf = f'RuntimeTransferEncryptionDh{role}Rows{start:03d}Part{len(block_names[start]) - 1:02d}'
        output += f'''    · exact {leaf}.source_satisfied rho
        ({chunk}.actual_block_satisfied rho
          (actual_chunk_satisfied rho satisfied {chunk}.rawRows (by simp only [actualBlocks, List.mem_cons, List.not_mem_nil, or_false]; tauto))
          {leaf}.rawRows (by simp only [{chunk}.actualBlocks, List.mem_cons, List.not_mem_nil, or_false]; tauto)) item present
'''
    audits = ['actual_chunk_satisfied', 'bits_covered', 'source_satisfied']
    for point in ('base', 'output'):
        for axis in range(2):
            original, actual = roles[point]['source'][axis], roles[point]['actual'][axis]
            theorem = f'{point}_{axis}_checked'
            output += f'''theorem {theorem} :
    Compiler.canonical {loop}.modulus (RowLinearSubstitution.linear {mapping}.columns {linear(original)}) =
      Compiler.canonical {loop}.modulus {linear(actual)} := by decide
'''
            audits.append(theorem)
        output += f'def {point} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F := ⟨eval rho {linear(roles[point]["actual"][0])}, eval rho {linear(roles[point]["actual"][1])}⟩\n'
        original_point = f'{loop}.base' if point == 'base' else 'RuntimeRnkTrace112.window13_output'
        output += f'''theorem {point}_role {{F : Type}} [Field F] [CharP F {loop}.modulus]
    (rho : Nat → F) :
    {original_point} (fun column => eval rho ({mapping}.columns column)) = {point} rho := by
  change Group.Point.mk
    (eval (fun column => eval rho ({mapping}.columns column)) {linear(roles[point]['source'][0])})
    (eval (fun column => eval rho ({mapping}.columns column)) {linear(roles[point]['source'][1])}) = {point} rho
  exact congrArg₂ Group.Point.mk
    (RowLinearSubstitution.checked_linear rho {mapping}.columns {linear(roles[point]['source'][0])} {linear(roles[point]['actual'][0])} {point}_0_checked)
    (RowLinearSubstitution.checked_linear rho {mapping}.columns {linear(roles[point]['source'][1])} {linear(roles[point]['actual'][1])} {point}_1_checked)
'''
        audits.append(f'{point}_role')
    output += 'def bits : List Linear := [' + ', '.join(linear(bit) for bit in roles['bits']['actual']) + ']\n'
    output += f'''theorem bits_checked : {loop}.bits.map (RowLinearSubstitution.linear {mapping}.columns) = bits := by decide
theorem bits_role {{F : Type}} [Field F] (rho : Nat → F) :
    ScalarBits.decodeBits (fun column => eval rho ({mapping}.columns column)) {loop}.bits =
      ScalarBits.decodeBits rho bits := by
  rw [RowLinearSubstitutionSoundness.decode_bits, bits_checked]
theorem actual_multiplication {{F J : Type}} [Field F] [CharP F {loop}.modulus] [AddCommGroup J]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (codec : TransferReduction.CanonicalField F)
    (model : Group.StandardCurveModel J ({loop}.coefficientD : F)) (inputBase : J)
    (baseRole : base rho = model.coordinates inputBase)
    (satisfied : Satisfies rho rawRows) :
    output rho = model.coordinates (ShielddSecurity.binary (ScalarBits.decodeBits rho bits) • inputBase) := by
  have oneSource := RowLinearSubstitution.constant_preserved rho {mapping}.columns {mapping}.columns_zero one
  have baseSource := (base_role rho).trans baseRole
  have result := {loop}.actual_multiplication
    (fun column => eval rho ({mapping}.columns column)) oneSource four codec model inputBase baseSource
    (source_satisfied rho satisfied)
  rw [output_role rho, bits_role rho] at result
  exact result
'''
    audits.extend(['bits_checked', 'bits_role', 'actual_multiplication'])
    output += ''.join('#print axioms ' + theorem + '\n' for theorem in audits)
    output += f'end ShielddSecurity.{name}\n'
    return name, _signature_audits(output)


def generate(template_chunks, template_rows, target_chunks, target_rows, template_sources):
    modules, checked = generate_rows(template_chunks, template_rows, target_chunks, target_rows, template_sources)
    blocks = {start: [name for name, _ in template_blocks(template_sources[start], start)] for start in range(0, 126, 16)}
    modules.extend(chunk_source(checked['role'], start, blocks[start]) for start in range(0, 126, 16))
    modules.append(loop_source(checked, blocks))
    if len(modules) != 144:
        raise relation.RelationError('DH transport exact complete module count')
    return modules, checked
