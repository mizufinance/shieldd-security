"""Split accepted receiver range checks into eight-bit proof pages."""
import ast
import re
from . import transfer_relation as relation
from .generate_hash_round import linear, _signature_audits


def _lc(text):
    values = ast.literal_eval(re.sub(r'\((-?\d+) : Int\)', r'\1', text))
    if not isinstance(values, list) or any(not isinstance(t, tuple) or len(t) != 2 or
            any(type(x) is not int for x in t) for t in values):
        raise relation.RelationError('closed captured integer linear expression required')
    if text != linear(values):
        raise relation.RelationError('exact captured linear spelling required')
    return values


def generate(source):
    namespace = 'RuntimeTransferReceiverLifecycleRange'
    if f'namespace ShielddSecurity.{namespace}\n' not in source:
        raise relation.RelationError('accepted physical receiver range required')
    def literal(name):
        match = re.search(r'^def ' + name + r' : List Nat := (\[[0-9, ]+\])$', source, re.M)
        if match is None: raise relation.RelationError('exact captured list ' + name)
        return ast.literal_eval(match.group(1))
    bits, original, kept = literal('bits'), literal('originalRows'), literal('kept')
    if bits != list(range(1849, 1980)) or len(original) != 133:
        raise relation.RelationError('exact disjoint 131-bit receiver layout required')
    match = re.search(r'^def rawRows : List Row := \[\n(.*?)\]\ndef rows', source, re.M | re.S)
    if match is None: raise relation.RelationError('closed actual receiver raw rows required')
    raw = []
    for line in match.group(1).splitlines():
        row = re.fullmatch(r'⟨(\[.*\]),(\[.*\])⟩,?', line)
        if row is None: raise relation.RelationError('exact physical receiver row spelling')
        raw.append((_lc(row[1]), _lc(row[2])))
    if len(raw) != 133: raise relation.RelationError('exact physical row coverage')
    boolean = {}; boundary = []
    weighted = [(1767, -1), *((c, 2**i) for i, c in enumerate(bits))]
    for index, (a, b) in zip(original, raw):
        if b and len(a) == len(b) == 1 and b[0][0] in bits and b[0][1] == 1 and a[0] in ((b[0][0], 1), (b[0][0], -1)):
            if b[0][0] in boolean: raise relation.RelationError('unique physical Boolean row required')
            boolean[b[0][0]] = (index, (a, b))
        elif not b and (a == weighted or a == [(c, -v) for c, v in weighted] or a == [(0, 1), (200692, -1)]):
            boundary.append((index, (a, b)))
        else: raise relation.RelationError('unexpected receiver physical row')
    if set(boolean) != set(bits) or len(boundary) != 2 or len(set(original)) != 133:
        raise relation.RelationError('complete exact receiver row partition required')
    if set(kept) & set(bits): raise relation.RelationError('receiver write/read-only disjointness required')
    pages = [bits[i:i+8] for i in range(0, 131, 8)]
    data = namespace + 'Data'
    row_text = lambda rows: '[\n' + ',\n'.join('⟨' + linear(a) + ',' + linear(b) + '⟩' for a, b in rows) + ']'
    text = f'''import ShielddSecurity.Compiler
namespace ShielddSecurity.{data}
set_option maxHeartbeats 200000
def modulus : Nat := {relation.MODULUS}
def bits : List Nat := {bits}
'''
    ordered = []
    for i, columns in enumerate(pages):
        entries = [boolean[c] for c in columns]; ordered.extend(index for index, _ in entries)
        text += f'def bits{i:02} : List Nat := {columns}\n'
        text += f'def rawRows{i:02} : List Row := {row_text([row for _, row in entries])}\n'
    ordered.extend(index for index, _ in boundary)
    text += f'def boundaryRows : List Row := {row_text([row for _, row in boundary])}\n'
    text += f'def originalRows : List Nat := {ordered}\n'
    text += f'def bitBlocks : List (List Nat) := [{",".join(f"bits{i:02}" for i in range(17))}]\n'
    text += f'def blocks : List (List Row) := [{",".join(f"rawRows{i:02}" for i in range(17))},boundaryRows]\n'
    text += '''def rawRows : List Row := blocks.flatten
theorem layout : bits = bitBlocks.flatten := by decide
theorem range_layout : bits = List.range' 1849 131 := by decide
#print axioms layout
#print axioms range_layout
'''
    text += f'end ShielddSecurity.{data}\n'
    outputs = [(data, _signature_audits(text), 2)]
    for i in range(17):
        name = f'{namespace}Page{i:02}'
        part, columns = f'{data}.rawRows{i:02}', f'{data}.bits{i:02}'
        text = f'''import ShielddSecurity.{data}
import ShielddSecurity.RowOrientationSoundness
namespace ShielddSecurity.{name}
set_option maxHeartbeats 200000
theorem booleans {{F : Type}} [Field F] [CharP F {data}.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho {data}.rawRows) :
    Satisfies rho ({columns}.map booleanRow) := by
  have actual : Satisfies rho {part} := by
    intro row member
    exact satisfied row (List.mem_flatten.mpr ⟨{part},by simp [{data}.blocks],member⟩)
  exact RowOrientationSoundness.checked_rows rho {part} ({columns}.map booleanRow) (by decide) actual
theorem coverage : ∀ actual ∈ {part},∃ expected ∈ {columns}.map booleanRow,
    Compiler.canonical {data}.modulus (Compiler.unoutline 200692 actual.a) = Compiler.canonical {data}.modulus expected.a ∧
    Compiler.canonical {data}.modulus (Compiler.unoutline 200692 actual.b) = Compiler.canonical {data}.modulus expected.b := by
  have certificate : {part}.all (fun actual => ({columns}.map booleanRow).any (fun expected => decide
    (Compiler.canonical {data}.modulus (Compiler.unoutline 200692 actual.a) = Compiler.canonical {data}.modulus expected.a ∧
     Compiler.canonical {data}.modulus (Compiler.unoutline 200692 actual.b) = Compiler.canonical {data}.modulus expected.b))) = true := by decide
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp certificate) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩
#print axioms booleans
#print axioms coverage
end ShielddSecurity.{name}
'''
        outputs.append((name, _signature_audits(text), 2))
    boundary_name = namespace + 'Boundary'
    text = f'''import ShielddSecurity.{data}
namespace ShielddSecurity.{boundary_name}
set_option maxHeartbeats 300000
def expectedRows : List Row := [reconstructionRow 1767 {data}.bits,
  ⟨scaleLinear (-1) (reconstructionRow 1767 {data}.bits).a,[]⟩,⟨[],[]⟩]
theorem constantLink : Compiler.checkRow {data}.modulus {data}.boundaryRows ⟨[(0,1),(200692,-1)],[]⟩ = true := by decide
theorem reconstruction {{F : Type}} [Field F] [CharP F {data}.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho {data}.rawRows) :
    Square (eval rho (reconstructionRow 1767 {data}.bits).a) (eval rho (reconstructionRow 1767 {data}.bits).b) := by
  have actual : Satisfies rho {data}.boundaryRows := by
    intro row member
    exact satisfied row (List.mem_flatten.mpr ⟨{data}.boundaryRows,by simp [{data}.blocks],member⟩)
  have normalized := Compiler.unoutline_rows_sound rho 200692 {data}.boundaryRows actual constantLink
  exact Compiler.checked_row_sound rho (Compiler.unoutlineRows 200692 {data}.boundaryRows)
    (reconstructionRow 1767 {data}.bits) normalized (by decide)
theorem coverage : ∀ actual ∈ {data}.boundaryRows,∃ expected ∈ expectedRows,
    Compiler.canonical {data}.modulus (Compiler.unoutline 200692 actual.a) = Compiler.canonical {data}.modulus expected.a ∧
    Compiler.canonical {data}.modulus (Compiler.unoutline 200692 actual.b) = Compiler.canonical {data}.modulus expected.b := by
  have certificate : {data}.boundaryRows.all (fun actual => expectedRows.any (fun expected => decide
    (Compiler.canonical {data}.modulus (Compiler.unoutline 200692 actual.a) = Compiler.canonical {data}.modulus expected.a ∧
     Compiler.canonical {data}.modulus (Compiler.unoutline 200692 actual.b) = Compiler.canonical {data}.modulus expected.b))) = true := by decide
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp certificate) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩
#print axioms constantLink
#print axioms reconstruction
#print axioms coverage
end ShielddSecurity.{boundary_name}
'''
    outputs.append((boundary_name, _signature_audits(text), 3))
    outputs.append((namespace, _signature_audits(_main(source, data, boundary_name, kept)), 6))
    return outputs


def _main(source, data, boundary, kept):
    namespace = 'RuntimeTransferReceiverLifecycleRange'
    imports = [data, boundary, 'ScalarBooleanCanonical', *(f'{namespace}Page{i:02}' for i in range(17))]
    text = ''.join(f'import ShielddSecurity.{name}\n' for name in imports)
    text += f'''namespace ShielddSecurity.{namespace}
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
def modulus : Nat := {relation.MODULUS}
def originalRows : List Nat := {data}.originalRows
def rawRows : List Row := {data}.rawRows
def rows : List Row := Compiler.unoutlineRows 200692 rawRows
def bits : List Nat := {list(range(1849,1980))}
def kept : List Nat := {kept}
def expectedRows : List Row := (List.range' 1849 131).map booleanRow ++
  [reconstructionRow 1767 (List.range' 1849 131),
   ⟨scaleLinear (-1) (reconstructionRow 1767 (List.range' 1849 131)).a,[]⟩,⟨[],[]⟩]
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) (n : Nat) : Nat → F :=
  writeBits rho 1849 (encodeBits 131 n)
theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),(200692,-1)],[]⟩ = true := by decide

theorem word {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    ∃ n : Nat,n < 2^131 ∧ (n : F) = rho 1767 ∧
      bits.map rho = (encodeBits 131 n).map (fun bit => if bit then (1 : F) else 0) := by
  have booleans : Satisfies rho (bits.map booleanRow) := by
    intro row member
    obtain ⟨column,present,rfl⟩ := List.mem_map.mp member
    change column ∈ {data}.bits at present
    rw [{data}.layout] at present
    obtain ⟨part,inside,present⟩ := List.mem_flatten.mp present
    simp only [{data}.bitBlocks,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with {' | '.join('rfl' for _ in range(17))}
'''
    for i in range(17):
        text += f'    · exact {namespace}Page{i:02}.booleans rho satisfied _ (List.mem_map.mpr ⟨column,present,rfl⟩)\n'
    text += f'''  have result := ScalarBooleanCanonical.columns_word rho bits 1767 booleans ({boundary}.reconstruction rho satisfied)
  have width : bits.length = 131 := by decide
  simpa only [width] using result

theorem actual_range {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    ∃ n : Nat,n < 2^131 ∧ (n : F) = rho 1767 := by
  obtain ⟨n,bound,meaning,_⟩ := word rho satisfied
  exact ⟨n,bound,meaning⟩

private theorem boolean_expected (part : List Nat) (inside : part ∈ {data}.bitBlocks)
    (expected : Row) (member : expected ∈ part.map booleanRow) : expected ∈ expectedRows := by
  obtain ⟨column,present,rfl⟩ := List.mem_map.mp member
  have full : column ∈ {data}.bits := by
    rw [{data}.layout]
    exact List.mem_flatten.mpr ⟨part,inside,present⟩
  rw [{data}.range_layout] at full
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨column,full,rfl⟩

theorem coverage : ∀ actual ∈ rawRows,∃ expected ∈ expectedRows,
    Compiler.canonical modulus (Compiler.unoutline 200692 actual.a) = Compiler.canonical modulus expected.a ∧
    Compiler.canonical modulus (Compiler.unoutline 200692 actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨part,inside,present⟩ := List.mem_flatten.mp member
  simp only [{data}.blocks,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with {' | '.join('rfl' for _ in range(18))}
'''
    for i in range(17):
        text += f'''  · obtain ⟨expected,member,left,right⟩ := {namespace}Page{i:02}.coverage actual present
    exact ⟨expected,boolean_expected {data}.bits{i:02} (by simp [{data}.bitBlocks]) expected member,left,right⟩
'''
    text += f'''  · obtain ⟨expected,member,left,right⟩ := {boundary}.coverage actual present
    have tail : expected ∈ [reconstructionRow 1767 (List.range' 1849 131),
        ⟨scaleLinear (-1) (reconstructionRow 1767 (List.range' 1849 131)).a,[]⟩,⟨[],[]⟩] := by
      simpa only [{boundary}.expectedRows,{data}.range_layout] using member
    exact ⟨expected,List.mem_append_right _ tail,left,right⟩
'''
    start = source.index('theorem preserved ')
    end = source.index('theorem complete_actual_range ', start)
    # Keep the accepted symbolic writeBits construction, with its audited
    # preservation/normalization proof; only the expensive coverage is replaced.
    text += source[start:end]
    start = source.index('theorem complete_actual_range ')
    end = source.index('set_option pp.all true in', start)
    text += source[start:end]
    text += '\n'.join(f'#print axioms {name}' for name in ('constantLink','word','actual_range','coverage','preserved','complete_actual_range')) + '\n'
    text += f'end ShielddSecurity.{namespace}\n'
    return text
