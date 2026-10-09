"""Actual captured two-note amount/position range blocks, bounded one at a time."""
import hashlib
from . import transfer_note_spend as notes,transfer_arithmetic as arithmetic,transfer_relation as relation
from .transfer_balance_rows import canonical,combine
from .generate_hash_round import linear,_signature_audits


def boundary(data,accepted_roles,slot,kind):
    if type(slot) is not int or slot not in (0,1) or kind not in ('amount','position'):
        raise relation.RelationError('note range role must be slot0/1 amount/position')
    checked=notes.inspect_metadata(data,accepted_roles);spend=checked['spends'][slot]
    bits=spend[kind+'_bits'];value=spend['note'][1] if kind=='amount' else spend['position']
    if len(value)!=1 or value[0][1]!=1 or any(len(bit)!=1 or bit[0][1]!=1 for bit in bits):
        raise relation.RelationError('note range requires actual unit witness LCs')
    columns=[bit[0][0] for bit in bits];width=128 if kind=='amount' else 48
    if columns!=list(range(columns[0],columns[0]+width)):
        raise relation.RelationError('note range captured bit witnesses are not contiguous')
    weighted=canonical((column,2**index) for index,column in enumerate(columns))
    return dict(checked=checked,columns=columns,value=value[0][0],width=width,weighted=weighted,slot=slot,kind=kind)


def extract(data,stream,accepted_roles,slot,kind):
    selected=boundary(data,accepted_roles,slot,kind);obj=selected['checked']['metadata'];copy=obj['constant_copy']
    required={(canonical([(0,1),(copy,-1)]),()):['constant-copy']}
    for index,column in enumerate(selected['columns']):required[(((column,1),),((column,1),))]=['bit.'+str(index)]
    required[(combine(selected['weighted'],((selected['value'],1),),-1),())]=['reconstruction']
    result=arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],
                                        required,[],[],label='note-'+str(slot)+'-'+kind)
    result.update(metadata_sha256=hashlib.sha256(data).hexdigest(),slot=slot,kind=kind,
                  scope='one actual note range block only; hash/tree/native byte codec joins open')
    return result


def generate(data,extracted,accepted_roles,slot,kind):
    selected=boundary(data,accepted_roles,slot,kind)
    obj=selected['checked']['metadata']
    handles={tuple(h) for h in obj['spends'][slot][kind+'_bits']}
    return _generate_boundary(data,extracted,accepted_roles,selected,slot,kind,handles,
                              f'RuntimeTransferNote{slot}{kind.title()}Range')


def _generate_boundary(data,extracted,accepted_roles,selected,slot,kind,owned_handles,ns):
    """Shared emitter after a component's exact source/range ingress checks."""
    obj=selected['checked']['metadata'];copy=obj['constant_copy']
    raw,normalized=arithmetic.normalize_selection(extracted,obj,hashlib.sha256(data).hexdigest())
    if extracted.get('slot')!=slot or extracted.get('kind')!=kind:
        raise relation.RelationError('note range extraction role mismatch')
    columns=selected['columns'];value=selected['value'];width=selected['width'];weighted=selected['weighted']
    if any((((c,1),),((c,1),)) not in normalized.values() for c in columns):
        raise relation.RelationError('note range bit row selection missing')
    delta=combine(weighted,((value,1),),-1)
    reverse=(delta,()) not in normalized.values()
    reconstruction=next((i for i,row in normalized.items() if row==((canonical((c,-v) for c,v in delta) if reverse else delta),())),None)
    if reconstruction is None or len(raw)!=width+2:
        raise relation.RelationError('note range exact reconstruction/row coverage mismatch')
    bits_set=set(columns);kept={0,1,2,copy}
    other_lcs=[lc for handle,lc in selected['checked']['observed'].items() if handle not in owned_handles]
    other_lcs.extend(accepted_roles['observed'].values())
    for lc in other_lcs:
        if any(c in bits_set for c,_ in lc):
            raise relation.RelationError('note range owned bits occur in another source role')
        kept.update(c for c,_ in lc)
    if value in bits_set:raise relation.RelationError('note range value aliases owned bits')
    start=columns[0]
    source=f'''import ShielddSecurity.Compiler
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{ns}
-- Exact full relation: {obj['relation_digest']}; metadata SHA256: {hashlib.sha256(data).hexdigest()}
-- Actual range role only; shared hash/tree construction is separate.
def modulus : Nat := {relation.MODULUS}
def originalRows : List Nat := {list(raw)}
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩' for a,b in raw.values())+']\n'
    source+=f'''def rows : List Row := Compiler.unoutlineRows {copy} rawRows
def bits : List Nat := {columns}
def kept : List Nat := {sorted(kept)}
def expectedRows : List Row := (List.range' {start} {width}).map booleanRow ++
  [reconstructionRow {value} (List.range' {start} {width}),
   ⟨scaleLinear (-1) (reconstructionRow {value} (List.range' {start} {width})).a,[]⟩,⟨[],[]⟩]
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) (n : Nat) : Nat → F :=
  writeBits rho {start} (encodeBits {width} n)

theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide

theorem actual_range {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    ∃ n : Nat, n < 2^{width} ∧ (n : F) = rho {value} := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have certificates : bits.all (fun column => Compiler.checkRow modulus rows (booleanRow column)) = true := by decide
  have booleans : ∀ x ∈ bits.map rho, Square x x := by
    intro x present
    obtain ⟨column,member,rfl⟩ := List.mem_map.mp present
    have checked := Compiler.checked_row_sound rho rows (booleanRow column) normalized
      ((List.all_eq_true.mp certificates) column member)
    simpa only [booleanRow,eval,Int.cast_one,one_mul,add_zero] using checked
  have reconstruction := Compiler.checked_assertion_sound rho rows
    ({'[(%s,1)]'%value if reverse else linear(weighted)})
    ({linear(weighted) if reverse else '[(%s,1)]'%value}) normalized (by decide)
  have reconstructed : fieldBinary (bits.map rho) = rho {value} := by
    have weightedValue : eval rho {linear(weighted)} = fieldBinary (bits.map rho) := by
      have same : {linear(weighted)} = weighted bits 1 := by decide
      rw [same,weighted_eval]
      simp only [Int.cast_one,one_mul]
    {'have reconstruction := reconstruction.symm' if reverse else ''}
    have singleton : eval rho [({value},1)] = rho {value} := by
      simp only [eval,Int.cast_one,one_mul,add_zero]
    rw [weightedValue,singleton] at reconstruction
    exact reconstruction
  have result := range_sound (bits.map rho) (rho {value}) booleans reconstructed
  have bitCount : bits.length = {width} := by decide
  simpa only [List.length_map,bitCount] using result

theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈ expectedRows,
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  have certificate : rawRows.all (fun actual => expectedRows.any (fun expected => decide
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
     Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp certificate) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩

theorem preserved {{F : Type}} [Field F] (rho : Nat → F) (n column : Nat)
    (member : column ∈ kept) : completeAssignment rho n column = rho column := by
  have outside : column < {start} ∨ {start}+{width} ≤ column := by
    have certificate : kept.all (fun c => decide (c < {start} ∨ {start}+{width} ≤ c)) = true := by decide
    exact of_decide_eq_true ((List.all_eq_true.mp certificate) column member)
  exact writeBits_preserves rho {start} (encodeBits {width} n) column
    (by simpa only [encodeBits_length] using outside)

theorem complete_actual_range {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (n : Nat) (bound : n < 2^{width}) (meaning : rho {value} = (n : F))
    (linked : rho {copy} = rho 0) :
    Satisfies (completeAssignment rho n) rawRows ∧
      (∀ column ∈ kept, completeAssignment rho n column = rho column) := by
  have rangeRows := writeBits_range_complete rho {value} {start} {width} n bound meaning (by decide)
  have completed : Satisfies (completeAssignment rho n) expectedRows := by
    intro row member
    have grouped : row ∈ ((List.range' {start} {width}).map booleanRow ++
      [reconstructionRow {value} (List.range' {start} {width})]) ++
      [⟨scaleLinear (-1) (reconstructionRow {value} (List.range' {start} {width})).a,[]⟩,⟨[],[]⟩] := by
      simpa only [expectedRows,List.append_assoc] using member
    rcases List.mem_append.mp grouped with present | present
    · exact rangeRows row present
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with rfl | rfl
      · have valid : Square (eval (completeAssignment rho n)
          (reconstructionRow {value} (List.range' {start} {width})).a) 0 :=
          rangeRows _ (List.mem_append_right _ (by simp only [List.mem_singleton]))
        have zero := square_zero _ valid
        change Square (eval (completeAssignment rho n)
          (scaleLinear (-1) (reconstructionRow {value} (List.range' {start} {width})).a))
          (eval (completeAssignment rho n) [])
        rw [eval_scale,zero]
        simp only [Square,eval,mul_zero,zero_mul]
      · simp [Square,eval]
  have copyLink : completeAssignment rho n {copy} = completeAssignment rho n 0 := by
    rw [preserved rho n {copy} (by decide),preserved rho n 0 (by decide),linked]
  constructor
  · intro actual member
    obtain ⟨expected,present,left,right⟩ := coverage actual member
    have result : Square (eval (completeAssignment rho n) expected.a)
      (eval (completeAssignment rho n) expected.b) := completed expected present
    rw [← Compiler.canonical_equal (completeAssignment rho n) _ _ left,
      ← Compiler.canonical_equal (completeAssignment rho n) _ _ right] at result
    simpa only [Compiler.eval_unoutline (completeAssignment rho n) {copy} _ copyLink] using result
  · intro column member
    exact preserved rho n column member

#print axioms constantLink
#print axioms actual_range
#print axioms coverage
#print axioms preserved
#print axioms complete_actual_range
end ShielddSecurity.{ns}
'''
    return _signature_audits(source)
