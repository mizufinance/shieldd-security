"""Actual contiguous canonical255 construction inside the map numeric program."""
from . import transfer_asset_map_completion as completion
from . import transfer_asset_map_comparator_completion as canonical
from . import transfer_relation as relation


def plan(data,extracted,accepted_roles):
    recipe=completion.plan(data,extracted,accepted_roles);bits=canonical.plan(data,extracted,accepted_roles)
    positions=[]
    keys=('kind','left','right','remainder','output','auxiliary')
    for target in bits['steps']:
        matches=[i for i,step in enumerate(recipe['steps']) if step['rows']==target['rows']]
        if len(matches)!=1:raise relation.RelationError('canonical sequence exact physical product match')
        position=matches[0]
        if any(recipe['steps'][position].get(key)!=target.get(key) for key in keys):
            raise relation.RelationError('canonical sequence actual product orientation/pivot/remainder mismatch')
        positions.append(position)
    if positions!=list(range(positions[0],positions[0]+len(positions))):
        raise relation.RelationError('canonical sequence must be one exact contiguous block')
    before=recipe['steps'][:positions[0]];after=recipe['steps'][positions[-1]+1:]
    if not 1<=len(before)<=16 or not 1<=len(after)<=64:
        raise relation.RelationError('canonical sequence bounded surrounding phases')
    protected={bits['value'],*bits['bits']}
    reads=lambda step:{c for lc in ([step['input']] if step['kind']=='square' else [step['left'],step['right']])+[step['remainder']] for c,_ in lc}
    if any(reads(step)&protected or set(step['writes'])&protected for step in before):
        raise relation.RelationError('canonical sequence before phase reads/writes native root bits')
    if any(set(step['writes'])&set(bits['owned_writes']) for step in before+after):
        raise relation.RelationError('canonical sequence surrounding phases overwrite canonical ownership')
    copy=recipe['checked']['metadata']['constant_copy']
    support={c for row in bits['raw'].values() for lc in row for c,_ in lc if c!=copy}
    floor=max(support)+1;writes={c for step in after for c in step['writes']}
    exceptions=sorted(c for c in writes if c<floor)
    if len(exceptions)>8 or writes&({copy}|support):
        raise relation.RelationError('canonical sequence suffix exact row support/fence')
    return dict(recipe=recipe,canonical=bits,before=before,after=after,floor=floor,exceptions=exceptions,
                original_indices=sorted(set(recipe['material_rows'])|set(bits['raw'])))


def construct(data,extracted,accepted_roles,base,native_value):
    result=plan(data,extracted,accepted_roles);rho=dict(base);p=completion.maps.P
    def evaluate(lc):return sum(rho.get(c,0)*n for c,n in lc)%p
    def run(steps):
        for step in steps:
            if step['kind']=='square':value=evaluate(step['input'])**2-evaluate(step['remainder'])
            else:
                left,right=evaluate(step['left']),evaluate(step['right'])
                value=left*right-evaluate(step['remainder'])
                rho[step['auxiliary']]=(left-right)**2%p
            rho[step['output']]=value%p
    run(result['before'])
    rho=canonical.construct(data,extracted,accepted_roles,rho,native_value)['assignment']
    run(result['after'])
    rows={i:result['recipe']['raw'][i] for i in result['original_indices']}
    if any(evaluate(a)**2%p!=evaluate(b) for a,b in rows.values()):
        raise relation.RelationError('canonical sequence original numeric/canonical row failed')
    owned=set(result['canonical']['owned_writes'])|{c for s in result['before']+result['after'] for c in s['writes']}
    if any(rho.get(c,0)!=v for c,v in base.items() if c not in owned):
        raise relation.RelationError('canonical sequence changed column outside ownership')
    return dict(assignment=rho,plan=result,owned=sorted(owned),proof=False,
                scope='actual numeric/canonical858rows only; remaining12 native assertions/full map/Transfer open')


def generate(data,extracted,accepted_roles):
    from .generate_hash_round import linear,_signature_audits
    result=plan(data,extracted,accepted_roles);recipe=result['recipe'];bits=result['canonical']
    copy=recipe['checked']['metadata']['constant_copy'];root=bits['value'];start=bits['bits'][0]
    name='RuntimeTransferAssetMapCanonicalSequence';numeric='RuntimeTransferAssetMapNumericConstruction'
    canonical_name='RuntimeTransferAssetMapCanonicalConstruction';native_bits='RuntimeTransferAssetMapNativeBits'
    def step_source(step):
        if step['kind']=='square':return '.square '+linear(step['input'])+' '+linear(step['remainder'])+' '+str(step['output'])
        return '.product '+linear(step['left'])+' '+linear(step['right'])+' '+linear(step['remainder'])+' '+str(step['output'])+' '+str(step['auxiliary'])
    source=f'''import ShielddSecurity.{numeric}
import ShielddSecurity.{canonical_name}
import ShielddSecurity.{native_bits}
import ShielddSecurity.CompilerPatchCommutation
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Exact actual metadata SHA256 {recipe['checked']['metadata_sha256']}.
-- Numeric600 + canonical766 rows overlap508 products:858 distinct original
-- rows. Remaining12 native map assertions/full Transfer are separate joins.
abbrev modulus := {numeric}.modulus
def before : List CompilerCompletion.Step := [
'''+',\n'.join(map(step_source,result['before']))+''']
def after : List CompilerCompletion.Step := [
'''+',\n'.join(map(step_source,result['after']))+f''']
def rootBitsWrites : List Nat := [{root}] ++ List.range' {start} 255
def rawRows : List Row := {numeric}.rawRows ++ {canonical_name}.rawRows
def distinctOriginalRowIndices : List Nat := {result['original_indices']}

theorem program_split : {numeric}.steps = before ++ {canonical_name}.stages ++ after := by rfl
theorem separation_checked : before.all (fun step =>
    (CompilerPatchCommutation.reads step).all (fun term => decide (term.1 ∉ rootBitsWrites)) &&
    step.writes.all (fun column => decide (column ∉ rootBitsWrites))) = true := by decide
theorem separated : ∀ step ∈ before, CompilerPatchCommutation.Separated rootBitsWrites step := by
  intro step member
  have checks := Bool.and_eq_true_iff.mp (List.all_eq_true.mp separation_checked step member)
  exact ⟨fun term present => of_decide_eq_true (List.all_eq_true.mp checks.1 term present),
    fun column present => of_decide_eq_true (List.all_eq_true.mp checks.2 column present)⟩

variable {{F : Type}} [Field F] [CharP F modulus]
def rootBitsValues (codec : TransferReduction.CanonicalField F) (value : F) (column : Nat) : F :=
  if column = {root} then value else if (encodeBits 255 (codec.decode value))[column-{start}]?.getD false then 1 else 0
theorem bitBase_patch (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (value : F) :
    {canonical_name}.bitBase codec rho value = patchAssignment rho (rootBitsValues codec value) rootBitsWrites := by
  simpa only [{canonical_name}.bitBase,rootBitsValues,rootBitsWrites,encodeBits_length] using
    CompilerPatchCommutation.root_bits_patch rho {root} {start} value (encodeBits 255 (codec.decode value))
      (by simp only [encodeBits_length]; decide)
theorem before_commutes (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (value : F) :
    CompilerCompletion.run ({canonical_name}.bitBase codec rho value) before =
      {canonical_name}.bitBase codec (CompilerCompletion.run rho before) value := by
  rw [bitBase_patch,bitBase_patch]
  exact CompilerPatchCommutation.run_commutes rho (rootBitsValues codec value) rootBitsWrites before separated

def completeAssignment (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (value : F) : Nat → F :=
  CompilerCompletion.run ({canonical_name}.completeAssignment codec (CompilerCompletion.run rho before) value) after
theorem assignment_equal (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (value : F) :
    completeAssignment codec rho value =
      {numeric}.completeAssignment ({native_bits}.completeAssignment codec rho value) := by
  have nativeBase : {native_bits}.completeAssignment codec rho value = {canonical_name}.bitBase codec rho value := rfl
  unfold completeAssignment {canonical_name}.completeAssignment {numeric}.completeAssignment
  rw [nativeBase,program_split,CompilerSequenceCompletion.run_append,CompilerSequenceCompletion.run_append,before_commutes]

theorem writes_checked : CompilerSequenceCompletion.checkWrites {copy} {result['floor']} {result['exceptions']}
    (PoseidonCompletion.writes after) = true := by decide
theorem rows_checked : CompilerSequenceCompletion.checkRows {copy} {result['floor']} {result['exceptions']}
    {canonical_name}.rawRows = true := by decide
theorem after_frame : ∀ row ∈ {canonical_name}.rawRows, ∀ term ∈ row.a ++ row.b,
    term.1 ∉ PoseidonCompletion.writes after :=
  CompilerSequenceCompletion.frame_rows {copy} {result['floor']} {result['exceptions']}
    (PoseidonCompletion.writes after) {canonical_name}.rawRows writes_checked rows_checked

theorem numeric_complete (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (value : F)
    (linked : rho {copy} = rho 0) : Satisfies (completeAssignment codec rho value) {numeric}.rawRows := by
  rw [assignment_equal]
  apply {numeric}.complete
  rw [{native_bits}.preserves codec rho value {copy} (by decide) (by decide),
    {native_bits}.preserves codec rho value 0 (by decide) (by decide),linked]
theorem canonical_complete (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (value : F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    Satisfies (completeAssignment codec rho value) {canonical_name}.rawRows := by
  have beforeOne : CompilerCompletion.run rho before 0 = 1 :=
    (PoseidonCompletion.run_outside rho before 0 (by decide)).trans one
  have beforeLinked : CompilerCompletion.run rho before {copy} = CompilerCompletion.run rho before 0 := by
    rw [PoseidonCompletion.run_outside rho before {copy} (by decide),
      PoseidonCompletion.run_outside rho before 0 (by decide),linked]
  exact CompilerSequenceCompletion.preserves_rows
    ({canonical_name}.completeAssignment codec (CompilerCompletion.run rho before) value)
    after {canonical_name}.rawRows
    ({canonical_name}.complete_rows codec (CompilerCompletion.run rho before) value beforeOne four beforeLinked) after_frame
theorem complete_rows (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (value : F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (linked : rho {copy} = rho 0) :
    Satisfies (completeAssignment codec rho value) rawRows := by
  intro row member
  rcases List.mem_append.mp member with numeric | canonical
  · exact numeric_complete codec rho value linked row numeric
  · exact canonical_complete codec rho value one four linked row canonical
theorem preserves (codec : TransferReduction.CanonicalField F) (rho : Nat → F) (value : F) (column : Nat)
    (outsideNumeric : column ∉ PoseidonCompletion.writes {numeric}.steps)
    (outsideRoot : column ≠ {root}) (outsideBits : column < {start} ∨ {start}+255 ≤ column) :
    completeAssignment codec rho value column = rho column := by
  rw [assignment_equal,{numeric}.preserves _ column outsideNumeric]
  exact {native_bits}.preserves codec rho value column outsideRoot outsideBits
'''
    exports=['program_split','separation_checked','separated','bitBase_patch','before_commutes','assignment_equal',
             'writes_checked','rows_checked','after_frame','numeric_complete','canonical_complete','complete_rows','preserves']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
