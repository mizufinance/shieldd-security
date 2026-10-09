"""Actual final cofactor generator inverse; preserve the complete map ingress.

This is a narrow row boundary. Native subgroup/nonidentity correspondence,
map/hash constructor composition and full Transfer remain separate obligations.
"""
import hashlib
import json
from . import transfer_asset_map as maps, transfer_arithmetic as arithmetic, transfer_relation as relation
from .transfer_balance_rows import canonical, combine, source_index
from .generate_hash_round import linear, _signature_audits


def inspect_metadata(data, accepted_roles):
    if not isinstance(data, bytes) or len(data)>4*1024*1024:
        raise relation.RelationError('asset generator nonidentity metadata bound')
    obj=relation.record(data)
    if not isinstance(obj,dict) or obj.get('schema') not in ('shieldd-transfer-asset-nonidentity-v1','shieldd-transfer-asset-nonidentity-v2'):
        raise relation.RelationError('asset generator nonidentity schema')
    n=obj.get('nonidentity')
    if not isinstance(n,dict) or set(n)!={'asset','hash','generator','inverse'}:
        raise relation.RelationError('asset generator nonidentity closed roles')
    if n['asset']!=obj.get('asset') or n['hash']!=obj.get('hash') or not isinstance(obj.get('cofactor'),list) or len(obj['cofactor'])!=4 or n['generator']!=obj['cofactor'][3]:
        raise relation.RelationError('asset generator exact final cofactor links')
    ref=n['inverse']
    if not isinstance(ref,dict) or set(ref)!={'source'}:
        raise relation.RelationError('asset generator actual inverse source required')
    handle=source_index(ref['source'])
    if handle[0]!=1:
        raise relation.RelationError('asset generator inverse must be witness')
    # Delegate every map equation, all255 canonical bits, the full cofactor
    # recurrence and caller asset linkage. Remove exactly the new witness LC;
    # its occurrence elsewhere fails the retained map's exact cone inventory.
    expressions=obj.get('expressions')
    if not isinstance(expressions,list) or len(expressions)>4096:
        raise relation.RelationError('asset generator expression bound')
    inverse=[e for e in expressions if isinstance(e,dict) and e.get('source')==ref['source']]
    if len(inverse)!=1 or set(inverse[0])!={'source','terms'}:
        raise relation.RelationError('asset generator exact inverse LC inventory')
    map_obj={k:v for k,v in obj.items() if k!='nonidentity'}
    map_obj['schema']='shieldd-transfer-asset-map-v2' if obj['schema'].endswith('-v2') else 'shieldd-transfer-asset-map-v1'
    map_obj['expressions']=[e for e in expressions if e is not inverse[0]]
    checked=maps.inspect_metadata((json.dumps(map_obj,separators=(',',':'))+'\n').encode(),accepted_roles)
    terms=inverse[0]['terms']
    expected=[[handle[1]+3,f'{1:064x}']]
    if terms!=expected or handle[1]+3>=obj['domain_size']:
        raise relation.RelationError('asset generator exact unit inverse witness LC')
    column=handle[1]+3
    if any(column==c for lc in checked['observed'].values() for c,_ in lc) or any(column==c for lc in accepted_roles['observed'].values() for c,_ in lc):
        raise relation.RelationError('asset generator inverse aliases shared map/caller source')
    checked.update(metadata=obj,metadata_sha256=hashlib.sha256(data).hexdigest(),inverse=((column,1),),inverse_handle=handle)
    checked['observed']=dict(checked['observed'])
    checked['observed'][handle]=checked['inverse']
    return checked


def extract(data,stream,accepted_roles):
    checked=inspect_metadata(data,accepted_roles);obj=checked['metadata'];copy=obj['constant_copy']
    inverse=checked['inverse'];x=checked['points'][3][0]
    outline=lambda lc:canonical((copy if c==0 else c,v) for c,v in lc)
    required={(canonical([(0,1),(copy,-1)]),()):['constant-copy']}
    products=[('asset-generator.nonidentity',outline(combine(inverse,x,-1)),outline(combine(inverse,x)),None,((copy,1),))]
    result=arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],required,products,[],label='asset-generator-nonidentity')
    result.update(metadata_sha256=checked['metadata_sha256'],scope='one actual final asset generator inverse triple plus constant link; native/subgroup/full Transfer open')
    return result


def _certificates(checked,extracted):
    raw,rows=arithmetic.normalize_selection(extracted,checked['metadata'],checked['metadata_sha256'])
    cert=arithmetic.quotient_certificate(((0,1),),checked['points'][3][0],checked['inverse'],rows)
    copy=checked['metadata']['constant_copy']
    links=[i for i,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),())]
    if cert['kind']!='product' or len(cert['rows'])!=3 or len(links)!=1 or set(raw)!=set(cert['rows'])|set(links):
        raise relation.RelationError('asset generator exact inverse3/constant1 coverage')
    return dict(checked=checked,raw=raw,rows=rows,certificate=cert)


def certificates(data,extracted,accepted_roles):
    return _certificates(inspect_metadata(data,accepted_roles),extracted)


def derived_map_view(data,accepted_roles):
    """Complete map projection from the actual qualified nonidentity capture.

The original parent identity remains attached. The projected map_data is an
explicit parser view, not a separate runtime capture or qualification result.
All map roles, source DAG, captured/derived LCs and native equations were checked
before projection. Exactly one distinct inverse LC and its companion roles are
removed; every retained qualification flag is inherited without changing it.
"""
    checked=inspect_metadata(data,accepted_roles);obj=checked['metadata']
    handle=checked['inverse_handle']
    projected={k:v for k,v in obj.items() if k!='nonidentity'}
    projected['schema']='shieldd-transfer-asset-map-v2' if obj['schema'].endswith('-v2') else 'shieldd-transfer-asset-map-v1'
    projected['expressions']=[e for e in obj['expressions'] if source_index(e['source'])!=handle]
    map_data=(json.dumps(projected,separators=(',',':'))+'\n').encode()
    maps.inspect_metadata(map_data,accepted_roles)
    return dict(kind='derived-map-of-qualified-nonidentity',parent_data=data,
        parent_metadata_sha256=checked['metadata_sha256'],parent_schema=obj['schema'],
        map_data=map_data,map_view_sha256=hashlib.sha256(map_data).hexdigest(),
        ordinary_full_ordered_rows_equal=obj['ordinary_full_ordered_rows_equal'],
        repeated_observations_equal=obj['repeated_observations_equal'])


def completion_plan(data,extracted,accepted_roles):
    selected=certificates(data,extracted,accepted_roles);checked=selected['checked']
    cert=selected['certificate'];normalized=selected['rows']
    # The original squared assertion may be numerator-product. Keep its exact
    # bytes in raw; normalize only this already-certified sign for constructor
    # shape selection, then prove signed transport in the emitted theorem.
    assertion=cert['rows'][-1];expected=(combine(cert['output'],cert['numerator'],-1),())
    if normalized[assertion] == (canonical((c,-n) for c,n in expected[0]),()):
        normalized=dict(normalized);normalized[assertion]=expected
    plan=arithmetic.completion_certificate(cert,normalized)
    if plan is None:raise relation.RelationError('asset generator inverse constructor row shape unsupported')
    writes=[plan[k] for k in ('quotient','product','auxiliary')]
    kept=[((0,1),),((1,1),),((2,1),),((checked['metadata']['constant_copy'],1),)]
    kept.extend(lc for handle,lc in checked['observed'].items() if handle!=checked['inverse_handle'])
    kept.extend(accepted_roles['observed'].values())
    if any(c in writes for lc in kept for c,_ in lc):
        raise relation.RelationError('asset generator inverse writes affect map/caller source')
    return dict(plan,checked=checked,writes=writes,kept=list(dict.fromkeys(kept)),raw={i:selected['raw'][i] for i in plan['rows']})


def generate_sound(data,extracted,accepted_roles):
    selected=certificates(data,extracted,accepted_roles);cert=selected['certificate'];copy=selected['checked']['metadata']['constant_copy']
    name='RuntimeTransferAssetGeneratorNonidentity'
    q,x=cert['quotient'],cert['denominator'];left,right=(x,q) if cert['swapped'] else (q,x)
    forward=selected['rows'][cert['rows'][-1]]==(combine(cert['output'],((0,1),),-1),())
    a,b=(cert['output'],((0,1),)) if forward else (((0,1),),cert['output'])
    assertion=f'Compiler.checked_assertion_sound rho rows {linear(a)} {linear(b)} normalized (by decide)'
    if not forward:assertion='('+assertion+').symm'
    source=f'''import ShielddSecurity.Compiler
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Only the actual final generator inverse3 and constant link; native joins open.
def modulus : Nat := {relation.MODULUS}
def generatorX : Linear := {linear(x)}
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩' for a,b in selected['raw'].values())+f''']
def rows : List Row := Compiler.unoutlineRows {copy} rawRows
theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide
theorem actual_inverse {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho {linear(q)} * eval rho generatorX = 1 := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have multiplied := Compiler.checked_product_sound rho rows {linear(left)} {linear(right)} {linear(cert['output'])}
    {linear(cert['auxiliary'])} four normalized (by decide) (by decide)
  have asserted := {assertion}
  have unit : eval rho [(0,1)] = 1 := by simp only [eval,Int.cast_one,one_mul,one,add_zero]
  simpa only [generatorX,asserted,unit,mul_comm] using multiplied.symm
theorem generator_x_nonzero {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho generatorX ≠ 0 := by
  intro zero
  have equation := actual_inverse rho one four satisfied
  rw [zero,mul_zero] at equation
  exact zero_ne_one equation
'''
    for export in ('constantLink','actual_inverse','generator_x_nonzero'):source+=f'#print axioms {export}\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')


def generate_completion(data,extracted,accepted_roles):
    plan=completion_plan(data,extracted,accepted_roles);q,p,a=(plan[k] for k in ('quotient','product','auxiliary'))
    copy=plan['checked']['metadata']['constant_copy'];name='RuntimeTransferAssetGeneratorInverseCompletion'
    source=f'''import ShielddSecurity.GroupRowCompletion
import ShielddSecurity.CompilerSignedCompletion
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Only3 original inverse rows; every other map/caller source LC is preserved.
def modulus : Nat := {relation.MODULUS}
def generatorX : Linear := {linear(plan['denominator'])}
def remainder : Linear := {linear(plan['remainder'])}
def ownedWrites : List Nat := {plan['writes']}
def kept : List Nat := {sorted({c for terms in plan['kept'] for c,_ in terms})}
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(left)+','+linear(right)+'⟩' for left,right in plan['raw'].values())+f''']
def completeAssignment {{F : Type}} [Field F] (rho : Nat → F) : Nat → F :=
  GroupRowCompletion.extendQuotient rho [(0,1)] generatorX remainder {q} {p} {a}
theorem coverage_checked : rawRows.all (fun actual =>
    (GroupRowCompletion.quotientRows [(0,1)] generatorX remainder {q} {p} {a}).any (fun expected =>
      decide ((Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
        Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
        Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide
theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈
    GroupRowCompletion.quotientRows [(0,1)] generatorX remainder {q} {p} {a},
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp coverage_checked) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩
theorem preserves {{F : Type}} [Field F] (rho : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : completeAssignment rho column = rho column :=
  GroupRowCompletion.extend_preserves rho [(0,1)] generatorX remainder {q} {p} {a} column outside
theorem kept_checked : kept.all (fun column => decide (column ∉ ownedWrites)) = true := by decide
theorem kept_preserved {{F : Type}} [Field F] (rho : Nat → F) (terms : Linear)
    (covered : ∀ term ∈ terms, term.1 ∈ kept) :
    eval (completeAssignment rho) terms = eval rho terms := by
  apply eval_agrees
  intro term present
  exact preserves rho term.1 (of_decide_eq_true
    ((List.all_eq_true.mp kept_checked) term.1 (covered term present)))
theorem complete_rows {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (linked : rho {copy} = rho 0) (legal : eval rho generatorX ≠ 0) :
    Satisfies (completeAssignment rho) rawRows := by
  have completed := GroupRowCompletion.extend_complete rho [(0,1)] generatorX remainder {q} {p} {a}
    (by decide) (by decide) (by decide) (by decide) legal
  have copyValue : completeAssignment rho {copy} = completeAssignment rho 0 := by
    rw [preserves rho {copy} (by decide),preserves rho 0 (by decide),linked]
  exact CompilerSignedCompletion.original_rows (completeAssignment rho)
    (GroupRowCompletion.quotientRows [(0,1)] generatorX remainder {q} {p} {a}) rawRows
    {copy} copyValue completed coverage
theorem inverse_value {{F : Type}} [Field F] (rho : Nat → F) (one : rho 0 = 1) :
    completeAssignment rho {q} = (eval rho generatorX)⁻¹ := by
  have unit : eval rho [(0,1)] = 1 := by simp only [eval,Int.cast_one,one_mul,one,add_zero]
  change GroupRowCompletion.extendQuotient rho [(0,1)] generatorX remainder {q} {p} {a} {q} = _
  rw [GroupRowCompletion.quotient_value,unit,one_div]
theorem complete_inverse {{F : Type}} [Field F] [CharP F modulus] (rho : Nat → F)
    (one : rho 0 = 1) (linked : rho {copy} = rho 0) (legal : eval rho generatorX ≠ 0) :
    Satisfies (completeAssignment rho) rawRows ∧
      completeAssignment rho {q} = (eval rho generatorX)⁻¹ ∧
      (∀ column ∉ ownedWrites, completeAssignment rho column = rho column) :=
  ⟨complete_rows rho linked legal,inverse_value rho one,preserves rho⟩
'''
    for export in ('coverage_checked','coverage','preserves','kept_checked','kept_preserved','complete_rows','inverse_value','complete_inverse'):
        source+=f'#print axioms {export}\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')


def generate_kept_boundaries(data,extracted,accepted_roles,*,term_limit=512):
    """Audit all exact captured map/caller LCs in bounded preservation slices.

    Shared column equality proves LC preservation for arbitrary coefficients.
    Freshness checks compare each actual term with only the three owned writes,
    avoiding a wide source-LC declaration or quadratic column-set membership.
    """
    if type(term_limit) is not int or not 256 <= term_limit <= 1024:
        raise relation.RelationError('asset inverse kept LC finite term bound')
    plan=completion_plan(data,extracted,accepted_roles);chunks=[];current=[];size=0
    for terms in plan['kept']:
        if len(terms)>term_limit:
            raise relation.RelationError('asset inverse one kept LC exceeds finite term bound')
        if current and size+len(terms)>term_limit:
            chunks.append(current);current=[];size=0
        current.append(terms);size+=len(terms)
    if current:chunks.append(current)
    modules={};offset=0;parent='RuntimeTransferAssetGeneratorInverseCompletion'
    for number,chunk in enumerate(chunks):
        name='RuntimeTransferAssetGeneratorInverseKept'+str(number)
        source=f'''import ShielddSecurity.{parent}
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact nonidentity metadata SHA256 {plan['checked']['metadata_sha256']}.
-- Kept source-LC offsets {offset}..{offset+len(chunk)-1}; at most{term_limit} total terms.
def keptExpressions : List Linear := [{', '.join(linear(terms) for terms in chunk)}]
theorem freshness_checked : keptExpressions.all (fun terms => terms.all
    (fun term => decide (term.1 ∉ {parent}.ownedWrites))) = true := by decide
theorem actual_kept_preserved {{F : Type}} [Field F] (rho : Nat → F) :
    ∀ terms ∈ keptExpressions, eval ({parent}.completeAssignment rho) terms = eval rho terms := by
  intro terms member
  apply eval_agrees
  intro term present
  exact {parent}.preserves rho term.1 (of_decide_eq_true
    ((List.all_eq_true.mp ((List.all_eq_true.mp freshness_checked) terms member)) term present))
#print axioms freshness_checked
#print axioms actual_kept_preserved
end ShielddSecurity.{name}
'''
        modules[name]=_signature_audits(source);offset+=len(chunk)
    if offset!=len(plan['kept']):raise relation.RelationError('asset inverse full kept LC coverage')
    return modules
