"""Actual two-note quaternary source wiring and bounded level-row ingress.

This accepts no hash result equation. Hash semantics and all48level composition
remain separate from the captured source/LC and actual product-row joins here.
"""
import hashlib
from . import transfer_relation as relation, transfer_arithmetic as arithmetic
from . import transfer_note_spend as notes, transfer_note_hash as hashes
from .transfer_authorization_roles import _expressions
from .transfer_balance_rows import canonical, combine, source_index

SCOPE='48 current note-only state levels and six source products each; actual rows/native joins open'


def inspect_metadata(data,note_data,accepted_roles):
    accepted=notes.inspect_metadata(note_data,accepted_roles)
    if not isinstance(data,bytes) or len(data)>4*1024*1024:
        raise relation.RelationError('note tree metadata byte bound')
    obj=relation.record(data)
    keys={'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
          'ordinary_full_ordered_rows_equal','repeated_observations_equal','domain','depth','levels','expressions','spend'}
    if (set(obj)!=keys or (obj['schema'],obj['family'],obj['scope'])!=
        ('shieldd-transfer-note-tree-v1','transfer',SCOPE)):
        raise relation.RelationError('note tree closed schema/scope')
    if (obj['ordinary_full_ordered_rows_equal'] is not True or obj['repeated_observations_equal'] is not True or
        any(obj[k]!=accepted['metadata'][k] for k in ('relation_digest','domain_size','full_rows','constant_copy'))):
        raise relation.RelationError('note tree accepted note identity/pending mismatch')
    if obj['spend']!=accepted['metadata']:
        raise relation.RelationError('note tree embedded accepted spend mismatch')
    if type(obj['domain']) is not int or obj['domain']!=1 or type(obj['depth']) is not int or obj['depth']!=24:
        raise relation.RelationError('note tree state domain/depth')
    levels=obj['levels']
    if not isinstance(levels,list) or len(levels)!=48:
        raise relation.RelationError('note tree exact48 level inventory')
    observed=_expressions(obj['expressions'],obj['domain_size'],obj['constant_copy'],4096,'note-tree')
    required=set(accepted['observed']);parsed=[]
    if any(observed.get(h)!=lc for h,lc in accepted['observed'].items()):
        raise relation.RelationError('note tree shared note LC mismatch')
    def value(ref):
        if not isinstance(ref,dict) or set(ref)!={'source'}:
            raise relation.RelationError('note tree actual source reference required')
        h=source_index(ref['source']);required.add(h)
        if h not in observed:raise relation.RelationError('note tree source LC coverage')
        return observed[h]
    def array(refs,size):
        if not isinstance(refs,list) or len(refs)!=size:
            raise relation.RelationError('note tree source array shape')
        return tuple(value(ref) for ref in refs)
    for ordinal,level in enumerate(levels):
        slot,index=divmod(ordinal,24)
        if (not isinstance(level,dict) or set(level)!=
            {'slot','level','node','low','high','siblings','swaps','children','output','products'} or
            type(level['slot']) is not int or type(level['level']) is not int or
            (level['slot'],level['level'])!=(slot,index)):
            raise relation.RelationError('note tree native level order/closed shape')
        spend=accepted['metadata']['spends'][slot]
        previous=spend['commitment'] if index==0 else levels[ordinal-1]['output']
        if (level['node']!=previous or level['low']!={'source':spend['position_bits'][2*index]} or
            level['high']!={'source':spend['position_bits'][2*index+1]} or
            index==23 and level['output']!=spend['computed_anchor']):
            raise relation.RelationError('note tree bit/consecutive/final source mismatch')
        current={name:value(level[name]) for name in ('node','low','high','output')}
        for name,size in (('siblings',3),('swaps',2),('children',4)):
            current[name]=array(level[name],size)
        if not isinstance(level['products'],list) or len(level['products'])!=6:
            raise relation.RelationError('note tree exact six source products')
        products=tuple(array(p,3) for p in level['products'])
        node,low,high=current['node'],current['low'],current['high']
        first,second,third=current['siblings'];ls,rs=current['swaps']
        left_first=combine(node,ls);left_second=combine(first,ls,-1)
        right_third=combine(node,rs);right_fourth=combine(third,rs,-1)
        wanted=((low,combine(first,node,-1)),(low,combine(third,node,-1)),
                (high,combine(first,left_first,-1)),(high,combine(second,left_second,-1)),
                (high,combine(right_third,second,-1)),(high,combine(right_fourth,third,-1)))
        if any(p[:2]!=w for p,w in zip(products,wanted)):
            raise relation.RelationError('note tree six product operand LC mismatch')
        if (level['products'][0][2]!=level['swaps'][0] or level['products'][1][2]!=level['swaps'][1] or
            current['children']!=tuple(combine(base,p[2]) for base,p in
                zip((left_first,left_second,second,third),products[2:]))):
            raise relation.RelationError('note tree child/select source LC mismatch')
        current['products']=products;parsed.append(current)
    if set(observed)!=required:raise relation.RelationError('note tree exact source LC coverage')
    return dict(metadata=obj,observed=observed,levels=parsed,notes=accepted,
                metadata_sha256=hashlib.sha256(data).hexdigest())


def inspect_hash_link(data,hash_data,note_data,accepted_roles):
    """Join one actual state permutation page to its exact source child order."""
    checked=inspect_metadata(data,note_data,accepted_roles)
    hashed=hashes.inspect_boundaries(hash_data,note_data,accepted_roles)
    obj=hashed['metadata']
    if obj['role']!='state' or obj['block']!=0:
        raise relation.RelationError('note tree state hash page required')
    level=checked['metadata']['levels'][obj['slot']*24+obj['level']]
    if (obj['hash']['inputs']!=[{'native':f'{obj["level"]+1:064x}'},*level['children']] or
        obj['hash']['output']!=level['output']):
        raise relation.RelationError('note tree/hash exact source order mismatch')
    for handle,lc in checked['observed'].items():
        if handle in hashed['observed'] and hashed['observed'][handle]!=lc:
            raise relation.RelationError('note tree/hash shared source LC mismatch')
    return checked


def extract_level(data,stream,note_data,accepted_roles,slot,level):
    """Select actual copy, two boolean and six materialized product pairs."""
    checked=inspect_metadata(data,note_data,accepted_roles);obj=checked['metadata']
    slot=relation.natural(slot,2);level=relation.natural(level,24)
    current=checked['levels'][slot*24+level];copy=obj['constant_copy']
    outline=lambda lc:canonical((copy if c==0 else c,v) for c,v in lc)
    required={(canonical([(0,1),(copy,-1)]),()):['constant-copy']}
    for name in ('low','high'):
        bit=outline(current[name]);required[(bit,bit)]=[name+'.boolean']
    products=[('tree.'+str(i),outline(combine(a,b,-1)),outline(combine(a,b)),outline(z),None)
              for i,(a,b,z) in enumerate(current['products'])]
    result=arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],
                                       required,products,[],label='note-tree-level')
    result.update(metadata_sha256=checked['metadata_sha256'],slot=slot,level=level,
                  scope='actual one note state level wiring rows only; full path/hash joins open')
    return result


def certificates(data,extracted,note_data,accepted_roles):
    checked=inspect_metadata(data,note_data,accepted_roles);obj=checked['metadata']
    slot=relation.natural(extracted.get('slot'),2);level=relation.natural(extracted.get('level'),24)
    raw,rows=arithmetic.normalize_selection(extracted,obj,checked['metadata_sha256'])
    current=checked['levels'][slot*24+level];used=set()
    for name in ('low','high'):
        matches=[i for i,row in rows.items() if row==(current[name],current[name])]
        if len(matches)!=1:raise relation.RelationError('note tree boolean row missing/duplicate')
        used.update(matches)
    certs=[]
    for a,b,z in current['products']:
        cert=arithmetic.product_certificate(a,b,z,rows)
        if cert['kind']!='product':raise relation.RelationError('note tree unsupported materialized lowering')
        used.update(cert['rows']);certs.append(cert)
    copy=obj['constant_copy']
    links=[index for index,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),())]
    if len(links)!=1 or used|set(links)!=set(rows):
        raise relation.RelationError('note tree exact physical row coverage')
    return dict(checked=checked,raw=raw,rows=rows,products=certs,slot=slot,level=level)


def generate_level(data,extracted,note_data,accepted_roles):
    """Generate a narrow actual-row ordered-child theorem, no child equations assumed."""
    from .generate_hash_round import linear,_signature_audits
    selected=certificates(data,extracted,note_data,accepted_roles)
    checked=selected['checked'];obj=checked['metadata'];copy=obj['constant_copy']
    current=checked['levels'][selected['slot']*24+selected['level']]
    namespace=f'RuntimeTransferNoteTree{selected["slot"]}Level{selected["level"]}'
    source=f'''import ShielddSecurity.Compiler
import ShielddSecurity.Tree
set_option maxHeartbeats 500000
namespace ShielddSecurity.{namespace}
-- Full ordinary relation {obj['relation_digest']}; local tree wiring only.
-- Metadata SHA256 (identity only): {checked['metadata_sha256']}
-- Whole path/native hash joins remain OPEN.
def modulus : Nat := {relation.MODULUS}
def originalRows : List Nat := {list(selected['raw'])}
def rawRows : List Row := [
'''
    source+=',\n'.join('  ⟨'+linear(a)+','+linear(b)+'⟩' for a,b in selected['raw'].values())+']\n'
    source+=f'def rows : List Row := Compiler.unoutlineRows {copy} rawRows\n'
    for name in ('node','low','high'):
        source+=f'def {name} : Linear := {linear(current[name])}\n'
    for name,values in (('sibling',current['siblings']),('child',current['children']),
                        ('product',[p[2] for p in current['products']])):
        for i,lc in enumerate(values):source+=f'def {name}{i} : Linear := {linear(lc)}\n'
    source+=f'''theorem constantLink : Compiler.checkRow modulus rawRows
    ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide
'''
    rights=['Compiler.subtract sibling0 node','Compiler.subtract sibling2 node',
            'Compiler.subtract sibling0 (node ++ product0)',
            'Compiler.subtract sibling1 (Compiler.subtract sibling0 product0)',
            'Compiler.subtract (node ++ product1) sibling1',
            'Compiler.subtract (Compiler.subtract sibling2 product1) sibling2']
    equations=['eval rho low * (eval rho sibling0 - eval rho node)',
               'eval rho low * (eval rho sibling2 - eval rho node)',
               'eval rho high * (eval rho sibling0 - (eval rho node + eval rho product0))',
               'eval rho high * (eval rho sibling1 - (eval rho sibling0 - eval rho product0))',
               'eval rho high * ((eval rho node + eval rho product1) - eval rho sibling1)',
               'eval rho high * ((eval rho sibling2 - eval rho product1) - eval rho sibling2)']
    for i,cert in enumerate(selected['products']):
        left='low' if i<2 else 'high';right=rights[i]
        a,b=(right,left) if cert['swapped'] else (left,right)
        source+=f'''theorem product{i}_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho product{i} = {equations[i]} := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have multiplied := Compiler.checked_product_sound rho rows ({a}) ({b}) product{i}
    ({linear(cert['auxiliary'])}) four normalized (by decide) (by decide)
  simpa only [Compiler.eval_subtract, eval_append, mul_comm] using multiplied
'''
    source+=f'''theorem ordered_children {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    ∃ lowBit highBit : Bool, Tree.bit lowBit = eval rho low ∧ Tree.bit highBit = eval rho high ∧
      [eval rho child0,eval rho child1,eval rho child2,eval rho child3] =
        Tree.children lowBit highBit (eval rho node)
          (eval rho sibling0) (eval rho sibling1) (eval rho sibling2) := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have lowBoolean : Square (eval rho low) (eval rho low) :=
    Compiler.checked_row_sound rho rows ⟨low,low⟩ normalized (by decide)
  have highBoolean : Square (eval rho high) (eval rho high) :=
    Compiler.checked_row_sound rho rows ⟨high,high⟩ normalized (by decide)
'''
    for i in range(6):source+=f'  have p{i} := product{i}_sound rho four satisfied\n'
    bases=['(node ++ product0)','(Compiler.subtract sibling0 product0)','sibling1','sibling2']
    for i,base in enumerate(bases):
        source+=f'  have c{i} := Compiler.canonical_equal rho child{i} ({base} ++ product{i+2}) (by decide)\n'
    source+='''  simp only [Compiler.eval_subtract,eval_append] at c0 c1 c2 c3
  have wired : [eval rho child0,eval rho child1,eval rho child2,eval rho child3] =
      Tree.wiredChildren (eval rho low) (eval rho high) (eval rho node)
        (eval rho sibling0) (eval rho sibling1) (eval rho sibling2) := by
    rw [c0,c1,c2,c3,p2,p3,p4,p5,p0,p1]
    simp only [Tree.wiredChildren,Tree.select]
    refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_
      (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl))) <;> ring
  rcases Tree.wiring_sound (eval rho low) (eval rho high) (eval rho node)
    (eval rho sibling0) (eval rho sibling1) (eval rho sibling2) lowBoolean highBoolean with
    ⟨lo,hi,hlo,hhi,hwired⟩
  exact ⟨lo,hi,hlo,hhi,wired.trans hwired⟩
#print axioms constantLink
'''
    for i in range(6):source+=f'#print axioms product{i}_sound\n'
    source+=f'#print axioms ordered_children\nend ShielddSecurity.{namespace}\n'
    return _signature_audits(source)
