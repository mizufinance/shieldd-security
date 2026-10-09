"""Concrete actual balance spec from genuine captures and typed native parents.

No ordinary stream is opened. The caller object is reconstructed using its real
IVK/reduction/RNK/authorization parsers, rather than serializing tuple-keyed LCs
or trusting a JSON assertion that caller acceptance succeeded.
"""
from pathlib import Path
import hashlib,json
from circuits import transfer_relation as relation

SCHEMA='shieldd-balance-caller-parser-recipe-v1'
DIGEST='16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236'
INPUT_PACKET='balance-joint-actual-inputs-09'
JOINT_PACKET='balance-joint-actual-13'
ENDPOINT_PACKET='balance-native-endpoint-post-joint-actual-08'
sha=lambda path:hashlib.sha256(Path(path).read_bytes()).hexdigest()
path_text=lambda path:Path(path).resolve().as_posix()

def bounded(path,limit):
    path=Path(path)
    if not path.is_file() or path.is_symlink():raise relation.RelationError('real qualified parent/input required')
    with path.open('rb') as handle:data=handle.read(limit+1)
    if len(data)>limit:raise relation.RelationError('bounded balance semantic input required')
    return data

def restore_caller(recipe,pins):
    from circuits import transfer_ivk_rows as ivk,transfer_ivk_reduction as reduction
    from circuits import transfer_ownership as ownership,transfer_authorization_roles as roles
    if (not isinstance(recipe,dict) or set(recipe)!={'schema','ivk','reduction','rnk','roles','parameters'}
            or recipe['schema']!=SCHEMA or not isinstance(pins,dict)):
        raise relation.RelationError('closed actual caller parser recipe required')
    parameters=Path(recipe['parameters'])
    required=[Path(recipe[key]) for key in ('ivk','reduction','rnk','roles')]+[
        parameters/'poseidon381.json',parameters/'poseidon381-wide.json']
    for path in required:
        if path_text(path) not in pins or sha(path)!=pins[path_text(path)]:
            raise relation.RelationError('every independent caller/parameter file must be pinned')
    a=ivk.inspect_metadata(bounded(recipe['ivk'],4194304),parameters,DIGEST)
    b=reduction.inspect_metadata(bounded(recipe['reduction'],4194304),a,DIGEST)
    c=ownership.inspect_rnk_metadata(bounded(recipe['rnk'],4194304),DIGEST,
        a['metadata']['handles'],b['metadata']['remainder_bits'],b['metadata']['remainder'])
    return roles.inspect_metadata(bounded(recipe['roles'],4194304),DIGEST,
        a['metadata']['handles'],c['metadata'],a['metadata'])

def build(root,destination):
    """Derive exact selected source objects; refuse if sender19 is not qualified.

    Native H is read from the real VALUE_BLINDING capture and the asset source
    from the independently accepted map's final cofactor role. These source
    associations do not discharge the global native GroupModel/codec laws.
    """
    from circuits import transfer_asset_generator_nonidentity as asset
    from circuits import transfer_balance_variable as variable,transfer_balance_blinding_fixed as blinding
    from circuits import transfer_balance_final_add as final,transfer_remaining_pages as remaining
    root=Path(root).resolve();destination=Path(destination).resolve()
    if destination!=root/INPUT_PACKET or destination.exists():
        raise relation.RelationError('fresh exact balance input packet required')
    params=Path('C:/src/shieldd-pr160-844389ee/crates/crypto/primitives/params')
    recipe=dict(schema=SCHEMA,ivk=path_text(root/'runtime-ivk-capture-direct-02/stdout.txt'),
        reduction=path_text(root/'runtime-ivk-reduction-capture-direct-02/stdout.txt'),
        rnk=path_text(root/'cargo-rnk-capture-04/stdout.txt'),roles=path_text(root/'cargo-spool-roles-qualify-03/stdout.txt'),
        parameters=path_text(params))
    vparent=root/'balance-variable-qualify-12/stdout.txt';bparent=root/'balance-blinding-qualify-10/stdout.txt'
    cparent=root/'remaining-sender-qualify-03/stdout.txt';cpage=root/'remaining-sender-first-02/capture.pending-page-000.json'
    vp=[root/f'balance-variable-first-12/capture.page{i}.pending.json' for i in range(5)]
    bp=[root/f'balance-blinding-first-10/capture.page{i}.pending.json' for i in range(8)]
    signed_path=root/'signed-balance-actual-completion-source-03/recipe.json'
    map_path=root/'cargo-future-asset-qualify-07/stdout.txt'
    # The exact original input-header identity is retained by the completed
    # row parser before failed19's later H frame check. No ordinary reread.
    layout_path=root/'balance-joint-actual-09/extraction.json'
    paths=[*[Path(recipe[k]) for k in ('ivk','reduction','rnk','roles')],params/'poseidon381.json',params/'poseidon381-wide.json',
        vparent,bparent,cparent,cpage,*vp,*bp,signed_path,map_path,layout_path]
    # Missing genuine sender qualification refuses BEFORE any output writes.
    for path in paths:bounded(path,4194304)
    pins={path_text(path):sha(path) for path in paths}
    caller=restore_caller(recipe,pins)
    signed=json.loads(bounded(signed_path,4194304))
    map_checked=asset.inspect_metadata(bounded(map_path,4194304),caller)
    asset_base=map_checked['metadata']['cofactor'][3]
    raw_h=json.loads(bounded(bp[0],2097152))
    if raw_h.get('schema')!='shieldd-transfer-balance-blinding-fixed-v1':
        raise relation.RelationError('genuine named VALUE_BLINDING source page required')
    blinding_base=raw_h['base']
    vdata=bounded(vparent,32768);bdata=bounded(bparent,32768);cdata=bounded(cparent,32768);cr=bounded(cpage,2097152)
    vpages=[bounded(p,2097152) for p in vp];bpages=[bounded(p,2097152) for p in bp]
    v=variable.inspect_pages(vdata,vpages,DIGEST,signed,asset_base)
    c=remaining.inspect_page(cdata,cr,0,caller)
    scalar=c['records']['caller','shared',0][6]
    blinding.inspect_pages(bdata,bpages,blinding_base,scalar)
    # Match pre-outline LC semantics, not merely source-handle/hash identity.
    for axis,ref in enumerate(asset_base):
        handle=tuple(ref['source'])
        if v['chunks'][0]['derived'][handle]!=map_checked['points'][3][axis]:
            raise relation.RelationError('actual variable asset seed LC differs from final map cofactor')
    association=final.from_ingress(vdata,vpages,bdata,bpages,cdata,cr,caller,signed,asset_base,blinding_base)
    if any(sha(path)!=pins[path_text(path)] for path in paths):raise relation.RelationError('actual source inputs changed')
    destination.mkdir()
    def write(name,obj):
        path=destination/name;path.write_bytes((json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode());pins[path_text(path)]=sha(path);return path_text(path)
    recipe_path=write('caller-parser-recipe.json',recipe)
    asset_path=write('asset-source-base.json',asset_base)
    h_path=write('value-blinding-source-base.json',blinding_base)
    readonly={terms for terms in caller['observed'].values()}
    # Native precompute owns the seed coordinates. Reusing the preceding map
    # assignment is an explicit semantic join, not a fresh-column frame claim.
    seed_columns={c for terms in map_checked['points'][3] for c,_ in terms}
    readonly={terms for terms in readonly if not any(c in seed_columns for c,_ in terms)}
    from circuits import transfer_balance_input_layout as layout
    layout_bytes=bounded(layout_path,4194304)
    if hashlib.sha256(layout_bytes).hexdigest()!='096094c19d5266ffb60f69d7fb6ef4359df6d5023a1c9f3eb69dc0852353fef1':
        raise relation.RelationError('exact root failed19 retained original projection required')
    public_shadows=layout.public_witness_shadows(json.loads(layout_bytes)['identity'])
    readonly.update(((i,1),) for i in [0,1,2,6,9,200692,*public_shadows,*signed['amounts']])
    spec=dict(schema='shieldd-balance-joint-consumer-root-v1',destination=path_text(root/JOINT_PACKET),
        ordinary=path_text(root/'cargo-capture-02/relation.jsonl'),variable_parent=path_text(vparent),variable_pages=list(map(path_text,vp)),
        blinding_parent=path_text(bparent),blinding_pages=list(map(path_text,bp)),caller_parent=path_text(cparent),caller_page=path_text(cpage),
        accepted_roles=recipe_path,signed=path_text(signed_path),asset_base=asset_path,blinding_base=h_path,
        readonly_lcs=sorted(readonly),inputs=dict(pins))
    write('activation-spec.json',spec)
    write('source-association.json',dict(association=association,asset_map_parent=sha(map_path),
        native_value_blinding_source='Pinned circuits::map::VALUE_BLINDING passed as actual Generators.value_blinding at exact balance hook; native parameter/codec/CurveModel law remains explicit.',
        source_only=True,ordinary_replays=0,qualification=False,certification=False))
    return destination/'activation-spec.json'
