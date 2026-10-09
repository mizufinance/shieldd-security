"""Overlay retained paged source on a fresh, identical diagnostic source copy.

Does not copy a workspace, compile, run a capture or qualify evidence. The caller
creates the disposable copy first; every original source hash is checked before
any overlay write, and the base is never written.
"""
import hashlib,json
from pathlib import Path
from .staging import _inventory
from . import note_spend_observer as spends,note_hash_observer as hashes

SDK='crates/crypto/circuits/src/'
COMPILER='third_party/commonware/cryptography/src/zk/pari/circuit.rs'
REPLACEMENTS={'future/note.rs':SDK+'note.rs','future/hash.rs':SDK+'hash.rs',
              'future/tree.rs':SDK+'tree.rs','future/catalogue.rs':SDK+'catalogue.rs',
              'future/compile-pages.rs':COMPILER}
RESOURCES={'note_spend.rs':SDK+'note/spend_inspection.rs','note_hash.rs':SDK+'hash/note_inspection.rs',
           'note_tree.rs':SDK+'tree/note_inspection.rs'}
for name in ('note_spend','note_hash','note_hash_pages','note_tree','note_t4_pages'):
    RESOURCES[name+'_catalogue.rs']=SDK+name+'_catalogue.rs'
DIRECTORIES=('crates/crypto/circuits/src','crates/crypto/primitives/src',
             'crates/crypto/primitives/params','third_party/commonware/cryptography/src/zk')


def diagnostic_note(data):
    if not isinstance(data,bytes) or any(data.count(anchor)!=1 for anchor in
        (b'scalar::inspection::spend_target(&randomizer);',
         b'group::fixed_inspection::spend_scope(&randomizer);',
         b'crate::transfer::inspection::spend(ak, &randomizer, &bits, &generator,')):
        raise ValueError('exact existing scalar/fixed/authorization note hooks required')
    return hashes.instrument_note(spends.instrument_note(data))


def digest(data):return hashlib.sha256(data).hexdigest()


def prepare_t4_source(base,fresh,packet):
    """Use packet's explicit original relative hashes, then retain an overlay receipt."""
    base,fresh,packet=(Path(p).resolve() for p in (base,fresh,packet))
    if base==fresh or not fresh.is_dir() or (fresh/'.git').exists():
        raise ValueError('T4 source overlay requires an existing disposable fresh copy')
    manifest=json.loads((packet/'manifest.json').read_bytes())
    expected=manifest.get('activation_base_files')
    if not isinstance(expected,dict) or set(expected)!=set(REPLACEMENTS.values()):
        raise ValueError('retained successor packet needs exact activation base hashes')
    before={name:_inventory(base,name) for name in DIRECTORIES}
    if before!={name:_inventory(fresh,name) for name in DIRECTORIES}:
        raise ValueError('fresh source copy differs from selected base inventories')
    payloads={}
    for source,target in REPLACEMENTS.items():
        original=base/target
        if original.is_symlink() or digest(original.read_bytes())!=expected[target]:
            raise ValueError('activation base source drift: '+target)
        payloads[target]=(packet/source).read_bytes()
        if digest(payloads[target])!=manifest['files'].get(source):
            raise ValueError('retained replacement source drift: '+source)
    for source,target in RESOURCES.items():
        snapshot='integration-observers-'+source
        payloads[target]=(packet/snapshot).read_bytes()
        if digest(payloads[target])!=manifest['files'].get(snapshot):
            raise ValueError('retained observer resource drift: '+source)
        if (fresh/target).exists() and (fresh/target).read_bytes()!=payloads[target]:
            raise ValueError('divergent pre-existing future observer resource: '+target)
    authored=Path(__file__).resolve().parent/'src/bin/transfer-ownership-inspection.rs'
    exporter=(packet/'future/exporter.rs').read_bytes()
    if digest(exporter)!=manifest['files'].get('future/exporter.rs') or authored.read_bytes()!=exporter:
        raise ValueError('future exporter differs from current authored source')
    payloads['crates/crypto/circuits/examples/transfer-ownership-inspection.rs']=exporter
    for relative in payloads:
        current=fresh
        for part in Path(relative).parts:
            current/=part
            if current.is_symlink():raise ValueError('linked future overlay target')
    for relative,data in payloads.items():
        target=fresh/relative;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    if before!={name:_inventory(base,name) for name in DIRECTORIES}:
        raise ValueError('diagnostic base drifted; retain fresh overlay for inspection')
    if any((fresh/name).read_bytes()!=data for name,data in payloads.items()):
        raise ValueError('fresh source overlay byte mismatch')
    return {'base':str(base),'fresh':str(fresh),'overlay':{k:digest(v) for k,v in payloads.items()},
            'scope':'fresh diagnostic source overlay only; no build/runtime/qualification result'}
