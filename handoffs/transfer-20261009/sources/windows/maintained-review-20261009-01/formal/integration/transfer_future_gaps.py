"""Pure fresh-successor composition: retained RK/65 plus recovery74 and asset inverse.

Callers validate immutable packet identities before supplying this byte map.
No file is written here. Old modes, includes and ordinary lowerer remain owned
by the supplied merged parent, rather than by a historical exporter specimen.
"""
from . import asset_nonidentity_observer as asset, recovery_t4_capture as recovery
from .recovery_hash_observer import instrument_hash
from .recovery_capsule_observer import import_existing_inverse_field

SDK='crates/crypto/circuits/src/'
EXPORT='crates/crypto/circuits/examples/transfer-ownership-inspection.rs'


def compose(parent, recovery_resources, asset_resources):
    if not all(isinstance(v,dict) and all(isinstance(k,str) and isinstance(b,bytes) for k,b in v.items())
               for v in (parent,recovery_resources,asset_resources)):
        raise ValueError('future successor byte maps required')
    result=dict(parent)
    if SDK+'recovery.rs' in result or any('asset_nonidentity' in k or 'recovery_pages' in k for k in result):
        raise ValueError('fresh retained RK/65 parent required')
    required=[SDK+'balance.rs',SDK+'group.rs',SDK+'hash.rs',SDK+'catalogue.rs',
              SDK+'asset_map_catalogue.rs',EXPORT]
    if any(k not in result for k in required):raise ValueError('complete merged parent source required')
    original_export=result[EXPORT]
    if b'rk-subgroup-spool' not in original_export or b'transfer-t4-pages-spool' not in original_export:
        raise ValueError('retained RK/65 modes required')
    result[SDK+'balance.rs']=asset.instrument_balance(result[SDK+'balance.rs'])
    result[SDK+'group.rs']=asset.instrument_group(result[SDK+'group.rs'])
    result[SDK+'hash.rs']=instrument_hash(result[SDK+'hash.rs'])
    result[SDK+'catalogue.rs']=asset.instrument_catalogue(recovery.instrument_catalogue(result[SDK+'catalogue.rs']))
    result[SDK+'asset_map_catalogue.rs']=asset_resources['catalogue']
    result[SDK+'asset_nonidentity_catalogue.rs']=asset.catalogue(result[SDK+'asset_map_catalogue.rs'])
    result[SDK+'balance/asset_nonidentity_inspection.rs']=asset_resources['observer']
    for relative, data in recovery_resources.items():
        if relative in ('exporter','qualifier'):continue
        if relative in result:raise ValueError('recovery overlay would overwrite retained source')
        result[relative]=data
    result[SDK+'recovery.rs']=import_existing_inverse_field(result[SDK+'recovery.rs'])
    with_recovery=recovery.instrument_exporter(original_export,recovery_resources['exporter'],recovery_resources['qualifier'])
    result[EXPORT]=asset.instrument_exporter(with_recovery,asset.exporter(asset_resources['exporter']),asset_resources['qualifier'])
    return result
