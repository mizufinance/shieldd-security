"""Pure future-stage ASSET_GENERATOR26/1 hash scope; no map source changes."""
from .asset_map_observer import _source


def instrument_balance(data):
    text,newline=_source(data)
    if 'asset_hash_inspection' in text:raise ValueError('asset hash scope already activated')
    anchor='    let hash = params.circuit(map::ASSET_GENERATOR, &[asset.clone()]);'
    if text.count(anchor)!=1:raise ValueError('asset hash exact balance call changed')
    replacement='''    #[cfg(feature = "formal-observer")]
    let asset_hash_scope = crate::hash::asset_hash_inspection::scope(asset);
'''+anchor+'''
    #[cfg(feature = "formal-observer")]
    crate::hash::asset_hash_inspection::finish_scope(asset_hash_scope, &hash);'''
    return text.replace(anchor,replacement).replace('\n',newline).encode()


def instrument_hash(data):
    text,newline=_source(data)
    if 'asset_hash_inspection' in text:raise ValueError('asset hash sink already activated')
    anchors={
        '            let note_call = note_inspection::start(domain, inputs);':
        '            let note_call = note_inspection::start(domain, inputs);\n            let asset_call = asset_hash_inspection::start(domain, inputs);',
        '                note_inspection::state(&note_call, block, after, state);':
        '                note_inspection::state(&note_call, block, after, state);\n                asset_hash_inspection::state(&asset_call, block, after, state);',
        '            note_inspection::finish(note_call, &output);':
        '            note_inspection::finish(note_call, &output);\n            asset_hash_inspection::finish(asset_call, &output);'}
    for old,new in anchors.items():
        if text.count(old)!=1:raise ValueError('asset hash existing sink anchor drift')
        text=text.replace(old,new)
    return ('#[cfg(feature = "formal-observer")]\npub mod asset_hash_inspection;\n'+text).replace('\n',newline).encode()


def compose_observed_balance(data):
    """Retain the current balance relation observer when adding map/hash scopes.

    The fresh combined capture also exposes the existing balance mode. A clean
    fixture lacking those hooks is not a suitable composition base.
    """
    from .asset_map_observer import instrument_balance as map_scope
    text,_=_source(data)
    for anchor in ('pub mod inspection {', 'inspection::record("signed",',
                   'let hash = params.circuit(map::ASSET_GENERATOR, &[asset.clone()]);'):
        if text.count(anchor)!=1:raise ValueError('combined balance existing observer/source anchor drift')
    return instrument_balance(map_scope(data))
