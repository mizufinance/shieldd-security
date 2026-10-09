"""Exact fresh-source hooks over retained recovery02 and observed hash65 bytes."""


def replace_once(text,old,new):
    if text.count(old)!=1:raise ValueError('recovery hash exact source anchor drift')
    return text.replace(old,new)


def instrument_recovery(data):
    if not isinstance(data,bytes) or b'hash_inspection' in data:raise ValueError('fresh recovery hash source required')
    text=data.decode().replace('\r\n','\n')
    text=replace_once(text,'pub mod capsule_inspection;','pub mod capsule_inspection;\n#[cfg(feature = "formal-observer")]\npub mod hash_inspection;')
    text=replace_once(text,'    let _capsule_scope = capsule_inspection::scope();',
        '    let _capsule_scope = capsule_inspection::scope();\n    #[cfg(feature = "formal-observer")]\n    let _recovery_hash_scope = hash_inspection::scope();')
    return text.encode()


def instrument_hash(data):
    if not isinstance(data,bytes) or b'recovery::hash_inspection' in data:raise ValueError('fresh observed hash source required')
    text=data.decode().replace('\r\n','\n')
    for old,new in [
        ('            let output_call = crate::note::output_hash_inspection::start(domain, inputs);',
         '            let output_call = crate::note::output_hash_inspection::start(domain, inputs);\n            let recovery_call = crate::recovery::hash_inspection::start(domain, inputs);'),
        ('                crate::note::output_hash_inspection::state(&output_call, block, after, state);',
         '                crate::note::output_hash_inspection::state(&output_call, block, after, state);\n                crate::recovery::hash_inspection::state(&recovery_call, block, after, state);'),
        ('            crate::note::output_hash_inspection::finish(output_call, &output);',
         '            crate::note::output_hash_inspection::finish(output_call, &output);\n            crate::recovery::hash_inspection::finish(recovery_call, &output);')]:
        text=replace_once(text,old,new)
    return text.encode()
