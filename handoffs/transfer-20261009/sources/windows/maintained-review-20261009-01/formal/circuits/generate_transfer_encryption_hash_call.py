"""Emit finite soundness modules for one fully captured encryption hash call."""
from . import transfer_encryption_hash_union as bundle, transfer_note_hash as hashes
from . import transfer_note_hash_join as joins, transfer_relation as relation


def generate(manifest_data,page_data,extracted,accepted_roles,parameter_root,call_index):
    call_index=relation.natural(call_index,24)
    bundle.validate(manifest_data,page_data,extracted,accepted_roles,parameter_root)
    ordinal=call_index+1
    checked=next(item for index,item in bundle.checked_pages(manifest_data,page_data,accepted_roles,parameter_root)
                 if index==ordinal)
    selected=hashes._select_permutation(checked,extracted['parts'][str(ordinal)],parameter_root,role_prefix='remaining')
    assert checked['block']==0 and len(checked['metadata']['hash']['blocks'])==1
    domain=checked['metadata']['hash']['domain']
    base=f'RuntimeTransferEncryptionHash{call_index}Domain{domain}'
    return joins._generate_checked([checked],[selected],base,
        linear_declarations_per_module=32,width=checked['graph']['width'])
