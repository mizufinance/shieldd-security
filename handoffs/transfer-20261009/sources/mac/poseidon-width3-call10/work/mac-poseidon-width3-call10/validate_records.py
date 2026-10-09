"""Reject inconsistent raw source and compiler-certificate records before export."""
def validate_node(node):
    certificate=node['certificate'];constructor=certificate['constructor'];operation=node['operation']
    if certificate['node']!=node['source_node'] or certificate['left']!=node['left'] or certificate['right']!=node['right']:
        raise ValueError('raw source/certificate node or operand mismatch')
    if operation=='add':
        if constructor!='add':raise ValueError('raw add requires add certificate')
    elif operation=='mul':
        if constructor not in ['foldedLeft','foldedRight','deferred','square','product']:
            raise ValueError('raw mul requires multiplication certificate')
    else:raise ValueError('unknown source operation')
    expected={'add':0,'foldedLeft':0,'foldedRight':0,'deferred':0,'square':1,'product':2}[constructor]
    rows=certificate['rows']
    if len(rows)!=expected or len(set(rows))!=expected or any(type(i) is not int or i<0 for i in rows):
        raise ValueError('compiler row shape mismatch')
    if constructor=='foldedLeft' and node['left'][0]!=0:raise ValueError('foldedLeft constant port mismatch')
    if constructor=='foldedRight' and node['right'][0]!=0:raise ValueError('foldedRight constant port mismatch')
