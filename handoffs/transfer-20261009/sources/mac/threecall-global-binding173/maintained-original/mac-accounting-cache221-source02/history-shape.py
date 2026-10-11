def history_shape(identity):
    global _HISTORY_TREE_BYTES
    checked_pin(identity) # NO cache hit is permitted before exact fresh-phase verification.
    key=(identity['path'],identity['bytes'],identity['sha256'])
    if key in _HISTORY_TREES: return _HISTORY_TREES[key]
    h=strict_json(read_pin(identity))
    roots=tuple(h['roots']); entries=[]
    for path,item in h['entries'].items():
        require(item['path']==path,'historical key/path association')
        parents=[i for i,r in enumerate(roots) if path.startswith(r+'/')]
        require(len(parents)==1,'one exact protected historical root')
        parent=parents[0]; relative=path[len(roots[parent])+1:]
        require(relative and not pathlib.PurePosixPath(relative).is_absolute() and '..' not in pathlib.PurePosixPath(relative).parts,'closed historical relative path')
        if 'symlink_target' in item:
            require(set(item)=={'path','symlink_target','target'},'closed historical symlink record')
            target=history_pool(item['target'])
            link=target['path'] if item['symlink_target']==target['path'] else item['symlink_target']
            entries.append((parent,relative,link,target))
        else:
            entries.append((parent,relative,None,history_pool(item)))
    meta=(h['consumed_attempts'],h['consumed_lean_seconds'],
          tuple(history_pool(p) for p in h['receipts']),tuple(h['expected_statuses']))
    aliases=tuple((path,history_pool(identity)) for path,identity in h.get('historical_aliases',{}).items())
    shape=(roots,tuple(entries),tuple(history_pool(p) for p in h.get('parents',[])),meta,aliases)
    charge=history_size((key,shape))
    if len(_HISTORY_TREES)<4096 and _HISTORY_TREE_BYTES+charge<=128*1024*1024:
        _HISTORY_TREES[key]=shape; _HISTORY_TREE_BYTES+=charge
    return shape
