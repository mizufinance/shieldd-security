def accounting_history_aliases(identity):
    # Metadata shape is byte-pinned before reuse; no source/object bytes cached.
    shape=history_shape(identity); roots,items,parents,_=shape[:4]
    result={}
    for parent in parents: result.update(accounting_history_aliases(parent))
    for path,target in shape[4]: result[path]=target
    return result

def bytes_in(root, aliases):
    root=os.fspath(root); total=metadata=0
    if os.path.exists(root):
        pending=[(root,())]
        while pending:
            directory,parts=pending.pop()
            with os.scandir(directory) as items:
                for item in items:
                    st=item.stat(follow_symlinks=False); relative=parts+(item.name,)
                    if stat.S_ISLNK(st.st_mode):
                        require(item.path in aliases and os.readlink(item.path)==aliases[item.path]['path'], 'unapproved batch symlink')
                        total+=st.st_size
                    elif stat.S_ISDIR(st.st_mode): pending.append((item.path,relative))
                    elif stat.S_ISREG(st.st_mode):
                        total+=st.st_size
                        if 'runtime' in relative or pathlib.PurePath(item.name).suffix in {'.json','.jsonl','.log','.stdout','.stderr'}: metadata+=st.st_size
    return total,metadata

