"""Hash imported official source/object closure, including split olean artifacts."""
import hashlib,json,re,subprocess
from pathlib import Path

def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as stream:
        while raw:=stream.read(1024**2):h.update(raw)
    return h.hexdigest()

def freeze_external(project,custom_sources):
    packages=json.loads((project/'lake-manifest.json').read_text())['packages']
    roots=[];revisions={}
    for package in packages:
        root=project/'.lake/packages'/package['name']
        actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
        assert actual==package['rev'],'official package revision changed'
        assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],
            cwd=root,text=True).strip(),'official package tracked source modified'
        revisions[package['name']]=actual
        roots.append((package['name'],root,root,root/'.lake/build/lib/lean'))
    toolchain=Path.home()/'.elan/toolchains/leanprover--lean4---v4.30.0'
    roots.append(('lean4',toolchain,toolchain/'src/lean',toolchain/'lib/lean'))
    pattern=r'^(?:(?:public|private)\s+)?(?:meta\s+)?import\s+([^\n]+)'
    def remove_comments(text):
        result=[];i=0;depth=0
        while i<len(text):
            if text[i:i+2]=='/-':depth+=1;i+=2
            elif depth and text[i:i+2]=='-/':depth-=1;i+=2
            elif not depth and text[i:i+2]=='--':
                end=text.find('\n',i);i=len(text) if end<0 else end
            else:
                if not depth or text[i]=='\n':result.append(text[i])
                i+=1
        return ''.join(result)
    def imports(source):
        return [word for line in re.findall(pattern,remove_comments(source.read_text()),re.M)
                for word in line.split() if word!='all']
    pending=['Init']
    for source in custom_sources:pending+=imports(source)
    seen=set();files={}
    while pending:
        name=pending.pop()
        if name in seen or name.startswith('ShielddSecurity.'):continue
        seen.add(name)
        relative=Path(name.replace('.','/'))
        options=[entry for entry in roots if (entry[2]/relative.with_suffix('.lean')).is_file()]
        assert len(options)==1,'ambiguous/missing official import '+name
        label,root,sources,objects=options[0]
        source=sources/relative.with_suffix('.lean')
        obj=objects/relative.with_suffix('.olean')
        assert obj.is_file(),'missing official object '+name
        metadata=objects/relative.with_suffix('.ilean')
        assert metadata.is_file(),'missing official import metadata '+name
        declared=json.loads(metadata.read_text())
        assert declared['module']==name,'official import metadata module mismatch'
        assert all(type(row) is list and len(row)==4 and type(row[0]) is str
            for row in declared['directImports']),'official direct imports malformed'
        paths=[source,obj,metadata]+[path for suffix in ['.olean.private','.olean.server']
                            if (path:=objects/relative.with_suffix(suffix)).exists()]
        for path in paths:files[label+'/'+str(path.relative_to(root))]=digest(path)
        pending+=[row[0] for row in declared['directImports']]
        assert len(seen)<=10000 and len(pending)<=50000,'official closure finite guard'
    for name in ['lean','lake']:
        path=toolchain/'bin'/name
        files['lean4/bin/'+name]=digest(path)
    return dict(revisions=revisions,modules=len(seen),files=files,
        official_prebuilt_objects='reused and hashed, not locally rebuilt')
