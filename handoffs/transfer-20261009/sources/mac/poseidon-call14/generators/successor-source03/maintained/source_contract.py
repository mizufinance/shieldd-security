"""Closed maintained directory and conservative transitive Lean source guards."""
import hashlib,json,re
from pathlib import Path
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def closed(directory,inventory,executing):
    declared=inventory['maintained_files']
    found={p.name for p in directory.iterdir()}
    assert found==set(declared),'maintained directory is not exactly closed'
    for name,entry in declared.items():
        path=directory/name
        assert path.is_file() and not path.is_symlink(),'directory/symlink refused: '+name
        assert path.stat().st_size==entry['bytes'] and sha(path)==entry['sha256'],'maintained identity mismatch: '+name
    assert executing.resolve().parent==directory.resolve()
    assert executing.name in declared and sha(executing)==declared[executing.name]['sha256'],'executing recipe identity'
def code_without_comments(text):
    result=[];i=0;depth=0
    while i<len(text):
        if text[i:i+2]=='/-':depth+=1;i+=2
        elif depth and text[i:i+2]=='-/':depth-=1;i+=2
        elif not depth and text[i:i+2]=='--':
            end=text.find('\n',i);i=len(text) if end<0 else end
        else:
            if not depth or text[i]=='\n':result.append(text[i])
            i+=1
    assert depth==0,'unclosed comment'
    return ''.join(result)
def safe_lean(text):
    code=code_without_comments(text)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b|\+\s*native\b|\bLean\.ofReduceBool\b|\bdebug\.skipKernelTC\b',code),'refused Lean code token'
def audit_names(source,command):
    namespace='';stack=[];result=[]
    for line in source.read_text().splitlines():
        match=re.match(r'^namespace (\S+)',line)
        if match:
            stack.append(namespace);namespace=(namespace+'.' if namespace else '')+match.group(1)
        if re.match(r'^end(?: |$)',line):namespace=stack.pop() if stack else ''
        match=re.match(command,line)
        if match:
            name=match.group(1)
            result.append(name if name.startswith('ShielddSecurity.') else namespace+'.'+name)
    assert len(result)==len(set(result)),'duplicate audit name'
    return result
