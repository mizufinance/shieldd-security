"""Replay the owned SDK hash model against the actual encryption recipes.

Fresh module names preserve existing proof objects and their import receipts.
Only namespace references and the three identical signed parameter definitions
are redirected. Every proof body is replayed; no object is transported.
"""
import re

PREFIX = 'TransferEncryptionSdk'
RECIPE = 'RuntimeTransferEncryptionHashGroup0'


def generate(census, texts, signatures):
    selected = census['selected']
    assert set(texts) == set(signatures) == set(selected)
    rename = {name:PREFIX+name for name in selected}
    parameters = {record['old_namespace']+'.parameters':record['replacement']
                  for record in census['parameter_tables'].values()}
    assert len(parameters) == 3
    token = re.compile(r'\b('+'|'.join(re.escape(name) for name in sorted(rename,key=len,reverse=True))+r')\b')
    result = {}
    for module in census['order']:
        original = texts[module]
        for old, new in parameters.items():
            original = re.sub(r'\b'+re.escape(old)+r'\b',new,original)
        lines = original.splitlines()
        body = []
        seen_imports = set()
        for index,line in enumerate(lines):
            dependency = re.fullmatch(r'import ShielddSecurity\.([\w.]+)\s*',line)
            if dependency:
                name = dependency[1]
                if name in census['parameter_tables']:
                    name = RECIPE
                else:
                    assert name in selected or name in census['cuts'],name
                    name = rename.get(name,name)
                if name not in seen_imports:
                    body.append('import ShielddSecurity.'+name)
                    seen_imports.add(name)
                continue
            # Regenerate a complete ordered full-signature/standard-axiom audit.
            # This changes printing directives, never a declaration or proof.
            if re.fullmatch(r'#(?:check\s+@|print axioms\s+)[\w.]+\s*',line):
                continue
            if line.strip() == 'set_option pp.all true in':
                next_command = next((x for x in lines[index+1:] if x.strip()),'')
                assert next_command.startswith('#check @')
                continue
            body.append(token.sub(lambda found:rename[found[1]],line))
        source = '\n'.join(body).rstrip()+'\n\n'
        names = [token.sub(lambda found:rename[found[1]],name) for name in signatures[module]]
        assert names and len(names) == len(set(names))
        source += ''.join(f'set_option pp.all true in\n#check @{name}\n#print axioms {name}\n' for name in names)
        for record in census['parameter_tables'].values():
            assert not re.search(r'\b'+re.escape(record['old_namespace'])+r'\b',source)
        assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',source)
        result[rename[module]] = dict(source=source,names=names,origin=module)
    assert len(result) == 12 and sum(len(row['names']) for row in result.values()) == 72
    return result
