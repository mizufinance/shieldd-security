from pathlib import Path
import json,hashlib,re,ast
J=Path(__file__).resolve().parent;D=J/'windows-tagged-codec-publication-review01';P=D/'packet01';G=J.parent/'shared-build-handoff';owned=json.loads((P/'context/owned-composition-review.json').read_text())['selected']
def pin(p):return dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
mods={'oldSource':('TransferNativeGetterPublication01',G/'handoffs/transfer-20261009/sources/windows/native-getter-publication-20261011-01/native-getter-publication/source/ShielddSecurity/TransferNativeGetterPublication01.lean')};env={'re':re}
for v,(m,p)in mods.items():
 e=next(x for x in owned if x['module']==m);assert all(pin(p)[k]==e['source'][k]for k in ['bytes','sha256']);env[v]=p.read_text()
recipe=P/'qualified/prepare_recipe.py';nodes=ast.parse(recipe.read_text()).body;cut=next(i for i,n in enumerate(nodes)if isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='mkdir');body=[];allowed={'source','names','oldSource','nativeOnly','t','start','end','head','proof'}
for n in nodes[:cut]:
 if isinstance(n,ast.Assign)and all(isinstance(t,(ast.Name,ast.Tuple))for t in n.targets)and all(x.id in allowed for t in n.targets for x in ast.walk(t)if isinstance(x,ast.Name)):
  if isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='read_text':assert n.targets[0].id in mods
  else:body.append(n)
 elif isinstance(n,ast.For)and isinstance(n.iter,ast.Name)and n.iter.id=='names':body.append(n)
 elif isinstance(n,ast.AugAssign)and isinstance(n.target,ast.Name)and n.target.id=='source':body.append(n)
for n in body:
 for c in ast.walk(n):
  if isinstance(c,ast.Call):assert isinstance(c.func,ast.Attribute)and c.func.attr in ['findall','index','replace','split','sub']and ((isinstance(c.func.value,ast.Name)and c.func.value.id in ['re','source','oldSource','nativeOnly','t','head'])or(isinstance(c.func.value,ast.Call)and c.func.attr=='replace'))
exec(compile(ast.Module(body=body,type_ignores=[]),'<pure-native-getter-generation>','exec'),env);S=P/'source/ShielddSecurity/TransferTaggedCodecPublication01.lean';assert env['source']==S.read_text()and len(env['names'])==8;assert not list(P.glob('rejected*'));s=S.read_text();assert '(supportedRoundtrip :'not in s and '(encodeNative :'not in s[s.index('theorem tagged_codec_source_'):]
r=dict(status='PASSED',kind='Independent exact pure maintained source composition and tagged-codec contract review, no Lean execution',source=pin(S),recipe=pin(recipe),review_helper=pin(Path(__file__).resolve()),upstreams=[pin(p)for _,p in mods.values()],fresh_reports=8,scope='Typed NativePending/Other sum injects pending enum and gives exact restored roundtrip by definition; cached tree receives Other tag. Installed getter/source/finalizer model removes caller codec/roundtrip hypotheses. Actual Rust Any/downcast/Clone/cache/type/selector/ownership/OS/full trace correspondence remains owned OPEN. Uses predecessor defined finalizer ordering; later corrected worker source pending independent review',full_transfer='OPEN',native_execution='UNRUN');(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status='PASSED',reports=8)))
