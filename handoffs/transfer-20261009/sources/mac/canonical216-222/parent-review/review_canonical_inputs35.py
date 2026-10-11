"""Independently parse all concrete comparison literals against frozen exact capture DATA."""
from pathlib import Path
import json,hashlib,re,zlib
J=Path(__file__).resolve().parent;W=J.parent;D=J/'canonical216-222-review01';P=W/'mac-canonical216-222-kernel-result01';G=W/'shared-build-handoff';Q=W/'mac-canonical-comparisons216-data01';p=52435875175126190479447740508185965837690552500527637822603658699938581184513
def pin(f):
 b=f.read_bytes();return dict(path=str(f),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
assert(Q/'selected-data01.json.zlib').read_bytes()==(D/'data-replay01/selected-data01.json.zlib').read_bytes()
raw=zlib.decompress((Q/'selected-data01.json.zlib').read_bytes());q=json.loads((Q/'qualification01.json').read_text());assert len(raw)==q['decoded_bytes']and hashlib.sha256(raw).hexdigest()==q['decoded_sha256'];data=json.loads(raw);assert len(data['chains'])==14
mods=json.loads((P/'source-object-receipt01.json').read_text());fresh={e['module']:Path(e['source']['path'])for e in mods};pub=json.loads((J/'source-integration-20261011-01/mac-source-closure1562.json').read_text())['custom_sources'];checked={}
def source(name):
 if name in fresh:f=fresh[name]
 else:
  v=pub[name];f=G/v['published_paths'][0];assert len(f.read_bytes())==v['bytes']and hashlib.sha256(f.read_bytes()).hexdigest()==v['sha256']
 checked[name]=pin(f);return f.read_text()
def linear(x):
 out={}
 for col,value in x:out[col]=(out.get(col,0)+value)%p
 return sorted([[c,v]for c,v in out.items()if v])
def entries(s):
 expression=re.search(r'^def entries : List Entry := ([\s\S]*?)(?=\n(?:def|noncomputable def|theorem))',s,re.M)[1].strip();assert expression.startswith('[⟨')
 expression=re.sub(r'\(\(p:Int\)-([0-9]+)\)',lambda m:str(p-int(m[1])),expression);expression=expression.translate(str.maketrans({'⟨':'[','⟩':']','(':'[',')':']'}));return json.loads(expression)
chains=[];literal_modules=0
for c in data['chains']:
 word=c['word_index'];name=f'CapturedCanonical216W{word:02}';root=source(name)
 if word==3:
  old=source('CapturedValueComparison105');parts=re.findall(r'^private abbrev E\d := ([\w.]+)\.entries',old,re.M);assert len(parts)==8
  chosen=sum((entries(source(x))for x in parts),[])
 else:
  parts=re.findall(r'^private abbrev E\d := ([\w.]+)\.entries',root,re.M);assert parts==[name+f'C{i:02}'for i in range(8)]
  chosen=[]
  for i,part in enumerate(parts):
   t=source(part);xs=entries(t);assert len(xs)==(32 if i<7 else 30)
   m=re.search(r'CompilerRowSlice63.check CapturedFullArithmetic52.rowAt (\d+) (\d+) actualRows',t);assert m and(int(m[1]),int(m[2]))==(c['row_start']+64*i,2*len(xs));chosen+=xs;literal_modules+=1
 assert len(chosen)==len(c['entries'])==254
 for actual,expected in zip(chosen,c['entries']):
  col,bit,before,after,pivot,aux,rows=actual;assert(col,bit,pivot,aux)==(expected['bitColumn'],expected['maximumBit'],expected['pivot'],expected['auxiliary']);assert linear(before)==linear(expected['before'])and linear(after)==linear(expected['after']);assert len(rows)==2
  for row,e in zip(rows,expected['rows']):assert linear(row[0])==linear(e['a'])and linear(row[1])==linear(e['b'])
 assert f'CanonicalWord215.columns {c["slot"]["start"]} entries=WordHints210.columns Word'in root
 assert f'CapturedFullAssertions54.recipeAt {c["terminal"]["position"]}=some (true,.linear [(0,1)] sourceOutput)'in root
 output=re.search(r'^def sourceOutput : Linear := (.*)$',root,re.M)[1];output=re.sub(r'\(\(p:Int\)-([0-9]+)\)',lambda m:str(p-int(m[1])),output);output=json.loads(output.replace('(','[').replace(')',']'));assert linear(output)==linear(c['terminal']['raw_output'])
 maximum=re.search(r'change binary (\[[^\n]*\])=p-1',root)[1];bits=json.loads(maximum);assert len(bits)==255 and sum(int(b)<<i for i,b in enumerate(bits))==p-1
 assert f'(one : rho 0=1)'in root and f'(n:F)=rho {c["slot"]["value"]}'in root
 chains.append(dict(module=name,value_column=c['slot']['value'],bit_start=c['slot']['start'],word_index=word,row_start=c['row_start'],arithmetic_rows=c['row_count'],terminal_position=c['terminal']['position']))
assert literal_modules==104 and sum(c['arithmetic_rows']for c in chains)==7112
collector=source('CanonicalInputs222');columns=json.loads(re.search(r'^def columns : List Nat := (.*)$',collector,re.M)[1]);assert columns==[c['value_column']for c in chains];assert re.findall(r'(CapturedCanonical216W\d+).sound rho satisfied one',collector)==[c['module']for c in chains]
scope='All fourteen actual 255-bit word comparisons: exact 32130 captured source nodes, 7112 arithmetic rows and fourteen terminal assertions independently regenerated from frozen read-only capture; every literal entry/body/row slice/port/max(p-1)/word-column binding parsed independently against that DATA, including prior W03 leaves. Full captured SAT and rho0=1 derive bounded natural representatives and casts without caller terminal/max/canonical premises. One shared collector defines their chosen values, uniqueness and relation to a lawful canonical representation. Actual field/representation instance, full concrete crypto/row interpretation, all legal-input witness construction, native correspondence and full Transfer remain owned OPEN.'
report=dict(status='PASSED',kind='Independent exact captured DATA replay and literal/source semantic association; no Lean/native execution',modules=120,reports=1153,concrete_words=14,slices=104,arithmetic_rows=7112,source_nodes=32130,terminal_assertions=14,chains=chains,source_pins=checked,original_data=pin(Q/'selected-data01.json.zlib'),replay_data=pin(D/'data-replay01/selected-data01.json.zlib'),scope=scope,full_transfer='OPEN');(D/'source-semantic-review01.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(status='PASSED',words=14,arithmetic_rows=7112,terminals=14,source_pins=len(checked))))
