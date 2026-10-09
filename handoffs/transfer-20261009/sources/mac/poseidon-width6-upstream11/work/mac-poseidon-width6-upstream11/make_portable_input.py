"""Lossless consumed-data projection of the immutable qualified full descriptor."""
import argparse,hashlib,json
from pathlib import Path
if not __debug__:raise RuntimeError('Optimized Python unsupported')
a=argparse.ArgumentParser();a.add_argument('--descriptor',type=Path,required=True);a.add_argument('--output',type=Path,required=True);args=a.parse_args();raw=args.descriptor.read_bytes();full=hashlib.sha256(raw).hexdigest();assert full=='3be245c6c55f473352481dbbc43d876591f8bbcedb61bd9c9c633de785112d6e';p=json.loads(raw)
c={k:p[k] for k in ['runtime_sha','modulus','parameter_sha256','parameters','input_ports','input_terms','prefix_scopes']}
c.update(schema='upstream11-portable-generation-v1',full_descriptor_sha256=full,qualified_inputs=p['qualified_inputs'],raw_program_identity=p['raw_program_identity'],ordinary_relation_identity=p['ordinary_relation_identity'])
c['indexed_original_rows']=[{k:r[k] for k in ['capture_index','a','b']} for r in p['indexed_original_rows']]
c['blocks']=[]
for b in p['blocks']:
 cb={k:b[k] for k in ['block','node_span','before_absorption','absorbed','chunk']};cb['rounds']=[]
 for r in b['rounds']:
  cr={k:r[k] for k in ['round','row_indices']};cr['ports']={}
  if r['round']==2:cr['ports']['before']=r['ports']['before']
  if r['round']==64:cr['ports']['after']=r['ports']['after']
  cb['rounds'].append(cr)
 c['blocks'].append(cb)
c['translations']=[{k:t[k] for k in ['block','column_offset','tail_indices']} for t in p['translations']]
result=(json.dumps(c,sort_keys=True,separators=(',',':'))+'\n').encode();assert hashlib.sha256(result).hexdigest()=='74189456aa7380c35040e1c67d3b9d3ad48ce75d332ac80ad44971f1c0812ab9'
if args.output.exists():assert args.output.read_bytes()==result
else:args.output.write_bytes(result)
print(json.dumps(dict(status='passed',bytes=len(result),sha256=hashlib.sha256(result).hexdigest(),full_local_descriptor_sha256=full)))
