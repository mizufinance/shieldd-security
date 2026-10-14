import gzip
from pathlib import Path
import json,sys
root=Path(__file__).resolve().parent;d=json.loads(gzip.decompress((root/'data.json.gz').read_bytes()));out=Path(sys.argv[1])/'source-root/ShielddSecurity';out.mkdir(parents=True)
for call in d['calls']:
 ci=call['index'];phase=next(x for x in d['phases'] if x['call']==ci and x['round']==2);offset=phase['pivots'][0]-23100
 s=(root/'composition.lean.in').read_text().replace('RoutingParameterHashComposition876',f'VolumePathHashComposition929C{ci}').replace('RoutingParameterHashTail875',f'VolumePathHashTail928C{ci}').replace('RoutingParameterHashCapture873C180B0',f'VolumePathHashCapture926C{ci}B0').replace('396 161393','396 '+str(offset))
 (out/f'VolumePathHashComposition929C{ci}.lean').write_text(s)
