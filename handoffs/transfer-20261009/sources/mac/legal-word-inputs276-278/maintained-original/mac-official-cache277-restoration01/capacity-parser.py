from pathlib import Path,PurePosixPath
import runpy,urllib.request,compression.zstd as z,struct,hashlib,json
ns=runpy.run_path('/tmp/inspect_field_cache275_02.py',run_name='SOURCE_READ_ONLY');missing=ns['missing'];dictionary=urllib.request.urlopen('https://raw.githubusercontent.com/digama0/leangz/v0.1.19/dict/v1.dict',timeout=15).read(2097153)
if len(dictionary)>2097152:raise ValueError('dictionary bound')
dictobj=z.ZstdDict(dictionary);estimates=[]
def require(x,m):
 if not x:raise ValueError(m)
for name,item in missing.items():
 raw=Path(item['archives'][0]).read_bytes();require(raw[:4]==b'LTR3'and len(raw)<=4*1024**2,'fixed bounded archive');position=12;names=[];capacity=0
 def take(n):
  global position
  require(n>=0 and position+n<=len(raw),'exact framing');b=raw[position:position+n];position+=n;return b
 def byte():return take(1)[0]
 def string():
  global position
  end=raw.find(b'\0',position);require(end>=position and end-position<=1024,'bounded terminated string');s=take(end-position).decode();take(1);return s
 def path(indexed=True):
  if indexed:require(byte()==0,'single base root')
  s=string()
  if s:require(not PurePosixPath(s).is_absolute()and '..'not in PurePosixPath(s).parts and s.startswith('./.lake/build/'),'confined build path');names.append(s)
  return s
 def payload():
  global capacity
  code=byte()
  if code==5:path();path()
  if code in [0,1,5]:
   n=struct.unpack('<Q',take(8))[0];data=take(n)
   if code==0:
    d=z.ZstdDecompressor();body=d.decompress(data,max_length=16*1024**2+1);require(d.eof and not d.unused_data and len(body)<=16*1024**2,'bounded ordinary frame');capacity+=len(body)
   else:
    prefix=z.ZstdDecompressor(zstd_dict=dictobj).decompress(data,max_length=16);require(len(prefix)==16,'LGZ prefix');size=struct.unpack('<Q',prefix[8:16])[0];require(size<=16*1024**2,'bounded LGZ capacity');capacity+=size+3*65536
  elif code in [2,3]:take(8);capacity+=1024
  elif code==4:
   take(32)
   while True:
    token=byte()
    if token==0:break
    require(token in[1,2],'closed trace output hash tags');take(8)
   capacity+=4096
  else:raise ValueError('compression '+str(code))
 path(False);payload()
 while position<len(raw):
  if path():payload()
  else:string()
 require(position==len(raw),'EOF');estimates.append({'module':name,'capacity_bound':capacity,'entries':len(names)})
print(json.dumps({'dict_bytes':len(dictionary),'dict_sha256':hashlib.sha256(dictionary).hexdigest(),'archives':len(estimates),'expanded_capacity_bound':sum(v['capacity_bound']for v in estimates),'max':max(v['capacity_bound']for v in estimates),'scope':'Read-only LTR3 framing/Zstd prefix capacity inspection; no extraction or Lean.'}))
