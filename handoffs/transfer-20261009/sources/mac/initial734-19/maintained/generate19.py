"""SOURCE19 only: bounded extraction, symbolic emission, no prover/subprocess."""
import argparse, ast, hashlib, json, re, sqlite3, struct, sys, zlib
from pathlib import Path

def require(ok, why):
    if not ok: raise ValueError(why)
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize, 'use -I -B -S without -O')
P=52435875175126190479447740508185965837690552500527637822603658699938581184513
COPY=200692
RUNTIME='844389ee069e1fb2e576708842d0b389b4d9a44a'
CANONICAL='cec1b30defc23497c8e9b30528dca12b09d328ea'
def sha(b): return hashlib.sha256(b).hexdigest()
def rec(p):
    p=Path(p).resolve(); b=p.read_bytes(); return dict(path=str(p),bytes=len(b),sha256=sha(b))
def canon(ts):
    out={}
    for c,k in ts: out[c]=(out.get(c,0)+k)%P
    return sorted([[c,k] for c,k in out.items() if k])
def valid(ts):
    return all(type(c) is int and type(k) is int and 0<=c<262144 and 0<k<P for c,k in ts) and all(ts[i][0]<ts[i+1][0] for i in range(len(ts)-1))
def unique(xs):
    d={}
    for k,v in xs: require(k not in d,'duplicate JSON');d[k]=v
    return d
def bounded_json(p):
    z=zlib.decompressobj();b=z.decompress(Path(p).read_bytes(),1048577)
    require(len(b)<=1048576 and z.eof and not z.unused_data and not z.unconsumed_tail,'DATA framing/size')
    require(b.endswith(b'\n') and b.count(b'\n')==1,'single JSON line')
    return json.loads(b[:-1],object_pairs_hook=unique)
def literal(p):
    text=Path(p).read_text();body=text.split('noncomputable def rows : List Row := [',1)[1].split('\n]\n',1)[0]
    rows=[]
    for line in body.splitlines():
        line=line.strip().rstrip(',')
        if not line: continue
        require(line.startswith('⟨') and line.endswith('⟩'),'literal syntax')
        a,b=ast.literal_eval('('+line[1:-1]+')');rows.append(dict(a=[list(t) for t in a],b=[list(t) for t in b]))
    return rows

def extract(root):
    cap=root/'work/parent-full-program/capture';db=cap/'lowering-resume01.sqlite';spool=cap/'ordinary01.rows'
    stat=lambda p:[p.stat().st_size,p.stat().st_mtime_ns,p.stat().st_ino]
    before={str(p):stat(p) for p in (db,spool)}
    require(before[str(db)][0]==3070353408 and before[str(spool)][0]==86250856,'qualified sizes')
    boundary=root/'work/mac-captured-transfer-boundary17-source01/selected-data01.json'
    q=json.loads(boundary.read_bytes());require(q['runtime_sha']==RUNTIME and q['binary']['sha256']=='5f28e65e804c05828a6cd66515293e28af77a502e4b066f05d162ae33e4ca0c9' and q['database']['qualified_historical_sha256']=='da9026b92d643ea8cddaf560b06bc783b291f152f799b48cc836290f57ed9f7d','capture ancestry')
    lock=root/'work/shared-build-handoff/shieldd.lock';lk=json.loads(lock.read_bytes());require(lk['sha']==lk['ref']==RUNTIME,'runtime lock')
    source16=root/'work/parent-prior-row-frame16-source01/source02/ShielddSecurity';stored=[];pins={}
    for n in ['Generic01','Chunk01','Chunk02','Chunk03','Chunk04','Chunk05','Frame01']:
        p=source16/('CapturedPriorRows16'+n+'.lean');pins[p.stem]=rec(p)
        if n.startswith('Chunk'):stored+=literal(p)
    require(len(stored)==734,'exact SOURCE16 domain')
    co=sqlite3.connect('file:'+str(db)+'?mode=ro',uri=True);co.execute('PRAGMA query_only=ON');co.execute('PRAGMA cache_size=-8192')
    try:
        entries=list(co.execute('SELECT id,a,b,origin FROM rows WHERE id<734 ORDER BY id'))
        require([x[0] for x in entries]==list(range(734)),'DB every-position')
        rows=[dict(a=json.loads(a),b=json.loads(b)) for i,a,b,o in entries]
        require(rows==stored and all(valid(x[k]) for x in rows for k in ('a','b')),'SOURCE16 DB bodies')
        materialized={};w=[];counts={'square':0,'product':0}
        def lc(k,i):
            if k==0:return canon([[0,int(co.execute('SELECT value FROM constants WHERE id=?',(i,)).fetchone()[0])]])
            if k==1:return [[3+i,1]]
            require(k==2,'operand tag');kind,terms=co.execute('SELECT kind,terms FROM nodes WHERE id=?',(i,)).fetchone();require(kind=='linear','linear operand');return json.loads(terms)
        for i,a,b,o in entries:
            origin=json.loads(o);require(origin['kind']=='node','no assertion premises')
            node=origin['id']
            if node in materialized:continue
            op,l,li,rr,ri,terms,cert=co.execute('SELECT op,lk,li,rk,ri,terms,certificate FROM nodes WHERE id=?',(node,)).fetchone()
            cert=json.loads(cert);output=json.loads(terms);left,right=lc(l,li),lc(rr,ri)
            require(op=='mul' and cert['node']==node and cert['left']==[l,li] and cert['right']==[rr,ri] and cert['rows'][0]==i,'raw certificate agreement')
            pivot=output[0][0];require(output[0][1]==1,'unit output pivot');rest=output[1:]
            if cert['constructor']=='square':
                require(left==right and cert['rows']==[i],'square source/indices');expected=[dict(a=canon(left),b=canon(output))];writes=[pivot]
            else:
                require(cert['constructor']=='product' and cert['rows']==[i,i+1] and len(cert['auxiliary'])==1,'product shape')
                aux,one=cert['auxiliary'][0];require(one==1 and aux==pivot+1,'auxiliary window')
                expected=[dict(a=canon(left+[[c,-k] for c,k in right]),b=[[aux,1]]),dict(a=canon(left+right),b=canon([[c,4*k] for c,k in output]+[[aux,1]]))];writes=[pivot,aux]
            require(expected==rows[i:i+len(expected)] and all(c<pivot for c,k in left+right+rest),'actual equations/freshness')
            counts[cert['constructor']]+=1;w+=writes;materialized[node]=dict(indices=cert['rows'],writes=writes,raw_sha256=sha(json.dumps([op,l,li,rr,ri,output,cert],separators=(',',':')).encode()))
        require(w==list(range(22738,23472)) and counts=={'square':238,'product':248},'all writes/counts')
    finally:co.close()
    h=hashlib.sha256();consumed=0
    with spool.open('rb') as f:
        def exact(n):
            nonlocal consumed
            b=f.read(n);require(len(b)==n,'truncated stream');h.update(b);consumed+=n;return b
        for i in range(734):
            actual={}
            for side in ('a','b'):
                n=struct.unpack('>Q',exact(8))[0];require(n<=32768,'term bound');raw=exact(36*n)
                ts=[[int.from_bytes(raw[o:o+4],'big'),int.from_bytes(raw[o+4:o+36],'big')] for o in range(0,len(raw),36)]
                require(valid(ts),'binary canonical framing');actual[side]=ts
            require(actual=={k:canon([[COPY if c==0 else c,v] for c,v in rows[i][k]]) for k in ('a','b')},'independent outlined row '+str(i))
    def swap(start,width,offset,c):
        return c+offset if start<=c<start+width else c-offset if start+offset<=c<start+offset+width else c
    for block,off in [(1,9),(2,21),(3,28)]:
        def rename(c):return swap(22738,64,64*block,swap(14,7,off,c))
        require([dict(a=canon([[rename(c),k] for c,k in row['a']]),b=canon([[rename(c),k] for c,k in row['b']])) for row in rows[:64]]==rows[64*block:64*(block+1)],'exact subgroup renaming')
    require({str(p):stat(p) for p in (db,spool)}==before,'capture changed')
    audit18=root/'work/mac-prior-registered-audit18-source01/source-root/ShielddSecurity/CapturedPriorRows18RegisteredAudit01.lean';pins[audit18.stem]=rec(audit18)
    join=root/'work/mac-poseidon-threecall-join15-source02/source-root/ShielddSecurity'
    for p in sorted(join.glob('*.lean')):pins[p.stem]=rec(p)
    inherited=json.loads((root/'work/mac-poseidon-threecall-join15-source02/inherited-closure01.json').read_bytes())['modules']
    # Extra qualified roots supplement the existing byte-qualified inherited DAG.
    for name,receipt in [('TransferFirstSubgroupCompletion01','outputs/mac-connected-subgroup02/build-TransferFirstSubgroupCompletion01-01.json'),('CompilerWindowRenaming05','outputs/mac-poseidon-rename05/build-CompilerWindowRenaming05-02.json')]:
        rp=root/receipt;d=json.loads(rp.read_bytes());cmd=d['command'];s=rec(cmd[-1]);ob=rec(cmd[cmd.index('-o')+1]);require(d['status']=='passed' and type(d['exit']) is int and d['exit']==0 and s['sha256']==d['source_sha256'] and ob['sha256']==d['object_sha256'],'qualified root')
        inherited[name]=dict(source=s,object=ob,receipt=rec(rp),parts={},fresh_execution_credit=0,legacy_signature_inventory_absent='full_signature_sha256' not in d)
        for full,binding in d['frozen_imports'].items():
            if not full.startswith('ShielddSecurity.'):continue
            dep=full.split('.')[-1]
            if dep in inherited:
                require(inherited[dep]['source']['sha256']==binding['source_sha256'],'inherited source agreement '+dep)
                continue
            matches=[]
            for folder in ('mac-connected-subgroup02','mac-connected-subgroup01','mac-poseidon-rename05'):
                for candidate in (root/'outputs'/folder).glob('build-'+dep+'-*.json'):
                    entry=json.loads(candidate.read_bytes())
                    if entry.get('status')=='passed' and entry.get('source_sha256')==binding['source_sha256']:
                        command=entry['command'];src=rec(command[-1]);obj=rec(command[command.index('-o')+1])
                        if obj['sha256']==entry['object_sha256'] and src['sha256']==entry['source_sha256']:matches.append((src,obj,rec(candidate),entry))
            require(matches,'qualified missing import '+dep);src,obj,receipt,entry=matches[0]
            inherited[dep]=dict(source=src,object=obj,receipt=receipt,parts={},fresh_execution_credit=0,legacy_signature_inventory_absent='full_signature_sha256' not in entry)
    inherited_ref=rec(root/'work/mac-poseidon-threecall-join15-source02/inherited-closure01.json')
    existing=json.loads(Path(inherited_ref['path']).read_bytes())['modules']
    extra={k:v for k,v in inherited.items() if k not in existing}
    row_ranges=[]
    for low,count in [(0,64),(64,64),(128,64),(192,64),(256,66),(322,412)]:
        selected=entries[low:low+count]
        row_ranges.append(dict(start=low,count=count,bodies_sha256=sha(json.dumps(rows[low:low+count],separators=(',',':')).encode()),cells_sha256=sha(b''.join(a+b+o for i,a,b,o in selected))))
    materialized_digest=sha(json.dumps(materialized,sort_keys=True,separators=(',',':')).encode())
    return dict(schema='SOURCE19-DATA-only',runtime=RUNTIME,canonical=CANONICAL,p=P,copy=COPY,source_only=pins,inherited_reference=inherited_ref,extra_inherited=extra,lock=rec(lock),capture_ancestry=rec(boundary),database=dict(path=str(db),historical_sha256=q['database']['qualified_historical_sha256'],stat=before[str(db)],fresh_hash=False,cache_MiB=8),binary=dict(path=str(spool),qualified_sha256=q['binary']['sha256'],stat=before[str(spool)],prefix_bytes=consumed,prefix_sha256=h.hexdigest(),fresh_full_hash=False),row_ranges=row_ranges,materialized_digest=materialized_digest,counts=counts,write_interval=[22738,23472],renamings=[[14,7,9,22738,64,64],[14,7,21,22738,64,128],[14,7,28,22738,64,192]],scope='DATA replay only; all SOURCE16/18/19/Join15 modules UNRUN. No assertion truth, native or full-relation proof.')

HEADER='''-- GENERATED by generate19.py; edit maintained source and regenerate.
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
'''
GENERIC='''import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CompilerSegmentCompletion11
import ShielddSecurity.CompilerIndexed01
@HEADER@
namespace ShielddSecurity.CapturedInitial73419Generic01
open Compiler CompilerCompletion CompilerIndexed01 CompilerSegmentCompletion11
def p : Nat := @P@
def copy : Nat := 200692
def normalized (rows : List Row) : List Row := unoutlineRows copy rows
def matchRows (target source : List Row) : Bool :=
  checkOriginalCoverage p 0 target.toArray source.toArray (List.range target.length).toArray
def outlined (rows : List Row) : List Row := rows.map (fun row =>
  ⟨canonical p (CompilerColumnRenaming05.linear (fun c => if c=0 then copy else c) row.a),
   canonical p (CompilerColumnRenaming05.linear (fun c => if c=0 then copy else c) row.b)⟩)
def writeCheck (low high : Nat) (steps : List Step) : Bool :=
  (PoseidonCompletion.writes steps).all (fun c => decide (low≤c ∧ c<high))
def supportCheck (high : Nat) (rows : List Row) : Bool :=
  rows.all (fun row => (row.a++row.b).all (fun term => decide (term.1<high ∨ term.1=copy)))
variable {F : Type} [Field F] [CharP F p]
theorem transfer (target source : List Row) (checked : matchRows target source=true)
    (rho : Nat → F) (satisfied : Satisfies rho source) : Satisfies rho target := by
  have coverage := checked_inclusion p target.toArray source.toArray
    (List.range target.length).toArray checked
  intro actual member
  obtain ⟨expected,present,left,right⟩ := coverage actual (by simpa using member)
  have result := satisfied expected (by simpa using present)
  rw [←canonical_equal rho _ _ left,←canonical_equal rho _ _ right] at result
  exact result
omit [CharP F p] in
theorem normalized_satisfied (rows : List Row) (rho : Nat → F)
    (linked : rho copy=rho 0) (satisfied : Satisfies rho rows) : Satisfies rho (normalized rows) := by
  intro value member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  simpa only [eval_unoutline rho copy _ linked] using satisfied original present
theorem outlined_satisfied (rows : List Row) (rho : Nat → F)
    (linked : rho copy=rho 0) (satisfied : Satisfies rho rows) : Satisfies rho (outlined rows) := by
  have same : (fun c => rho (if c=0 then copy else c))=rho := by
    funext c
    by_cases zero : c=0
    · simp [zero,linked]
    · simp [zero]
  intro value member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  simpa only [eval_canonical,CompilerColumnRenaming05.eval_linear,same] using satisfied original present
def makeSegment (steps : List Step) (rows : List Row) (low high : Nat)
    (writes : writeCheck low high steps=true) (support : supportCheck high rows=true)
    (complete : ∀ base : Nat → F,base copy=base 0 → Satisfies (run base steps) rows) : Segment F copy where
  steps := steps
  rows := rows
  low := low
  high := high
  writes := by
    intro c member
    exact of_decide_eq_true (List.all_eq_true.mp writes c member)
  support := by
    intro row member term present
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp support row member) term present)
  complete := complete
end ShielddSecurity.CapturedInitial73419Generic01
'''
SUBGROUP='''import ShielddSecurity.CapturedInitial73419Generic01
import ShielddSecurity.TransferFirstSubgroupCompletion01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CapturedPriorRows16Chunk01
@HEADER@
namespace ShielddSecurity.CapturedInitial73419Subgroups01
open Compiler CompilerCompletion CapturedInitial73419Generic01 CompilerSegmentCompletion11
def firstSteps : List Step := TransferFirstSubgroupData01.materializedSteps
def firstOriginal : List Row := TransferFirstSubgroupData01.arithmeticRows.toList.take 64
def firstRows : List Row := CapturedPriorRows16Chunk01.rows.take 64
variable {F : Type} [Field F] [CharP F p]
theorem first_direct_complete (base : Nat → F) (linked : base copy=base 0) :
    Satisfies (run base firstSteps) firstOriginal := by
  have result := (original_rows_complete base TransferFirstSubgroupData01.arithmeticSteps [0,copy]
    TransferFirstSubgroupData01.arithmeticRows.toList copy
    TransferFirstSubgroupCompletion01.ordered (TransferFirstSubgroupCompletion01.legal base)
    (by simp) (by simp) linked TransferFirstSubgroupCertificates01.arithmetic_reverse_coverage).1
  have same : run base TransferFirstSubgroupData01.arithmeticSteps=run base firstSteps := by
    unfold TransferFirstSubgroupData01.arithmeticSteps firstSteps
    rw [CompilerSequenceCompletion.run_append]
    rfl
  rw [same] at result
  intro row member
  exact result row (List.mem_of_mem_take member)
theorem first_match : matchRows firstRows (normalized firstOriginal)=true := by decide +kernel
theorem first_writes : writeCheck 22738 22802 firstSteps=true := by decide +kernel
theorem first_support : supportCheck 22802 firstRows=true := by decide +kernel
def firstSegment : Segment F copy := makeSegment firstSteps firstRows 22738 22802 first_writes first_support (by
  intro base linked
  have writes : ∀ c∈PoseidonCompletion.writes firstSteps,22738≤c ∧ c<22802 := by
    intro c member;exact of_decide_eq_true (List.all_eq_true.mp first_writes c member)
  have fixed (c : Nat) (outside : c<22738 ∨ 22802≤c) : run base firstSteps c=base c := by
    apply PoseidonCompletion.run_outside
    intro member;have bounds:=writes c member;omega
  apply transfer firstRows (normalized firstOriginal) first_match
  apply normalized_satisfied firstOriginal _
  · rw [fixed copy (Or.inr (by decide)),fixed 0 (Or.inl (by decide))];exact linked
  · exact first_direct_complete base linked)
@RENAMINGS@
def prefix1 : Segment F copy := append copy firstSegment group1 (by change 22802 ≤ 22802; decide) (by change 22738 ≤ 22802; decide) (by change 22802 ≤ 22866; decide) (by change 0 < 22738; decide) (by change 22802 ≤ 200692 ∧ 22866 ≤ 200692; decide)
def prefix2 : Segment F copy := append copy prefix1 group2 (by change 22866 ≤ 22866; decide) (by change 22738 ≤ 22866; decide) (by change 22866 ≤ 22930; decide) (by change 0 < 22738; decide) (by change 22866 ≤ 200692 ∧ 22930 ≤ 200692; decide)
def subgroupSegment : Segment F copy := append copy prefix2 group3 (by change 22930 ≤ 22930; decide) (by change 22738 ≤ 22930; decide) (by change 22930 ≤ 22994; decide) (by change 0 < 22738; decide) (by change 22930 ≤ 200692 ∧ 22994 ≤ 200692; decide)
def subgroupRows : List Row := CapturedPriorRows16Chunk01.rows.take 256
theorem subgroup_rows_exact : (subgroupSegment (F:=F)).rows=subgroupRows := by
  change (((firstRows ++ rows1) ++ rows2) ++ rows3) = subgroupRows
  decide +kernel
theorem subgroup_steps_count : (subgroupSegment (F:=F)).steps.length=144 := by
  change (((firstSteps ++ steps1) ++ steps2) ++ steps3).length = 144
  decide +kernel
theorem subgroup_complete (base : Nat → F) (linked : base copy=base 0) :
    Satisfies (run base (subgroupSegment (F:=F)).steps) subgroupRows := by
  rw [←subgroup_rows_exact (F:=F)]
  exact subgroupSegment.complete base linked
end ShielddSecurity.CapturedInitial73419Subgroups01
'''
RENAMING='''def rename@J@ (c : Nat) : Nat :=
  CompilerWindowRenaming05.swap 22738 64 @OFFSET@ (CompilerWindowRenaming05.swap 14 7 @INPUT@ c)
theorem injective@J@ : Function.Injective rename@J@ := by
  intro x y equality
  exact (CompilerWindowRenaming05.injective 14 7 @INPUT@ (by decide))
    ((CompilerWindowRenaming05.injective 22738 64 @OFFSET@ (by decide)) equality)
theorem fixed@J@ : rename@J@ 0=0 ∧ rename@J@ copy=copy := by decide +kernel
def steps@J@ : List Step := CompilerColumnRenaming05.steps rename@J@ firstSteps
def rows@J@ : List Row := (CapturedPriorRows16Chunk01.rows.drop @ROW@).take 64
theorem match@J@ : matchRows rows@J@ (CompilerColumnRenaming05.rows rename@J@ firstRows)=true := by decide +kernel
theorem writes@J@ : writeCheck @LOW@ @HIGH@ steps@J@=true := by decide +kernel
theorem support@J@ : supportCheck @HIGH@ rows@J@=true := by decide +kernel
def group@J@ : Segment F copy := makeSegment steps@J@ rows@J@ @LOW@ @HIGH@ writes@J@ support@J@ (by
  intro base linked
  apply transfer rows@J@ (CompilerColumnRenaming05.rows rename@J@ firstRows) match@J@
  exact CompilerColumnRenaming05.completed_rows rename@J@ injective@J@ base firstSteps firstRows
    (firstSegment.complete (fun c => base (rename@J@ c)) (by simpa only [fixed@J@.1,fixed@J@.2] using linked)))
'''
CALL_FRAME = 'import ShielddSecurity.CapturedPriorRows16Frame01\n@HEADER@\nnamespace ShielddSecurity.CapturedInitial73419CallFrame01\nopen Compiler\ndef call0 : List Row := CapturedPriorRows16Chunk01.rows.drop 322\ndef call1 : List Row := CapturedPriorRows16Chunk02.rows\ndef call2 : List Row := CapturedPriorRows16Chunk03.rows\ndef call3 : List Row := CapturedPriorRows16Chunk04.rows\ndef call4 : List Row := CapturedPriorRows16Chunk05.rows\ndef callRows : List Row := (((call0++call1)++call2)++call3)++call4\ntheorem call_in_prior (row : Row) (member : row∈callRows) : row∈CapturedPriorRows16Frame01.capturedPriorRows := by\n  change row ∈ (((call0 ++ call1) ++ call2) ++ call3) ++ call4 at member\n  simp only [List.mem_append] at member\n  simp only [CapturedPriorRows16Frame01.capturedPriorRows,List.mem_append]\n  rcases member with (((member|member)|member)|member)|member\n  · exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_of_mem_drop member))))\n  · exact Or.inl (Or.inl (Or.inl (Or.inr member)))\n  · exact Or.inl (Or.inl (Or.inr member))\n  · exact Or.inl (Or.inr member)\n  · exact Or.inr member\ntheorem call_support (row : Row) (member : row∈callRows) (term : Nat×Int)\n    (present : term∈row.a++row.b) : term.1<23472 :=\n  CapturedPriorRows16Frame01.columns_below row (call_in_prior row member) term present\nend ShielddSecurity.CapturedInitial73419CallFrame01\n'
CALL_WRITES = 'import ShielddSecurity.CapturedInitial73419Generic01\nimport ShielddSecurity.TransferPoseidonCall04Program01\n@HEADER@\nnamespace ShielddSecurity.CapturedInitial73419CallWrites01\nopen Compiler CapturedInitial73419Generic01\ntheorem checked : writeCheck 23060 23472 TransferPoseidonCall04Program01.materializedSteps=true := by decide +kernel\nend ShielddSecurity.CapturedInitial73419CallWrites01\n'
COMPLETION='''import ShielddSecurity.CapturedInitial73419CallMatch00
import ShielddSecurity.CapturedInitial73419CallMatch01
import ShielddSecurity.CapturedInitial73419CallMatch02
import ShielddSecurity.CapturedInitial73419CallMatch03
import ShielddSecurity.CapturedInitial73419CallMatch04
import ShielddSecurity.CapturedInitial73419CallFrame01
import ShielddSecurity.CapturedInitial73419CallWrites01
import ShielddSecurity.CapturedInitial73419Subgroups01
import ShielddSecurity.CapturedPriorRows18RegisteredAudit01
import ShielddSecurity.TransferPoseidonCall04Program01
import ShielddSecurity.CapturedPriorRows16Frame01
@HEADER@
namespace ShielddSecurity.CapturedInitial73419Completion01
open Compiler CompilerCompletion CompilerSegmentCompletion11 CapturedInitial73419Generic01 CapturedInitial73419Subgroups01
abbrev auditRows : List Row := CapturedPriorRows18RegisteredAudit01.dbRows
abbrev call0 : List Row := CapturedInitial73419CallFrame01.call0
abbrev call1 : List Row := CapturedInitial73419CallFrame01.call1
abbrev call2 : List Row := CapturedInitial73419CallFrame01.call2
abbrev call3 : List Row := CapturedInitial73419CallFrame01.call3
abbrev call4 : List Row := CapturedInitial73419CallFrame01.call4
abbrev callRows : List Row := CapturedInitial73419CallFrame01.callRows
variable {F : Type} [Field F] [CharP F p]
def auditSegment : Segment F copy := makeSegment CapturedPriorRows18RegisteredAudit01.steps auditRows 22994 23060
  (by decide +kernel) (by decide +kernel) (by
    intro base linked
    exact CapturedPriorRows18RegisteredAudit01.completed_source16 base linked)
theorem call_writes : writeCheck 23060 23472 TransferPoseidonCall04Program01.materializedSteps=true := CapturedInitial73419CallWrites01.checked
theorem call_in_prior (row : Row) (member : row∈callRows) : row∈CapturedPriorRows16Frame01.capturedPriorRows := CapturedInitial73419CallFrame01.call_in_prior row member
theorem call_support (row : Row) (member : row∈callRows) (term : Nat×Int)
    (present : term∈row.a++row.b) : term.1<23472 :=
  CapturedInitial73419CallFrame01.call_support row member term present
@CALL_MATCHES@
omit [CharP F p] in
theorem call_transfer (rho : Nat → F) (satisfied : Satisfies rho (normalized TransferPoseidonCall04Program01.arithmeticRows)) : Satisfies rho callRows := by
  have part (start count : Nat) : Satisfies rho (normalized ((TransferPoseidonCall04Program01.arithmeticRows.drop start).take count)) := by
    intro row member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    apply satisfied
    apply List.mem_map.mpr
    exact ⟨original,List.mem_of_mem_drop (List.mem_of_mem_take present),rfl⟩
  have a:=CapturedInitial73419Collected01.transfer call0 _ call_match0 rho (part 0 183)
  have b:=CapturedInitial73419Collected01.transfer call1 _ call_match1 rho (part 183 71)
  have c:=CapturedInitial73419Collected01.transfer call2 _ call_match2 rho (part 254 50)
  have d:=CapturedInitial73419Collected01.transfer call3 _ call_match3 rho (part 304 104)
  have e:=CapturedInitial73419Collected01.transfer call4 _ call_match4 rho (part 408 4)
  intro row member
  change row ∈ (((call0 ++ call1) ++ call2) ++ call3) ++ call4 at member
  simp only [List.mem_append] at member
  rcases member with (((member|member)|member)|member)|member
  · exact a row member
  · exact b row member
  · exact c row member
  · exact d row member
  · exact e row member
theorem call_direct_complete (base : Nat → F) (linked : base copy=base 0) :
    Satisfies (run base TransferPoseidonCall04Program01.materializedSteps) TransferPoseidonCall04Program01.arithmeticRows :=
  (original_rows_complete base TransferPoseidonCall04Program01.materializedSteps [0,copy]
    TransferPoseidonCall04Program01.arithmeticRows copy
    (TransferPoseidonCall04Program01.certificate8 (F:=F)).ordered
    ((TransferPoseidonCall04Program01.certificate8 (F:=F)).legal base)
    (by simp) (by simp) linked (TransferPoseidonCall04Program01.certificate8 (F:=F)).coverage).1
def callSegment : Segment F copy where
  steps := TransferPoseidonCall04Program01.materializedSteps
  rows := callRows
  low := 23060
  high := 23472
  writes := by
    intro c member
    exact of_decide_eq_true (List.all_eq_true.mp call_writes c member)
  support := fun row member term present => Or.inl (call_support row member term present)
  complete := by
    intro base linked
    have preserved (c : Nat) (outside : c<23060 ∨ 23472≤c) :
        run base TransferPoseidonCall04Program01.materializedSteps c=base c := by
      apply PoseidonCompletion.run_outside
      intro member
      have bounds := of_decide_eq_true (List.all_eq_true.mp call_writes c member)
      omega
    apply call_transfer
    apply normalized_satisfied _ _
    · rw [preserved copy (Or.inr (by decide)),preserved 0 (Or.inl (by decide))];exact linked
    · exact call_direct_complete base linked
def initialPrefix : Segment F copy := append copy subgroupSegment auditSegment (by change 22994 ≤ 22994; decide) (by change 22738 ≤ 22994; decide) (by change 22994 ≤ 23060; decide) (by change 0 < 22738; decide) (by change 22994 ≤ 200692 ∧ 23060 ≤ 200692; decide)
def initialSegment : Segment F copy := append copy initialPrefix callSegment (by change 23060 ≤ 23060; decide) (by change 22738 ≤ 23060; decide) (by change 23060 ≤ 23472; decide) (by change 0 < 22738; decide) (by change 23060 ≤ 200692 ∧ 23472 ≤ 200692; decide)
theorem actual_rows_exact : (initialSegment (F:=F)).rows=CapturedPriorRows16Frame01.capturedPriorRows := by
  change (((((firstRows ++ rows1) ++ rows2) ++ rows3) ++ auditRows) ++ callRows) = CapturedPriorRows16Frame01.capturedPriorRows
  let xs := CapturedPriorRows16Chunk01.rows
  have partition : (((((xs.take 64 ++ (xs.drop 64).take 64) ++ (xs.drop 128).take 64) ++ (xs.drop 192).take 64) ++ (xs.drop 256).take 66) ++ xs.drop 322) = xs := by
    rw [←List.take_add (i:=64) (j:=64),←List.take_add (i:=128) (j:=64),←List.take_add (i:=192) (j:=64),←List.take_add (i:=256) (j:=66),List.take_append_drop]
  have expanded := congrArg (fun z : List Row => (((z++CapturedPriorRows16Chunk02.rows)++CapturedPriorRows16Chunk03.rows)++CapturedPriorRows16Chunk04.rows)++CapturedPriorRows16Chunk05.rows) partition
  simpa only [xs,firstRows,rows1,rows2,rows3,auditRows,CapturedPriorRows18RegisteredAudit01.dbRows,callRows,CapturedInitial73419CallFrame01.callRows,CapturedInitial73419CallFrame01.call0,CapturedInitial73419CallFrame01.call1,CapturedInitial73419CallFrame01.call2,CapturedInitial73419CallFrame01.call3,CapturedInitial73419CallFrame01.call4,CapturedPriorRows16Frame01.capturedPriorRows,List.append_assoc] using expanded
theorem steps_count : (initialSegment (F:=F)).steps.length=486 := by
  change ((subgroupSegment (F:=F)).steps ++ CapturedPriorRows18RegisteredAudit01.steps ++ TransferPoseidonCall04Program01.materializedSteps).length = 486
  rw [List.length_append,List.length_append,subgroup_steps_count,CapturedPriorRows18RegisteredAudit01.steps_length]
  decide +kernel
def initial (base : Nat → F) : Nat → F := run base (initialSegment (F:=F)).steps
theorem initial_rows (base : Nat → F) (linked : base copy=base 0) :
    Satisfies (initial base) CapturedPriorRows16Frame01.capturedPriorRows := by
  rw [←actual_rows_exact (F:=F)]
  exact initialSegment.complete base linked
theorem outside_preserved (base : Nat → F) (c : Nat) (outside : c<22738 ∨ 23472≤c) : initial base c=base c :=
  CompilerSegmentCompletion11.outside copy initialSegment base c outside
theorem originals_preserved (base : Nat → F) (input : Nat) (bound : input<22735) : initial base (3+input)=base (3+input) :=
  outside_preserved base _ (Or.inl (by omega))
theorem fixed_columns (base : Nat → F) : initial base 0=base 0 ∧ initial base 1=base 1 ∧ initial base 2=base 2 ∧ initial base copy=base copy :=
  ⟨outside_preserved base 0 (Or.inl (by decide)),outside_preserved base 1 (Or.inl (by decide)),
   outside_preserved base 2 (Or.inl (by decide)),outside_preserved base copy (Or.inr (by decide))⟩
def final (base : Nat → F) : Nat → F := TransferPoseidonThreeCallJoin15Program01.completed (initial base)
theorem same_assignment_rows (base : Nat → F) (linked : base copy=base 0) :
    Satisfies (final base) CapturedPriorRows16Frame01.capturedPriorRows ∧
    Satisfies (final base) TransferPoseidonThreeCallJoin15Program01.originalRows := by
  refine ⟨CapturedPriorRows16Frame01.conditional_prior_rows (initial base) (initial_rows base linked),?_⟩
  apply TransferPoseidonThreeCallJoin15Program01.completed_rows (initial base)
  change initial base copy=initial base 0
  rw [(fixed_columns base).2.2.2,(fixed_columns base).1]
  exact linked
theorem original_capture_rows (base : Nat → F) (linked : base copy=base 0) :
    Satisfies (final base) (outlined CapturedPriorRows16Frame01.capturedPriorRows) := by
  apply outlined_satisfied _ _ _ (same_assignment_rows base linked).1
  change TransferPoseidonThreeCallJoin15Program01.completed (initial base) TransferPoseidonThreeCallJoin15Data01.copy=TransferPoseidonThreeCallJoin15Program01.completed (initial base) 0
  rw [TransferPoseidonThreeCallJoin15Program01.copy_preserved,
    TransferPoseidonThreeCallJoin15Program01.outside_preserved (initial base) 0 (Or.inl (by decide))]
  change initial base copy=initial base 0
  rw [(fixed_columns base).2.2.2,(fixed_columns base).1]
  exact linked
theorem final_outside (base : Nat → F) (c : Nat) (outside : c<22738 ∨ 25044≤c) : final base c=base c := by
  unfold final
  rw [TransferPoseidonThreeCallJoin15Program01.outside_preserved (initial base) c (by omega)]
  exact outside_preserved base c (by omega)
theorem final_originals (base : Nat → F) (input : Nat) (bound : input<22735) : final base (3+input)=base (3+input) :=
  final_outside base _ (Or.inl (by omega))
end ShielddSecurity.CapturedInitial73419Completion01
'''

def render(data):
    require(data['runtime']==RUNTIME and data['canonical']==CANONICAL and data['counts']=={'square':238,'product':248},'render pins')
    rename=''
    for j,inp in [(1,9),(2,21),(3,28)]:
        t=RENAMING
        for k,v in {'J':j,'INPUT':inp,'OFFSET':64*j,'ROW':64*j,'LOW':22738+64*j,'HIGH':22802+64*j}.items():t=t.replace('@'+k+'@',str(v))
        rename+=t
    checks=''
    for j,(start,count) in enumerate([(0,183),(183,71),(254,50),(304,104),(408,4)]):
        checks+=f'theorem call_match{j} : call{j} = CapturedInitial73419Collected01.collected (normalized ((TransferPoseidonCall04Program01.arithmeticRows.drop {start}).take {count})) := CapturedInitial73419CallMatch0{j}.checked\n'
    result={}
    for j,(start,count) in enumerate([(0,183),(183,71),(254,50),(304,104),(408,4)]):
        name='CapturedInitial73419CallMatch0'+str(j)
        text='import ShielddSecurity.CapturedInitial73419Collected01\nimport ShielddSecurity.CapturedInitial73419Generic01\nimport ShielddSecurity.CapturedInitial73419CallFrame01\nimport ShielddSecurity.TransferPoseidonCall04Program01\n'+HEADER+'\nnamespace ShielddSecurity.'+name+'\nopen CapturedInitial73419Generic01\n'
        text+=f'theorem checked : CapturedInitial73419CallFrame01.call{j} = CapturedInitial73419Collected01.collected (normalized ((TransferPoseidonCall04Program01.arithmeticRows.drop {start}).take {count})) := by decide +kernel\n'
        text+='end ShielddSecurity.'+name+'\nset_option pp.all true in\n#check @ShielddSecurity.'+name+'.checked\n#print axioms ShielddSecurity.'+name+'.checked\n'
        result[name]=text.encode()
    for name,text in [('CapturedInitial73419Generic01',GENERIC),('CapturedInitial73419Subgroups01',SUBGROUP),('CapturedInitial73419CallFrame01',CALL_FRAME),('CapturedInitial73419CallWrites01',CALL_WRITES),('CapturedInitial73419Completion01',COMPLETION)]:
        text=text.replace('@HEADER@',HEADER).replace('@P@',str(P)).replace('@RENAMINGS@',rename).replace('@CALL_MATCHES@',checks)
        names=re.findall(r'^(?:theorem|def|abbrev) ([A-Za-z0-9_]+)',text,re.M)
        early=[]
        if name=='CapturedInitial73419Completion01':
            early=['auditSegment','call_writes','call_in_prior','call_support']+['call_match'+str(j) for j in range(5)]+['call_transfer','call_direct_complete','callSegment','initialPrefix','initialSegment','actual_rows_exact','steps_count']
            for n in early:
                start=re.search(r'(?m)^(?:theorem|def) '+re.escape(n)+r'\b',text).start()
                nxt=re.search(r'(?m)^(?:theorem|def) ',text[start+1:])
                require(nxt is not None,'next declaration for early named audit')
                at=start+1+nxt.start()
                if text[:at].rstrip().endswith('omit [CharP F p] in'): at=text.rfind('omit [CharP F p] in',0,at)
                audit=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
                text=text[:at]+audit+text[at:]
        for n in names:
            if n not in early:text+=f'\nset_option pp.all true in\n#check @ShielddSecurity.{name}.{n}\n#print axioms ShielddSecurity.{name}.{n}\n'
        require('@HEADER@' not in text and len(text.encode())<=262144,'source size/placeholders')
        result[name]=text.encode()
    return result

def main():
    a=argparse.ArgumentParser();a.add_argument('--root',required=True);a.add_argument('--emit',action='store_true');v=a.parse_args()
    here=Path(__file__).resolve().parent;stage=here.parent;root=Path(v.root).resolve()
    require({p.name for p in here.iterdir()}=={'generate19.py'},'closed maintained directory')
    if v.emit:require(not (stage/'producer-manifest01.json').exists() and not (stage/'selected-data01.json.zlib').exists(),'sealed/existing output')
    data=extract(root) if v.emit else bounded_json(stage/'selected-data01.json.zlib')
    for pin in data['source_only'].values():require(rec(pin['path'])==pin,'source dependency changed')
    inherited=json.loads(Path(data['inherited_reference']['path']).read_bytes())['modules']
    require(rec(data['inherited_reference']['path'])==data['inherited_reference'],'inherited reference changed')
    inherited.update(data['extra_inherited'])
    for m,d in inherited.items():
        for k in ('source','object','receipt'):require(rec(d[k]['path'])==d[k],m+' '+k)
        rp=json.loads(Path(d['receipt']['path']).read_bytes());require(rp['status']=='passed' and type(rp['exit']) is int and rp['exit']==0,'inherited receipt status')
    sources=render(data)
    # Deterministic second render is held only in memory, never a physical Lean copy.
    require(render(data)==sources,'in-memory byte replay')
    packed=zlib.compress((json.dumps(data,separators=(',',':'))+'\n').encode(),9)
    md=dict(schema='SOURCE19-producer',scope=data['scope'],status='SOURCE-only; all new predicates/audits UNRUN',maintained=rec(__file__),data=dict(path='selected-data01.json.zlib',sha256=sha(packed),bytes=len(packed)),generated={n:dict(sha256=sha(b),bytes=len(b),audits=re.findall(rb'#check @([^\n]+)',b)) for n,b in sources.items()},premises=['Field F','CharP F p','base copy = base 0 only for completeness','outside-window bound only for frame conclusions'],open=['All SOURCE16/18/19/Join15 dependencies UNRUN','198463 remaining captured rows','global positional inclusion','assertion truth and native semantics'],new_kernel_runs=0)
    for n in md['generated']:md['generated'][n]['audits']=[x.decode() for x in md['generated'][n]['audits']]
    metadata=(json.dumps(md,separators=(',',':'))+'\n').encode()
    if v.emit:
        charge=sum(p.stat().st_size for p in stage.rglob('*') if p.is_file())+len(packed)+len(metadata)+sum(map(len,sources.values()))+2048
        require(charge<=122880,'worker budget preflight')
        with (stage/'selected-data01.json.zlib').open('xb') as f:f.write(packed)
        out=stage/'source-root/ShielddSecurity';out.mkdir(parents=True,exist_ok=False)
        for n,b in sources.items():
            with (out/(n+'.lean')).open('xb') as f:f.write(b)
        with (stage/'producer-manifest01.json').open('xb') as f:f.write(metadata)
    else:
        require(packed==(stage/'selected-data01.json.zlib').read_bytes(),'exact DATA bytes')
        for n,b in sources.items():require(b==(stage/'source-root/ShielddSecurity'/(n+'.lean')).read_bytes(),'generated bytes')
    print(json.dumps(dict(status='SOURCE-only',generated={n:dict(bytes=len(b),sha256=sha(b)) for n,b in sources.items()},audits=sum(len(x['audits']) for x in md['generated'].values()),compressed_data_bytes=len(packed),kernel_runs=0),separators=(',',':')))
if __name__=='__main__':main()
