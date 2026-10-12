from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-word-stage-cache-publication-endpoint-20261011-03'
assert not (ROOT/'assemble.py').exists()
s=(OLD/'assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("'imported_complete_reports': 6","'imported_complete_reports': len(manager_reports)")
replace("'complete_owned_modules': 133, 'inherited_complete_reports': 1113","'complete_owned_modules': pool['objects'], 'inherited_complete_reports': len(pool['inherited_public_reports'])")
s=s.replace('1113 original inherited complete reports','1121 original inherited complete reports').replace('verified 1113 inherited reports','verified 1121 inherited reports')
at=s.index("dump(ROOT / 'review.json', review)")
s=s[:at]+"oldEndpoint=DIAG/'transfer-word-stage-cache-publication-endpoint-20261011-03'\noldArchive=oldEndpoint/'portable-windows-word-stage-cache-publication-endpoint01.tar.xz'\nassert pin(oldArchive)['sha256']=='d6fdd0ee2ddc545f7340d6322907fbb7e587e12dea96bab3b8946ddbabf10e30'\nfor name in ['prepare_assembly.py','assemble.py','inherited-reference.json','review.json','manifest.json']:\n    add(oldEndpoint/name,'rejected-metadata-endpoint03/'+name,'immutable original endpoint with stale inherited-reference labels only; no proof replay or new credit')\nhistory={'original_archive':pin(oldArchive),'repaired_fields':['inherited-reference imported_complete_reports6→8','complete_owned_modules133→134','inherited_complete_reports1113→1121','two explanatory count labels'],'scope':'Fresh assembly source derives counts from verified original pool and reports. Original source/object/full report/plan identities unchanged. No proof replay or extra credit.'}\ndump(ROOT/'metadata-history.json',history)\nadd(ROOT/'metadata-history.json','context/metadata-history.json','original metadata archive identity and exact corrected fields')\nreview['metadata_repair_history']=history\nassert reference['complete_owned_modules']==134 and reference['inherited_complete_reports']==1121\nassert reference['checked_word_stage_refinement']['imported_complete_reports']==8\n"+s[at:]
(ROOT/'assemble.py').write_text(s)
print({'metadata_source_repair_only':True,'counts_derived_from_originals':True,'unchanged_proof_and_ancestry':True})
