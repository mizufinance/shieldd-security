from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-canonical-source-publication-endpoint-20261011-01/assemble.py').read_text()
needle="assert len(fresh) == 5 and fresh == events[-1]['result']['audits']"
assert s.count(needle)==1
s=s.replace(needle,needle+"\ndeclaration_kinds = __import__('re').findall(r'^(def|theorem|structure|inductive) ', m.code_only((CURRENT / ('handwritten/' + MODULE + '.lean')).read_text()), __import__('re').M)\nassert len(declaration_kinds) == len(fresh)\nassert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 3")
needle="'fresh_definition_audits': 3, 'fresh_structure_audits': 0, 'fresh_theorem_audits': 5"
assert s.count(needle)==1
s=s.replace(needle,"'fresh_definition_audits': declaration_kinds.count('def'), 'fresh_structure_audits': declaration_kinds.count('structure') + declaration_kinds.count('inductive'), 'fresh_theorem_audits': declaration_kinds.count('theorem')")
needle="manager_endpoint = DIAG / 'transfer-canonical-source-word-retention-endpoint-20261011-01'"
assert s.count(needle)==1;s=s.replace(needle,"manager_endpoint = DIAG / 'transfer-canonical-source-word-retention-endpoint-20261011-02'")
needle='a73c5de332a59b0aa773caeb664400521dad3094b7b6599f31ecca29a20c6e0d'
assert s.count(needle)==1;s=s.replace(needle,'5820d77836a349d7fd1735513c8c986900b46822de80c7327447a6deb16b33f5')
at=s.index("review = {'status':")
s=s[:at]+"superseded = DIAG / 'transfer-canonical-source-publication-endpoint-20261011-01'\nfor name in ['prepare_assembly.py', 'assemble.py', 'manifest.json', 'review.json']:\n    add(superseded / name, 'superseded-metadata/' + name, 'unchanged prior packet with stale declaration-kind counters; no failed proof or replay')\nmetadata_history = {'original_archive': pin(superseded / archive.name), 'error': 'Fresh definition/theorem counters inherited as 3/5 although complete original declaration audits are 2/3. Corrected from source declaration kinds; raw source/object/type/axiom reports unchanged, no rerun or added proof credit. Corrected canonical retention parent carries its original metadata repair history.'}\ndump(ROOT / 'metadata-history.json', metadata_history)\nadd(ROOT / 'metadata-history.json', 'context/metadata-history.json', 'exact original superseded archive identity and correction scope')\n"+s[at:]
s=s.replace("'fresh_sources': 1,","'metadata_correction': metadata_history, 'fresh_sources': 1,",1)
(ROOT/'assemble.py').write_text(s)
print({'corrected_source_counts':{'definitions':2,'theorems':3},'replay':False,'original_packet_retained':True})
