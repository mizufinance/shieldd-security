from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-pow-field-20261012-05'
assert not (ROOT/'prepare.py').exists() and not (OLD/'events.jsonl').exists()
(ROOT/'handwritten').mkdir();(ROOT/'context').mkdir()
(ROOT/'handwritten/TransferScalarPowField01.lean').write_bytes((OLD/'handwritten/TransferScalarPowField01.lean').read_bytes())
(ROOT/'context/scalar-pow-field-shape.json').write_bytes((OLD/'context/scalar-pow-field-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("UPSTREAM = DIAG / 'transfer-scalar-inverse-correctness-20261012-04'","UPSTREAM = DIAG / 'transfer-scalar-pow-bit-integer-20261012-03'").replace("POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-05'","POOL = DIAG / 'transfer-scalar-pow-field-owned-floor-20261012-06'")
start=s.index("stdout = UPSTREAM /");end=s.index('originalInputs=inputs[:]',start)
branch="""stdout = UPSTREAM / 'runs/01-TransferScalarPowBitInteger01/stdout.txt'
current = m.audit(stdout.read_text(), target['audit_names'])
assert len(current)==6 and current==events[-1]['result']['audits']
assert pin(stdout)==events[-1]['result']['stdout'] and set(audits).isdisjoint(current)
audits.update(current)
records.append(('TransferScalarPowBitInteger01',target['source'],events[-1]['result']['objects'][0]))
inputs += [pin(UPSTREAM/n) for n in ['prepare_recipe.py','prepare.py','plan.json','events.jsonl','execute_bounded.py','source-mapping.json','handwritten/TransferScalarPowBitInteger01.lean','project/ShielddSecurity/TransferScalarPowBitInteger01.lean']]+[pin(stdout)]
assert len(records)==163 and len(audits)==1296
bits=UPSTREAM

"""
s=s[:start]+branch+s[end:]
start=s.index("composition['field_foundation']");end=s.index('composition_file =',start)
s=s[:start]+"composition['scope']='Complete163-module first owned root and1296 complete original reports: exact qualified whole bit-integer/word branch reused without replay. The independently qualified inverse/prime branch remains a separate original packet; no unsupported external imports selected.'\n"+s[end:]
s=s.replace("'objects': 204","'objects': 163")
s=s.replace("mapping['scalar_inverse_correctness_source_shape']=pin(DIAG/'transfer-scalar-inverse-correctness-20261012-04/context/scalar-inverse-correctness-shape.json')\n",'')
start=s.index("plan['external_floor']=pin(");end=s.index("plan['owned_import_pool']",start)
s=s[:start]+"# Exact already qualified pure Core floor and package roots inherited unchanged from the bit branch.\n"+s[end:]
start=s.index("mapping['scope'] =");end=s.index('\n',start)
s=s[:start]+"mapping['scope'] = 'Actual modeled constant/variable bit/word folds derive complete source pow mathematical field values from exact ONE and little-endian exponent reconstruction. Six theorem audits. Complete163-module1296-report qualified word branch reused unchanged without replay. Independently qualified inverse/prime branch preserved as its separate original packet; native Choice/compiler/caller/full Transfer remain open.'"+s[end:]
extra="""unrunPowerFifth=DIAG/'transfer-scalar-pow-field-20261012-05'
assert not (unrunPowerFifth/'events.jsonl').exists()
unrunPowerFifthNames=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/scalar-pow-field-shape.json','handwritten/TransferScalarPowField01.lean','project/ShielddSecurity/TransferScalarPowField01.lean']
plan['pins'] += [pin(unrunPowerFifth/n) for n in unrunPowerFifthNames]
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
s=s.replace('complete204-module owned root with exact shared word foundation and qualified prime/bit branches, and unchanged original qualified Mathlib/core floor','complete163-module qualified word root and unchanged original qualified Core floor; inverse/prime packet preserved separately')
s=s.replace('SCALAR_POW_FIELD_COMPLETE_TWO_HUNDRED_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_POW_FIELD_COMPLETE_WORD_BRANCH_SELF_REVIEWED_UNRUN')
(ROOT/'prepare.py').write_text(s)
print({'six_theorem_source_bytes_unchanged':True,'only_complete_actual_word_dependency_cone_selected':True,'owned_modules':163,'inherited_reports':1296,'inverse_prime_original_packet_preserved_separately':True,'all_execution_guards_unchanged':True})
