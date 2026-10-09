"""Verify compact generation projection against full qualification and prior DATA audit."""
import json,hashlib
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=H/'frozen/inputs/portable-input01.json';full=R/'outputs/mac-poseidon-width6-upstream11/upstream01.json'
compact=json.loads(p.read_text());d=json.loads(full.read_text());assert sha(full)==compact['full_descriptor_sha256']=='3be245c6c55f473352481dbbc43d876591f8bbcedb61bd9c9c633de785112d6e'
assert compact['schema']=='upstream11-portable-generation-v1'
projected=['blocks','indexed_original_rows','translations'];exact=[]
for k,v in compact.items():
    if k in projected or k in ['schema','full_descriptor_sha256']:continue
    assert v==d[k];exact.append(k)
def assert_projection(part,original):
    if isinstance(part,dict):
        assert isinstance(original,dict) and part.keys()<=original.keys()
        for k,v in part.items():assert_projection(v,original[k])
    elif isinstance(part,list):
        assert isinstance(original,list) and len(part)==len(original)
        for a,b in zip(part,original,strict=True):assert_projection(a,b)
    else:assert part==original
for key in projected:assert_projection(compact[key],d[key])
assert len(compact['prefix_scopes'])==4 and sum(len(x['nodes']) for x in compact['prefix_scopes'])==377
assert len(compact['indexed_original_rows'])==837
assert [x['capture_index'] for x in compact['indexed_original_rows']]==list(range(38040,38876))+[200769]
prior=R/'work/parent-width6-upstream11-plan01/descriptor-audit01.json';j=json.loads(prior.read_text())
result={'schema':'parent-upstream11-portable-projection-data-v1','portable_input_sha256':sha(p),'bytes':p.stat().st_size,'full_descriptor_sha256':sha(full),'exact_fields':exact,'exact_recursive_key_projections':projected,'retained_block_round_ports':sum(sum(len(rnd['ports']) for rnd in b['rounds']) for b in compact['blocks']),'initial_parent_parser_refusal':'Shallowprojection compared nestedroundportdictionary to full nonprunedports; nooutput/credit. Correctedrecursive exactprojectionaudit.','prefix_nodes':377,'selected_rows':837,'prior_DB_descriptor_audit_sha256':sha(prior),'prior_scope':'377prefixnodes3120roundports837rows exactDBsourceLC/pinnedparameters; dataonly','portable_generation_replay':'OPEN','new_kernel_credit':0,'full_transfer':'OPEN'}
out=H/'portable-input-audit01.json';assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
