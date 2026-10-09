"""Instantiate the audited symbolic EPK relation proofs for real captured scopes.

The driver supplies the exact audited scope-one proof sources and a freshly
accepted typed physical correspondence. Each emitted proof is checked again
against its own captured map, canonical rows, template transports and native
publication. No imported scope-one conclusion substitutes for a target proof.
"""
import re
from . import transfer_relation as relation


def generate(pair, bases):
    scope = pair.get('scope_id')
    if type(scope) is not int or not 2 <= scope <= 5:
        raise relation.RelationError('exact genuine remaining captured EPK scope required')
    pairs = pair.get('restricted_map')
    if not isinstance(pairs,list) or any(not isinstance(row,list) or len(row)!=2
            or any(type(v)is not int or v<0 for v in row) for row in pairs):
        raise relation.RelationError('typed actual scoped operand map required')
    columns = dict(pairs)
    if len(columns)!=len(pairs) or len(set(columns.values()))!=len(columns):
        raise relation.RelationError('injective actual scoped operand map required')
    roles = [0,200692,4922,4923,4930,5433,5434]
    if any(role not in columns for role in roles) or columns[0]!=0 or columns[200692]!=200692:
        raise relation.RelationError('actual public/scalar/output/unit operands required')
    expected = {'Relation':4,'NativeRelation':2,'Completion':5,'Frame':2}
    if set(bases)!=set(expected):
        raise relation.RelationError('all four exact audited symbolic basis sources required')
    target_columns={6326:columns[4922],6327:columns[4923],6334:columns[4930],
        6837:columns[5433],6838:columns[5434]}
    output=[]
    for suffix,count in expected.items():
        original='TransferEpkScope1'+suffix
        source=bases[suffix]
        if (type(source)is not str or source.count('namespace ShielddSecurity.'+original+'\n')!=1
                or source.count('end ShielddSecurity.'+original+'\n')!=1
                or len(re.findall(r'^#check @',source,re.M))!=count
                or re.findall(r'^#check @([\w.]+)',source,re.M)!=re.findall(r'^#print axioms ([\w.]+)',source,re.M)
                or re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)):
            raise relation.RelationError('exact audited placeholder-free symbolic proof basis required')
        source=source.replace('RuntimeTransferEpk1',f'RuntimeTransferEpk{scope}')
        source=source.replace('TransferEpkScope1',f'TransferEpkScope{scope}')
        # Simultaneous whole-token replacement prevents a target column from
        # being interpreted as another source role during instantiation.
        source=re.sub(r'(?<![A-Za-z0-9_])(?:6326|6327|6334|6837|6838)(?![A-Za-z0-9_])',
            lambda token:str(target_columns[int(token[0])]),source)
        output.append((f'TransferEpkScope{scope}'+suffix,source))
    return output
