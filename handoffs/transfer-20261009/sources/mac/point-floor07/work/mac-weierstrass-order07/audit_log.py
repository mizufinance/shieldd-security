"""Fail-closed named signature and axiom census for bounded Lean output."""
import hashlib,re

def validate(text,expected_axioms,expected_checks):
    assert 'sorryAx' not in text and 'error:' not in text,'Lean error/placeholder'
    assert len(expected_axioms)==len(set(expected_axioms)),'duplicate requested axiom audit'
    assert len(expected_checks)==len(set(expected_checks)),'duplicate requested signature'
    assert all(name.startswith(('ShielddSecurity.','WeierstrassCurve.Affine.Point.')) for name in expected_axioms+expected_checks)
    audits=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)
    zero=re.findall(r"'([^']+)' does not depend on any axioms",text)
    for theorem,axioms in audits:
        assert not set(x.strip() for x in axioms.split(',')) - {
            'propext','Quot.sound','Classical.choice'},'unexpected axioms: '+theorem
    observed=[name for name,_ in audits]+zero
    assert sorted(observed)==sorted(expected_axioms),'exact named axiom audit census mismatch'
    signatures={}
    for theorem in expected_checks:
        pattern=r'^@?'+re.escape(theorem)+r'\s*:[\s\S]*?(?=^\''+re.escape(theorem)+r'\')'
        matches=re.findall(pattern,text,re.M)
        assert len(matches)==1,'exact named full signature missing/duplicated: '+theorem
        signatures[theorem]=hashlib.sha256(matches[0].strip().encode()).hexdigest()
    return dict(axiom_audits=len(observed),full_signature_sha256=signatures)
