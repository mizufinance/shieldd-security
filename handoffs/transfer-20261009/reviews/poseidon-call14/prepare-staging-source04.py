"""Add SOURCE provenance for the append-only parent acceptance and actual reviews."""
from pathlib import Path
import hashlib
V=Path(__file__).resolve().parent;p=V/'stage-publication03.py';old=p.read_bytes();s=old.decode()
needle="V/'stage-publication03.py',V/'publication-plan03.json',V/'parent-report-corrections01.json',V/'prepare-review-report-corrections01.py'"
assert needle in s
s=s.replace(needle,"V/'stage-publication04.py',V/'publication-plan03.json',V/'parent-report-corrections01.json',V/'prepare-review-report-corrections01.py',V/'accept-scoped-checkpoint01.py',V/'inspect-staged-publication01.py',V/'review-final-call14-02.py',V/'review-final-call14-03.py',V/'prepare-staging-source04.py'",1)
target=V/'stage-publication04.py';compile(s,str(target),'exec');target.open('xb').write(s.encode());assert p.read_bytes()==old
print({'factory':str(target),'sha256':hashlib.sha256(s.encode()).hexdigest(),'actual_factory_invoked':False})
