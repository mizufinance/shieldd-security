from pathlib import Path
local=Path('C:/src/shieldd-transfer-handoffs')
body=(local/'prepare-point-smoke-20261009-02.py').read_text().replace('point-smoke-20261009-02','point-smoke-20261009-03').replace('safe-point-smoke-boundary-2026100902','safe-point-smoke-boundary-2026100903').replace('TransferOwnedPointSmokeBoundary2026100902','TransferOwnedPointSmokeBoundary2026100903')
needle="exec(compile(body,str(local/'prepare-point-smoke-20261009-03.py'),'exec'))"
assert needle in body
correction=needle+"\nauditor=diag/('audit-'+stem+'.py')\naudit_body=auditor.read_text()\nold_pattern=\"re.escape(full)+r'\\\\s*:'\"\nnew_pattern=\"re.escape(full)+r'(?:\\\\.\\\\{[^}\\\\n]*\\\\})?\\\\s*:'\"\nassert old_pattern in audit_body\nauditor.write_text(audit_body.replace(old_pattern,new_pattern))"
body=body.replace(needle,correction)
(local/'prepare-point-smoke-20261009-03.py').write_text(body)
exec(compile(body,str(local/'prepare-point-smoke-20261009-03.py'),'exec'))
