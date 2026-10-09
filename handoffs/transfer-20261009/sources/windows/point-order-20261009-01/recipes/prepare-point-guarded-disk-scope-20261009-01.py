from pathlib import Path
import argparse, hashlib

p = argparse.ArgumentParser()
p.add_argument('--prefix', required=True, choices=['point-trace-composition', 'point-order'])
args = p.parse_args()
local = Path('C:/src/shieldd-transfer-handoffs')
original = local / f'prepare-{args.prefix}-20261009-01.py'
expected = {'point-trace-composition': 'b3ed654e25ef6fb3d9f07ee8f7d9f258564089a326bcf31167325afce63524b0',
            'point-order': '3132dfe9d2981512abcdd5c992810934ff828b88c3bf667253c33f1f957b6209'}
assert hashlib.sha256(original.read_bytes()).hexdigest() == expected[args.prefix]
body = original.read_text()
needle = 'controller.write_text(guard)'
assert body.count(needle) == 1
addition = r'''
disk_source = r"""function Assert-TaskScopedArtifactDiskBudget {
 $taskArtifactFiles=@(Get-ChildItem -LiteralPath $taskStage -Recurse -File)
 $taskArtifactBytes=($taskArtifactFiles|Measure-Object Length -Sum).Sum
 ([DateTime]::UtcNow.ToString('o')+' '+$taskArtifactFiles.Count+' '+$taskArtifactBytes)|Add-Content "$taskBatch/scoped-artifact-disk-samples.txt"
 if($taskArtifactBytes -gt 2147483648){throw 'scoped artifacts including inherited and new companions exceed 2GiB disk budget'}
}
Assert-TaskScopedArtifactDiskBudget
"""
assert guard.count('$env:LEAN_PATH=') == 1
guard = guard.replace('$env:LEAN_PATH=', disk_source + '$env:LEAN_PATH=', 1)
admission = ' foreach($taskName in $taskManifest.order){\n  $taskMemory='
assert guard.count(admission) == 1
guard = guard.replace(admission, ' foreach($taskName in $taskManifest.order){\n  Assert-TaskScopedArtifactDiskBudget\n  $taskMemory=', 1)
completed = '  Write-Output "Compiled exact maintained $taskName"'
assert guard.count(completed) == 1
guard = guard.replace(completed, '  Assert-TaskScopedArtifactDiskBudget\n' + completed, 1)
auditing = " & 'C:/Users/acyrn/AppData/Local/Programs/Python/Python313/python.exe' $taskAudit $taskBatch"
assert guard.count(auditing) == 1
guard = guard.replace(auditing, ' Assert-TaskScopedArtifactDiskBudget\n' + auditing, 1)
controller.write_text(guard)
'''
# The extra text is inserted in the producer before creation of a fresh guard.
# No existing source, guard, receipt, object, or running batch is edited.
body = body.replace(needle, addition, 1)
exec(compile(body, str(original), 'exec'))
