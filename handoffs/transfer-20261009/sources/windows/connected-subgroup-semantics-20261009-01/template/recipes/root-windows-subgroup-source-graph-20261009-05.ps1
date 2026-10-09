$ErrorActionPreference='Stop'
$taskRoot='C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002'
$taskSource="$taskRoot/windows-subgroup-source-graph-20261009-05-source"
$taskBatch="$taskRoot/windows-subgroup-source-graph-20261009-05-kernel"
$taskStage="$taskBatch/project"
$taskExternal="$taskRoot/windows-jubjub-isolated-05/modules"
$taskLean='C:/Users/acyrn/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean.exe'
$taskAudit="$taskRoot/audit-windows-subgroup-source-graph-20261009-05.py"
$taskAuditHash=(Get-FileHash -LiteralPath $taskAudit).Hash
$taskGuardHash=(Get-FileHash -LiteralPath $PSCommandPath).Hash
$taskCacheManifest=Get-Content -LiteralPath "$taskRoot/windows-jubjub-isolated-05/inputs.json" -Raw|ConvertFrom-Json
if($taskCacheManifest.packages.mathlib -ne 'c5ea00351c28e24afc9f0f84379aa41082b1188f'){throw 'matched Mathlib cache required'}
$taskWaitStart=[DateTime]::UtcNow
while(!(Test-Path -LiteralPath "$taskRoot/semantic-tail-current-project-kernel-3050/end.txt")){
 if(([DateTime]::UtcNow-$taskWaitStart).TotalSeconds -ge 604800){throw 'finite initial-storage predecessor wait expired'}
 Start-Sleep -Seconds 5
}
if(Test-Path -LiteralPath $taskBatch){throw 'fresh module check required'}
if(!(Test-Path -LiteralPath "$taskRoot/root-encryption-dh-selector-recovery-3009/complete.txt") -or
   !(Test-Path -LiteralPath "$taskRoot/root-encryption-dh-selector-recovery-3009/end.txt") -or
   (Get-Content -LiteralPath "$taskRoot/root-encryption-dh-selector-recovery-3009/exit.txt" -Raw).Trim() -ne '0'){throw 'actual completed DH slot required'}
if(!(Test-Path -LiteralPath "$taskRoot/semantic-tail-current-project-kernel-3050/complete.txt") -or (Get-Content -LiteralPath "$taskRoot/semantic-tail-current-project-kernel-3050/exit.txt" -Raw).Trim() -ne '0'){throw 'actual settled cross-key native predecessor required'}
if(Get-CimInstance Win32_Process|Where-Object {$_.Name -in @('lean.exe','lake.exe','cargo.exe','rustc.exe')}){throw 'one heavy job per Windows host required'}
. "$taskRoot/native-host-memory-api-01.ps1"
$taskManifest=Get-Content -LiteralPath "$taskSource/manifest.json" -Raw|ConvertFrom-Json
foreach($taskName in $taskManifest.sources.PSObject.Properties.Name){
 $taskInput=$taskManifest.sources.$taskName
 if((Get-FileHash -LiteralPath $taskInput.path).Hash.ToLowerInvariant() -ne $taskInput.sha256){throw 'maintained source identity required'}
 if((Get-FileHash -LiteralPath "$taskSource/$taskName.lean").Hash.ToLowerInvariant() -ne $taskInput.sha256){throw 'exact source preparation required'}
}
foreach($taskName in $taskManifest.order){
 if((Get-FileHash -LiteralPath "$taskSource/$taskName-audited.lean").Hash.ToLowerInvariant() -ne $taskManifest.audited_candidates.$taskName){throw 'exact type/axiom audited candidate required'}
}
if((Get-FileHash -LiteralPath $taskLean).Hash.ToLowerInvariant() -ne '8132256d484b8ecc4561bec70abd1271f4c0d03badbc3bc272f6c4053af9fdbc'){throw 'exact Lean executable required'}
New-Item -ItemType Directory -Path "$taskStage/ShielddSecurity"|Out-Null
[DateTime]::UtcNow.ToString('o')|Set-Content "$taskBatch/start.txt"
Copy-Item -LiteralPath "$taskSource/manifest.json" -Destination "$taskBatch/manifest.json"
Copy-Item -LiteralPath "$taskRoot/windows-jubjub-isolated-05/inputs.json" -Destination "$taskBatch/cache-inputs.json"
@{guard_sha256=$taskGuardHash;audit_sha256=$taskAuditHash;threads=1;memory_MiB=1536;finite_seconds_per_module=240}|ConvertTo-Json|Set-Content "$taskBatch/recipe.json"
foreach($taskReceipt in $taskManifest.frozen_import_receipts.PSObject.Properties){
 if((Get-FileHash -LiteralPath $taskReceipt.Name).Hash.ToLowerInvariant() -ne $taskReceipt.Value){throw 'exact actual import receipt required'}
}
foreach($taskImport in $taskManifest.reused){
 if((Get-FileHash -LiteralPath $taskImport.source).Hash.ToLowerInvariant() -ne $taskImport.source_sha256 -or (Get-FileHash -LiteralPath $taskImport.object).Hash.ToLowerInvariant() -ne $taskImport.object_sha256){throw 'exact qualified import pair required'}
 Copy-Item -LiteralPath $taskImport.source -Destination "$taskStage/ShielddSecurity/$($taskImport.name).lean"
 Copy-Item -LiteralPath $taskImport.object -Destination "$taskStage/ShielddSecurity/$($taskImport.name).olean"
}
$taskDeps=@(Get-ChildItem -LiteralPath $taskExternal -Recurse -File|ForEach-Object {[ordered]@{path=$_.FullName;sha256=(Get-FileHash -LiteralPath $_.FullName).Hash}})
ConvertTo-Json -InputObject $taskDeps -Depth 4|Set-Content "$taskBatch/external-before.json"
$env:LEAN_PATH="$taskStage;$taskExternal"
$env:LEAN_NUM_THREADS='1'
try{
 foreach($taskName in $taskManifest.order){
  $taskMemory=Get-TaskMemorySnapshot
  if($taskMemory.PhysicalKiB -lt 3145728 -or $taskMemory.CommitFreeKiB -lt 2621440){throw 'memory admission required'}
  $taskLeaf="$taskBatch/$taskName"
  New-Item -ItemType Directory -Path $taskLeaf|Out-Null
  $taskCandidate="$taskSource/$taskName-audited.lean"
  Copy-Item -LiteralPath $taskCandidate -Destination "$taskStage/ShielddSecurity/$taskName.lean"
  $taskStart=[DateTime]::UtcNow
  $taskStart.ToString('o')|Set-Content "$taskLeaf/start.txt"
  $taskJob=Start-Process -FilePath $taskLean -ArgumentList @('-j1','-M','1536','-o',"$taskStage/ShielddSecurity/$taskName.olean","$taskStage/ShielddSecurity/$taskName.lean") -WorkingDirectory $taskStage -RedirectStandardOutput "$taskLeaf/stdout.txt" -RedirectStandardError "$taskLeaf/stderr.txt" -PassThru -WindowStyle Hidden
  $taskJob.Id|Set-Content "$taskLeaf/owned-pid.txt"
  try{
   while(!$taskJob.HasExited){
    $taskMemory=Get-TaskMemorySnapshot
    $taskJob.Refresh()
    ([DateTime]::UtcNow.ToString('o')+' '+$taskMemory.PhysicalKiB+' '+$taskMemory.CommitFreeKiB+' '+$taskJob.WorkingSet64)|Add-Content "$taskLeaf/memory.txt"
    if($taskMemory.PhysicalKiB -lt 1572864 -or $taskMemory.CommitFreeKiB -lt 524288){'host-memory-pressure'|Set-Content "$taskLeaf/stop.txt";break}
    if(([DateTime]::UtcNow-$taskStart).TotalSeconds -ge 240){'finite-240s-budget'|Set-Content "$taskLeaf/stop.txt";break}
    Start-Sleep -Milliseconds 400
   }
  }finally{
   if(!$taskJob.HasExited){Stop-Process -Id $taskJob.Id -Force -ErrorAction SilentlyContinue}
   $taskJob.WaitForExit()
   $taskJob.ExitCode|Set-Content "$taskLeaf/exit.txt"
   [DateTime]::UtcNow.ToString('o')|Set-Content "$taskLeaf/end.txt"
  }
  if($taskJob.ExitCode -ne 0 -or (Test-Path "$taskLeaf/stop.txt")){throw "actual module failure: $taskName"}
  if((Get-FileHash "$taskCandidate").Hash -ne (Get-FileHash "$taskStage/ShielddSecurity/$taskName.lean").Hash){throw 'compiled source changed'}
  Write-Output "Compiled exact maintained $taskName"
 }
foreach($taskReceipt in $taskManifest.frozen_import_receipts.PSObject.Properties){
 if((Get-FileHash -LiteralPath $taskReceipt.Name).Hash.ToLowerInvariant() -ne $taskReceipt.Value){throw 'exact actual import receipt required'}
}
foreach($taskImport in $taskManifest.reused){
 if((Get-FileHash "$taskStage/ShielddSecurity/$($taskImport.name).lean").Hash.ToLowerInvariant() -ne $taskImport.source_sha256 -or (Get-FileHash "$taskStage/ShielddSecurity/$($taskImport.name).olean").Hash.ToLowerInvariant() -ne $taskImport.object_sha256){throw 'copied import pair changed'}
}
 foreach($taskDep in $taskDeps){if((Get-FileHash -LiteralPath $taskDep.path).Hash -ne $taskDep.sha256){throw 'external dependency changed'}}
 if((Get-FileHash -LiteralPath $taskAudit).Hash -ne $taskAuditHash -or (Get-FileHash -LiteralPath $PSCommandPath).Hash -ne $taskGuardHash){throw 'check recipe changed'}
 & 'C:/Users/acyrn/AppData/Local/Programs/Python/Python313/python.exe' $taskAudit $taskBatch
 if($LASTEXITCODE -ne 0){throw 'module type/axiom audit failed'}
 'Typed SourceGraph 22735 80 subgroup template, original input IDs 11 through 17, source-syntax matching, independent evaluation and all six assertions. Soundness derives OnCurve and nativeEight; completeness constructs preimage and three shared inverses from independently admitted subgroup input and named curve/codec contracts, permitting identity. Exact extracted graph instance, original rows, concrete Crypto and full Transfer remain OPEN.'|Set-Content "$taskBatch/complete.txt"
 '0'|Set-Content "$taskBatch/exit.txt"
}catch{$_|Out-String|Set-Content "$taskBatch/failure.txt";'1'|Set-Content "$taskBatch/exit.txt";throw}
finally{[DateTime]::UtcNow.ToString('o')|Set-Content "$taskBatch/end.txt"}
