$ErrorActionPreference='Stop'
$taskRoot='C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002'
$taskSource="$taskRoot/windows-concrete-point-20261009-04-source"
$taskBatch="$taskRoot/windows-concrete-point-20261009-04-kernel"
$taskStage="$taskBatch/project"
$taskExternal="$taskRoot/windows-jubjub-isolated-05/modules"
$taskLean='C:/Users/acyrn/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean.exe'
$taskAudit="$taskRoot/audit-windows-concrete-point-20261009-04.py"
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
$taskComposer='C:/src/shieldd-transfer-handoffs/compose-concrete-point-cache-20261009-04.py'
if((Get-FileHash -LiteralPath $taskComposer).Hash.ToLowerInvariant() -ne 'c78f7826189ca98f242c661425d756e61f791d00d8741dd7a8f6e2950dc08811'){throw 'exact diagnostic cache composer required'}
& 'C:/Users/acyrn/AppData/Local/Programs/Python/Python313/python.exe' $taskComposer $taskStage
if($LASTEXITCODE -ne 0){throw 'complete diagnostic cache composition required'}
[DateTime]::UtcNow.ToString('o')|Set-Content "$taskBatch/start.txt"
Copy-Item -LiteralPath "$taskSource/manifest.json" -Destination "$taskBatch/manifest.json"
Copy-Item -LiteralPath "$taskRoot/windows-jubjub-isolated-05/inputs.json" -Destination "$taskBatch/cache-inputs.json"
@{guard_sha256=$taskGuardHash;audit_sha256=$taskAuditHash;threads=1;memory_MiB=1536;finite_seconds_per_module=240}|ConvertTo-Json|Set-Content "$taskBatch/recipe.json"
foreach($taskReceipt in $taskManifest.frozen_import_receipts.PSObject.Properties){
 if((Get-FileHash -LiteralPath $taskReceipt.Name).Hash.ToLowerInvariant() -ne $taskReceipt.Value){throw 'exact actual import receipt required'}
}
foreach($taskImport in $taskManifest.reused){
 if((Get-FileHash -LiteralPath $taskImport.source).Hash.ToLowerInvariant() -ne $taskImport.source_sha256 -or (Get-FileHash -LiteralPath $taskImport.object).Hash.ToLowerInvariant() -ne $taskImport.object_sha256){throw 'exact qualified import pair required'}
 Copy-Item -LiteralPath $taskImport.source -Destination "$taskStage/$($taskImport.lean_relative_path)"
 Copy-Item -LiteralPath $taskImport.object -Destination "$taskStage/$($taskImport.lean_relative_path.Replace('.lean','.olean'))"
 foreach($taskExtra in $taskImport.sidecars){
  if((Get-FileHash -LiteralPath $taskExtra.path).Hash.ToLowerInvariant() -ne $taskExtra.sha256){throw 'qualified companion changed'}
  Copy-Item -LiteralPath $taskExtra.path -Destination "$taskStage/$($taskExtra.lean_relative_path)"
 }

}
$taskDeps=@(Get-ChildItem -LiteralPath $taskExternal -Recurse -File|ForEach-Object {[ordered]@{path=$_.FullName;sha256=(Get-FileHash -LiteralPath $_.FullName).Hash}})
ConvertTo-Json -InputObject $taskDeps -Depth 4|Set-Content "$taskBatch/external-before.json"
$env:LEAN_PATH="$taskStage"
$env:LEAN_NUM_THREADS='1'
try{
 foreach($taskName in $taskManifest.order){
  $taskMemory=Get-TaskMemorySnapshot
  if($taskMemory.PhysicalKiB -lt 3145728 -or $taskMemory.CommitFreeKiB -lt 2621440){throw 'memory admission required'}
  $taskRelativeSource=$taskManifest.sources.$taskName.lean_relative_path
  $taskRelativeObject=$taskRelativeSource.Replace('.lean','.olean')
  $taskLeaf="$taskBatch/$taskName"
  New-Item -ItemType Directory -Path $taskLeaf|Out-Null
  $taskCandidate="$taskSource/$taskName-audited.lean"
  New-Item -ItemType Directory -Path (Split-Path -Parent "$taskStage/$taskRelativeSource") -Force|Out-Null
  Copy-Item -LiteralPath $taskCandidate -Destination "$taskStage/$taskRelativeSource"
  $taskStart=[DateTime]::UtcNow
  $taskStart.ToString('o')|Set-Content "$taskLeaf/start.txt"
  $taskJob=Start-Process -FilePath $taskLean -ArgumentList @('-j1','-M','1536','-o',"$taskStage/$taskRelativeObject","$taskStage/$taskRelativeSource") -WorkingDirectory $taskStage -RedirectStandardOutput "$taskLeaf/stdout.txt" -RedirectStandardError "$taskLeaf/stderr.txt" -PassThru -WindowStyle Hidden
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
  if((Get-FileHash "$taskCandidate").Hash -ne (Get-FileHash "$taskStage/$taskRelativeSource").Hash){throw 'compiled source changed'}
  Write-Output "Compiled exact maintained $taskName"
 }
foreach($taskReceipt in $taskManifest.frozen_import_receipts.PSObject.Properties){
 if((Get-FileHash -LiteralPath $taskReceipt.Name).Hash.ToLowerInvariant() -ne $taskReceipt.Value){throw 'exact actual import receipt required'}
}
foreach($taskImport in $taskManifest.reused){
 if((Get-FileHash "$taskStage/$($taskImport.lean_relative_path)").Hash.ToLowerInvariant() -ne $taskImport.source_sha256 -or (Get-FileHash "$taskStage/$($taskImport.lean_relative_path.Replace('.lean','.olean'))").Hash.ToLowerInvariant() -ne $taskImport.object_sha256){throw 'copied import pair changed'}
}
 foreach($taskImport in $taskManifest.reused){foreach($taskExtra in $taskImport.sidecars){
 if((Get-FileHash -LiteralPath "$taskStage/$($taskExtra.lean_relative_path)").Hash.ToLowerInvariant() -ne $taskExtra.sha256){throw 'copied qualified companion changed'}
 }}
 foreach($taskDep in $taskDeps){if((Get-FileHash -LiteralPath $taskDep.path).Hash -ne $taskDep.sha256){throw 'external dependency changed'}}
 if((Get-FileHash -LiteralPath $taskAudit).Hash -ne $taskAuditHash -or (Get-FileHash -LiteralPath $PSCommandPath).Hash -ne $taskGuardHash){throw 'check recipe changed'}
 & 'C:/Users/acyrn/AppData/Local/Programs/Python/Python313/python.exe' $taskAudit $taskBatch
 if($LASTEXITCODE -ne 0){throw 'module type/axiom audit failed'}
 'Concrete certified field and parameters instantiate Mathlib affine curve: exact discriminant, ellipticity, full Edwards point-set bijection and exceptional identity/torsion images. Addition homomorphism, StandardCurveModel, cardinality, full curve order and native representation OPEN.'|Set-Content "$taskBatch/complete.txt"
 '0'|Set-Content "$taskBatch/exit.txt"
}catch{$_|Out-String|Set-Content "$taskBatch/failure.txt";'1'|Set-Content "$taskBatch/exit.txt";throw}
finally{[DateTime]::UtcNow.ToString('o')|Set-Content "$taskBatch/end.txt"}
