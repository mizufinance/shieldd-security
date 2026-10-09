$ErrorActionPreference='Stop'
$taskRoot='C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002'
$taskBatch="$taskRoot/windows-point-cache-20261009-02-cache"
if(Test-Path -LiteralPath $taskBatch){throw 'fresh qualified-artifact retrieval receipt required'}
if(Get-CimInstance Win32_Process|Where-Object {$_.Name -in @('lean.exe','lake.exe','cargo.exe','rustc.exe')}){throw 'one heavy job required'}
. "$taskRoot/native-host-memory-api-01.ps1"
$taskMemory=Get-TaskMemorySnapshot
if($taskMemory.PhysicalKiB -lt 1572864 -or $taskMemory.CommitFreeKiB -lt 524288){throw 'existing host reserves required'}
if((Get-PSDrive C).Free -lt 4294967296){throw 'four GiB disk headroom required'}
New-Item -ItemType Directory -Path $taskBatch|Out-Null
$taskStart=[DateTime]::UtcNow
$taskStart.ToString('o')|Set-Content "$taskBatch/start.txt"
$taskScript='C:/src/shieldd-transfer-handoffs/fetch-point-official-artifacts-20261009-02.py'
$taskCatalog='C:/src/shieldd-transfer-handoffs/PointCacheHashCatalog01.lean'
$taskCleanup='C:/src/shieldd-transfer-handoffs/stop-point-owned-fetch-20261009-02.py'
@{fetch_sha256=(Get-FileHash -LiteralPath $taskScript).Hash;catalog_sha256=(Get-FileHash -LiteralPath $taskCatalog).Hash;cleanup_sha256=(Get-FileHash -LiteralPath $taskCleanup).Hash;finite_seconds=240;dependency_cap_bytes=2147483648;lean_heap_MiB=1536;threads=1}|ConvertTo-Json|Set-Content "$taskBatch/recipe.json"
$taskJob=Start-Process -FilePath 'wsl.exe' -ArgumentList @('-e','python3','/mnt/c/src/shieldd-transfer-handoffs/fetch-point-official-artifacts-20261009-02.py') -RedirectStandardOutput "$taskBatch/stdout.txt" -RedirectStandardError "$taskBatch/stderr.txt" -PassThru -WindowStyle Hidden
$taskJob.Id|Set-Content "$taskBatch/owned-pid.txt"
try{
 while(!$taskJob.HasExited){
  $taskJob.Refresh();$taskMemory=Get-TaskMemorySnapshot
  ([DateTime]::UtcNow.ToString('o')+' '+$taskMemory.PhysicalKiB+' '+$taskMemory.CommitFreeKiB)|Add-Content "$taskBatch/memory.txt"
  if($taskMemory.PhysicalKiB -lt 1572864 -or $taskMemory.CommitFreeKiB -lt 524288){'host-memory-pressure'|Set-Content "$taskBatch/stop.txt";break}
  if(([DateTime]::UtcNow-$taskStart).TotalSeconds -ge 240){'finite-240s-budget'|Set-Content "$taskBatch/stop.txt";break}
  Start-Sleep -Milliseconds 400
 }
}finally{
 if(!$taskJob.HasExited){
  & wsl.exe -e python3 /mnt/c/src/shieldd-transfer-handoffs/stop-point-owned-fetch-20261009-02.py
  if($LASTEXITCODE -ne 0){throw 'owned Linux process group cleanup failed'}
  Stop-Process -Id $taskJob.Id -Force -ErrorAction SilentlyContinue
 }
 $taskJob.WaitForExit();$taskJob.ExitCode|Set-Content "$taskBatch/exit.txt"
 [DateTime]::UtcNow.ToString('o')|Set-Content "$taskBatch/end.txt"
}
if($taskJob.ExitCode -ne 0 -or(Test-Path -LiteralPath "$taskBatch/stop.txt")){throw 'qualified Point artifact retrieval failed; zero credit'}
if(!(Test-Path -LiteralPath 'C:/src/shieldd-transfer-handoffs/point-artifact-stage-20261009-02/receipt.json')){throw 'actual qualified closure receipt missing'}
'qualified artifact retrieval, not proof'|Set-Content "$taskBatch/complete.txt"
Get-Content -LiteralPath "$taskBatch/stdout.txt"
