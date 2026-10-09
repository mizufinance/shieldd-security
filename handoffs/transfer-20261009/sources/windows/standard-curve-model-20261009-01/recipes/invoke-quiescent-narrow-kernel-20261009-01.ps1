param(
 [Parameter(Mandatory=$true)][string]$Guard,
 [Parameter(Mandatory=$true)][string]$GuardSha256,
 [Parameter(Mandatory=$true)][string]$Boundary
)
$ErrorActionPreference='Stop'
$taskRoot='C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002'
if($Guard -notmatch '^root-windows-[a-z0-9-]+$' -or $Boundary -notmatch '^quiescent-[a-z0-9-]+$'){throw 'named diagnostic scope required'}
$taskGuard="$taskRoot/$Guard.ps1"
$taskPacket="$taskRoot/$($Guard.Substring(5))-kernel"
$taskOutput="$taskRoot/$Boundary"
if(Test-Path -LiteralPath $taskOutput){throw 'fresh quiescent boundary required'}
if(Test-Path -LiteralPath $taskPacket){throw 'fresh kernel packet required'}
if((Get-FileHash -LiteralPath $taskGuard).Hash.ToLowerInvariant() -ne $GuardSha256){throw 'exact guard source required'}
$taskProcesses=@(Get-CimInstance Win32_Process)
if($taskProcesses|Where-Object {$_.Name -in @('lean.exe','lake.exe','cargo.exe','rustc.exe')}){throw 'one heavy verifier required'}
if($taskProcesses|Where-Object {$_.Name -eq 'pwsh.exe' -and $_.CommandLine.Contains('root-field-native-epk-cast-repair-3130')}){throw 'native controller requires its own exact safe-boundary protocol'}
. "$taskRoot/native-host-memory-api-01.ps1"
New-Item -ItemType Directory -Path $taskOutput|Out-Null
[DateTime]::UtcNow.ToString('o')|Set-Content "$taskOutput/start.txt"
$PID|Set-Content "$taskOutput/helper-owned-pid.txt"
@{kind='Quiescent host, native controller absent; no suspension or resume operation';guard_sha256=$GuardSha256;memory=(Get-TaskMemorySnapshot);heavy_processes=@();kernel_packet=$taskPacket}|ConvertTo-Json -Depth 6|Set-Content "$taskOutput/admission.json"
try{
 & $taskGuard
 if(!(Test-Path -LiteralPath "$taskPacket/end.txt") -or !(Test-Path -LiteralPath "$taskPacket/complete.txt") -or
   (Get-Content -LiteralPath "$taskPacket/exit.txt" -Raw).Trim() -ne '0'){throw 'actual scoped kernel completion required'}
 'Actual narrow kernel and type/axiom audits completed; full Transfer OPEN.'|Set-Content "$taskOutput/complete.txt"
 '0'|Set-Content "$taskOutput/exit.txt"
}catch{
 $_|Out-String|Set-Content "$taskOutput/failure.txt"
 '1'|Set-Content "$taskOutput/exit.txt"
 throw
}finally{
 'not-applicable: native controller absent; no suspend/resume performed'|Set-Content "$taskOutput/native-resume-disposition.txt"
 [DateTime]::UtcNow.ToString('o')|Set-Content "$taskOutput/end.txt"
}
