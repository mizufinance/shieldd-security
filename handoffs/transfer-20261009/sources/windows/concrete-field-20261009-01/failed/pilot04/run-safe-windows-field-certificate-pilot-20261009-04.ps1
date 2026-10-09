$ErrorActionPreference='Stop'
$taskRoot='C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002'
$taskOutput="$taskRoot/safe-field-certificate-pilot-boundary-2026100904"
$taskRootPid=3300
$taskRootSha='1ca48d4ab943f2ff9c40cab6abd34d9f45a21b7424745d19a45a490947ecd4c4'
$taskRootCommand='root-field-native-epk-cast-repair-3130'
$taskConsolePid=25376
$taskConsoleCommand='\??\C:\WINDOWS\system32\conhost.exe 0x4'
$taskConsole=Get-CimInstance Win32_Process -Filter "ProcessId=$taskConsolePid"
if($null -eq $taskConsole -or $taskConsole.ParentProcessId -ne $taskRootPid -or $taskConsole.Name -ne 'conhost.exe' -or $taskConsole.CommandLine -ne $taskConsoleCommand){throw 'exact persistent owned console host required'}
$taskConsoleCreation=$taskConsole.CreationDate
$taskSteps=@(
 @{name='windows-field-certificate-pilot-20261009-04';guard='root-windows-field-certificate-pilot-20261009-04';packet='windows-field-certificate-pilot-20261009-04-kernel';sha='0370e308e8f96b74963052cd22678064629a7eb79974318612b6b6af45d3e797'}
)
if(Test-Path -LiteralPath $taskOutput){throw 'fresh safe-boundary receipt required'}
if((Get-FileHash -LiteralPath "$taskRoot/$taskRootCommand.ps1").Hash.ToLowerInvariant() -ne $taskRootSha){throw 'exact owned controller source required'}
$taskOwned=Get-CimInstance Win32_Process -Filter "ProcessId=$taskRootPid"
if($null -eq $taskOwned -or $taskOwned.Name -ne 'pwsh.exe' -or !$taskOwned.CommandLine.Contains($taskRootCommand) -or !$taskOwned.CommandLine.Contains($taskRootSha)){throw 'exact task-owned controller process required'}
foreach($taskStep in $taskSteps){
 if((Get-FileHash -LiteralPath "$taskRoot/$($taskStep.guard).ps1").Hash.ToLowerInvariant() -ne $taskStep.sha){throw 'exact inverse guard required'}
 if(Test-Path -LiteralPath "$taskRoot/$($taskStep.packet)"){throw 'fresh inverse kernel required'}
}
Add-Type -TypeDefinition @'
using System;
using System.Runtime.InteropServices;
public static class TransferOwnedFieldCertificatePilotBoundary2026100904 {
  [DllImport("kernel32.dll", SetLastError=true)] public static extern IntPtr OpenProcess(uint access, bool inherit, uint pid);
  [DllImport("kernel32.dll")] public static extern bool CloseHandle(IntPtr handle);
  [DllImport("ntdll.dll")] public static extern int NtSuspendProcess(IntPtr handle);
  [DllImport("ntdll.dll")] public static extern int NtResumeProcess(IntPtr handle);
}
'@
$taskHandle=[TransferOwnedFieldCertificatePilotBoundary2026100904]::OpenProcess(0x1800,$false,$taskRootPid)
if($taskHandle -eq [IntPtr]::Zero){throw 'owned controller handle unavailable'}
New-Item -ItemType Directory -Path $taskOutput|Out-Null
$PID|Set-Content "$taskOutput/helper-owned-pid.txt"
$taskOwned | Select-Object ProcessId,CreationDate,Name,CommandLine | ConvertTo-Json | Set-Content "$taskOutput/root-owner.json"
[DateTime]::UtcNow.ToString('o')|Set-Content "$taskOutput/start.txt"
$taskSuspended=$false
$taskJournal=@()
$taskWaitStart=[DateTime]::UtcNow
try {
 while(!$taskSuspended){
  if(([DateTime]::UtcNow-$taskWaitStart).TotalSeconds -gt 3600){throw 'finite safe-boundary wait exceeded'}
  if(Test-Path -LiteralPath "$taskRoot/$taskRootCommand/end.txt"){throw 'owned controller settled before boundary insertion'}
  if([TransferOwnedFieldCertificatePilotBoundary2026100904]::NtSuspendProcess($taskHandle) -ne 0){throw 'owned suspension failed'}
  $taskSuspended=$true
  $taskProcesses=@(Get-CimInstance Win32_Process)
  $taskConflict=@($taskProcesses|Where-Object {
   $_.Name -in @('lean.exe','lake.exe','cargo.exe','rustc.exe') -or
   ($_.ParentProcessId -eq $taskRootPid -and !(
    $_.ProcessId -eq $taskConsolePid -and $_.Name -eq 'conhost.exe' -and
    $_.CommandLine -eq $taskConsoleCommand -and $_.CreationDate -eq $taskConsoleCreation))
  })
  $taskOpenTimed=$false
  foreach($taskFolder in @(Get-ChildItem -LiteralPath $taskRoot -Directory -Filter 'dh-primary-*-metadata-2515-guard')){
   if((Test-Path -LiteralPath "$($taskFolder.FullName)/start.txt") -and !(Test-Path -LiteralPath "$($taskFolder.FullName)/end.txt")){$taskOpenTimed=$true}
  }
  foreach($taskFolder in @(Get-ChildItem -LiteralPath $taskRoot -Directory -Filter 'narrow-dh-primary-*-2515-kernel')){
   foreach($taskLeaf in @(Get-ChildItem -LiteralPath $taskFolder.FullName -Directory)){
    if((Test-Path -LiteralPath "$($taskLeaf.FullName)/start.txt") -and !(Test-Path -LiteralPath "$($taskLeaf.FullName)/end.txt")){$taskOpenTimed=$true}
   }
  }
  if($taskConflict.Count -or $taskOpenTimed){
   if([TransferOwnedFieldCertificatePilotBoundary2026100904]::NtResumeProcess($taskHandle) -ne 0){throw 'immediate owned resume failed'}
   $taskSuspended=$false
   Start-Sleep -Milliseconds 500
  }
 }
 [DateTime]::UtcNow.ToString('o')|Set-Content "$taskOutput/suspended-at-safe-boundary.txt"
 'No heavy process, no owned child except exact persistent conhost25376, no unfinished timed metadata/kernel leaf; controller source unchanged.'|Set-Content "$taskOutput/boundary.txt"
 $taskConsole|Select-Object ProcessId,CreationDate,Name,CommandLine|ConvertTo-Json|Set-Content "$taskOutput/exempt-console-host.json"
 Write-Output 'Owned controller held between timed child builds; starting one narrow inverse check at a time.'
 foreach($taskStep in $taskSteps){
  if(Get-CimInstance Win32_Process|Where-Object {$_.Name -in @('lean.exe','lake.exe','cargo.exe','rustc.exe')}){throw 'one verifier required'}
  & "$taskRoot/$($taskStep.guard).ps1"
  $taskPacket="$taskRoot/$($taskStep.packet)"
  if(!(Test-Path -LiteralPath "$taskPacket/end.txt") -or !(Test-Path -LiteralPath "$taskPacket/complete.txt") -or (Get-Content -LiteralPath "$taskPacket/exit.txt" -Raw).Trim() -ne '0' -or (Test-Path -LiteralPath "$taskPacket/stop.txt")){throw 'actual inverse completion required'}
  $taskJournal+=@([pscustomobject]@{name=$taskStep.name;packet=$taskStep.packet;actual=$true;exit=0})
  ConvertTo-Json -InputObject @($taskJournal) -Depth 5|Set-Content "$taskOutput/journal.json"
 }
 'One actual narrow inverse/canonical checks completed; full Transfer remains OPEN.'|Set-Content "$taskOutput/complete.txt"
 '0'|Set-Content "$taskOutput/exit.txt"
}catch {
 $_|Out-String|Set-Content "$taskOutput/failure.txt"
 '1'|Set-Content "$taskOutput/exit.txt"
 throw
}finally {
 if($taskSuspended){
  $taskResume=[TransferOwnedFieldCertificatePilotBoundary2026100904]::NtResumeProcess($taskHandle)
  $taskResume|Set-Content "$taskOutput/resume-status.txt"
  if($taskResume -ne 0){Write-Error 'Owned controller resume failed; use retained root-owner receipt immediately.'}
 }
 [TransferOwnedFieldCertificatePilotBoundary2026100904]::CloseHandle($taskHandle)|Out-Null
 [DateTime]::UtcNow.ToString('o')|Set-Content "$taskOutput/end.txt"
}



