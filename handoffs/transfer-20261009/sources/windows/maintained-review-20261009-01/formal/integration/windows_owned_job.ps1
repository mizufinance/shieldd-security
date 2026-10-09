param([Parameter(Mandatory=$true)][string]$Spec)
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$taskSpec=Get-Content -LiteralPath $Spec -Raw | ConvertFrom-Json
$taskOutput=[IO.Path]::GetFullPath($taskSpec.output)
if(Test-Path -LiteralPath $taskOutput){throw 'fresh job receipt required'}
$taskSource=Join-Path $PSScriptRoot 'windows_owned_job.cs'
$taskSelfHash=(Get-FileHash -LiteralPath $PSCommandPath -Algorithm SHA256).Hash.ToLowerInvariant()
$taskSpecHash=(Get-FileHash -LiteralPath $Spec -Algorithm SHA256).Hash.ToLowerInvariant()
if($taskSelfHash -ne $taskSpec.wrapper_sha256){throw 'limiter wrapper changed'}
$taskHash=(Get-FileHash -LiteralPath $taskSource -Algorithm SHA256).Hash.ToLowerInvariant()
if($taskHash -ne $taskSpec.limiter_sha256){throw 'limiter source changed'}
if((Get-FileHash -LiteralPath $taskSpec.executable -Algorithm SHA256).Hash.ToLowerInvariant() -ne $taskSpec.executable_sha256){throw 'exact executable changed'}
if($taskSpec.memory_mib -lt 32 -or $taskSpec.memory_mib -gt 3072 -or $taskSpec.seconds -lt 1 -or $taskSpec.seconds -gt 3600){throw 'finite diagnostic budget required'}
if($taskSpec.stop_physical_kib -lt 1572864 -or $taskSpec.stop_commit_kib -lt 524288){throw 'host reserves cannot be lowered'}
if($taskSpec.admission_physical_kib -lt 2621440 -or $taskSpec.admission_commit_kib -lt 1310720){throw 'native admission cannot be lowered'}
New-Item -ItemType Directory -Path $taskOutput | Out-Null
Copy-Item -LiteralPath $Spec -Destination (Join-Path $taskOutput 'spec.json')
Add-Type -Path $taskSource
$taskResult=[ShielddOwnedWindowsJob]::Run($taskSpec.executable,[string[]]$taskSpec.arguments,$taskSpec.cwd,$taskOutput,
    [uint64]$taskSpec.memory_mib*1048576,[int]$taskSpec.seconds,[uint64]$taskSpec.admission_physical_kib*1024,
    [uint64]$taskSpec.admission_commit_kib*1024,[uint64]$taskSpec.stop_physical_kib*1024,[uint64]$taskSpec.stop_commit_kib*1024)
$taskResult | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath (Join-Path $taskOutput 'result.json')
if((Get-FileHash -LiteralPath $taskSource -Algorithm SHA256).Hash.ToLowerInvariant() -ne $taskHash){throw 'limiter source drift'}
if((Get-FileHash -LiteralPath $PSCommandPath -Algorithm SHA256).Hash.ToLowerInvariant() -ne $taskSelfHash){throw 'limiter wrapper drift'}
if((Get-FileHash -LiteralPath $Spec -Algorithm SHA256).Hash.ToLowerInvariant() -ne $taskSpecHash){throw 'owned job spec drift'}
if((Get-FileHash -LiteralPath $taskSpec.executable -Algorithm SHA256).Hash.ToLowerInvariant() -ne $taskSpec.executable_sha256){throw 'executed binary drift'}
if($taskResult.reason -ne 'completed' -or -not $taskResult.cleanupComplete -or $taskResult.exitCode -ne 0){exit 1}
Set-Content -LiteralPath (Join-Path $taskOutput 'complete.txt') -Value 'Owned process tree exited zero; source/binary stable; no runtime correspondence implied.'
