param([Parameter(Mandatory=$true)][string]$Recipe)
# ROOT ONLY: this script compiles and launches real dummy processes. Source prep
# never invokes it. A compilation/admission failure is not a semantic control.
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$taskRecipe=Get-Content -LiteralPath $Recipe -Raw | ConvertFrom-Json
foreach($taskInput in $taskRecipe.inputs.PSObject.Properties){
    if((Get-FileHash -LiteralPath $taskInput.Name -Algorithm SHA256).Hash.ToLowerInvariant() -ne $taskInput.Value){throw 'control source changed'}
}
$taskRoot=$taskRecipe.output
if(Test-Path -LiteralPath $taskRoot){throw 'fresh controls receipt required'}
New-Item -ItemType Directory -Path $taskRoot | Out-Null
$taskDummy=Join-Path $taskRoot 'owned-dummy.exe'
Add-Type -Path $taskRecipe.dummy_source -OutputAssembly $taskDummy -OutputType ConsoleApplication
$taskDummyHash=(Get-FileHash -LiteralPath $taskDummy -Algorithm SHA256).Hash.ToLowerInvariant()
$taskCases=@(
    @{name='ok';mode='ok';seconds=10;cap=64;reason='completed';marker='actual-ok'},
    @{name='nonzero';mode='nonzero';seconds=10;cap=64;reason='child-exit';marker='actual-nonzero'},
    @{name='descendants';mode='tree';seconds=3;cap=96;reason='wall-time-limit';marker='actual-descendant'},
    @{name='memory-baseline';mode='memory';seconds=15;cap=256;reason='completed';marker='actual-allocation-succeeded requested=100663296'},
    @{name='memory';mode='memory';seconds=15;cap=64;reason='job-memory';marker=''}
)
foreach($taskCase in $taskCases){
    $taskSpec=@{executable=$taskDummy;executable_sha256=$taskDummyHash;arguments=@($taskCase.mode);cwd=$taskRoot;
        output=(Join-Path $taskRoot $taskCase.name);limiter_sha256=$taskRecipe.limiter_sha256;wrapper_sha256=$taskRecipe.wrapper_sha256;
        memory_mib=$taskCase.cap;seconds=$taskCase.seconds;admission_physical_kib=2621440;admission_commit_kib=1310720;
        stop_physical_kib=1572864;stop_commit_kib=524288}
    $taskSpecPath=Join-Path $taskRoot ($taskCase.name+'-spec.json')
    $taskSpec | ConvertTo-Json -Depth 5 | Set-Content -LiteralPath $taskSpecPath
    # Each wrapper compiles only the tiny limiter and owns exactly one dummy tree.
    $taskWrapper=Start-Process -FilePath $taskRecipe.powershell -ArgumentList @('-NoProfile','-ExecutionPolicy','Bypass','-File',$taskRecipe.wrapper,'-Spec',$taskSpecPath) -WindowStyle Hidden -Wait -PassThru
    $taskResult=Get-Content -LiteralPath (Join-Path $taskSpec.output 'result.json') -Raw | ConvertFrom-Json
    if(-not $taskResult.launched -or -not $taskResult.assignedBeforeResume -or -not $taskResult.cleanupComplete -or $taskResult.activeAfter -ne 0){throw 'owned-tree lifecycle control did not complete'}
    $taskStdout=Get-Content -LiteralPath (Join-Path $taskSpec.output 'stdout.txt') -Raw
    if($taskCase.marker -and $taskStdout -notmatch [regex]::Escape($taskCase.marker)){throw 'intended child action not observed'}
    if($taskCase.name -eq 'memory'){
        if($taskStdout -notmatch 'actual-allocation-denied requested=100663296 win32=(8|1455)' -or $taskResult.jobMemoryLimit -ne 67108864){throw 'actual denied commit at queried cap not observed'}
        if($taskResult.reason -eq 'child-exit'){
            if($taskResult.exitCode -ne 42){throw 'allocation denial exit not preserved'}
        }elseif($taskResult.reason -notin @('job-memory-limit','job-memory-near-limit')){throw 'wrong semantic memory failure'}
    }elseif($taskResult.reason -ne $taskCase.reason){throw 'wrong semantic control failure'}
    if($taskCase.name -eq 'descendants' -and $taskResult.totalProcesses -lt 2){throw 'no descendant entered owned job'}
    if($taskCase.name -eq 'descendants'){
        $taskPidMatch=[regex]::Match($taskStdout,'actual-descendant ([0-9]+)')
        if(-not $taskPidMatch.Success){throw 'actual owned descendant PID missing'}
        if(Get-Process -Id ([int]$taskPidMatch.Groups[1].Value) -ErrorAction SilentlyContinue){throw 'owned descendant PID remains alive'}
        if(Get-Process -Id ([int]$taskResult.pid) -ErrorAction SilentlyContinue){throw 'owned root PID remains alive'}
    }
    if($taskCase.name -eq 'memory-baseline' -and ($taskResult.exitCode -ne 0 -or $taskWrapper.ExitCode -ne 0 -or $taskResult.jobMemoryLimit -ne 268435456)){throw 'independent same-allocation baseline did not succeed'}
    if($taskCase.name -eq 'ok' -and ($taskWrapper.ExitCode -ne 0 -or $taskResult.exitCode -ne 0)){throw 'normal completion refused'}
    if($taskCase.name -eq 'nonzero' -and $taskResult.exitCode -ne 17){throw 'child exit was not preserved'}
    if($taskCase.name -notin @('ok','memory-baseline') -and $taskWrapper.ExitCode -eq 0){throw 'resource/nonzero stop incorrectly marked complete'}
}
foreach($taskInput in $taskRecipe.inputs.PSObject.Properties){
    if((Get-FileHash -LiteralPath $taskInput.Name -Algorithm SHA256).Hash.ToLowerInvariant() -ne $taskInput.Value){throw 'control source changed during tests'}
}
'Five actual owned-job controls passed: normal, nonzero, descendant timeout, independent allocation baseline and denied commit at queried job cap. No circuit negative-control credit.' | Set-Content -LiteralPath (Join-Path $taskRoot 'complete.txt')
