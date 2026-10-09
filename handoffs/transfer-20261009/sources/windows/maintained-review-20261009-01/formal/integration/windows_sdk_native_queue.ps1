param([Parameter(Mandatory=$true)][string]$Recipe,[Parameter(Mandatory=$true)][string]$StageSpec)
# ROOT ONLY. Every substantive executable runs in the task-owned Windows job.
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$taskRecipe=Get-Content -LiteralPath $Recipe -Raw | ConvertFrom-Json
if($env:RUSTFLAGS -or $env:CARGO_ENCODED_RUSTFLAGS){throw 'global Rust flags must be absent; exporter root cfg is explicit'}
foreach($taskInput in $taskRecipe.inputs.PSObject.Properties){
    if((Get-FileHash -LiteralPath $taskInput.Name -Algorithm SHA256).Hash.ToLowerInvariant() -ne $taskInput.Value){throw 'frozen Windows recipe source changed'}
}
if(-not (Test-Path -LiteralPath (Join-Path $taskRecipe.controls_output 'complete.txt'))){throw 'actual five job controls required before SDK'}
if($env:VCToolsVersion -ne '14.44.35207' -or -not $env:WindowsSDKVersion -or $env:WindowsSDKVersion.TrimEnd('\') -ne '10.0.22621.0'){throw 'root must supply the exact verified MSVC/SDK developer environment first'}
$taskOutput=$taskRecipe.output
if(Test-Path -LiteralPath $taskOutput){throw 'fresh SDK root receipts required'}
$taskSourceSpec=Get-Content -LiteralPath $StageSpec -Raw | ConvertFrom-Json
if($taskSourceSpec.child -ne $taskRecipe.child -or $taskSourceSpec.receipt -ne (Join-Path $taskOutput 'stage')){throw 'exact private Windows source child required'}
if(Test-Path -LiteralPath $taskRecipe.cargo_home){throw 'fresh separate Cargo cache required'}
if(Test-Path -LiteralPath $taskRecipe.target){throw 'fresh separate Cargo target required'}
if(Test-Path -LiteralPath $taskRecipe.private_binary){throw 'fresh private executable required'}
New-Item -ItemType Directory -Path $taskOutput | Out-Null
$taskStageBefore=(Get-FileHash -LiteralPath $StageSpec -Algorithm SHA256).Hash.ToLowerInvariant()
$taskSpecCopy=Join-Path $taskOutput 'actual-stage-spec.json'
Copy-Item -LiteralPath $StageSpec -Destination $taskSpecCopy
function Invoke-Owned([string]$Name,[string]$Executable,[string[]]$Arguments,[string]$Cwd,[int]$Seconds,[int]$Cap){
    $taskJob=Join-Path $taskOutput $Name
    $taskSpec=@{executable=$Executable;executable_sha256=(Get-FileHash -LiteralPath $Executable -Algorithm SHA256).Hash.ToLowerInvariant();arguments=$Arguments;cwd=$Cwd;output=$taskJob;
        limiter_sha256=$taskRecipe.limiter_sha256;wrapper_sha256=$taskRecipe.wrapper_sha256;memory_mib=$Cap;seconds=$Seconds;
        admission_physical_kib=3145728;admission_commit_kib=2097152;stop_physical_kib=1572864;stop_commit_kib=524288}
    $taskSpecFile=Join-Path $taskOutput ($Name+'-job-spec.json')
    $taskSpec | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath $taskSpecFile
    $taskWrapper=Start-Process -FilePath $taskRecipe.powershell -ArgumentList @('-NoProfile','-ExecutionPolicy','Bypass','-File',$taskRecipe.wrapper,'-Spec',$taskSpecFile) -WindowStyle Hidden -PassThru
    try {
        if(-not $taskWrapper.WaitForExit(($Seconds+90)*1000)){throw 'finite owned wrapper timeout'}
        if($taskWrapper.ExitCode -ne 0 -or -not (Test-Path -LiteralPath (Join-Path $taskJob 'complete.txt'))){throw ('owned SDK job failed: '+$Name)}
    } finally {
        if(-not $taskWrapper.HasExited){Stop-Process -Id $taskWrapper.Id -Force; $taskWrapper.WaitForExit()}
    }
    return $taskJob
}
function Check-Source {
    $taskExpected=Get-Content -LiteralPath (Join-Path $taskOutput 'stage/child-after.json') -Raw | ConvertFrom-Json
    $taskActual=@{}
    foreach($taskFile in Get-ChildItem -LiteralPath $taskRecipe.child -File -Recurse){
        if(($taskFile.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0){throw 'source reparse point refused'}
        $taskRelative=$taskFile.FullName.Substring($taskRecipe.child.Length+1).Replace('\','/')
        $taskActual[$taskRelative]=(Get-FileHash -LiteralPath $taskFile.FullName -Algorithm SHA256).Hash.ToLowerInvariant()
    }
    if($taskActual.Count -ne @($taskExpected.PSObject.Properties).Count){throw 'full source path set changed'}
    foreach($taskProperty in $taskExpected.PSObject.Properties){if($taskActual[$taskProperty.Name] -ne $taskProperty.Value){throw ('full source changed: '+$taskProperty.Name)}}
}
$null=Invoke-Owned 'stage-job' $taskRecipe.python @('-B',$taskRecipe.stage_adapter,$taskSpecCopy) $taskRecipe.formal_root 600 512
Check-Source
# The root supplies the exact developer environment. Cargo is launched directly;
# cmd.exe's command grammar is never passed through CRT argument quoting.
New-Item -ItemType Directory -Path $taskRecipe.cargo_home | Out-Null
New-Item -ItemType Directory -Path $taskRecipe.target | Out-Null
$env:CARGO_HOME=$taskRecipe.cargo_home; $env:CARGO_TARGET_DIR=$taskRecipe.target
$env:RUSTC=$taskRecipe.rustc; $env:RUSTDOC=$taskRecipe.rustdoc
$env:CARGO_BUILD_JOBS='1'; $env:RAYON_NUM_THREADS='1'; $env:CARGO_NET_GIT_FETCH_WITH_CLI='true'
$taskTests=@(@{name='epk-unit';filter='group::epk_fixed_inspection::tests';count=7},
    @{name='variable-unit';filter='group::balance_variable_inspection::tests';count=3},
    @{name='blinding-unit';filter='group::balance_blinding_fixed_inspection::tests';count=4})
foreach($taskTest in $taskTests){
    Check-Source
    $taskArguments=@('test','--locked','--profile','ci','--config','profile.ci.package.shieldd-sdk-circuits.opt-level=0','-j1','-p','shieldd-sdk-circuits','--features','formal-observer','--lib',$taskTest.filter,'--','--nocapture')
    $taskJob=Invoke-Owned $taskTest.name $taskRecipe.cargo $taskArguments $taskRecipe.child 1000 1024
    $taskLog=Get-Content -LiteralPath (Join-Path $taskJob 'stdout.txt') -Raw
    if($taskLog -notmatch [regex]::Escape('test result: ok. '+$taskTest.count+' passed; 0 failed;')){throw 'exact actual native tests did not pass'}
    Check-Source
}
$taskBuildArguments=@('rustc','-vv','--locked','--profile','ci','--config','profile.ci.package.shieldd-sdk-circuits.opt-level=0','-j1','-p','shieldd-sdk-circuits','--features','formal-observer','--example','transfer-ownership-inspection','--','--cfg','shieldd_formal_example')
$null=Invoke-Owned 'build' $taskRecipe.cargo $taskBuildArguments $taskRecipe.child 1000 1024
Check-Source
$taskBuilt=Join-Path $taskRecipe.target 'ci/examples/transfer-ownership-inspection.exe'
New-Item -ItemType Directory -Path (Split-Path -Parent $taskRecipe.private_binary) | Out-Null
Copy-Item -LiteralPath $taskBuilt -Destination $taskRecipe.private_binary
$taskBinaryHash=(Get-FileHash -LiteralPath $taskRecipe.private_binary -Algorithm SHA256).Hash.ToLowerInvariant()
if($taskBinaryHash -ne (Get-FileHash -LiteralPath $taskBuilt -Algorithm SHA256).Hash.ToLowerInvariant()){throw 'private binary differs'}
$taskBinaryHash | Set-Content -LiteralPath (Join-Path $taskOutput 'private-binary.sha256')
foreach($taskCase in @(@{name='ordinary1';mode='ordinary-spool'},@{name='ordinary2';mode='ordinary-spool'},
    @{name='epk-first';mode='epk-all-fixed-pages-spool'},@{name='epk-repeat';mode='epk-all-fixed-pages-spool'},
    @{name='variable-first';mode='balance-variable-pages-spool'},@{name='variable-repeat';mode='balance-variable-pages-spool'},
    @{name='blinding-first';mode='balance-blinding-fixed-pages-spool'},@{name='blinding-repeat';mode='balance-blinding-fixed-pages-spool'})){
    Check-Source
    if((Get-FileHash -LiteralPath $taskRecipe.private_binary -Algorithm SHA256).Hash.ToLowerInvariant() -ne $taskBinaryHash){throw 'frozen private binary drift'}
    $taskPrefix=Join-Path $taskOutput ($taskCase.name+'-capture')
    $null=Invoke-Owned $taskCase.name $taskRecipe.private_binary @($taskCase.mode,$taskPrefix) $taskRecipe.child 2400 1024
    Check-Source
}
foreach($taskKind in @('epk','variable','blinding')){
    $taskArguments=@('qualify-spools',(Join-Path $taskOutput ($taskKind+'-first-capture')),(Join-Path $taskOutput 'ordinary1-capture'),(Join-Path $taskOutput 'ordinary2-capture'),(Join-Path $taskOutput ($taskKind+'-repeat-capture')))
    $null=Invoke-Owned ($taskKind+'-qualifier') $taskRecipe.private_binary $taskArguments $taskRecipe.child 900 1024
    Check-Source
}
if((Get-FileHash -LiteralPath $StageSpec -Algorithm SHA256).Hash.ToLowerInvariant() -ne $taskStageBefore){throw 'actual source activation spec changed'}
foreach($taskInput in $taskRecipe.inputs.PSObject.Properties){
    if((Get-FileHash -LiteralPath $taskInput.Name -Algorithm SHA256).Hash.ToLowerInvariant() -ne $taskInput.Value){throw 'frozen Windows source changed during native queue'}
}
'Native tests/build/eight captures/three Rust qualifiers completed; full Linux-row correspondence still REQUIRED and UNRUN.' | Set-Content -LiteralPath (Join-Path $taskOutput 'native-complete.txt')
