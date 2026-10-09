# Read-only Windows memory snapshot. Preserve the existing reserve thresholds.
# Official field layout/units:
# https://learn.microsoft.com/en-us/windows/win32/api/psapi/ns-psapi-performance_information
if(-not ('TransferHostMemory.Native' -as [type])) {
 Add-Type -TypeDefinition @'
using System;
using System.Runtime.InteropServices;
namespace TransferHostMemory {
 [StructLayout(LayoutKind.Sequential)]
 public struct PerformanceInformation {
  public uint cb;
  public UIntPtr CommitTotal, CommitLimit, CommitPeak;
  public UIntPtr PhysicalTotal, PhysicalAvailable, SystemCache;
  public UIntPtr KernelTotal, KernelPaged, KernelNonpaged, PageSize;
  public uint HandleCount, ProcessCount, ThreadCount;
 }
 public static class Native {
  [DllImport("psapi.dll", SetLastError=true)]
  [return: MarshalAs(UnmanagedType.Bool)]
  public static extern bool GetPerformanceInfo(out PerformanceInformation info, uint cb);
 }
}
'@
}
function Get-TaskMemorySnapshot {
 $taskInfo=[TransferHostMemory.PerformanceInformation]::new()
 $taskSize=[Runtime.InteropServices.Marshal]::SizeOf($taskInfo)
 $taskWatch=[Diagnostics.Stopwatch]::StartNew()
 if(-not [TransferHostMemory.Native]::GetPerformanceInfo([ref]$taskInfo,$taskSize)){throw 'native host memory API failed'}
 $taskWatch.Stop()
 if($taskWatch.ElapsedMilliseconds -gt 1000){throw 'native host memory API stale'}
 $taskPage=$taskInfo.PageSize.ToUInt64()
 $taskLimit=$taskInfo.CommitLimit.ToUInt64()
 $taskTotal=$taskInfo.CommitTotal.ToUInt64()
 $taskPhysical=$taskInfo.PhysicalAvailable.ToUInt64()
 if($taskPage -lt 1024 -or $taskPage -gt 65536 -or $taskLimit -lt $taskTotal -or $taskPhysical -gt $taskInfo.PhysicalTotal.ToUInt64()){throw 'invalid native host memory snapshot'}
 [pscustomobject]@{
  PhysicalKiB=[Math]::Floor(([decimal]$taskPhysical*$taskPage)/1024)
  CommitFreeKiB=[Math]::Floor(([decimal]($taskLimit-$taskTotal)*$taskPage)/1024)
  CommitLimitBytes=[decimal]$taskLimit*$taskPage
  CommitTotalBytes=[decimal]$taskTotal*$taskPage
  ApiMilliseconds=$taskWatch.Elapsed.TotalMilliseconds
 }
}
