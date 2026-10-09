// Root-run diagnostic limiter. No breakaway flags, global process enumeration,
// named jobs, or PID-based termination. Assign before the first instruction runs.
using System;
using System.ComponentModel;
using System.Diagnostics;
using System.IO;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading;

public static class ShielddOwnedWindowsJob {
    [StructLayout(LayoutKind.Sequential)] struct Limits {
        public long userTime, jobTime; public uint flags;
        public UIntPtr minWorking, maxWorking; public uint activeLimit;
        public UIntPtr affinity; public uint priority, scheduling;
    }
    [StructLayout(LayoutKind.Sequential)] struct Io {
        public ulong readOps, writeOps, otherOps, readBytes, writeBytes, otherBytes;
    }
    [StructLayout(LayoutKind.Sequential)] struct Extended {
        public Limits basic; public Io io;
        public UIntPtr processMemory, jobMemory, peakProcessMemory, peakJobMemory;
    }
    [StructLayout(LayoutKind.Sequential)] struct Accounting {
        public long user, kernel, periodUser, periodKernel;
        public uint faults, total, active, terminated;
    }
    [StructLayout(LayoutKind.Sequential)] struct Port { public IntPtr key, handle; }
    [StructLayout(LayoutKind.Sequential)] struct Security {
        public uint length; public IntPtr descriptor; public int inherit;
    }
    [StructLayout(LayoutKind.Sequential, CharSet=CharSet.Unicode)] struct Startup {
        public uint cb; public IntPtr reserved, desktop, title;
        public uint x,y,width,height,xchars,ychars,fill,flags;
        public ushort show,reservedBytes; public IntPtr reservedData,input,output,error;
    }
    [StructLayout(LayoutKind.Sequential)] struct ProcessInfo {
        public IntPtr process, thread; public uint pid, tid;
    }
    [StructLayout(LayoutKind.Sequential)] struct Memory {
        public uint length, load;
        public ulong totalPhysical, availablePhysical, totalCommit, availableCommit,
            totalVirtual, availableVirtual, extendedVirtual;
    }
    [DllImport("kernel32.dll",SetLastError=true,CharSet=CharSet.Unicode)] static extern IntPtr CreateJobObject(IntPtr security,string name);
    [DllImport("kernel32.dll",SetLastError=true)] static extern bool SetInformationJobObject(IntPtr job,int kind,IntPtr info,uint length);
    [DllImport("kernel32.dll",SetLastError=true)] static extern bool QueryInformationJobObject(IntPtr job,int kind,IntPtr info,uint length,IntPtr returned);
    [DllImport("kernel32.dll",SetLastError=true)] static extern bool AssignProcessToJobObject(IntPtr job,IntPtr process);
    [DllImport("kernel32.dll",SetLastError=true)] static extern bool TerminateJobObject(IntPtr job,uint code);
    [DllImport("kernel32.dll",SetLastError=true)] static extern bool TerminateProcess(IntPtr process,uint code);
    [DllImport("kernel32.dll",SetLastError=true)] static extern bool CloseHandle(IntPtr handle);
    [DllImport("kernel32.dll",SetLastError=true)] static extern uint ResumeThread(IntPtr thread);
    [DllImport("kernel32.dll",SetLastError=true)] static extern bool GetExitCodeProcess(IntPtr process,out uint code);
    [DllImport("kernel32.dll",SetLastError=true)] static extern IntPtr CreateIoCompletionPort(IntPtr file,IntPtr existing,UIntPtr key,uint threads);
    [DllImport("kernel32.dll",SetLastError=true)] static extern bool GetQueuedCompletionStatus(IntPtr port,out uint bytes,out UIntPtr key,out IntPtr overlapped,uint milliseconds);
    [DllImport("kernel32.dll",SetLastError=true)] static extern bool GlobalMemoryStatusEx(ref Memory memory);
    [DllImport("kernel32.dll",SetLastError=true,CharSet=CharSet.Unicode)] static extern IntPtr CreateFile(string path,uint access,uint sharing,ref Security security,uint creation,uint attributes,IntPtr template);
    [DllImport("kernel32.dll",SetLastError=true,CharSet=CharSet.Unicode)] static extern bool CreateProcess(string executable,StringBuilder command,IntPtr processSecurity,IntPtr threadSecurity,bool inherit,uint flags,IntPtr environment,string cwd,ref Startup startup,out ProcessInfo process);

    public sealed class Result {
        public uint pid, exitCode, activeAfter, totalProcesses;
        public ulong jobMemoryLimit, peakJobCommit, minimumPhysical=UInt64.MaxValue, minimumCommit=UInt64.MaxValue;
        public string reason="", launchError="";
        public bool launched, assignedBeforeResume, cleanupComplete;
        public double seconds;
    }
    static void Check(bool ok) { if (!ok) throw new Win32Exception(Marshal.GetLastWin32Error()); }
    static void Set<T>(IntPtr job,int kind,T value) {
        int size=Marshal.SizeOf(typeof(T)); IntPtr p=Marshal.AllocHGlobal(size);
        try { Marshal.StructureToPtr(value,p,false); Check(SetInformationJobObject(job,kind,p,(uint)size)); }
        finally { Marshal.FreeHGlobal(p); }
    }
    static T Get<T>(IntPtr job,int kind) {
        int size=Marshal.SizeOf(typeof(T)); IntPtr p=Marshal.AllocHGlobal(size);
        try { Check(QueryInformationJobObject(job,kind,p,(uint)size,IntPtr.Zero)); return (T)Marshal.PtrToStructure(p,typeof(T)); }
        finally { Marshal.FreeHGlobal(p); }
    }
    static Memory Sample(Result result) {
        Memory m=new Memory(); m.length=(uint)Marshal.SizeOf(typeof(Memory)); Check(GlobalMemoryStatusEx(ref m));
        result.minimumPhysical=Math.Min(result.minimumPhysical,m.availablePhysical);
        result.minimumCommit=Math.Min(result.minimumCommit,m.availableCommit); return m;
    }
    // CommandLineToArgv-compatible quoting: trailing backslashes double before quote.
    public static string Quote(string value) {
        if(value==null || value.IndexOf('\0')>=0) throw new ArgumentException("invalid argument");
        StringBuilder s=new StringBuilder("\""); int slashes=0;
        foreach(char c in value) {
            if(c=='\\') { slashes++; continue; }
            if(c=='\"') { s.Append('\\',slashes*2+1); s.Append(c); }
            else { s.Append('\\',slashes); s.Append(c); } slashes=0;
        }
        s.Append('\\',slashes*2); return s.Append('"').ToString();
    }
    public static Result Run(string executable,string[] args,string cwd,string outputDirectory,
        ulong memoryBytes,int seconds,ulong admissionPhysical,ulong admissionCommit,
        ulong stopPhysical,ulong stopCommit) {
        if(IntPtr.Size!=8 || memoryBytes<33554432 || seconds<1 || seconds>3600 ||
            admissionPhysical<stopPhysical || admissionCommit<stopCommit ||
            !Path.IsPathRooted(executable) || !File.Exists(executable) || !Directory.Exists(cwd) ||
            !Directory.Exists(outputDirectory)) throw new ArgumentException("invalid finite owned-job contract");
        Result result=new Result(); Stopwatch clock=Stopwatch.StartNew();
        IntPtr job=IntPtr.Zero,port=IntPtr.Zero,stdout=IntPtr.Zero,stderr=IntPtr.Zero,stdin=IntPtr.Zero;
        ProcessInfo pi=new ProcessInfo(); bool assigned=false;
        try {
            Memory initial=Sample(result);
            if(initial.availablePhysical<admissionPhysical || initial.availableCommit<admissionCommit) {
                result.reason="admission-refused"; return result;
            }
            job=CreateJobObject(IntPtr.Zero,null); Check(job!=IntPtr.Zero);
            Extended limit=new Extended(); limit.basic.flags=0x2000|0x200; // KILL_ON_JOB_CLOSE + JOB_MEMORY
            limit.jobMemory=new UIntPtr(memoryBytes); Set(job,9,limit);
            Extended installed=Get<Extended>(job,9); result.jobMemoryLimit=installed.jobMemory.ToUInt64();
            if(result.jobMemoryLimit!=memoryBytes || installed.basic.flags!=limit.basic.flags) throw new InvalidOperationException("job limit readback differs");
            port=CreateIoCompletionPort(new IntPtr(-1),IntPtr.Zero,UIntPtr.Zero,1); Check(port!=IntPtr.Zero);
            Port binding=new Port(); binding.key=new IntPtr(1); binding.handle=port; Set(job,7,binding);
            Security security=new Security(); security.length=(uint)Marshal.SizeOf(typeof(Security)); security.inherit=1;
            stdout=CreateFile(Path.Combine(outputDirectory,"stdout.txt"),0x40000000,1,ref security,1,0x80,IntPtr.Zero); Check(stdout!=new IntPtr(-1));
            stderr=CreateFile(Path.Combine(outputDirectory,"stderr.txt"),0x40000000,1,ref security,1,0x80,IntPtr.Zero); Check(stderr!=new IntPtr(-1));
            stdin=CreateFile("NUL",0x80000000,1,ref security,3,0x80,IntPtr.Zero); Check(stdin!=new IntPtr(-1));
            Startup si=new Startup(); si.cb=(uint)Marshal.SizeOf(typeof(Startup)); si.flags=0x100;
            si.input=stdin; si.output=stdout; si.error=stderr;
            StringBuilder command=new StringBuilder(Quote(executable));
            foreach(string arg in args) command.Append(" ").Append(Quote(arg));
            Check(CreateProcess(executable,command,IntPtr.Zero,IntPtr.Zero,true,0x4|0x08000000,IntPtr.Zero,cwd,ref si,out pi));
            result.pid=pi.pid; result.launched=true;
            Check(AssignProcessToJobObject(job,pi.process)); assigned=true; result.assignedBeforeResume=true;
            Check(ResumeThread(pi.thread)!=UInt32.MaxValue);
            using(StreamWriter samples=new StreamWriter(Path.Combine(outputDirectory,"memory.csv"),false)) {
                samples.WriteLine("utc,physical_free,commit_free,job_peak_commit,active,total");
                while(true) {
                    uint message; UIntPtr key; IntPtr detail;
                    while(GetQueuedCompletionStatus(port,out message,out key,out detail,0)) {
                        if(message==9 || message==10) result.reason="job-memory-limit";
                    }
                    Memory memory=Sample(result); Accounting account=Get<Accounting>(job,1); Extended usage=Get<Extended>(job,9);
                    result.peakJobCommit=usage.peakJobMemory.ToUInt64(); result.activeAfter=account.active; result.totalProcesses=account.total;
                    samples.WriteLine(DateTime.UtcNow.ToString("o")+","+memory.availablePhysical+","+memory.availableCommit+","+result.peakJobCommit+","+account.active+","+account.total); samples.Flush();
                    if(memory.availablePhysical<stopPhysical || memory.availableCommit<stopCommit) result.reason="host-memory-pressure";
                    if(clock.Elapsed.TotalSeconds>=seconds && result.reason=="") result.reason="wall-time-limit";
                    // Memory messages are advisory; a near-cap sample also refuses success.
                    if(result.peakJobCommit>=memoryBytes-memoryBytes/50 && result.reason=="") result.reason="job-memory-near-limit";
                    if(result.reason!="") break;
                    if(account.active==0) { Check(GetExitCodeProcess(pi.process,out result.exitCode)); result.reason=result.exitCode==0?"completed":"child-exit"; break; }
                    Thread.Sleep(400);
                }
            }
        } catch(Exception e) { result.reason="launch-or-monitor-error"; result.launchError=e.ToString(); }
        finally {
            if(job!=IntPtr.Zero) {
                // Always own only this job; no arbitrary child PID or process-name kill.
                if(assigned) {
                    if(result.reason!="completed" && result.reason!="child-exit") TerminateJobObject(job,124);
                    Stopwatch cleanup=Stopwatch.StartNew();
                    try {
                        do { Accounting a=Get<Accounting>(job,1); result.activeAfter=a.active; result.totalProcesses=a.total; if(a.active==0) break; Thread.Sleep(50); } while(cleanup.Elapsed.TotalSeconds<10);
                        result.cleanupComplete=result.activeAfter==0;
                        uint code; if(pi.process!=IntPtr.Zero && GetExitCodeProcess(pi.process,out code)) result.exitCode=code;
                    } catch(Exception e) { result.cleanupComplete=false; result.launchError+=" cleanup: "+e.Message; }
                }
                CloseHandle(job); // Kernel fallback also kills assigned descendants.
            }
            if(pi.process!=IntPtr.Zero && !assigned) TerminateProcess(pi.process,124); // still suspended, never ran
            foreach(IntPtr handle in new IntPtr[]{pi.thread,pi.process,port,stdout,stderr,stdin})
                if(handle!=IntPtr.Zero && handle!=new IntPtr(-1)) CloseHandle(handle);
            result.seconds=clock.Elapsed.TotalSeconds;
        }
        return result;
    }
}
