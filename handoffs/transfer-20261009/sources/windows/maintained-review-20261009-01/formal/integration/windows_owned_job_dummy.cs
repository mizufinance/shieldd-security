// Root-only semantic controls for the limiter; compiling/launching is never a source test.
using System;
using System.Diagnostics;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using System.Threading;
public class ShielddOwnedJobDummy {
    [DllImport("kernel32.dll",SetLastError=true)] static extern IntPtr VirtualAlloc(IntPtr address,UIntPtr bytes,uint kind,uint protection);
    public static int Main(string[] args) {
        if(args.Length!=1) return 2;
        if(args[0]=="ok") { Console.WriteLine("actual-ok"); return 0; }
        if(args[0]=="nonzero") { Console.WriteLine("actual-nonzero"); return 17; }
        if(args[0]=="sleep") { Console.WriteLine("actual-sleeper "+Process.GetCurrentProcess().Id); Console.Out.Flush(); Thread.Sleep(60000); return 0; }
        if(args[0]=="tree") {
            Process child=Process.Start(new ProcessStartInfo(Process.GetCurrentProcess().MainModule.FileName,"sleep") {UseShellExecute=false,CreateNoWindow=true});
            Console.WriteLine("actual-descendant "+child.Id); Console.Out.Flush(); Thread.Sleep(60000); return 0;
        }
        if(args[0]=="memory") {
            const int requested=100663296; // Same 96MiB allocation in baseline and constrained job.
            IntPtr p=VirtualAlloc(IntPtr.Zero,new UIntPtr(requested),0x3000,4);
            if(p==IntPtr.Zero) {
                Console.WriteLine("actual-allocation-denied requested="+requested+" win32="+Marshal.GetLastWin32Error());
                Console.Out.Flush(); Thread.Sleep(1500); return 42;
            }
            for(int offset=0;offset<requested;offset+=4096) Marshal.WriteByte(p,offset,1);
            Console.WriteLine("actual-allocation-succeeded requested="+requested); Console.Out.Flush(); Thread.Sleep(1500); return 0;
        }
        return 2;
    }
}
