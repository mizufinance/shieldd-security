from pathlib import Path
import sys,subprocess
for ci,bi,offset in [(55,0,26728),(56,0,37722),(56,1,38142)]:
 subprocess.run([sys.executable,'-B','-I','-S',str(Path(__file__).with_name('worker.py')),sys.argv[1],str(ci),str(bi),str(offset)],check=True)
