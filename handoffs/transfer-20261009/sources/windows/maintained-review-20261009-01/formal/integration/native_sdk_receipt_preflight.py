"""Strict adoption of the real SDK build, units and ordinary capture receipts.

This is prelaunch identity/admission plumbing, never runtime qualification.
The native qualifier must still compare complete ordinary and repeated spools.
"""
from pathlib import Path
import hashlib
import re
import sys
try:
    from . import native_receipt_framing as framing
except ImportError:
    import native_receipt_framing as framing

BINARY='571e86929c05c72f502ad7d8d2c6153f23abfda692dea18ec71f8e9aa471e88b'
BINARY_PATH='/root/.cache/shieldd-security-verification/transfer-epk-balance-blinding-binary-20261004-03/transfer-ownership-inspection'
BASE=('epk-all-unit-guard-09','epk-all-balance-unit-09','balance-blinding-unit-guard-07',
      'epk-all-build-guard-14','epk-all-ordinary1-13','epk-all-ordinary2-13')

def bounded(path, maximum=4194304):
    path=Path(path)
    if not path.is_file() or path.is_symlink():raise ValueError('real regular receipt required')
    with path.open('rb') as handle:data=handle.read(maximum+1)
    if len(data)>maximum:raise ValueError('bounded SDK prerequisite receipt required')
    return data

def verify(root, extra=()):
    root=Path(root)
    for job in (*BASE,*extra):
        if not re.fullmatch('[A-Za-z0-9-]+',job):raise ValueError('closed owned job name required')
        directory=root/job
        framing.verify([directory/'exit.txt',directory/'wrapper-exit.txt'])
        bounded(directory/'end.txt',128)
        if (directory/'stop.txt').exists() or (directory/'wrapper-exception.txt').exists():
            raise ValueError('stopped/failed prerequisite is not success')
        for left,right in [('sdk-source-before.txt','sdk-source-after.txt'),
                           ('formal-exporters-before.txt','formal-exporters-after.txt'),
                           ('source-inputs.txt','source-inputs-after.txt'),
                           ('runner-script-before.txt','runner-script-after.txt')]:
            if bounded(directory/left)!=bounded(directory/right):raise ValueError('SDK prerequisite source changed')
        if job in BASE[4:] or job in extra:
            before=bounded(directory/'executed-before.txt',512)
            after=bounded(directory/'executed-after.txt',512)
            wanted=(BINARY+'  '+BINARY_PATH+'\n').encode()
            if before!=wanted or after!=wanted:raise ValueError('same exact private binary required')
    for job,count in zip(BASE[:3],(7,3,4)):
        if not re.search(rb'test result: ok\. '+str(count).encode()+rb' passed; 0 failed;',bounded(root/job/'stdout.txt')):
            raise ValueError('actual selected SDK unit count required')
    if bounded(root/BASE[3]/'frozen-binary.sha256',512)!=(BINARY+'  '+BINARY_PATH+'\n').encode():
        raise ValueError('actual accepted build/private binary required')

if __name__=='__main__':verify(sys.argv[1],sys.argv[2:])
