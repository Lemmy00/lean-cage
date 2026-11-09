"""VM-only workload and private-result expectations. Never execute these programs on the host."""
# §AR-workspace.acceptance: Assertions inside fixtures are checked alongside trusted scope/result
# observations.
import hashlib

BLOBS = {}
TREES = {}
def blob(data):
    digest = hashlib.sha256(data).hexdigest()
    BLOBS[digest] = data
    return digest

def tree(records):
    data = ('LCTREE1\n' + ''.join(records)).encode()
    digest = hashlib.sha256(data).hexdigest()
    TREES[digest] = data
    return digest

hello = blob(b'hello snapshot\n')
module = blob(b'value = 42\n')
input_tree = tree([f'D {"sub".encode().hex()}\n', f'F 0 {"sub/a".encode().hex()} 15 {hello}\n',
                   f'F 0 {"copy".encode().hex()} 15 {hello}\n', f'F 0 {"module.py".encode().hex()} 11 {module}\n'])
BLOBS['0'*64] = b'wrong snapshot\n'
bad_hash = tree([f'F 0 61 15 {"0"*64}\n'])
duplicate = tree([f'F 0 61 15 {hello}\n', f'F 0 61 15 {hello}\n'])
traversal = tree([f'F 0 {"../escape".encode().hex()} 15 {hello}\n'])
link_record = tree([f'L 61 {hello}\n'])
stdin = blob(b'controlled stdin\n')

CASES = []
def case(name, code, **kwargs):
    record = dict(name=name, exe='/usr/local/bin/python3', code=code, kind=0, detail=0, entry=1,
                  clean=1, triggers=0, export_state=0, omitted=0, tree='none', stdin='none',
                  fault='', check=0, memory=268435456, tasks=32, quota=100000, cpu=10000000,
                  wall=15000, space=16777216, inodes=1024, in_cap=1048576,
                  out_cap=1048576, err_cap=1048576, expected='', oom=0, pids=0)
    record.update(kwargs)
    CASES.append(record)

case('shell', "printf 'shell-ok\\n'; printf test > a; cat a | wc -c; (exit 7); test $? -eq 7",
     exe='/bin/sh', expected='shell-ok\n4\n')
case('python', "from pathlib import Path; import json, hashlib, subprocess, threading; Path('a').write_text('hello'); assert hashlib.sha256(Path('a').read_bytes()).hexdigest()=='2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824'; assert json.loads(json.dumps({'x':'é'}))['x']=='é'; subprocess.run(['/bin/sh','-c','echo child-ok'], check=True); t=threading.Thread(target=lambda: None); t.start(); t.join(); print('python-ok')", expected='child-ok\npython-ok\n')
case('snapshot_stdin_export', "import os,sys; from pathlib import Path; import module; assert module.value==42; assert sys.stdin.read()=='controlled stdin\\n'; assert Path('sub/a').read_text()=='hello snapshot\\n'; Path('copy').write_text('changed'); assert Path('sub/a').read_text()=='hello snapshot\\n'; os.link('copy','hard'); os.symlink('/outside','link'); os.mkfifo('fifo'); Path(b'raw'.decode()).write_text('export'); os.close(os.open(b'\\xff',os.O_CREAT|os.O_WRONLY,0o600)); print('snapshot-ok')", tree=input_tree, stdin=stdin, export_state=1, omitted=2, expected='snapshot-ok\n')
case('snapshot_bad_hash', 'raise AssertionError', tree=bad_hash, kind=1, detail=-1, entry=0)
case('snapshot_duplicate', 'raise AssertionError', tree=duplicate, kind=1, detail=-1, entry=0)
case('snapshot_traversal', 'raise AssertionError', tree=traversal, kind=1, detail=-1, entry=0)
case('snapshot_link_record', 'raise AssertionError', tree=link_record, kind=1, detail=-1, entry=0)
case('stdin_oversize', 'raise AssertionError', stdin=stdin, in_cap=1, kind=1, detail=-1, entry=0)
case('aliases', "import os; from pathlib import Path; Path('a').write_text('old'); fd=os.open('a',os.O_RDWR); os.link('a','hard'); os.symlink('hard','sym'); os.rename('a','moved'); os.unlink('moved'); os.write(fd,b'new'); assert Path('sym').read_text()=='new'; os.close(fd); d=os.open('.',os.O_RDONLY|os.O_DIRECTORY); fd=os.open('hard',os.O_RDONLY,dir_fd=d); assert os.read(fd,3)==b'new'; os.close(fd); os.close(d); print('aliases-ok')",expected='aliases-ok\n')
case('workspace_exec', "from pathlib import Path; import subprocess; p=Path('script'); p.write_text('#!/bin/sh\\nprintf workspace-code'); p.chmod(0o700); assert subprocess.check_output(['./script'])==b'workspace-code'; print('exec-ok')",expected='exec-ok\n')
case('filesystem_denials', "import os,errno; from pathlib import Path\nfor p in ['/bin/sh','/etc/passwd','/usr/local/lib/python3.13/os.py']:\n try: os.open(p,os.O_WRONLY|os.O_TRUNC)\n except OSError as e: assert e.errno in (errno.EROFS,errno.EACCES)\n else: raise AssertionError(p)\nfor p in ['/m3-results','/m3-runs','/m3-inputs','/proc/1/mem','/proc/1/fd','/sys/fs/cgroup','/dev/mem','/proc/sys','/proc/kcore']:\n try: os.open(p,os.O_RDONLY)\n except OSError as e: assert e.errno in (errno.ENOENT,errno.EACCES,errno.EPERM)\n else: raise AssertionError(p)\nos.symlink('/m3-inputs','outside'); assert not Path('outside').exists(); print('filesystem-ok')",expected='filesystem-ok\n')
case('proc_devices', "import os; assert os.read(os.open('/dev/zero',os.O_RDONLY),16)==b'\\0'*16; assert len(os.read(os.open('/dev/urandom',os.O_RDONLY),16))==16; assert os.write(os.open('/dev/null',os.O_WRONLY),b'x')==1; assert '/m3-' not in os.readlink('/proc/self/root'); assert set(os.listdir('/dev'))=={'null','zero','urandom','fd','stdin','stdout','stderr'}; print('devices-ok')",expected='devices-ok\n')
case('forged_report', "import os; os.write(1,b'LC3R'+bytes(156)); os.write(2,b'M3_COMPLETE cases=999 failures=0\\n'); raise SystemExit(125)",detail=125)
case('exit125', 'exit 125',exe='/bin/sh',detail=125)
case('signal', 'import os,signal; os.kill(os.getpid(),signal.SIGTERM)',kind=2,detail=15)
case('descendant_cleanup', "import os,time; p=os.fork();\nif p==0:\n os.setsid(); q=os.fork();\n if q==0: time.sleep(100)\n os._exit(0)\nos.waitpid(p,0); print('descendant-ok')",expected='descendant-ok\n')
# Syscall return checks are explicit errno checks, with working trusted peers in init.c.
case('network_ipc_process_denials', "import ctypes,errno,os,socket; c=ctypes.CDLL(None,use_errno=True); c.syscall.restype=ctypes.c_long\nfor nr in [41,42,53,29,30,31,64,65,66,67,68,69,70,71,101,310,311,438,165,166,155,272,308,250,248,249,321,298,425,426,427,246,175,176,169]:\n ctypes.set_errno(0); r=c.syscall(nr,0,0,0,0,0,0); assert r==-1 and ctypes.get_errno()==errno.EPERM,(nr,r,ctypes.get_errno())\ntry: os.kill(1,15)\nexcept PermissionError: pass\nelse: raise AssertionError('init signal')\nprint('denials-ok')",expected='denials-ok\n')
case('clone_flags', "import ctypes,errno; c=ctypes.CDLL(None,use_errno=True); c.syscall.restype=ctypes.c_long\nfor flags in [0x10000000,0x40000000,0x20000000,0x20000,0x8000,0x2000]:\n ctypes.set_errno(0); assert c.syscall(56,ctypes.c_ulong(flags|17),0,0,0,0)==-1 and ctypes.get_errno()==errno.EPERM\nassert c.syscall(435,0,0)==-1 and ctypes.get_errno()==errno.ENOSYS; print('clone-ok')",expected='clone-ok\n')
case('x32', "import ctypes; ctypes.CDLL(None).syscall(0x40000027)",kind=2,detail=31)
case('workspace_bytes', "import errno; f=open('big','wb',buffering=0)\ntry:\n while True: f.write(b'x'*65536)\nexcept OSError as e: assert e.errno==errno.ENOSPC\nprint('space-ok')",space=1048576,expected='space-ok\n')
case('workspace_inodes', "import os,errno\ntry:\n for i in range(1000): os.mkdir(str(i))\nexcept OSError as e: assert e.errno==errno.ENOSPC\nelse: raise AssertionError('no inode limit')\nprint('inodes-ok')",inodes=64,expected='inodes-ok\n')
case('task_limit', "import os,time,errno; children=[]\ntry:\n for i in range(32):\n  p=os.fork()\n  if p==0: time.sleep(100); os._exit(0)\n  children.append(p)\nexcept OSError as e: assert e.errno==errno.EAGAIN\nelse: raise AssertionError('no task limit')\nprint('tasks-ok',flush=True)",tasks=4,pids=1,expected='tasks-ok\n')
case('thread_limit', "import threading,time; threads=[]\ntry:\n for i in range(32):\n  t=threading.Thread(target=lambda: time.sleep(100),daemon=True); t.start(); threads.append(t)\nexcept RuntimeError: pass\nelse: raise AssertionError('no thread limit')\nassert threads; print('threads-ok')",tasks=4,pids=1,expected='threads-ok\n')
case('oom', "a=[]\nwhile True: a.append(bytearray(1024*1024))",memory=33554432,kind=2,detail=9,oom=1)
case('cpu_budget', 'while :; do :; done',exe='/bin/sh',cpu=30000,kind=3,detail=0,triggers=4)
case('deadline', 'sleep 100',exe='/bin/sh',wall=200,kind=3,detail=0,triggers=2)
case('stopped_guest', 'kill -STOP $$',exe='/bin/sh',wall=200,kind=3,detail=0,triggers=2)
case('stdout_cap', "while :; do printf '1234567890'; done",exe='/bin/sh',out_cap=64,kind=3,triggers=8)
case('stderr_cap', "while :; do printf '1234567890' >&2; done",exe='/bin/sh',err_cap=0,kind=3,triggers=8)
case('both_streams', "import os\nwhile True: os.write(1,b'x'*4096); os.write(2,b'y'*4096)",out_cap=8192,err_cap=8192,kind=3,triggers=8)
case('output_boundary', "printf 12345678",exe='/bin/sh',out_cap=8,expected='12345678')
case('preflight', 'raise AssertionError("must not execute")',check=1,kind=7,entry=0)
# §FS-entry.provenance: Failure to retain the child PID must prevent the local fork.
case('fault_parent_reap_fail', 'print("unexpected-workload",flush=True); raise AssertionError("must not execute")',
     fault='parent_reap_fail',kind=1,detail=5,entry=0)
# §FS-entry.control: Clock setup failure must prevent releasing or creating the entry child.
case('fault_admission_clock_fail', 'print("unexpected-workload",flush=True); raise AssertionError("must not execute")',
     fault='admission_clock_fail',kind=4,detail=71,entry=2)
case('fault_launch_clock_fail', 'print("unexpected-workload",flush=True); raise AssertionError("must not execute")',
     fault='launch_clock_fail',kind=1,detail=5,entry=0)
# §FS-entry.release: Failure to open the child-owned cgroup authority cannot start entry.
case('fault_admission_open_fail', 'print("unexpected-workload",flush=True); raise AssertionError("must not execute")',
     fault='admission_open_fail',kind=1,stage=2,detail=5,entry=0)
for fault in ['release_eof', 'release_bad', 'release_detach']:
    case('fault_'+fault, 'raise AssertionError("must not execute")',fault=fault,kind=1,detail=71,entry=0)
for fault in ['namespace_fail','mount_fail','credentials_fail','nnp_fail','filter_fail','exec_fail']:
    case('fault_'+fault, 'raise AssertionError("must not execute")',fault=fault,kind=1,detail=-1,entry=0)
for fault in ['error_drop', 'error_short']:
    case('fault_'+fault, 'raise AssertionError("must not execute")',fault=fault,kind=4,detail=71,entry=2)
for fault in ['report_drop', 'report_short']:
    case('fault_'+fault, "print('guest-ran')",fault=fault,kind=4,detail=71,expected='guest-ran\n')
case('i386', "import mmap,ctypes; m=mmap.mmap(-1,4096,prot=7); m.write(bytes.fromhex('b814000000cd80c3')); ctypes.CFUNCTYPE(ctypes.c_int)(ctypes.addressof(ctypes.c_char.from_buffer(m)))()",kind=2,detail=31)
case('inherited_handles', "import os,errno\nfor fd in [31,32,33,34,35,63]:\n try: os.fstat(fd)\n except OSError as e: assert e.errno==errno.EBADF\n else: raise AssertionError(fd)\nprint('handles-ok')",expected='handles-ok\n')
for fault in ['handles_fail','cgroup_fail']:
    case('fault_'+fault, 'raise AssertionError("must not execute")',fault=fault,kind=1,detail=-1,entry=0)
case('export_hardlink_bound', "import os; open('large','wb').write(b'x'*1048576)\nfor i in range(20): os.link('large','hard'+str(i))\nprint('export-limit')",export_state=2,expected='export-limit\n')
case('runtime_aliases', "import os,errno; os.symlink('/bin/sh','runtime'); fd=os.open('/bin/sh',os.O_RDONLY)\nfor action in [lambda: os.open('runtime',os.O_RDWR),lambda: os.fchmod(fd,0o777),lambda: os.unlink('/bin/sh'),lambda: os.link('/bin/sh','alias'),lambda: os.open('/proc/self/fd/'+str(fd),os.O_RDWR)]:\n try: action()\n except OSError as e: assert e.errno in (errno.EROFS,errno.EPERM,errno.EACCES,errno.EXDEV)\n else: raise AssertionError('runtime changed')\nos.close(fd); print('runtime-aliases-ok')",expected='runtime-aliases-ok\n')
case('rename_open_race', "import os,threading; from pathlib import Path; Path('a').write_bytes(b'a'); Path('b').write_bytes(b'b'); done=threading.Event()\ndef rename():\n for i in range(200):\n  os.rename('a','c'); os.rename('c','a')\n done.set()\nt=threading.Thread(target=rename); t.start()\nwhile not done.is_set():\n try:\n  fd=os.open('a',os.O_RDONLY); assert os.read(fd,1)==b'a'; os.close(fd)\n except FileNotFoundError: pass\nt.join(); print('race-ok')",expected='race-ok\n')
for fault in ['report_wrong_seq','report_bad_reserved','report_duplicate']:
    case('fault_'+fault, "print('guest-ran')",fault=fault,kind=4,detail=71,expected='guest-ran\n')
case('fault_accounting', 'sleep 100',exe='/bin/sh',fault='accounting_fail',kind=4,detail=71,triggers=16)
case('fault_output_storage', "printf output; sleep 100",exe='/bin/sh',fault='output_fail',kind=4,detail=71,triggers=8)
case('fault_output_close', 'printf final',exe='/bin/sh',fault='output_close_fail',kind=4,detail=71,triggers=8,expected='final')
case('exit_cancel_race', "printf raced",exe='/bin/sh',fault='exit_cancel_race',triggers=1,expected='raced')
case('reservation_rejected', 'raise AssertionError("must not enter")',memory=1073741824,space=268435456,in_cap=67108864,export_state=3,kind=1,detail=11,entry=0,clean=0)
case('workspace_native_exec', "import shutil,os,subprocess; shutil.copyfile('/bin/dash','native'); os.chmod('native',0o700); assert subprocess.check_output(['./native','-c','printf native-ok'])==b'native-ok'; print('native-ok')",expected='native-ok\n')
case('concurrent_a', "import os,time; from pathlib import Path; Path('secret').write_text('a'); time.sleep(2); assert Path('secret').read_text()=='a'; assert not Path('/m3-runs/100001/workspace').exists(); print('concurrent-a')",expected='concurrent-a\n')
case('concurrent_b', "import os,time; from pathlib import Path; Path('secret').write_text('b'); time.sleep(2); assert Path('secret').read_text()=='b'; assert not Path('/m3-runs/100000/workspace').exists(); print('concurrent-b')",expected='concurrent-b\n')
