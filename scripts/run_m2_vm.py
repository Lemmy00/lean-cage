#!/usr/bin/env python3
"""Replay M2 only in its designated disposable VM; never execute fixtures on the host."""
# §AR-lifecycle.audit: Distinct historical checking, current artifacts and fresh VM replay.
import argparse
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shutil
import stat
import struct
import subprocess
import sys
import urllib.request

PROJECT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('m1_vm_helpers', PROJECT / 'scripts/run_m1_vm.py')
M1 = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M1)
WORK = PROJECT / '.tools/m2vm'
CONFIG = PROJECT / 'tests/m2/linux-6.18.59.config'
EVIDENCE = PROJECT / 'assurance/m2-vm-evidence.json'
TRANSCRIPT = PROJECT / 'assurance/m2-vm-transcript.log'
PROFILE = 'leancage-m2-linux-6.18.59-root-v1'
GUEST = 'M2_GUEST check=ok uid=65534 nnp=1 filter=2 handles=closed signals=reset'
# exit, exact result (kind, phase, detail, entry, clean), guest markers (None permits a race).
EXPECTED = {
    'allowed': (0,(0,0,0,1,1),1), 'inherited_aliases': (0,(0,0,0,1,1),1),
    'exit125': (125,(0,0,125,1,1),1), 'fork_exec': (0,(0,0,0,1,1),2),
    'leader_reexec': (0,(0,0,0,1,1),2),
    'daemon_escape': (0,(0,0,0,1,1),1), 'guest_signal': (143,(2,0,15,1,1),1),
    'x32_rejected': (159,(2,0,31,1,1),1), 'i386_rejected': (159,(2,0,31,1,1),1),
    'empty': (64,None,0), 'permissive': (64,None,0),
    'missing_profile': (125,(1,1,95,0,0),0), 'unprivileged_caller': (125,(1,1,1,0,0),0),
    'bad_elf': (125,(1,1,8,0,0),0), 'symlink': (125,(1,1,40,0,0),0),
    'noexec': (125,(1,1,13,0,0),0), 'existing_filter': (125,(1,1,95,0,0),0),
    'masked_filter': (125,(1,1,95,0,0),0),
    'changed_plan': (125,(1,1,22,0,0),0), 'external_tracer': (125,(1,1,95,0,0),0),
    'namespace_failure': (125,(1,2,22,0,0),0), 'mount_failure': (125,(1,2,19,0,1),0),
    'handles_failure': (125,(1,3,9,0,1),0), 'credentials_failure': (125,(1,4,22,0,1),0),
    'nnp_failure': (125,(1,6,22,0,1),0), 'filter_failure': (125,(1,7,22,0,1),0),
    'exec_failure': (125,(1,8,9,0,1),0), 'short_io': (125,(1,6,22,0,1),0),
    'error_drop': (126,(4,9,71,2,1),0), 'error_short': (126,(4,9,71,2,1),0),
    'final_drop': (126,(4,9,71,1,1),1), 'final_short': (126,(4,9,71,1,1),1),
    'signal_setup': (126,(4,9,71,2,1),0), 'cancel_before': (124,(3,0,0,2,1),0),
    'cancel_exec_race': (124,(3,0,0,1,1),None), 'deadline': (124,(3,0,0,1,1),1),
    'stopped_guest': (124,(3,0,0,1,1),1), 'early_controller_death': (137,(1,1,10,0,0),0),
    'early_helper_death': (137,None,0),
    'helper_death': (137,None,None), 'controller_death': (137,None,None),
    'init_death': (126,(4,9,71,1,1),0), 'snapshot_rename': (0,(0,0,0,1,1),1),
}


def source_identities():
    paths = [Path(__file__), PROJECT/'native/leancage_m2.c',
             PROJECT/'native/leancage_m1.c', PROJECT/'scripts/run_m1_vm.py',
             PROJECT/'scripts/audit_m2.py', PROJECT/'scripts/m2_axiom_query.lean',
             PROJECT/'lean-toolchain', PROJECT/'lake-manifest.json', PROJECT/'lakefile.lean',
             PROJECT/'m2/lean-toolchain',
             PROJECT/'LeanCage.lean', PROJECT/'tests/vm/bootstrap-pins.json']
    paths += sorted((PROJECT/'LeanCage').rglob('*.lean'))
    paths += [p for p in (PROJECT/'m2').rglob('*') if p.is_file() and
              '.lake' not in p.parts and '__pycache__' not in p.parts and p.suffix in ('.lean','.json','.py')]
    paths += sorted((PROJECT/'tests/m2').glob('*'))
    return {str(p.relative_to(PROJECT)): M1.sha256(p) for p in sorted(set(paths))}


def prepare(pins):
    host=platform.freedesktop_os_release()
    if platform.machine()!=pins['host_arch'] or host.get('ID')!=pins['host_distribution'] or host.get('VERSION_ID')!=pins['host_version']:
        raise ValueError('Only recorded Ubuntu 24.04 x86-64 bootstrap is supported')
    packages=WORK/'packages'; root=WORK/'root'
    packages.mkdir(parents=True,exist_ok=True); root.mkdir(exist_ok=True)
    for package in pins['packages']:
        path=packages/package['filename']; existing=M1.WORK/'packages'/package['filename']
        if not path.exists() and existing.exists(): shutil.copyfile(existing,path)
        if not path.exists():
            subprocess.run(['apt-get','download',f"{package['name']}={package['version']}"],cwd=packages,check=True)
        M1.check_hash(path,package['sha256'])
        M1.run(['dpkg-deb','--extract',path,root],stdout=subprocess.DEVNULL)
    archive=WORK/f"linux-{pins['kernel_version']}.tar.xz"
    if not archive.exists():
        existing=M1.WORK/archive.name
        if existing.exists(): shutil.copyfile(existing,archive)
        else: urllib.request.urlretrieve(pins['kernel_archive_url'],archive)
    M1.check_hash(archive,pins['kernel_archive_sha256'])
    kernel=WORK/f"linux-{pins['kernel_version']}"
    if kernel.exists(): shutil.rmtree(kernel)
    M1.run(['tar','--extract','--xz','--file',archive,'--directory',WORK])
    shutil.copyfile(CONFIG,kernel/'.config')
    environment=dict(os.environ,PATH=f'{root}/usr/bin:/usr/bin:/bin',M4=f'{root}/usr/bin/m4',
        BISON_PKGDATADIR=f'{root}/usr/share/bison',HOSTCFLAGS=f'-O2 -I{root}/usr/include',
        HOSTLDFLAGS=f'-L{root}/usr/lib/x86_64-linux-gnu',PKG_CONFIG_PATH=f'{root}/usr/lib/x86_64-linux-gnu/pkgconfig',
        KBUILD_BUILD_TIMESTAMP='2026-10-30 00:00:00 UTC',KBUILD_BUILD_USER='leancage',
        KBUILD_BUILD_HOST='disposable-m2',KBUILD_BUILD_VERSION='1')
    with (WORK/'kernel-build.log').open('w') as log:
        subprocess.run(['nice','-n','10','make','-j2','ARCH=x86_64','olddefconfig','bzImage'],
            cwd=kernel,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True)
    M1.check_hash(kernel/'.config',M1.sha256(CONFIG))


def build_image():
    subprocess.run(['lake','build','leancage-m2'],cwd=PROJECT/'m2',check=True)
    for name,source in [('init','tests/m2/init.c'),('guest','tests/m2/guest.c'),('leancage-m2-helper','native/leancage_m2.c')]:
        M1.run(['cc','-std=c11','-O2','-Wall','-Wextra','-Werror','-static','-no-pie',PROJECT/source,'-o',WORK/name])
    entries=[];directories={'dev','proc','sys','tmp'}
    def add(name,data,permissions=0o444):
        directories.update(str(p) for p in Path(name).parents if str(p)!='.')
        entries.append((name,stat.S_IFREG|permissions,data,0,0))
    launcher=PROJECT/'m2/.lake/build/bin/leancage-m2'
    add('leancage-m2',launcher.read_bytes(),0o555)
    for library in M1.dependencies(launcher):add(str(library).lstrip('/'),library.read_bytes(),0o555)
    for name in ('init','guest','leancage-m2-helper'):add(name,(WORK/name).read_bytes(),0o555)
    add('snapshot-guest',(WORK/'guest').read_bytes(),0o555)
    add('replacement',b'not executable after rename\n',0o555)
    add('guest-noexec',(WORK/'guest').read_bytes())
    add('bad-elf',b'not an ELF\n',0o555);add('sentinel-data',b'protected inherited descriptor\n')
    add('leancage-m2-disposable-vm',b'LeanCage-M2-root-VM-v1')
    rows=[(0x20,0,0,4),(0x15,1,0,0xc000003e),(6,0,0,0x80000000),(0x20,0,0,0),
          (0x35,0,1,0x40000000),(6,0,0,0x80000000),(0x15,0,1,110),(6,0,0,0x50001),(6,0,0,0x7fff0000)]
    canonical=b''.join(struct.pack('<HBBI',*r) for r in rows)
    permissive=bytearray(canonical);permissive[60:64]=struct.pack('<I',0x7fff0000)
    add('filter.bin',canonical);add('empty.bin',b'');add('permissive.bin',bytes(permissive))
    entries[:0]=[(name,stat.S_IFDIR|(0o1777 if name=='tmp' else 0o755),b'',0,0)
                 for name in sorted(directories,key=lambda p:(p.count('/'),p))]
    entries += [('dev/console',stat.S_IFCHR|0o600,b'',5,1),('dev/null',stat.S_IFCHR|0o666,b'',1,3),
                ('dev/urandom',stat.S_IFCHR|0o444,b'',1,9),('guest-link',stat.S_IFLNK|0o777,b'/guest',0,0)]
    image=WORK/'initramfs.cpio.gz';image.write_bytes(M1.cpio(entries))
    files={'/'+n:{'mode':m,'sha256':__import__('hashlib').sha256(d).hexdigest(),'major':a,'minor':b}
           for n,m,d,a,b in entries}
    return image,files


def validate_transcript(transcript,return_code):
    text=transcript.replace('\r','')
    if return_code!=33 or text.count(f'M2_COMPLETE cases={len(EXPECTED)} failures=0\n')!=1:
        raise ValueError('Incomplete or failing M2 VM')
    if text.count(f'M2_PROFILE name={PROFILE} kernel=6.18.59 uid=0\n')!=1:
        raise ValueError('Missing exact M2 profile')
    control='M2_CONTROL namespaces=present unix=present inet=present sysvipc=present cgroup_cpu_memory_pids=present\n'
    if text.count(control)!=1:raise ValueError('Missing capable-mechanism positive controls')
    matches=list(re.finditer(r'^M2_CASE_BEGIN name=(\w+)\n(.*?)^M2_CASE_END name=(\w+) exit=(\d+) expected=(\d+) owned_gone=(\d) sentinel_alive=(\d)\n',text,re.M|re.S))
    if [m[1] for m in matches]!=list(EXPECTED):raise ValueError('Missing/duplicate/reordered M2 cases')
    records=[];result_count=0;guest_count=0;scope_count=0
    for m in matches:
        name,body,end,exit_code,expected,gone,sentinel=m.groups()
        exit_value,result,guests=EXPECTED[name]
        if name!=end or int(exit_code)!=exit_value or int(expected)!=exit_value or gone!='1' or sentinel!='1':
            raise ValueError(f'Wrong outcome or incomplete owned-only teardown: {name}')
        lines=body.splitlines()
        results=[line for line in lines if line.startswith('M2_RESULT ')]
        wanted=[] if result is None else ['M2_RESULT kind=%d phase=%d detail=%d entry=%d clean=%d'%result]
        observed=[line for line in lines if line.startswith('M2_GUEST ')]
        if results!=wanted or any(line!=GUEST for line in observed) or (guests is not None and len(observed)!=guests) or len(observed)>2:
            raise ValueError(f'Wrong typed result or guest entry: {name}: {body}')
        validation=[line for line in lines if line.startswith('M2_VALIDATION ')]
        wanted_validation={'empty':'LeanCage.Linux.Filter.DecodeError.emptyInput',
                           'permissive':'LeanCage.Linux.Filter.DecodeError.unsupportedInstruction 7'}
        if validation!=([f'M2_VALIDATION error={wanted_validation[name]}'] if name in wanted_validation else []):
            raise ValueError(f'Wrong decoder result: {name}')
        masked=[line for line in lines if line.startswith('M2_FILTER_CONTROL ')]
        if masked!=(['M2_FILTER_CONTROL query_masked=1'] if name=='masked_filter' else []):
            raise ValueError('Missing inherited-filter masking positive control')
        scopes=[line for line in lines if line.startswith('M2_SCOPE ')]
        need_scope=name not in ('empty','permissive','missing_profile','unprivileged_caller','bad_elf','symlink','noexec','existing_filter','masked_filter','changed_plan','external_tracer','namespace_failure','early_helper_death','early_controller_death')
        if len(scopes)!=int(need_scope) or any(not re.fullmatch(r'M2_SCOPE init=[1-9]\d* helper=[1-9]\d*',s) for s in scopes):
            raise ValueError(f'Wrong process ownership evidence: {name}')
        descendants=[line for line in lines if line.startswith('M2_DESCENDANT ')]
        wanted_desc=['M2_DESCENDANT fork_exec=ok'] if name=='fork_exec' else ['M2_DESCENDANT daemon=ready'] if name=='daemon_escape' else []
        if descendants!=wanted_desc:raise ValueError(f'Missing hostile/useful descendant fixture: {name}')
        records.append({'name':name,'exit_code':exit_value,'result':None if result is None else dict(zip(('kind','phase','detail','entry','clean'),result)),
                        'guest_markers':len(observed),'owned_scope_gone':True,'unrelated_sentinel_alive':True,'passed':True})
        result_count+=len(results);guest_count+=len(observed);scope_count+=len(scopes)
    if text.count('M2_FILTER_CONTROL ')!=1:raise ValueError('Unattributed inherited-filter control')
    if text.count('M2_RESULT ')!=result_count or text.count('M2_GUEST ')!=guest_count or text.count('M2_SCOPE ')!=scope_count:
        raise ValueError('Unattributed M2 evidence outside cases')
    return records


# §AR-lifecycle.audit: Recorded paths describe the recording host, never the current checkout.
def recorded_layout(command):
    if not isinstance(command,list) or not command or not all(isinstance(v,str) for v in command):
        raise ValueError('Invalid M2 VM command')
    qemu=Path(command[0])
    if not qemu.is_absolute() or '..' in qemu.parts or len(qemu.parents)<6:
        raise ValueError('Unpinned M2 emulator location')
    recorded_project=qemu.parents[5]
    root=qemu.parents[1]
    permitted=[recorded_project/f'.tools/{name}/root/usr/bin/qemu-system-x86_64'
               for name in ('m1vm','m2vm')]
    if qemu not in permitted or command[0]!=str(qemu):
        raise ValueError('Unpinned M2 emulator location')
    return recorded_project,root


def validate_evidence(e):
    required={'schema_version','status','profile','kernel','machine','command','environment','return_code','timeout_seconds',
              'cases','source_sha256','artifacts_sha256','guest_files','transcript_sha256','tools','virtual_cpu','assumptions'}
    if set(e)!=required or e['schema_version']!=1 or e['status']!='passed' or e['profile']!=PROFILE:
        raise ValueError('Unsupported/incomplete M2 evidence schema')
    pins=json.loads(M1.PINS.read_text())
    if e['kernel']!={'version':pins['kernel_version'],'commit':pins['kernel_commit'],'archive_sha256':pins['kernel_archive_sha256'],
                     'config_sha256':M1.sha256(CONFIG)}:raise ValueError('Wrong M2 kernel identity')
    if e['machine']!={'acceleration':'tcg','cpu':'max','vcpus':1,'memory_mib':2048,'host_mounts':[],'network_devices':[],'persistent_disks':[]}:
        raise ValueError('Wrong M2 isolation profile')
    if e['timeout_seconds']!=240 or e['source_sha256']!=source_identities():raise ValueError('M2 source identities differ')
    if e['transcript_sha256']!=M1.sha256(TRANSCRIPT):raise ValueError('M2 transcript differs')
    if e['cases']!=validate_transcript(TRANSCRIPT.read_text(),e['return_code']):raise ValueError('M2 structured cases differ')
    for key in ('artifacts_sha256','guest_files','tools','environment','virtual_cpu','assumptions'):
        if not e[key]:raise ValueError(f'Missing M2 {key}')
    needed=['/init','/guest','/leancage-m2','/leancage-m2-helper','/filter.bin','/leancage-m2-disposable-vm','/dev/console','/dev/null']
    if not set(needed)<=set(e['guest_files']):raise ValueError('Incomplete M2 guest image inventory')
    if not all(re.fullmatch('[0-9a-f]{64}',v) for v in e['artifacts_sha256'].values()):raise ValueError('Malformed M2 artifact identity')
    command=e['command']
    recorded_project,root=recorded_layout(command)
    recorded_work=recorded_project/'.tools/m2vm'
    kernel=recorded_work/f"linux-{pins['kernel_version']}"
    expected_command=[str(root/'bin/qemu-system-x86_64'),'-L',str(root/'share/qemu'),'-no-user-config','-nodefaults','-machine','pc,accel=tcg',
        '-cpu','max','-smp','1','-m','2048M','-bios',str(root/'share/seabios/bios-256k.bin'),'-display','none','-serial','stdio','-monitor','none','-nic','none',
        '-no-reboot','-device','isa-debug-exit,iobase=0xf4,iosize=0x04','-kernel',str(kernel/'arch/x86/boot/bzImage'),'-initrd',str(recorded_work/'initramfs.cpio.gz'),
        '-append','console=ttyS0,115200 rdinit=/init panic=1 oops=panic loglevel=5']
    if command!=expected_command:raise ValueError('VM command differs from supported M2 profile')
    required_artifacts={command[0],command[command.index('-bios')+1],str(kernel/'arch/x86/boot/bzImage'),str(kernel/'.config'),
        str(recorded_work/'initramfs.cpio.gz'),str(recorded_work/'init'),str(recorded_work/'guest'),str(recorded_work/'leancage-m2-helper'),
        str(recorded_project/'m2/.lake/build/bin/leancage-m2'),str(root/'lib/x86_64-linux-gnu/qemu/accel-tcg-x86_64.so'),
        str(root/'share/qemu/kvmvapic.bin'),str(root/'share/qemu/linuxboot_dma.bin')}
    if not required_artifacts<=set(e['artifacts_sha256']):raise ValueError('Incomplete required M2 artifact inventory')
    if e['artifacts_sha256'][str(kernel/'.config')]!=M1.sha256(CONFIG):raise ValueError('Artifact configuration differs')
    tools=e['tools']
    if set(tools)!={'qemu','cc','libc','lean','host_distribution'} or not all(tools.values()) or '8.2.2' not in tools['qemu'] or '4.35.0' not in tools['lean']:
        raise ValueError('Incomplete or unsupported M2 runtime/tool identities')
    toolroot=root.parent
    if e['environment']!={'LD_LIBRARY_PATH':str(toolroot/'usr/lib/x86_64-linux-gnu'),
                           'QEMU_MODULE_DIR':str(toolroot/'usr/lib/x86_64-linux-gnu/qemu')}:
        raise ValueError('Wrong M2 emulator environment')
    for name,record in e['guest_files'].items():
        if not name.startswith('/') or set(record)!={'mode','sha256','major','minor'} or not isinstance(record['mode'],int) or not re.fullmatch('[0-9a-f]{64}',record['sha256']):
            raise ValueError('Malformed guest-file inventory')
    for name,path in {'/init':recorded_work/'init','/guest':recorded_work/'guest','/leancage-m2-helper':recorded_work/'leancage-m2-helper',
                      '/leancage-m2':recorded_project/'m2/.lake/build/bin/leancage-m2'}.items():
        if e['guest_files'][name]['sha256']!=e['artifacts_sha256'][str(path)]:raise ValueError('Guest binary differs from artifact inventory')
    if not all(isinstance(v,str) and v.startswith('M2_CPU ') for v in e['virtual_cpu']):raise ValueError('Malformed CPU record')


def check_evidence(current_artifacts=False):
    e=json.loads(EVIDENCE.read_text());validate_evidence(e)
    if current_artifacts:
        recorded_project,_=recorded_layout(e['command'])
        for path,digest in e['artifacts_sha256'].items():
            artifact=Path(path)
            if artifact.is_relative_to(recorded_project):
                artifact=PROJECT/artifact.relative_to(recorded_project)
            M1.check_hash(artifact,digest)
    print(f'M2 evidence verified: {len(e["cases"])} cases; '+('current recorded artifacts match.' if current_artifacts else 'archived source/transcript check; no VM replay.'))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group()
    group.add_argument('--prepare',action='store_true');group.add_argument('--check-evidence',action='store_true');group.add_argument('--check-artifacts',action='store_true')
    args=parser.parse_args()
    if args.check_evidence or args.check_artifacts:return check_evidence(args.check_artifacts)
    pins=json.loads(M1.PINS.read_text());WORK.mkdir(parents=True,exist_ok=True)
    if args.prepare:prepare(pins)
    root=WORK/'root' if (WORK/'root/usr/bin/qemu-system-x86_64').exists() else M1.WORK/'root'
    package_dir=WORK/'packages' if root==WORK/'root' else M1.WORK/'packages'
    for package in pins['packages']:M1.check_hash(package_dir/package['filename'],package['sha256'])
    kernel=WORK/f"linux-{pins['kernel_version']}"
    archive=WORK/f"linux-{pins['kernel_version']}.tar.xz"
    if not archive.exists():archive=M1.WORK/archive.name
    M1.check_hash(archive,pins['kernel_archive_sha256']);M1.check_hash(kernel/'.config',M1.sha256(CONFIG))
    qemu=root/'usr/bin/qemu-system-x86_64';firmware=root/'usr/share/seabios/bios-256k.bin'
    env=dict(os.environ,LD_LIBRARY_PATH=f'{root}/usr/lib/x86_64-linux-gnu',QEMU_MODULE_DIR=f'{root}/usr/lib/x86_64-linux-gnu/qemu')
    sources=source_identities();image,files=build_image()
    command=[str(qemu),'-L',str(root/'usr/share/qemu'),'-no-user-config','-nodefaults','-machine','pc,accel=tcg',
        '-cpu','max','-smp','1','-m','2048M','-bios',str(firmware),'-display','none','-serial','stdio','-monitor','none','-nic','none',
        '-no-reboot','-device','isa-debug-exit,iobase=0xf4,iosize=0x04','-kernel',str(kernel/'arch/x86/boot/bzImage'),'-initrd',str(image),
        '-append','console=ttyS0,115200 rdinit=/init panic=1 oops=panic loglevel=5']
    EVIDENCE.write_text(json.dumps({'schema_version':1,'status':'running'})+'\n')
    try:
        with TRANSCRIPT.open('w') as log:
            r=subprocess.run(command,cwd=PROJECT,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=240)
        transcript=TRANSCRIPT.read_text(errors='replace');cases=validate_transcript(transcript,r.returncode)
        if sources!=source_identities():raise ValueError('M2 sources changed during replay')
    except (ValueError,subprocess.SubprocessError):
        EVIDENCE.write_text(json.dumps({'schema_version':1,'status':'failed','transcript_sha256':M1.sha256(TRANSCRIPT)})+'\n');raise
    artifacts=[qemu,firmware,kernel/'arch/x86/boot/bzImage',kernel/'.config',image,WORK/'init',WORK/'guest',WORK/'leancage-m2-helper',
        PROJECT/'m2/.lake/build/bin/leancage-m2',root/'usr/share/qemu/kvmvapic.bin',root/'usr/share/qemu/linuxboot_dma.bin',
        root/'usr/lib/x86_64-linux-gnu/qemu/accel-tcg-x86_64.so',*M1.dependencies(qemu,env)]
    prefix=Path(M1.run(['lake','env','lean','--print-prefix'],capture_output=True,text=True).stdout.strip())
    artifacts += [prefix/'bin/lean',prefix/'bin/clang',prefix/'lib/lean/libleanrt.a',Path(shutil.which('cc')).resolve()]
    tools={}
    for key,cmd in {'qemu':[qemu,'--version'],'cc':['cc','--version'],'libc':['getconf','GNU_LIBC_VERSION'],'lean':['lake','env','lean','--version']}.items():
        tools[key]=M1.run(cmd,env=env,capture_output=True,text=True).stdout.strip()
    tools['host_distribution']=platform.freedesktop_os_release()
    evidence={'schema_version':1,'status':'passed','profile':PROFILE,
        'kernel':{'version':pins['kernel_version'],'commit':pins['kernel_commit'],'archive_sha256':pins['kernel_archive_sha256'],'config_sha256':M1.sha256(CONFIG)},
        'machine':{'acceleration':'tcg','cpu':'max','vcpus':1,'memory_mib':2048,'host_mounts':[],'network_devices':[],'persistent_disks':[]},
        'command':command,'environment':{k:env[k] for k in ('LD_LIBRARY_PATH','QEMU_MODULE_DIR')},'return_code':r.returncode,'timeout_seconds':240,
        'cases':cases,'source_sha256':sources,'artifacts_sha256':{str(p):M1.sha256(p) for p in sorted(set(artifacts))},
        'guest_files':files,'transcript_sha256':M1.sha256(TRANSCRIPT),'tools':tools,
        'virtual_cpu':[l for l in transcript.replace('\r','').splitlines() if l.startswith('M2_CPU ')],
        'assumptions':['Trusted root controller/helper/namespace init and public fixture root tree','C/Lean compiler, libc, runtime and process/ELF correspondence',
            'Linux namespace, ptrace, credential, pidfd, signal, seal and seccomp contracts','Fair scheduling and terminating kernel calls for liveness',
            'QEMU/firmware/hardware fidelity; no hardware confidentiality claim']}
    validate_evidence(evidence);EVIDENCE.write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n')
    print(f'M2 fresh VM replay passed: {len(cases)} cases, positive controls, owned-only teardown.')

if __name__=='__main__':
    try:main()
    except (ValueError,OSError,subprocess.SubprocessError) as e:
        print(f'M2 VM failed: {e}',file=sys.stderr);sys.exit(1)
