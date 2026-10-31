#!/usr/bin/env python3
"""Replay the M3 profile in a disposable VM, or validate archived source-bound evidence."""
# §AR-workspace.acceptance: No host mount, NIC, persistent disk, KVM or host guest execution.
import argparse
import hashlib
import importlib.util
import json
import os
import platform
import re
import shutil
from pathlib import Path
import stat
import struct
import subprocess
import sys
import urllib.request

PROJECT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PROJECT / 'scripts'))
import m3_runtime as RUNTIME
import m3_elf as ELF
SPEC = importlib.util.spec_from_file_location('m3_m1_helpers', PROJECT / 'scripts/run_m1_vm.py')
M1 = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M1)
WORK = PROJECT / '.tools/m3vm'
SPEC = importlib.util.spec_from_file_location('m3_cases', PROJECT / 'tests/m3/cases.py')
CASES = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CASES)


def filter_header(data):
    return ('// SPDX-License-Identifier: Apache-2.0\n'
            '// §AR-workspace.interfaces: Generated from LeanCageM3.Filter.bytes.\n'
            '// The audit compares every serialized byte.\nstatic const struct sock_filter m3_filter[]={\n' +
            ''.join('    {0x%x,0x%x,0x%x,0x%x},\n' % row for row in struct.iter_unpack('<HBBI',data)) + '};\n')


def build_image():
    WORK.mkdir(parents=True, exist_ok=True)
    fields = list(CASES.CASES[0])
    header = "static const struct testcase cases[]={\n"
    for case in CASES.CASES:
        header += "{" + ",".join("." + key + "=" + (json.dumps(case[key], ensure_ascii=True) if isinstance(case[key], str) else str(case[key])) for key in fields) + "},\n"
    (WORK / 'cases.h').write_text(header + "};\n")
    for name, source in [('init', 'tests/m3/init.c'), ('leancage-m3-helper', 'native/leancage_m3.c')]:
        subprocess.run(['cc', '-std=c11', '-O2', '-Wall', '-Wextra', '-Werror', '-static', '-no-pie', '-I', str(WORK), str(PROJECT / source), '-o', str(WORK / name)], check=True)
    runtime = RUNTIME.load_entries()
    if ELF.inventory(runtime,RUNTIME.resolve) != json.loads((PROJECT/"profiles/m3/elf-closure.json").read_text()):
        raise ValueError("Runtime ELF closure differs from reviewed inventory")
    # Explicit profile overlays are recorded as guest-image bytes, not changes to the upstream lock.
    for prefix in ('tmp', 'var/tmp', 'run', 'dev', 'proc', 'sys', 'workspace', 'etc/machine-id'):
        runtime = {name: entry for name, entry in runtime.items() if name != prefix and not name.startswith(prefix + '/')}
    for name in ('run', 'dev', 'proc', 'sys', 'workspace'):
        runtime[name] = {'kind': 'directory', 'mode': 0o755, 'data': b''}
    for name in ('tmp', 'var/tmp'):
        runtime[name] = {'kind': 'symlink', 'mode': 0o777, 'data': b'/workspace/.tmp'}
    for name in ('passwd', 'group', 'hostname', 'hosts', 'resolv.conf'):
        runtime['etc/' + name] = {'kind': 'file', 'mode': 0o444, 'data': b''}
    runtime['.leancage-runtime'] = {'kind': 'file', 'mode': 0o444, 'data': RUNTIME.load_lock()['manifest_digest'].encode()}
    entries = []
    for name in ('dev', 'proc', 'sys', 'm3-runs', 'm3-results', 'm3-inputs', 'm3-runtime'):
        entries.append((name, stat.S_IFDIR | (0o700 if name in ('m3-runs', 'm3-results', 'm3-inputs') else 0o755), b'', 0, 0))
    for name, entry in sorted(runtime.items(), key=lambda item: (item[0].count('/'), item[0])):
        kind = {'directory': stat.S_IFDIR, 'file': stat.S_IFREG, 'symlink': stat.S_IFLNK}[entry['kind']]
        entries.append(('m3-runtime/' + name, kind | entry['mode'], entry['data'], 0, 0))
    subprocess.run(['lake', 'build', 'leancage'], cwd=PROJECT / 'm3', check=True)
    launcher = PROJECT / 'm3/.lake/build/bin/leancage'
    subprocess.run([str(launcher),'emit-filter',str(WORK/'filter.bin')],check=True)
    if (PROJECT/'native/m3_filter.h').read_text() != filter_header((WORK/'filter.bin').read_bytes()):
        raise ValueError('Native filter header differs from proved Lean bytes')
    entries.append(('filter.bin',stat.S_IFREG | 0o444,(WORK/'filter.bin').read_bytes(),0,0))
    entries.append(('leancage', stat.S_IFREG | 0o555, launcher.read_bytes(), 0, 0))
    directories = set()
    for library in M1.dependencies(launcher):
        name = str(library).lstrip('/')
        directories.update(str(p) for p in Path(name).parents if str(p) != '.')
        entries.append((name, stat.S_IFREG | 0o555, library.read_bytes(), 0, 0))
    entries[:0] = [(name, stat.S_IFDIR | 0o755, b'', 0, 0) for name in sorted(directories, key=lambda p: (p.count('/'), p))]
    policy = json.loads((PROJECT / 'profiles/m3/example-policy.json').read_text())
    policy['workspace_input'] = 'sha256:' + CASES.input_tree
    policy['stdin_input'] = 'sha256:' + CASES.stdin
    policy['argv'] = ['/usr/local/bin/python3', '-c', "import module,sys; assert module.value==42; assert sys.stdin.read()=='controlled stdin\\n'; print('api-ok')"]
    policy['export'] = 'regular-files'
    entries.append(('api-policy.json', stat.S_IFREG | 0o400, json.dumps(policy).encode(), 0, 0))
    for kind, artifacts in [('trees', CASES.TREES), ('blobs', CASES.BLOBS)]:
        entries.append(('m3-inputs/' + kind, stat.S_IFDIR | 0o700, b'', 0, 0))
        for digest, data in artifacts.items():
            entries.append(('m3-inputs/' + kind + '/' + digest, stat.S_IFREG | 0o400, data, 0, 0))
    for name in ('init', 'leancage-m3-helper'):
        entries.append((name, stat.S_IFREG | 0o555, (WORK / name).read_bytes(), 0, 0))
    assurance = {'schema': 'leancage-m3-assurance-v1', 'source_sha256': source_identities(),
                 'helper_sha256': M1.sha256(WORK / 'leancage-m3-helper'), 'controller_sha256': M1.sha256(launcher),
                 'assumptions': ASSUMPTIONS}
    entries.append(('m3-assurance.json', stat.S_IFREG | 0o444, json.dumps(assurance, sort_keys=True).encode(), 0, 0))
    entries += [('leancage-m3-disposable-vm', stat.S_IFREG | 0o444, b'LeanCage-M3-root-VM-v1', 0, 0),
                ('dev/console', stat.S_IFCHR | 0o600, b'', 5, 1), ('dev/urandom', stat.S_IFCHR | 0o444, b'', 1, 9), ('dev/null', stat.S_IFCHR | 0o666, b'', 1, 3)]
    image = WORK / 'initramfs.cpio.gz'
    image.write_bytes(M1.cpio(entries))
    files = {'/' + name: {'mode': mode, 'sha256': hashlib.sha256(data).hexdigest(), 'major': major, 'minor': minor}
             for name, mode, data, major, minor in entries}
    if len(files) != len(entries):
        raise ValueError('Duplicate image path')
    return image, files


CONFIG = PROJECT / 'tests/m3/linux-6.18.59.config'
EVIDENCE = PROJECT / 'assurance/m3-vm-evidence.json'
TRANSCRIPT = PROJECT / 'assurance/m3-vm-transcript.log'
INVENTORY = PROJECT / 'assurance/m3-image-inventory.json'
PROFILE = 'linux-x86_64-offline-workspace-m3-v1'
MACHINE = dict(acceleration='tcg', cpu='max', vcpus=1, memory_mib=2048,
               host_mounts=[], network_devices=[], persistent_disks=[])
DEATHS = ['cancel_after_entry', 'helper_death', 'controller_death', 'init_death', 'helper_before_fork', 'controller_before_arm']
ASSUMPTIONS = [
    'Root-owned prepared artifacts, reserved UID pool, immutable preloaded runtime and no trusted-root reconfiguration',
    'Local filesystem/credential/cgroup/namespace/syscall contracts; model-to-native/Linux correspondence remains open',
    'Lean/C compilers, runtimes, libc, ELF loader, SHA-256 artifact identities and QEMU/firmware',
    'Scheduling fairness and terminating kernel calls are needed for progress; no unconditional overshoot bound',
    'No timing, cache, scheduling, speculation or physical hardware confidentiality claim']


def source_identities():
    paths = [PROJECT / p for p in ['scripts/run_m3_vm.py', 'scripts/m3_runtime.py', 'scripts/m3_elf.py', 'scripts/run_m1_vm.py',
        'scripts/audit_m3.py', 'scripts/m3_axiom_query.lean', 'lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
        'tests/vm/bootstrap-pins.json', 'docs/functional-spec/FS-workspace.md', 'docs/architecture/AR-workspace.md',
        'docs/decisions/architectural/DA-m3-profile.md']]
    for directory, suffixes in [('m3', {'.lean', '.json', '.py'}), ('tests/m3', {'.c', '.py', '.config', '.fragment'}),
                                ('profiles/m3', {'.json'}), ('LeanCage', {'.lean'}), ('m2/LeanCageM2', {'.lean'})]:
        paths += [p for p in (PROJECT / directory).rglob('*') if p.is_file() and p.suffix in suffixes
                  and '.lake' not in p.parts and '__pycache__' not in p.parts]
    paths += sorted((PROJECT / 'native').glob('*m3*'))
    paths += [PROJECT / p for p in ['m2/LeanCageM2.lean', 'm2/lakefile.lean', 'm2/lake-manifest.json', 'm2/lean-toolchain', 'LeanCage.lean', 'm3/lean-toolchain']]
    return {str(p.relative_to(PROJECT)): M1.sha256(p) for p in sorted(set(paths))}


def command_for(project):
    work = project / '.tools/m3vm'; root = work / 'root'
    return [str(root / 'usr/bin/qemu-system-x86_64'), '-L', str(root / 'usr/share/qemu'), '-no-user-config', '-nodefaults',
            '-machine', 'pc,accel=tcg', '-cpu', 'max', '-smp', '1', '-m', '2048M', '-bios', str(root / 'usr/share/seabios/bios-256k.bin'),
            '-display', 'none', '-serial', 'stdio', '-monitor', 'none', '-nic', 'none', '-no-reboot',
            '-device', 'isa-debug-exit,iobase=0xf4,iosize=0x04', '-kernel', str(work / 'linux-6.18.59/arch/x86/boot/bzImage'),
            '-initrd', str(work / 'initramfs.cpio.gz'), '-append',
            'console=ttyS0,115200 rdinit=/init panic=1 oops=panic loglevel=3 clocksource=acpi_pm tsc=unstable']


def environment_record():
    return {'inherit_host_environment': True, 'overrides': {
        'LD_LIBRARY_PATH': '{project}/.tools/m3vm/root/usr/lib/x86_64-linux-gnu',
        'QEMU_MODULE_DIR': '{project}/.tools/m3vm/root/usr/lib/x86_64-linux-gnu/qemu'}}


def environment():
    root = WORK / 'root'
    return dict(os.environ, LD_LIBRARY_PATH=str(root / 'usr/lib/x86_64-linux-gnu'),
                QEMU_MODULE_DIR=str(root / 'usr/lib/x86_64-linux-gnu/qemu'))


def validate_transcript(text, code):
    text = text.replace('\r', '')
    if code != 33 or text.count(f'M3_COMPLETE cases={len(CASES.CASES)} failures=0\n') != 1:
        raise ValueError('Incomplete or failing VM; a timeout/harness failure is not a denial')
    control = 'M3_CONTROL unix=roundtrip ipv4=roundtrip ipv6=roundtrip sysvipc=roundtrip posixshm=roundtrip ptrace=working cgroup=present runtime_readonly=1\n'
    if text.count(control) != 1 or text.count('M3_PROFILE kernel=6.18.59 uid=0\n') != 1:
        raise ValueError('Missing positive controls/profile')
    records = [json.loads(line.removeprefix('M3_RESULT ')) for line in text.splitlines() if line.startswith('M3_RESULT ')]
    if [r.get('name') for r in records] != [c['name'] for c in CASES.CASES]:
        raise ValueError('Missing, duplicated, reordered or unknown cases')
    keys = set('name frame_bytes kind stage detail entry clean triggers run uid cpu peak out err elapsed oom pids export omitted export_valid stdout_sha256 stderr_sha256 stdout_stored stderr_stored stdout_prefix_hex stderr_prefix_hex began ended exit sentinel extinct valid'.split())
    seen = set()
    for r, c in zip(records, CASES.CASES):
        if set(r) != keys or any(type(v) is not int or v < 0 for k, v in r.items() if k not in {'name','stdout_sha256','stderr_sha256','stdout_prefix_hex','stderr_prefix_hex'}):
            raise ValueError('Malformed case schema')
        if r['frame_bytes'] != 160 or r['kind'] != c['kind'] or r['entry'] != c['entry'] or r['clean'] != c['clean']:
            raise ValueError('Wrong private outcome: ' + c['name'])
        if (c['detail'] >= 0 and r['detail'] != c['detail']) or (c['detail'] < 0 and not 1 <= r['detail'] <= 4095):
            raise ValueError('Wrong outcome detail')
        if (c['triggers'] and r['triggers'] & c['triggers'] != c['triggers']) or (not c['triggers'] and r['triggers']):
            raise ValueError('Wrong cancellation evidence')
        expected_exit = c['detail'] if c['kind'] == 0 else 125 if c['kind'] == 1 else 128+c['detail'] if c['kind'] == 2 else 124 if c['kind'] == 3 else 0 if c['kind'] == 7 else 126
        if r['exit'] != expected_exit or not all(r[k] == 1 for k in ('sentinel','extinct','valid')):
            raise ValueError('Missing scope/sentinel or unsuccessful case')
        if r['export'] != c['export_state'] or r['omitted'] != c['omitted'] or (r['export'] == 1 and not r['export_valid']):
            raise ValueError('Wrong export observation')
        if c['triggers'] & 4 and r['cpu'] < c['cpu']: raise ValueError('CPU cancellation lacks threshold observation')
        if c['triggers'] & 2 and r['elapsed'] < c['wall']: raise ValueError('Deadline cancellation lacks elapsed observation')
        if c['triggers'] & 8 and c['fault'] not in {'output_fail','output_close_fail'} and r['out'] <= c['out_cap'] and r['err'] <= c['err_cap']:
            raise ValueError('Output cancellation lacks cap exceedance')
        if (c['oom'] and r['oom'] < 1) or (c['pids'] and r['pids'] < 1):
            raise ValueError('Resource denial lacks private counter evidence')
        if c['check']:
            if r['run'] or r['uid']: raise ValueError('Preflight claimed a guest run')
        elif c['name'] == 'reservation_rejected':
            if r['run'] or r['uid']: raise ValueError('Rejected reservation allocated an identity')
        elif not r['run'] or r['run'] in seen or not 100000 <= r['uid'] <= 100999:
            raise ValueError('Invalid/reused run identity')
        seen.add(r['run'])
        for stream in ('stdout', 'stderr'):
            cap = c['out_cap' if stream == 'stdout' else 'err_cap']; count = r['out' if stream == 'stdout' else 'err']
            stored = r[stream+'_stored']; digest = r[stream+'_sha256']; prefix = r[stream+'_prefix_hex']
            if stored > cap or (r['entry'] and stored != min(count, cap)) or not re.fullmatch('[0-9a-f]*', prefix) or len(prefix) % 2 or len(prefix) > 8192:
                raise ValueError('Unbounded/inconsistent output capture')
            if r['entry'] and not re.fullmatch('[0-9a-f]{64}', digest): raise ValueError('Missing output identity')
            if stored <= 4096 and digest and hashlib.sha256(bytes.fromhex(prefix)).hexdigest() != digest:
                raise ValueError('Output prefix differs from identity')
        if c['expected'] and r['stdout_sha256'] != hashlib.sha256(c['expected'].encode()).hexdigest():
            raise ValueError('Useful workload output differs')
        if r['ended'] < r['began']: raise ValueError('Nonmonotonic harness timestamps')
    a,b = records[-2:]
    if a['uid'] == b['uid'] or max(a['began'],b['began']) >= min(a['ended'],b['ended']):
        raise ValueError('Sibling runs did not overlap with distinct credentials')
    apis = []
    for line in text.splitlines():
        if line.startswith('M3_API '):
            m = re.fullmatch(r'M3_API name=(check|run|report) exit=0 json_hex=([0-9a-f]+)', line)
            if not m or len(m[2]) > 131072: raise ValueError('Invalid API transport')
            apis.append({'name': m[1], 'result': json.loads(bytes.fromhex(m[2]))})
    if [a['name'] for a in apis] != ['check','run','report'] or apis[1]['result'] != apis[2]['result']:
        raise ValueError('check/run/report did not use the same stored result')
    if apis[0]['result']['termination'] != 'preflight_supported' or apis[1]['result']['termination'] != 'exited' or apis[1]['result']['entry'] != 'yes' or apis[1]['result']['export'] != 'complete':
        raise ValueError('Useful API execution failed')
    deaths = [json.loads(l.removeprefix('M3_DEATH ')) for l in text.splitlines() if l.startswith('M3_DEATH ')]
    if [d.get('name') for d in deaths] != DEATHS: raise ValueError('Missing/reordered death boundaries')
    for d in deaths:
        if set(d) != set('name ready frame_bytes run extinct quarantined sentinel private_ok valid'.split()) or not all(d[k] == 1 for k in ('ready','extinct','sentinel','private_ok','valid')):
            raise ValueError('Death/cancellation evidence failed')
        if d['name'] in {'helper_death','controller_death','helper_before_fork'} and (d['frame_bytes'] or d['quarantined'] != 1):
            raise ValueError('Uncertain death must quarantine without fabricated result')
    return {'cases': records, 'api': apis, 'death': deaths}


def prepare():
    pins = json.loads(M1.PINS.read_text()); root = WORK / 'root'; packages = WORK / 'packages'
    host = platform.freedesktop_os_release()
    if platform.machine() != pins['host_arch'] or host.get('ID') != pins['host_distribution'] or host.get('VERSION_ID') != pins['host_version']:
        raise ValueError('Unsupported bootstrap host')
    packages.mkdir(parents=True, exist_ok=True); root.mkdir(exist_ok=True)
    for package in pins['packages']:
        path = packages / package['filename']
        if not path.exists(): subprocess.run(['apt-get','download',package['name']+'='+package['version']],cwd=packages,check=True)
        M1.check_hash(path,package['sha256'])
        subprocess.run(['dpkg-deb','--extract',str(path),str(root)],check=True)
    archive = WORK / 'linux-6.18.59.tar.xz'
    if not archive.exists(): urllib.request.urlretrieve(pins['kernel_archive_url'],archive)
    M1.check_hash(archive,pins['kernel_archive_sha256'])
    kernel = WORK / 'linux-6.18.59'
    if not kernel.exists(): subprocess.run(['tar','--extract','--xz','--file',str(archive),'--directory',str(WORK)],check=True)
    shutil.copyfile(CONFIG,kernel/'.config')
    env = dict(os.environ,PATH=f'{root}/usr/bin:/usr/bin:/bin',M4=f'{root}/usr/bin/m4',BISON_PKGDATADIR=f'{root}/usr/share/bison',
        HOSTCFLAGS=f'-O2 -I{root}/usr/include',HOSTLDFLAGS=f'-L{root}/usr/lib/x86_64-linux-gnu',
        PKG_CONFIG_PATH=f'{root}/usr/lib/x86_64-linux-gnu/pkgconfig',KBUILD_BUILD_TIMESTAMP='2026-10-31 00:00:00 UTC',
        KBUILD_BUILD_USER='leancage',KBUILD_BUILD_HOST='disposable-m3',KBUILD_BUILD_VERSION='1')
    with (WORK/'kernel-build.log').open('w') as log:
        subprocess.run(['nice','-n','10','make','-j2','ARCH=x86_64','olddefconfig','bzImage'],cwd=kernel,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
    M1.check_hash(kernel/'.config',M1.sha256(CONFIG))
    RUNTIME.fetch_layers(RUNTIME.load_lock())


def artifact_paths():
    root = WORK/'root'; prefix = Path(subprocess.run(['lake','env','lean','--print-prefix'],cwd=PROJECT,capture_output=True,text=True,check=True).stdout.strip())
    paths = {'qemu':root/'usr/bin/qemu-system-x86_64','firmware':root/'usr/share/seabios/bios-256k.bin',
        'qemu_accel':root/'usr/lib/x86_64-linux-gnu/qemu/accel-tcg-x86_64.so',
        'qemu_rom_kvmvapic':root/'usr/share/qemu/kvmvapic.bin','qemu_rom_linuxboot':root/'usr/share/qemu/linuxboot_dma.bin',
        'kernel':WORK/'linux-6.18.59/arch/x86/boot/bzImage','kernel_config':WORK/'linux-6.18.59/.config',
        'initramfs':WORK/'initramfs.cpio.gz','init':WORK/'init','helper':WORK/'leancage-m3-helper',
        'controller':PROJECT/'m3/.lake/build/bin/leancage','filter':WORK/'filter.bin','lean':prefix/'bin/lean','clang':prefix/'bin/clang',
        'leanrt':prefix/'lib/lean/libleanrt.a','cc':Path(shutil.which('cc')).resolve()}
    for path in M1.dependencies(paths['qemu'],environment()): paths['qemu_library:'+path.name] = path
    for path in M1.dependencies(paths['controller']): paths['controller_library:'+path.name] = path
    return paths


def validate_evidence(e, transcript=TRANSCRIPT, inventory=INVENTORY):
    expected = {'schema_version','status','profile','kernel','machine','command','return_code','timeout_seconds','observations',
                'source_sha256','artifacts_sha256','inventory_sha256','transcript_sha256','tools','assumptions','environment'}
    if set(e) != expected or e['schema_version'] != 1 or e['status'] != 'passed' or e['profile'] != PROFILE:
        raise ValueError('Unsupported/incomplete M3 evidence schema')
    pins = json.loads(M1.PINS.read_text())
    kernel = {'version':pins['kernel_version'],'commit':pins['kernel_commit'],'archive_sha256':pins['kernel_archive_sha256'],'config_sha256':M1.sha256(CONFIG)}
    if e['kernel'] != kernel or e['machine'] != MACHINE or e['command'] != command_for(Path('{project}')) or e['timeout_seconds'] != 300:
        raise ValueError('VM/kernel/isolation profile mismatch')
    if e['source_sha256'] != source_identities() or e['transcript_sha256'] != M1.sha256(transcript) or e['inventory_sha256'] != M1.sha256(inventory):
        raise ValueError('Stale source, transcript or image inventory')
    if e['environment'] != environment_record(): raise ValueError('Changed or mixed-root emulator environment')
    if e['observations'] != validate_transcript(transcript.read_text(),e['return_code']): raise ValueError('Structured observations differ')
    artifacts=e['artifacts_sha256']; needed={'qemu','firmware','qemu_accel','qemu_rom_kvmvapic','qemu_rom_linuxboot','kernel','kernel_config','initramfs','init','helper','controller','lean','clang','leanrt','cc'}
    if set(artifacts) != set(json.loads((PROJECT/'profiles/m3/artifact-labels.json').read_text())) or not needed <= artifacts.keys() or not all(re.fullmatch('[0-9a-f]{64}',v) for v in artifacts.values()) or artifacts['kernel_config'] != M1.sha256(CONFIG):
        raise ValueError('Missing/malformed artifact identities')
    files=json.loads(inventory.read_text())
    for name,record in files.items():
        if not name.startswith('/') or '..' in Path(name).parts or set(record) != {'mode','sha256','major','minor'} or not re.fullmatch('[0-9a-f]{64}',record['sha256']) or type(record['mode']) is not int:
            raise ValueError('Malformed image inventory')
    if len(files) < 6500 or not {'/m3-runtime/usr/bin/dash','/m3-runtime/usr/local/bin/python3.13','/api-policy.json','/dev/urandom','/m3-assurance.json'} <= files.keys():
        raise ValueError('Missing runtime/controller fixture closure')
    lock=RUNTIME.load_lock()
    for entry in lock['entrypoints'].values():
        if files['/m3-runtime'+entry['resolved_path']]['sha256'] != entry['sha256']: raise ValueError('Runtime executable/loader receipt differs')
    for name,key in [('/init','init'),('/leancage','controller'),('/leancage-m3-helper','helper'),('/filter.bin','filter')]:
        if files[name]['sha256'] != artifacts[key]: raise ValueError('Image binary differs from compiled artifact')
    tools=e['tools']
    if set(tools) != {'qemu','cc','libc','lean','host_distribution'} or not all(tools.values()) or '8.2.2' not in tools['qemu'] or '4.35.0' not in tools['lean'] or e['assumptions'] != ASSUMPTIONS:
        raise ValueError('Incomplete tool or assumption record')


def check_evidence(current_artifacts=False):
    e=json.loads(EVIDENCE.read_text()); validate_evidence(e)
    if current_artifacts:
        paths=artifact_paths()
        if set(paths) != set(e['artifacts_sha256']): raise ValueError('Current artifact inventory differs')
        for key,path in paths.items(): M1.check_hash(path,e['artifacts_sha256'][key])
    print(f'M3 evidence verified: {len(e["observations"]["cases"])} cases, 3 API checks, {len(DEATHS)} death/cancel boundaries; '+
          ('current artifacts match.' if current_artifacts else 'archived source/transcript check; no VM replay.'))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group()
    group.add_argument('--prepare',action='store_true'); group.add_argument('--check-evidence',action='store_true');group.add_argument('--check-artifacts',action='store_true');group.add_argument('--development',action='store_true')
    args=parser.parse_args()
    if args.check_evidence or args.check_artifacts: return check_evidence(args.check_artifacts)
    if args.prepare: return prepare()
    if not args.development:
        pins=json.loads(M1.PINS.read_text())
        for p in pins['packages']: M1.check_hash(WORK/'packages'/p['filename'],p['sha256'])
        M1.check_hash(WORK/'linux-6.18.59.tar.xz',pins['kernel_archive_sha256'])
    sources=source_identities(); image,files=build_image()
    M1.check_hash(WORK/'linux-6.18.59/.config',M1.sha256(CONFIG))
    command=command_for(PROJECT);env=environment(); log=WORK/('development-transcript.log' if args.development else 'replay-transcript.log')
    with log.open('w') as output:
        result=subprocess.run(command,env=env,stdout=output,stderr=subprocess.STDOUT,timeout=300)
    observations=validate_transcript(log.read_text(),result.returncode)
    if args.development:
        print(f'Development VM passed: {len(observations["cases"])} cases, API and death checks; no accepted record generated.');return
    if sources != source_identities(): raise ValueError('Sources changed during replay')
    inventory=WORK/'replay-inventory.json'
    inventory.write_text(json.dumps(files,indent=2,sort_keys=True)+'\n')
    tools={}
    for key,cmd in {'qemu':[command[0],'--version'],'cc':['cc','--version'],'libc':['getconf','GNU_LIBC_VERSION'],'lean':['lake','env','lean','--version']}.items():
        tools[key]=subprocess.run(cmd,cwd=PROJECT,env=env,capture_output=True,text=True,check=True).stdout.strip()
    tools['host_distribution']=platform.freedesktop_os_release(); pins=json.loads(M1.PINS.read_text())
    evidence={'schema_version':1,'status':'passed','profile':PROFILE,
        'kernel':{'version':pins['kernel_version'],'commit':pins['kernel_commit'],'archive_sha256':pins['kernel_archive_sha256'],'config_sha256':M1.sha256(CONFIG)},
        'machine':MACHINE,'command':command_for(Path('{project}')),'environment':environment_record(),'return_code':result.returncode,'timeout_seconds':300,
        'observations':observations,'source_sha256':sources,'artifacts_sha256':{key:M1.sha256(path) for key,path in artifact_paths().items()},
        'inventory_sha256':M1.sha256(inventory),'transcript_sha256':M1.sha256(log),'tools':tools,'assumptions':ASSUMPTIONS}
    validate_evidence(evidence,log,inventory)
    TRANSCRIPT.write_bytes(log.read_bytes());INVENTORY.write_bytes(inventory.read_bytes())
    EVIDENCE.write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n')
    print(f'M3 fresh VM replay passed: {len(observations["cases"])} cases, 3 API checks, {len(DEATHS)} death/cancel boundaries.')


if __name__ == '__main__':
    try: main()
    except (ValueError,OSError,subprocess.SubprocessError) as error:
        print(f'M3 VM failed: {error}',file=sys.stderr);sys.exit(1)
