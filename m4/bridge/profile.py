#!/usr/bin/env python3
"""Pinned, project-local experimental bridge profile; no host installation."""
# §AR-m4-bridge.profile: This profile is separate from the maintained Coq 8.18 profile.
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = ROOT / 'm4/bridge'
WORK = ROOT / '.tools/m4/bridge'
SWITCH = 'strict-9.3'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def lock():
    result = json.loads((DIRECTORY / 'toolchain-lock.json').read_text())
    if digest(DIRECTORY / 'opam-switch.export') != result['switch_export_sha256']:
        raise ValueError('bridge switch metadata differs from the pin')
    if digest(DIRECTORY / 'strict-importer.patch') != result['importer_patch_sha256']:
        raise ValueError('strict importer patch differs from the pin')
    return result


def environment():
    env = os.environ.copy()
    for key in ['OCAMLLIB', 'OCAMLFIND_CONF', 'OCAMLPATH', 'COQLIB', 'COQCORELIB']:
        env.pop(key, None)
    sysroot = WORK / 'sysroot/usr'
    env.update(OPAMROOT=str(WORK / 'opam'), OPAMJOBS='4',
               C_INCLUDE_PATH=f'{sysroot}/include:{sysroot}/include/x86_64-linux-gnu',
               LIBRARY_PATH=f'{sysroot}/lib/x86_64-linux-gnu',
               LD_LIBRARY_PATH=f'{sysroot}/lib/x86_64-linux-gnu')
    return env


def run(command, *, cwd=WORK, timeout=180, capture=True, profile=True):
    args = [str(WORK / 'opam-bin'), 'exec', '--switch=' + SWITCH, '--', *command] if profile else command
    return subprocess.run(args, cwd=cwd, env=environment(), text=True,
                          stdout=subprocess.PIPE if capture else None,
                          stderr=subprocess.STDOUT, timeout=timeout, check=True)


def fetch(record, path):
    if not path.exists():
        temporary = path.with_suffix(path.suffix + '.download')
        urllib.request.urlretrieve(record['url'], temporary)
        if digest(temporary) != record['sha256']:
            raise ValueError('download differs from pin: ' + record['url'])
        temporary.replace(path)
    if digest(path) != record['sha256']:
        raise ValueError('cached download differs from pin: ' + str(path))


def archive_files(archive):
    with tarfile.open(archive) as stream:
        for member in stream:
            parts = Path(member.name).parts[1:]
            if not parts or member.isdir():
                continue
            if not member.isfile() or '..' in parts or Path(*parts).is_absolute():
                raise ValueError('unsupported source archive member')
            yield Path(*parts), stream.extractfile(member).read(), member.mode


def source_tree(archive, target, overrides=None):
    if not target.exists():
        target.mkdir()
        for relative, data, mode in archive_files(archive):
            path = target / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            path.chmod(mode)
    for relative, data, _ in archive_files(archive):
        expected = (overrides or {}).get(str(relative), hashlib.sha256(data).hexdigest())
        if digest(target / relative) != expected:
            raise ValueError('bridge tool source differs: ' + str(target / relative))


def flags(*, checker=False):
    source = WORK / 'CompCert'
    args = ['-Q', str(WORK / 'rocq-lean-import/src'), 'LeanImport']
    if not checker:
        args += ['-I', str(WORK / 'rocq-lean-import/src')]
    for directory in ['lib', 'common', 'x86_64', 'x86', 'backend', 'cfrontend', 'driver', 'cparser', 'export']:
        args += ['-R', str(source / directory), 'compcert.' + directory]
    return args + ['-R', str(source / 'flocq'), 'Flocq',
                   '-R', str(source / 'MenhirLib'), 'MenhirLib',
                   '-Q', str(WORK / 'source'), '', '-Q', str(WORK / 'proofs'), '']


def lean_run(command, *, timeout=180):
    package = ROOT / 'm3'
    paths = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=package, text=True).strip()
    return subprocess.run(['lake', 'env', 'env', 'LEAN_PATH=' + str(WORK / 'modules') + ':' + paths, *command],
                          cwd=package, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          timeout=timeout, check=True)


def verify_tools():
    pins = lock()
    if (ROOT / 'm3/lean-toolchain').read_text().strip() != pins['lean_toolchain']:
        raise ValueError('Lean toolchain differs from bridge pin')
    if digest(WORK / 'opam-bin') != pins['opam']['sha256']:
        raise ValueError('opam binary differs from bridge pin')
    for key, directory in [('exporter', 'lean4export'), ('importer', 'rocq-lean-import'), ('compcert', 'CompCert')]:
        archive = WORK / (key + '-source.tar.gz')
        if digest(archive) != pins[key]['sha256']:
            raise ValueError('tool archive differs: ' + key)
        source_tree(archive, WORK / directory,
                    {'src/lean.ml': pins['patched_importer_source_sha256']} if key == 'importer' else None)
    installed = run([str(WORK / 'opam-bin'), 'list', '--installed', '--columns=name,version', '--short', '--switch=' + SWITCH]).stdout
    if dict(line.split() for line in installed.splitlines() if line.strip()) != pins['installed']:
        raise ValueError('installed bridge packages differ from the complete pinned set')
    for package in pins['packages']:
        path = WORK / 'packages' / package['name']
        if digest(path) != package['sha256']:
            raise ValueError('local GMP package differs')
    if not run(['rocq', '--version']).stdout.startswith('The Rocq Prover, version 9.3.0'):
        raise ValueError('unexpected bridge checker version')
    return pins


def prepare():
    host = platform.freedesktop_os_release()
    if platform.machine() != 'x86_64' or host.get('ID') != 'ubuntu' or host.get('VERSION_ID') != '24.04':
        raise ValueError('bridge bootstrap requires the recorded Ubuntu 24.04 x86_64 profile')
    pins = lock()
    WORK.mkdir(parents=True, exist_ok=True)
    fetch(pins['opam'], WORK / 'opam-bin')
    (WORK / 'opam-bin').chmod(0o755)
    (WORK / 'packages').mkdir(exist_ok=True)
    (WORK / 'sysroot').mkdir(exist_ok=True)
    for package in pins['packages']:
        path = WORK / 'packages' / package['name']
        fetch(package, path)
        run(['dpkg-deb', '--extract', str(path), str(WORK / 'sysroot')], profile=False)
    if not (WORK / 'opam/config').exists():
        run([str(WORK / 'opam-bin'), 'init', '--bare', '--no-setup', '--disable-sandboxing', '--yes',
             'default', 'https://opam.ocaml.org'], profile=False, timeout=600, capture=False)
    if not (WORK / 'opam' / SWITCH / '.opam-switch').exists():
        run([str(WORK / 'opam-bin'), 'switch', 'create', SWITCH, '--empty', '--yes'], profile=False)
    run([str(WORK / 'opam-bin'), 'switch', 'import', '--switch=' + SWITCH, '--yes', '--assume-depexts',
         str(DIRECTORY / 'opam-switch.export')], profile=False, timeout=1800, capture=False)
    for key, directory in [('exporter', 'lean4export'), ('importer', 'rocq-lean-import'), ('compcert', 'CompCert')]:
        archive = WORK / (key + '-source.tar.gz')
        fetch(pins[key], archive)
        target = WORK / directory
        overrides = None
        if key == 'importer' and target.exists() and digest(target / 'src/lean.ml') == pins['patched_importer_source_sha256']:
            overrides = {'src/lean.ml': pins['patched_importer_source_sha256']}
        source_tree(archive, target, overrides)
        if key == 'importer' and overrides is None:
            run(['patch', '-p1', '--forward', '-i', str(DIRECTORY / 'strict-importer.patch')], cwd=target, profile=False)
    run(['lake', 'build'], cwd=WORK / 'lean4export', profile=False, timeout=600, capture=False)
    run(['make', '-j4'], cwd=WORK / 'rocq-lean-import', timeout=600, capture=False)
    # Only the front-end's advertised-version check is bypassed; all proof checks remain enabled.
    run(['./configure', '-ignore-rocq-version', '-clightgen', '-prefix', str(WORK / 'installed'), 'x86_64-linux'],
        cwd=WORK / 'CompCert', capture=False)
    run(['make', '-j4', 'depend'], cwd=WORK / 'CompCert', timeout=600, capture=False)
    run(['make', '-j4', 'proof'], cwd=WORK / 'CompCert', timeout=1800, capture=False)
    verify_tools()


if __name__ == '__main__':
    prepare()
