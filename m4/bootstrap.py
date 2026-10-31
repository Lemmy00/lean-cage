#!/usr/bin/env python3
"""Extract pinned proof tools locally; no host installation or maintainer scripts."""
# §AR-m4-native.semantics: Research tooling is local, pinned, and separately licensed.
import hashlib
import json
import os
import platform
import tarfile
from pathlib import Path
import subprocess
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / '.tools/m4'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fetch(url, path, expected):
    if not path.exists():
        temporary = path.with_suffix('.download')
        urllib.request.urlretrieve(url, temporary)
        if digest(temporary) != expected:
            raise ValueError(f'download digest mismatch: {url}')
        temporary.replace(path)
    if digest(path) != expected:
        raise ValueError(f'pinned input mismatch: {path}')


def environment():
    root = WORK / 'root'
    return dict(os.environ, PATH=f'{root}/usr/bin:/usr/bin:/bin',
                OCAMLLIB=f'{root}/usr/lib/ocaml',
                OCAMLFIND_CONF=f'{WORK}/findlib.conf',
                OCAMLPATH=f'{root}/usr/lib/ocaml',
                CAML_LD_LIBRARY_PATH=f'{root}/usr/lib/ocaml/stublibs',
                COQLIB=f'{root}/usr/lib/ocaml/coq',
                COQCORELIB=f'{root}/usr/lib/ocaml/coq-core')


def prepare():
    host = platform.freedesktop_os_release()
    if platform.machine() != 'x86_64' or host.get('ID') != 'ubuntu' or host.get('VERSION_ID') != '24.04':
        raise ValueError('M4 bootstrap supports the recorded Ubuntu 24.04 x86-64 profile only')
    pins = json.loads((ROOT / 'm4/toolchain-lock.json').read_text())
    packages = WORK / 'packages'
    packages.mkdir(parents=True, exist_ok=True)
    root = WORK / 'root'
    root.mkdir(exist_ok=True)
    for package in pins['packages']:
        path = packages / package['url'].rsplit('/', 1)[1]
        fetch(package['url'], path, package['sha256'])
        subprocess.run(['dpkg-deb', '--extract', path, root], check=True)
    (WORK / 'findlib.conf').write_text(
        f'path="{root}/usr/lib/ocaml"\ndestdir="{root}/usr/lib/ocaml"\n')
    archive = WORK / 'compcert.tar.gz'
    fetch(pins['compcert']['url'], archive, pins['compcert']['sha256'])
    source = WORK / 'CompCert'
    if not source.exists():
        source.mkdir()
        subprocess.run(['tar', '-xzf', archive, '--strip-components=1', '-C', source], check=True)
    with tarfile.open(archive) as tar:
        for member in tar:
            if member.isfile():
                path = source / Path(*Path(member.name).parts[1:])
                if path.read_bytes() != tar.extractfile(member).read():
                    raise ValueError(f'changed CompCert source before build: {path}')
    env = environment()
    subprocess.run(['./configure', '-clightgen', '-prefix', str(WORK / 'installed'),
                    'x86_64-linux'], cwd=source, env=env, check=True)
    subprocess.run(['make', '-j2'], cwd=source, env=env, check=True)


if __name__ == '__main__':
    prepare()
