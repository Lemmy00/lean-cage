#!/usr/bin/env python3
"""Run the pinned prover on project proof inputs in an ignored build directory."""
# §AR-m4-native.evidence: Checked terms, not a compiler shortcut, are proof evidence.
from pathlib import Path
import shutil
import subprocess
import sys
from bootstrap import ROOT, WORK, environment


def flags():
    source = WORK / 'CompCert'
    args = []
    for directory in ['lib', 'common', 'x86_64', 'x86', 'backend', 'cfrontend', 'driver', 'cparser', 'export']:
        args += ['-R', str(source / directory), 'compcert.' + directory]
    return args + ['-R', str(source / 'flocq'), 'Flocq', '-R', str(source / 'MenhirLib'), 'MenhirLib',
                   '-Q', str(WORK / 'input'), '']


def compile_file(name):
    target = WORK / 'input' / name
    if (ROOT / 'm4' / name).exists():
        shutil.copyfile(ROOT / 'm4' / name, target)
    return subprocess.run([str(WORK / 'root/usr/bin/coqc'), '-q', *flags(), str(target)],
                          env=environment(), cwd=WORK / "input", text=True, capture_output=True, timeout=180)


if __name__ == '__main__':
    for name in sys.argv[1:]:
        result = compile_file(name)
        print(result.stdout + result.stderr, end='')
        if result.returncode:
            sys.exit(result.returncode)
