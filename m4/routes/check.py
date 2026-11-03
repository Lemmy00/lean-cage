#!/usr/bin/env python3
"""Replay reviewed early connection attempts; expected failures discharge no M4 edge."""
# SPDX-License-Identifier: Apache-2.0
# §AR-m4-routes.evidence: Exact inputs, checked audit and reproducible negative attempts.
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import shlex
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = ROOT / 'm4/routes'
WORK = ROOT / '.tools/m4/routes'
PORT = ROOT / '.tools/m4/proof-connection/clean'
KERNEL = ROOT / '.tools/m3vm/linux-6.18.59'
RECORD = ROOT / 'assurance/m4-route-feasibility.json'
RAW = ROOT / 'assurance/m4-route-feasibility-output.json.gz'
REVISION = '123f7f7767e215aceb4821f0d044336d78103ade'
REPOSITORY = 'https://github.com/Certora/clean.git'
TOOLCHAIN = 'leanprover/lean4:v4.35.0'
spec = importlib.util.spec_from_file_location('route_profile', ROOT / 'm4/bridge/profile.py')
profile = importlib.util.module_from_spec(spec)
spec.loader.exec_module(profile)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(command, cwd, expected=0):
    result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=180)
    output = result.stdout.replace(str(ROOT), '{project}')
    if result.returncode != expected:
        raise ValueError('unexpected attempt outcome: ' + repr(command) + '\n' + output[-3000:])
    return output


def sources():
    paths = [p for p in DIRECTORY.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
    paths += [ROOT / 'docs/architecture/AR-m4-routes.md',
              ROOT / 'docs/decisions/architectural/DA-m4-routes.md',
              ROOT / 'tests/vm/bootstrap-pins.json', ROOT / 'tests/m3/linux-6.18.59.config',
              ROOT / 'm3/lean-toolchain', ROOT / 'm4/bridge/toolchain-lock.json',
              ROOT / 'm4/bridge/strict-importer.patch', ROOT / 'm4/bridge/opam-switch.export']
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths)}


def prepare():
    PORT.parent.mkdir(parents=True, exist_ok=True)
    if not PORT.exists():
        run(['git', 'clone', '--no-checkout', REPOSITORY, str(PORT)], ROOT)
        run(['git', 'checkout', '--detach', REVISION], PORT)
    if run(['git', 'rev-parse', 'HEAD'], PORT).strip() != REVISION:
        raise ValueError('inspection checkout differs; preserve it and prepare the specified revision')


def collect(expected=None):
    started = time.monotonic()
    profile.verify_tools()
    if (ROOT / 'm3/lean-toolchain').read_text().strip() != TOOLCHAIN:
        raise ValueError('maintained Lean pin differs')
    if not PORT.is_dir() or not KERNEL.is_dir():
        raise ValueError('prepare the inspection checkout and existing M3 VM build inputs first; see m4/routes/README.md')
    if (run(['git', 'rev-parse', 'HEAD'], PORT).strip() != REVISION
            or run(['git', 'status', '--porcelain', '--untracked-files=no'], PORT).strip()):
        raise ValueError('experimental source revision or tracked bytes differ')
    before = sources()
    if expected is not None and before != expected['source_sha256']:
        raise ValueError('reviewed attempt sources differ')
    WORK.mkdir(parents=True, exist_ok=True)
    export = PORT / 'export'
    library_sources = list((export / 'CCLib').glob('*.lean'))
    library_sources += [export / 'CCLib.lean', export / 'lakefile.toml',
                        export / 'lean-toolchain', PORT / 'LICENSE']
    library = {str(p.relative_to(PORT)): digest(p) for p in sorted(library_sources)}
    kernel_inputs = {str(p.relative_to(KERNEL)): digest(p) for p in
                     [KERNEL / 'fs/pipe.c', KERNEL / 'include/uapi/linux/types.h',
                      KERNEL / 'fs/.pipe.o.cmd', KERNEL / '.config']}
    if expected is not None and (library != expected['lean_port_sources_sha256']
                                or kernel_inputs != expected['kernel_input_sha256']):
        raise ValueError('reviewed port or configured kernel inputs differ')
    logs = {'port_build': run(['lake', '+' + TOOLCHAIN, 'build', 'CCLib'], export)}
    logs['port_audit'] = run(['lake', '+' + TOOLCHAIN, 'env', 'lean', str(DIRECTORY / 'PortAudit.lean')], export)
    expected_audit = ['CC.Step', 'CC.doStep_sound', 'CC.externalFunctionsSem',
                      'CC.inlineAssemblySem', 'Classical.choice', 'Quot.sound', 'propext']
    if not all(fragment in logs['port_audit'] for fragment in expected_audit):
        raise ValueError('port theorem or foundation audit differs')
    closure = run(['lake', '+' + TOOLCHAIN, 'env',
                   str(ROOT / '.tools/m4/bridge/lean4export/.lake/build/bin/lean4export'),
                   'CCLib.Clight', '--', 'CC.Step'], export)
    (WORK / 'ported-step.ndjson').write_text(closure)
    for name in ['StrictPort', 'StrictPortScheme']:
        path = WORK / (name + '.v')
        shutil.copyfile(DIRECTORY / path.name, path)
        try:
            result = profile.run(['rocq', 'c', '-q', *profile.flags(), str(path)], cwd=WORK)
        except subprocess.CalledProcessError as error:
            output = error.stdout.replace(str(ROOT), '{project}')
            if error.returncode != 1 or not all(part in output for part in
                    ['for CC.Ty', 'src/lean.ml', 'Assertion failed']):
                raise ValueError('strict import failed differently: ' + output[-3000:]) from error
            logs[name] = output
        else:
            raise ValueError('strict import now succeeds; review the new connection before updating expectations')
    pins = json.loads((ROOT / 'tests/vm/bootstrap-pins.json').read_text())
    if (digest(ROOT / '.tools/m3vm/linux-6.18.59.tar.xz') != pins['kernel_archive_sha256']
            or digest(KERNEL / '.config') != digest(ROOT / 'tests/m3/linux-6.18.59.config')):
        raise ValueError('prepared kernel archive or configuration differs')
    # §AR-m4-routes.linux: Reuse the actual configured command; redirect all generated files.
    saved = (KERNEL / 'fs/.pipe.o.cmd').read_text().splitlines()[0].split(':=', 1)[1].split(';', 1)[0]
    command, args, index = shlex.split(saved), [], 0
    if command[0] != 'gcc':
        raise ValueError('unsupported saved kernel compiler')
    while index < len(command):
        item = command[index]
        if item == '-o':
            index += 2
            continue
        if item not in {'-c', 'fs/pipe.c'} and not item.startswith('-Wp,-MMD,'):
            args.append(item)
        index += 1
    args += ['-E', '-o', str(WORK / 'pipe.i'), 'fs/pipe.c']
    logs['preprocessor'] = run(args, KERNEL)
    frontend = ROOT / '.tools/m4/CompCert/clightgen'
    logs['kernel_frontend'] = run([str(frontend), '-normalize', '-fstruct-passing', '-o',
                                   str(WORK / 'Pipe.v'), str(WORK / 'pipe.i')], WORK, expected=2)
    if '__int128' not in logs['kernel_frontend'] or 'include/uapi/linux/types.h:17' not in logs['kernel_frontend']:
        raise ValueError('kernel frontend failed differently')
    if before != sources() or library != {str(p.relative_to(PORT)): digest(p) for p in sorted(library_sources)}:
        raise ValueError('attempt source changed during replay')
    gcc = Path(shutil.which(command[0])).resolve()
    return dict(schema_version=1, status='reproducible blocked connection attempts',
                full_m4_complete=False, original_obligations_closed=0, fresh_vm_workloads_run=False,
                source_sha256=before, lean_port_revision=REVISION, lean_toolchain=TOOLCHAIN,
                lean_port_sources_sha256=library, kernel=pins['kernel_commit'],
                kernel_input_sha256=kernel_inputs,
                kernel_saved_command=saved,
                preprocess_command=[item.replace(str(ROOT), '{project}') for item in args],
                compiler_sha256=digest(gcc), compiler_version=run([str(gcc), '--version'], ROOT),
                frontend_sha256=digest(frontend), closure_sha256=digest(WORK / 'ported-step.ndjson'),
                preprocessed_sha256=digest(WORK / 'pipe.i'), logs=logs,
                elapsed_seconds=round(time.monotonic() - started, 3))


def check():
    expected = json.loads(RECORD.read_text())
    archived = json.loads(gzip.decompress(RAW.read_bytes()))
    if digest(RAW) != expected.pop('raw_sha256'):
        raise ValueError('route attempt archive differs')
    actual = collect(expected)
    for row in [actual, archived]:
        row.pop('elapsed_seconds')
        row['logs'].pop('port_build')  # Cache-dependent build text; success is checked above.
        if json.dumps(row, sort_keys=True) != json.dumps(expected, sort_keys=True):
            raise ValueError('reviewed route inputs, audit or failed attempts differ')
    print('Early route attempts reproduced: port builds; both strict imports and unchanged kernel translation fail as recorded. M4 remains open.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare', action='store_true')
    parser.add_argument('--collect', action='store_true')
    args = parser.parse_args()
    if args.prepare:
        prepare()
    elif args.collect:
        report = collect()
        (WORK / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print('Ignored connection-attempt report collected; no expectations refreshed.')
    else:
        check()
