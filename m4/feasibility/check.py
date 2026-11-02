#!/usr/bin/env python3
"""Replay a bounded compiler-interface attempt, without applying compiler correctness."""
# SPDX-License-Identifier: Apache-2.0
# §AR-m4-effects.machine: Check the explicit stock/custom semantics boundary and remaining producer.
import argparse
import gzip
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = ROOT / 'm4/feasibility'
WORK = ROOT / '.tools/m4/feasibility'
EVIDENCE = ROOT / 'assurance/m4-compiler-feasibility.json'
RAW = ROOT / 'assurance/m4-compiler-feasibility-output.json.gz'
spec = importlib.util.spec_from_file_location('compiler_interface_parent', ROOT / 'm4/parent/check.py')
parent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent)
STATUS = 'local compiler-interface experiment; Linux producer and composed compiler/Lean connection open'


def collect():
    parent.profile.verify_tools()
    WORK.mkdir(parents=True, exist_ok=True)
    flags = parent.flags() + ['-Q', str(WORK), 'LeanCageFeasibility']
    source = DIRECTORY / 'CompilerBoundary.v'
    names = parent.inventory_module.declarations(source.read_text(), 'LeanCageFeasibility.CompilerBoundary.')
    path = WORK / source.name
    shutil.copyfile(source, path)
    logs = {'compile': parent.profile.run(['rocq', 'c', '-q', *flags, str(path)], cwd=WORK).stdout}
    query = ['From LeanCageFeasibility Require Import CompilerBoundary.', 'Set Printing All.',
             'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
    for i, name in enumerate(names):
        query += [f'Redirect "boundary-type-{i}" Check @{name}.',
                  f'Redirect "boundary-foundations-{i}" Print Assumptions {name}.']
    audit = WORK / 'BoundaryAudit.v'
    audit.write_text('\n'.join(query) + '\n')
    logs['audit'] = parent.profile.run(['rocq', 'c', '-q', *flags, str(audit)], cwd=WORK).stdout
    records = []
    for i, name in enumerate(names):
        statement = (WORK / f'boundary-type-{i}.out').read_text().strip()
        assumptions = (WORK / f'boundary-foundations-{i}.out').read_text().strip()
        axioms, uip = parent.bridge.foundations(assumptions)
        if uip or '...' in statement:
            raise ValueError('unexpected compiler-interface logical model or truncated type')
        records.append(dict(name=name, full_type=statement, transitive_assumptions=assumptions,
                            assumption_names=axioms, definitional_uip=uip))
    logs['kernel'] = parent.profile.run(['rocq', 'check', '-silent', *parent.flags(checker=True),
                                       '-Q', str(WORK), 'LeanCageFeasibility',
                                       'LeanCageFeasibility.CompilerBoundary'], cwd=WORK, timeout=300).stdout
    attempt = WORK / 'ForwardAttempt.v'
    attempt.write_text('''From compcert Require Import Integers AST Values Memory Events Clight.
Require Import Machine.
From LeanCageMain Require Import MainStructure.
From LeanCageParent Require Import ParentMachine.
From LeanCageFeasibility Require Import CompilerBoundary.
Theorem direct_local_to_stock : parent_observation_projection main_ge.
Proof.
 intros cell k m value LOCAL.
 exists E0.
 apply stock_parent_step_exact.
 cbn.
 exact LOCAL.
Qed.
''')
    try:
        parent.profile.run(['rocq', 'c', '-q', *flags, str(attempt)], cwd=WORK)
    except subprocess.CalledProcessError as error:
        if 'while it is expected to have type' not in error.stdout or 'external_functions_sem' not in error.stdout:
            raise ValueError('unexpected forward-connection blocker: ' + error.stdout) from error
        logs['rejected_forward_attempt'] = error.stdout
    else:
        raise ValueError('direct local observation unexpectedly supplied stock external semantics')
    report = dict(schema_version=1, status=STATUS, original_obligations_closed=0,
                  full_m4_complete=False, rocq_declarations=records,
                  source_sha256={str(p.relative_to(ROOT)): parent.digest(p)
                                 for p in DIRECTORY.iterdir() if p.is_file()},
                  compiler_source_sha256=parent.digest(ROOT / '.tools/m4/bridge/CompCert/driver/Compiler.v'),
                  parent_machine_sha256=parent.digest(ROOT / 'm4/parent/ParentMachine.v'),
                  parent_artifact_sha256={name: parent.digest(parent.WORK / 'proofs' / name)
                                          for name in ['ParentMachine.vo', 'ParentRuns.vo']},
                  artifact_sha256={'CompilerBoundary.vo': parent.digest(path.with_suffix('.vo'))},
                  attempted_goal_source=attempt.read_text(), logs=logs,
                  rejected_route='Naive local-to-stock projection requires every abstract signed observation to be producible.',
                  replacement_route='Refine stock executions into the custom model under actual effect safety contracts; compose with the stock compiler simulation.',
                  open_producer='Pinned libc/Linux parent_external_safety, byte/descriptor effects, waits/loss relation and whole compiler/runtime/loader composition.',
                  lean_security_connection='Still open; this Rocq interface supplies no ordinary Lean security theorem.')
    (WORK / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def check():
    actual = collect()
    expected = json.loads(EVIDENCE.read_text())
    archived = json.loads(gzip.decompress(RAW.read_bytes()))
    for record in [expected, archived, actual]:
        if (record['status'] != STATUS or record['full_m4_complete'] is not False
                or type(record['original_obligations_closed']) is not int
                or record['original_obligations_closed'] != 0):
            raise ValueError('compiler feasibility scope differs')
    for key in ['rocq_declarations', 'source_sha256', 'compiler_source_sha256', 'parent_machine_sha256', 'parent_artifact_sha256',
                'artifact_sha256', 'attempted_goal_source', 'rejected_route', 'replacement_route',
                'open_producer', 'lean_security_connection']:
        if expected[key] != actual[key] or archived[key] != actual[key]:
            raise ValueError('compiler feasibility evidence differs: ' + key)
    if expected['proof_output_sha256'] != parent.digest(RAW):
        raise ValueError('compiler feasibility raw receipt differs')
    print('Compiler interface checked; naive projection rejected; actual effect producer and full M4 remain open.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--collect', action='store_true', help='write an ignored interface-attempt report')
    args = parser.parse_args()
    try:
        collect() if args.collect else check()
    except subprocess.CalledProcessError as error:
        print(error.stdout)
        raise
