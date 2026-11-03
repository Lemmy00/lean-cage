#!/usr/bin/env python3
"""Check the composed reporting/compiler argument; unchanged inputs reuse evidence."""
# SPDX-License-Identifier: Apache-2.0
# §AR-compiled-reporting.certificate: Freeze checked types, foundations and compiler output.
import argparse
import gzip
import json
from pathlib import Path
import re
import subprocess

import profile
import source
import allocation
import amendment

ROOT = profile.ROOT
DIRECTORY = Path(__file__).resolve().parent
WORK = profile.WORK
RECORD = ROOT/'assurance/reporting-compiler.json.gz'
MODULES = ['CompilerPlatform','BinaryIteration','ExecutableIteration','OracleAllocation','PrimitiveCalls','StockCalls',
           'VerifiedBackend','CompilerCalls','CompiledReporting','AllocationCandidates','CandidateData',
           'FrontendCertificate','AllocationCertificate','AssemblyCertificate','CompilerCertificate']
AUDITED = ['RuntimeProgram','RuntimeInputs',*MODULES]
INTERFACES = ['PrimitiveCalls.runtime_contract','CompiledReporting.compiled_reporting_contract',
              'RuntimeProgram.program','RuntimeProgram.errno_root','VerifiedBackend.compile',
              'VerifiedBackend.backend_passes','OracleAllocation.transf_function',
              'AllocationCandidates.choose_candidate','CompilerPlatform.win64']
FOUNDATIONS = {
    'Axioms.proof_irr','Eqdep.Eq_rect_eq.eq_rect_eq',
    'ClassicalDedekindReals.sig_not_dec','ClassicalDedekindReals.sig_forall_dec',
    'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep',
    'Events.external_functions_sem','Events.inline_assembly_sem',
    'Events.external_functions_properties','Events.inline_assembly_properties',
}


def generated():
    return {'OracleAllocation':allocation.proof(profile.base.WORK/'CompCert')}


def project_graph():
    paths = [WORK/(name+'.v') for name in MODULES]
    return parsed_graph(paths)


def parsed_graph(paths):
    output = profile.run(['rocq','dep',*source.flags(),*[str(path) for path in paths]],timeout=20)
    result = {}
    for line in output.replace('\\\n',' ').splitlines():
        if ':' not in line:
            continue
        targets,dependencies = line.split(':',1)
        target = next((Path(x) for x in targets.split() if x.endswith('.vo')),None)
        if target is not None:
            values = [Path(x) for x in dependencies.split() if x.endswith('.vo')]
            if not target.is_absolute() or any(not x.is_absolute() for x in values):
                raise ValueError('non-absolute compiler dependency')
            result[target] = values
    return result


def freeze_dependencies():
    _,order,_ = source.plan()
    graph = profile.graph()
    graph.update(parsed_graph([source.WORK/(name+'.v')for name in order]+
                             [profile.connection.WORK/'rebase/main/proofs/Main.v']))
    graph.update(project_graph())
    selected = set()
    def visit(path):
        if path in selected:
            return
        selected.add(path)
        for dep in graph.get(path,[]):
            visit(dep)
    for path in [WORK/'CompilerCertificate.vo',source.WORK/'RuntimeInputs.vo']:
        visit(path)
    paths = selected | {path.with_suffix('.v')for path in selected if path.with_suffix('.v').exists()}
    snapshot = [str(path.relative_to(ROOT))for path in sorted(paths)]
    (WORK/'compiler-dependencies.json').write_text(json.dumps(snapshot,indent=2)+'\n')
    return snapshot


def build():
    profile.build()
    source.build()
    derived = generated()
    for name in MODULES:
        path = WORK/(name+'.v')
        if name in derived:
            desired = derived[name]
        elif name=='CandidateData':
            if not path.exists():
                raise ValueError('generate untrusted candidates with verification/compiler/candidates.py')
            continue
        else:
            desired = (DIRECTORY/path.name).read_text()
        if not path.exists() or path.read_text()!=desired:
            path.write_text(desired)
    dependencies = project_graph()
    for name in MODULES:
        path = WORK/(name+'.v')
        object_file = path.with_suffix('.vo')
        identity = dict(source=profile.sha(path),dependencies={str(x):profile.sha(x)
            for x in dependencies[object_file]})
        stamp = path.with_suffix('.checked-inputs.json')
        if object_file.exists() and stamp.exists() and json.loads(stamp.read_text())==identity:
            continue
        print('Checking reporting/compiler consumer '+name,flush=True)
        log_path = path.with_suffix('.checked.log')
        command = [str(profile.base.WORK/'opam-bin'),'exec','--switch='+profile.base.SWITCH,'--',
                   'rocq','c','-q','-time',*source.flags(),str(path)]
        with log_path.open('w')as log:
            try:
                result = subprocess.run(command,cwd=WORK,env=profile.base.environment(),text=True,
                                         stdout=log,stderr=subprocess.STDOUT,timeout=60)
            except subprocess.TimeoutExpired as error:
                raise ValueError('inspect focused compiler log '+str(log_path))from error
        if result.returncode:
            raise ValueError(log_path.read_text()[-3500:])
        stamp.write_text(json.dumps(identity,sort_keys=True)+'\n')
    freeze_dependencies()
    return dependencies


def inventory(signature,module):
    parser = profile.connection.load(ROOT/'m4/parent/inventory.py','compiler_signature_inventory')
    match = re.fullmatch(r'Module\s+'+re.escape(module)+r'\s*:=\s*Struct\s+(.*)\s+End',signature.strip(),re.S)
    if not match or '...' in signature:
        raise ValueError('unsupported compiler module signature '+module)
    body = match[1]
    if module=='OracleAllocation':
        aliases = 'Module ESF Module ESP Module ESD Module ESF2 Module ESP2 Module ESD2 '
        if not body.startswith(aliases):
            raise ValueError('allocator equation-set aliases differ')
        body = body[len(aliases):]
    result = []
    for field in parser.commands(body):
        if field.startswith('Module '):
            raise ValueError('unexpected compiler module alias '+field[:100])
        field = re.sub(r'^Variant\b','Inductive',field)
        if field.startswith('Record '):
            field = re.sub(r'\s+as\s+'+parser.IDENT+r'$','',field)
        result += parser.checked_declarations('Module '+module+' := Struct '+field+'. End',module)
    if len(result)!=len(set(result)):
        raise ValueError('duplicate compiler declaration '+module)
    return result


def audit():
    identity = proof_identity()
    header = ['From LeanImport Require Import Lean.','Require Import '+' '.join(AUDITED)+'.',
              'Set Printing All.','Set Printing Depth 1000000.','Set Printing Width 1000000.']
    query = header+[f'Redirect "compiler-signature-{i}" Print Module {name}.' for i,name in enumerate(AUDITED)]
    path = WORK/'CompilerAudit.v'
    path.write_text('\n'.join(query)+'\n')
    profile.run(['rocq','c','-q',*source.flags(),str(path)],timeout=30)
    names = []
    for i,name in enumerate(AUDITED):
        names += inventory((WORK/f'compiler-signature-{i}.out').read_text(),name)
    query = header
    for i,name in enumerate(names):
        query += [f'Redirect "compiler-type-{i}" Check @{name}.',
                  f'Redirect "compiler-foundations-{i}" Print Assumptions {name}.']
    path.write_text('\n'.join(query)+'\n')
    profile.run(['rocq','c','-q',*source.flags(),str(path)],timeout=60)
    rows = []
    for i,name in enumerate(names):
        statement = (WORK/f'compiler-type-{i}.out').read_text().strip()
        foundations = (WORK/f'compiler-foundations-{i}.out').read_text().strip()
        if '...' in statement or '⋯' in statement:
            raise ValueError('truncated compiler statement '+name)
        axioms,uip = foundation_names(foundations)
        rows.append(dict(name=name,full_type=statement,transitive_foundations=foundations,
                         assumption_names=axioms,definitional_uip=uip))
    output = profile.run(['rocq','check','-silent',*source.flags(checker=True),'CompilerCertificate',
                          'RuntimeInputs'],timeout=60)
    (WORK/'compiler-kernel-check.log').write_text(output)
    (WORK/'compiler-audit.json').write_text(json.dumps(rows,indent=2)+'\n')
    if proof_identity()!=identity:
        raise ValueError('compiler proof inputs changed during the audit')
    (WORK/'compiler-audit-reuse.json').write_text(json.dumps(dict(inputs=identity,
        result_sha256=profile.sha(WORK/'compiler-audit.json'),
        kernel_log_sha256=profile.sha(WORK/'compiler-kernel-check.log')),sort_keys=True)+'\n')
    return rows


def foundation_names(output):
    if output=='Closed under the global context':
        return [],[]
    if not output.startswith('Axioms:'):
        raise ValueError('unrecognized compiler foundation report')
    axioms,uip = [],[]
    for line in output.splitlines()[1:]:
        if not line or line[0].isspace():
            continue
        match = re.fullmatch(r'(\S+) relies on definitional UIP\.',line)
        if match:
            uip.append(match[1])
        else:
            axioms.append(line.split(':',1)[0].strip())
    allowed_uip = {'eq_inst1','eq','NormalizedImport.True',
                   'NormalizedImport.HEq_inst1','NormalizedImport.HEq'}
    if set(axioms)-FOUNDATIONS or set(uip)-allowed_uip:
        raise ValueError('unreviewed compiler foundation '+output)
    return sorted(axioms),sorted(uip)


def proof_identity():
    paths = [ROOT/name for name in json.loads((WORK/'compiler-dependencies.json').read_text())]
    paths += [profile.base.WORK/'opam/strict-9.3/bin/rocq',
              profile.base.WORK/'opam/strict-9.3/bin/rocqchk',
              profile.base.WORK/'opam/strict-9.3/lib/rocq-runtime/rocqworker',
              profile.base.WORK/'rocq-lean-import/src/lean_import.cmxs']
    files = {str(path.relative_to(ROOT))if path.is_relative_to(ROOT)else str(path):profile.sha(path)
             for path in sorted(set(paths))}
    return dict(files=files,compile_flags=source.flags(),kernel_flags=source.flags(checker=True))


def audited_result():
    receipt,data = WORK/'compiler-audit-reuse.json',WORK/'compiler-audit.json'
    if receipt.exists() and data.exists():
        saved = json.loads(receipt.read_text())
        if saved==dict(inputs=proof_identity(),result_sha256=profile.sha(data),
                       kernel_log_sha256=profile.sha(WORK/'compiler-kernel-check.log')):
            rows = json.loads(data.read_text())
            for row in rows:
                axioms,uip = foundation_names(row['transitive_foundations'])
                if row['assumption_names']!=axioms or row['definitional_uip']!=uip:
                    raise ValueError('compiler foundation inventory differs')
            return rows
    return audit()


def negative_controls():
    identity = dict(proofs=proof_identity(),checker_sha256=profile.sha(Path(__file__)))
    receipt = WORK/'compiler-negatives.json'
    if receipt.exists():
        saved = json.loads(receipt.read_text())
        if saved['inputs']==identity and all(profile.sha(WORK/(name+'.log'))==value
                for name,value in saved['logs'].items()):
            return saved['logs']
    runtime = (DIRECTORY/'RuntimeProgram.v').read_text()
    runtime = profile.replace_once(runtime,
        'prog_public:=runtime_errno::prog_public Main.prog;',
        'prog_public:=prog_public Main.prog;')
    candidates = (WORK/'CandidateData.v').read_text()
    candidates,count = re.subn(r'\(Op\.Aglobal \d+%positive',
                              '(Op.Aglobal 1%positive',candidates,count=1)
    if count!=1:
        raise ValueError('allocation mutation site differs')
    (WORK/'WrongCandidateData.v').write_text(candidates)
    wrong = '''From compcert Require Import Errors.
Require Import OracleAllocation AllocationCandidates WrongCandidateData FrontendCertificate.
Local Transparent ExecutableIteration.iterate CompilerPlatform.win64.
Goal (match OracleAllocation.transf_program (allocation_candidates WrongCandidateData.candidates)
 FrontendCertificate.rtl with OK _=>true|Error _=>false end)=true.
Proof. vm_compute;reflexivity. Qed.
'''
    logs = {}
    for name,text in [('WrongErrnoRoot',runtime),('WrongAllocation',wrong)]:
        if name=='WrongAllocation':
            profile.run(['rocq','c','-q',*source.flags(),str(WORK/'WrongCandidateData.v')],timeout=10)
        path = WORK/(name+'.v')
        path.write_text(text)
        try:
            profile.run(['rocq','c','-q',*source.flags(),str(path)],timeout=15)
        except RuntimeError as error:
            output = str(error)
            if 'Unable to unify "true" with "false"' not in output:
                raise ValueError('negative rejected for an unintended reason '+name+'\n'+output)from error
            (WORK/(name+'.log')).write_text(output)
            logs[name] = profile.sha(WORK/(name+'.log'))
        else:
            raise ValueError('kernel accepted invalid reporting/compiler evidence '+name)
    if dict(proofs=proof_identity(),checker_sha256=profile.sha(Path(__file__)))!=identity:
        raise ValueError('compiler proof inputs changed during negative controls')
    receipt.write_text(json.dumps(dict(inputs=identity,logs=logs),sort_keys=True)+'\n')
    return logs


def interface_definitions():
    identity = dict(proofs=proof_identity(),interfaces=INTERFACES)
    receipt,data = WORK/'compiler-interface-reuse.json',WORK/'compiler-interfaces.json'
    if receipt.exists() and data.exists() and json.loads(receipt.read_text())==dict(
            inputs=identity,result_sha256=profile.sha(data)):
        return json.loads(data.read_text())
    query = ['From LeanImport Require Import Lean.','Require Import CompilerCertificate.',
             'Set Printing All.','Set Printing Depth 1000000.','Set Printing Width 1000000.']
    query += [f'Redirect "compiler-interface-{i}" Print {name}.' for i,name in enumerate(INTERFACES)]
    path = WORK/'CompilerInterfaces.v'
    path.write_text('\n'.join(query)+'\n')
    profile.run(['rocq','c','-q',*source.flags(),str(path)],timeout=10)
    definitions = {name:(WORK/f'compiler-interface-{i}.out').read_text().strip()
                   for i,name in enumerate(INTERFACES)}
    if any('...' in text or '⋯' in text for text in definitions.values()):
        raise ValueError('truncated compiler interface definition')
    data.write_text(json.dumps(definitions,indent=2)+'\n')
    receipt.write_text(json.dumps(dict(inputs=identity,result_sha256=profile.sha(data)),sort_keys=True)+'\n')
    return definitions


def bindings():
    amendment.verify()
    paths = [p for p in DIRECTORY.iterdir() if p.is_file()]
    paths += [ROOT/'native/leancage_m3.c',ROOT/'assurance/reporting-connection.json.gz',
              ROOT/'m4/bridge/toolchain-lock.json',ROOT/'m4/toolchain-lock.json',
              ROOT/'assurance/reporting-compiler-before.json.gz',
              ROOT/'docs/architecture/AR-compiled-reporting.md',
              ROOT/'docs/decisions/architectural/DA-compiled-reporting.md',
              ROOT/'scripts/check_reporting_compiler.sh',WORK/'compiler-dependencies.json']
    paths += [ROOT/name for name in proof_identity()['files']]
    accepted = json.loads(gzip.decompress(profile.connection.RECORD.read_bytes()))
    paths += [ROOT/name for name in accepted['cache_sha256']]
    paths += [ROOT/name for name in accepted['host_inputs_sha256']]
    return {str(path.relative_to(ROOT))if path.is_relative_to(ROOT)else str(path):profile.sha(path)
            for path in sorted(set(paths))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build',action='store_true')
    parser.add_argument('--audit',action='store_true')
    parser.add_argument('--collect',action='store_true')
    args = parser.parse_args()
    if args.build:
        build()
    if args.audit:
        audited_result()
    if args.collect:
        result = dict(schema=1,status='conditional-compiler-model',inputs_sha256=bindings(),
            claim='Concrete compilation carries owned descriptor-1 reporting calls to the existing ordinary Lean decoder proof',
            spec_ids=['FS-workspace.results','FS-assurance.compiled','AR-compiled-reporting.connection'],
            producer='CompilerCertificate.current_compilation',
            consumer='CompilerCertificate.current_assembly_reporting',
            decoder='SourceConnection.source_sender_decoder -> LeanCage.Reporting.normalized_publication',
            compiler_passes=['Cshmgen','Cminorgen','Selection','RTLgen','OracleAllocation','Linearize','Stacking','Asmgen'],
            source_program='RuntimeProgram.program (unchanged Main helper bodies plus a public logical errno object)',
            target_program='AssemblyCertificate.assembly',
            abi='ELF x86-64; CompilerPlatform.win64=false',
            declarations=audited_result(),negative_controls=negative_controls(),
            interface_definitions=interface_definitions(),
            kernel_check=json.loads((WORK/'compiler-audit-reuse.json').read_text()),
            original_obligations_closed=[],
            remaining=['physical libc/TLS and Linux effect producers','caller/ABI state-relation producer',
                       'C frontend, assembly printer, assembler, runtime and retained GCC executable',
                       'asynchronous partial-call loss and controller/export composition'])
        (WORK/'compiler-proposed.json').write_text(json.dumps(result,indent=2)+'\n')
        print('Collected an unreviewed compiler record; the reviewed record was not changed.')
        return
    if not RECORD.exists():
        if args.build or args.audit:
            return
        raise ValueError('no reviewed reporting/compiler record')
    expected = json.loads(gzip.decompress(RECORD.read_bytes()))
    if expected['schema']!=1 or expected['status']!='conditional-compiler-model' or expected['original_obligations_closed']:
        raise ValueError('compiler record exceeds the checked conditional model boundary')
    if bindings()!=expected['inputs_sha256']:
        raise ValueError('reporting/compiler evidence inputs changed')
    if audited_result()!=expected['declarations']:
        raise ValueError('compiler type/foundation audit differs')
    if negative_controls()!=expected['negative_controls']:
        raise ValueError('compiler negative controls differ')
    if json.loads((WORK/'compiler-audit-reuse.json').read_text())!=expected['kernel_check']:
        raise ValueError('compiler kernel-check receipt differs')
    if interface_definitions()!=expected['interface_definitions']:
        raise ValueError('compiler interface definitions differ')
    print('Checked reporting/compiler model; matching proof artifacts reused.')


if __name__=='__main__':
    main()
