#!/usr/bin/env python3
"""Check the current helper's reporting call against the ordinary Lean decoder proof."""
# SPDX-License-Identifier: Apache-2.0
# §AR-reporting.proof: Reuse matching kernels and compile only changed proof consumers.
import argparse
import base64
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path(__file__).resolve().parent
WORK = ROOT / '.tools/reporting'
PROOFS = WORK / 'live'
MODULES = ['ReportingImport', 'CallProjection', 'SourceConnection', 'InputWitnesses', 'CurrentSource']
RECORD = ROOT / 'assurance/reporting-connection.json.gz'


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


profile = load(ROOT / 'm4/bridge/profile.py', 'reporting_connection_profile')


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def flags(checker=False):
    original = profile.flags(checker=checker)
    result, index = [], 0
    while index < len(original):
        if original[index] == '-Q' and original[index+1] in [str(profile.WORK/'source'), str(profile.WORK/'proofs')]:
            index += 3
        else:
            result.append(original[index])
            index += 1
    return result + ['-Q', str(PROOFS), '', '-Q', str(WORK/'rebase/main/proofs'), 'LeanCageMain']


def lean(command, timeout=30):
    paths = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT/'m3', text=True).strip()
    paths = str(WORK/'modules') + ':' + str(profile.WORK/'modules') + ':' + paths
    return subprocess.run(['lake', 'env', 'env', 'LEAN_PATH='+paths, *command], cwd=ROOT/'m3',
                          capture_output=True, text=True, check=True, timeout=timeout).stdout


def export_records(path):
    names, result = {0: ''}, []
    for line in path.read_text().splitlines():
        row = json.loads(line)
        if 'in' in row:
            value = row.get('str') or row.get('num')
            names[row['in']] = (names[value['pre']] + '.' if value['pre'] else '') + str(value.get('str', value.get('i')))
        current = []
        for kind in ['def', 'thm', 'opaque', 'axiom']:
            if kind in row:
                current = [names[row[kind]['name']]]
                if kind == 'axiom':
                    raise ValueError('publication proof exports an axiom: '+current[0])
        if 'inductive' in row:
            current = [names[item['name']] for kind in ['types', 'ctors', 'recs'] for item in row['inductive'][kind]]
        result.append((line, current))
    return result


def export_fingerprints(path):
    """Compare actual declarations independently of exporter-local table indices."""
    names, levels, expressions, declarations = {0: ''}, {0: 'zero'}, {}, {}
    def hashed(value):
        return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    def declaration(value):
        result = {}
        for key, data in value.items():
            if key in ['name', 'induct', 'ctor']:
                result[key] = names[data]
            elif key in ['all', 'levelParams', 'ctors']:
                result[key] = [names[x] for x in data]
            elif key in ['type', 'value', 'rhs']:
                result[key] = expressions[data]
            elif key == 'rules':
                result[key] = [declaration(x) for x in data]
            else:
                result[key] = data
        return result
    for line in path.read_text().splitlines():
        row = json.loads(line)
        if 'in' in row:
            data = row.get('str') or row.get('num')
            names[row['in']] = (names[data['pre']]+'.' if data['pre'] else '')+str(data.get('str', data.get('i')))
        if 'il' in row:
            body = {key: value for key, value in row.items() if key != 'il'}
            key, data = next(iter(body.items()))
            if key == 'param':
                data = names[data]
            elif key == 'succ':
                data = levels[data]
            elif key in ['max', 'imax']:
                if isinstance(data, dict):
                    data = {k: levels[v] for k, v in data.items()}
                else:
                    data = [levels[v] for v in data]
            else:
                raise ValueError('unreviewed universe expression: '+key)
            levels[row['il']] = hashed([key, data])
        if 'ie' in row:
            body = {key: value for key, value in row.items() if key != 'ie'}
            key, data = next(iter(body.items()))
            if key == 'const':
                data = [names[data['name']], [levels[x] for x in data['us']]]
            elif key == 'sort':
                data = levels[data]
            elif key in ['app', 'forallE', 'lam', 'letE', 'proj']:
                value = {}
                for field, item in data.items():
                    if field in ['name', 'binderInfo'] and key in ['forallE', 'lam', 'letE']:
                        continue  # Binder names and implicitness are elaborator annotations; indices bind terms.
                    if field in ['fn', 'arg', 'type', 'value', 'body', 'struct']:
                        value[field] = expressions[item]
                    elif field in ['name', 'typeName']:
                        value[field] = names[item]
                    else:
                        value[field] = item
                data = value
            elif key not in ['bvar', 'natVal', 'strVal']:
                raise ValueError('unreviewed exported expression: '+key)
            expressions[row['ie']] = hashed([key, data])
        for kind in ['def', 'thm', 'opaque', 'axiom']:
            if kind in row:
                data = row[kind]
                declarations[names[data['name']]] = hashed([kind, declaration(data)])
        if 'inductive' in row:
            group = row['inductive']
            fingerprint = hashed({kind: [declaration(x) for x in group[kind]] for kind in ['types', 'ctors', 'recs']})
            for kind in ['types', 'ctors', 'recs']:
                for data in group[kind]:
                    declarations[names[data['name']]] = fingerprint
    return declarations


def build_lean():
    (WORK/'modules').mkdir(exist_ok=True)
    src = DIRECTORY/'Reporting.lean'
    obj = WORK/'modules/Reporting.olean'
    stamp = WORK/'modules/Reporting.stamp'
    identity = digest(src)
    if not obj.exists() or not stamp.exists() or stamp.read_text() != identity:
        log = lean(['lean', '--root='+str(DIRECTORY), '-o', str(obj), str(src)])
        (WORK/'lean-publication.log').write_text(log)
        stamp.write_text(identity)
        print('Checked ordinary Lean reporting theorem.', flush=True)
    exported = WORK/'publication.ndjson'
    export_stamp = WORK/'publication.stamp'
    if not exported.exists() or not export_stamp.exists() or export_stamp.read_text() != digest(obj):
        exported.write_text(lean([str(profile.WORK/'lean4export/.lake/build/bin/lean4export'),
                                 'Reporting', '--', 'LeanCage.Reporting.normalized_publication']))
        export_stamp.write_text(digest(obj))
    base = profile.WORK/'normalized-decoder.ndjson'
    previous = export_fingerprints(base)
    current = export_fingerprints(exported)
    for name in previous.keys() & current.keys():
        if previous[name] != current[name]:
            raise ValueError('shared exported declaration changed: '+name)
    old = {name for _, names in export_records(base) for name in names}
    records = export_records(exported)
    extension = [line for line, names in records if not names or not set(names) <= old]
    (WORK/'publication-extension.ndjson').write_text('\n'.join(extension)+'\n')
    shutil.copy2(base, WORK/'normalized-decoder.ndjson')


def origins():
    result = {'Codec': ROOT/'m4/Codec.v'}
    for directory in [ROOT/'m4/connection', ROOT/'m4/bridge']:
        for path in directory.rglob('*.v'):
            if path.stem in result:
                raise ValueError('ambiguous source proof module: '+path.stem)
            result[path.stem] = path
    return result


def imports(text):
    text = re.sub(r'\(\*.*?\*\)', '', text, flags=re.S)
    result = []
    for match in re.finditer(r'(?:(?:From\s+(\w+)\s+)?Require\s+(?:(?:Import|Export)\s+)?([\w.\s]+?)\.(?!\w))', text):
        if match[1] is None:
            result.extend(match[2].split())
    return result


def adapted(name, raw):
    if name == 'ResultSource':
        helpers = (DIRECTORY/'Composite.v.inc').read_text()
        helpers = helpers[helpers.index('Definition checked_composite'):]
        raw = raw.replace('Ltac result_location', helpers+'\nLtac result_location')
    if name in ['ResultSource', 'DecoderSource', 'SenderAccess', 'FinishSource']:
        prefix = '' if name == 'ResultSource' else 'ResultSource.'
        raw = re.sub(r'eapply struct_location_value;\s*\[(\w+_expression)\|reflexivity\|reflexivity\|([^\]]+)\]',
                     lambda m: 'eapply struct_location_value with (co:='+prefix+'reporting_composite);['+m[1]+
                     '|reflexivity|exact '+prefix+'reporting_composite_lookup|rewrite '+prefix+'reporting_composite_members;'+m[2]+']', raw)
    if name == 'DecoderFields':
        raw = raw.replace('with (delta := scalar_offset cell)',
                          'with (co:=ResultSource.reporting_composite) (delta := scalar_offset cell)')
        raw = raw.replace('    + reflexivity.\n    + reflexivity.\n    + exact FIELD.',
                          '    + reflexivity.\n    + exact ResultSource.reporting_composite_lookup.\n'
                          '    + rewrite ResultSource.reporting_composite_members;exact FIELD.')
    return raw


def source_plan():
    files = origins()
    texts = {name: adapted(name, path.read_text()) for name, path in files.items()}
    current = (WORK/'rebase/main/proofs/Main.v').read_text()
    original = gzip.decompress((ROOT/'assurance/m4-slice.v.gz').read_bytes()).decode()
    extra = []
    for pattern in [r'^Definition (_m4_collect_failure) :[^\n]*\n', r'^Definition (f_m4_collect_failure) :=.*?^\|\}\.']:
        match = re.search(pattern, original, re.M|re.S)
        if not match:
            raise ValueError('missing preserved proof-only receiver declaration')
        extra.append(match[0])
    header = current[:current.index('Module Info.')]
    selected = re.findall(r'^Definition (f_\w+) :=', original, re.M)
    aliases = ['Definition '+name+' := Main.'+name+'.' for name in selected if name != 'f_m4_collect_failure']
    texts['Slice'] = (header+'From LeanCageMain Require Export Main.\n'+
                      'Definition prog := Main.prog.\n'+'\n'.join(aliases)+'\n'+
                      '\n'.join(extra)+'\n')
    texts.update({name: (DIRECTORY/(name+'.v')).read_text() for name in MODULES})
    order, seen, dependencies = [], set(), {}
    def visit(name):
        if name in seen:
            return
        if name not in texts:
            raise ValueError('unlisted project proof dependency: '+name)
        seen.add(name)
        deps = imports(texts[name])
        for item in deps:
            visit(item)
        dependencies[name] = deps
        order.append(name)
    for name in MODULES:
        visit(name)
    return texts, order, dependencies, files


def build_sources():
    PROOFS.mkdir(exist_ok=True)
    if not (WORK/'rebase/main/proofs/Main.vo').exists():
        subprocess.run([sys.executable, str(DIRECTORY/'check.py')], cwd=ROOT, check=True)
    texts, order, dependencies, files = source_plan()
    independent, changed = {}, set()
    for name in order:
        independent[name] = name != 'Slice' and name not in MODULES and all(independent[x] for x in dependencies[name])
        path = PROOFS/(name+'.v')
        previous = path.read_text() if path.exists() else None
        desired = texts[name]
        artifact, stamp = path.with_suffix('.vo'), PROOFS/(name+'.stamp')
        main_stamp = PROOFS/'Main.external.stamp'
        main_identity = digest(WORK/'rebase/main/proofs/Main.vo')
        cached = artifact.exists() and stamp.exists() and previous is not None and stamp.read_text() == hashlib.sha256(previous.encode()).hexdigest()
        if name == 'Slice' and (not main_stamp.exists() or main_stamp.read_text() != main_identity):
            cached = False
        if previous != desired:
            path.write_text(desired)
        if independent[name]:
            evidence = json.loads((ROOT/'assurance/m4-bridge-evidence.json').read_text())['artifact_sha256']
            for folder in ['source', 'proofs']:
                original = profile.WORK/folder/(name+'.vo')
                original_source = original.with_suffix('.v')
                key = folder+'/'+name+'.vo'
                if (original.exists() and original_source.exists() and original_source.read_text() == desired
                        and key in evidence and digest(original) == evidence[key]):
                    if not artifact.exists() or digest(artifact) != digest(original):
                        shutil.copy2(original, artifact)
                    stamp.write_text(digest(path))
                    break
            else:
                original = None
            if original is not None:
                continue
        # Existing stamps come from the checked focused replay of these exact
        # sources. Relevant changes invalidate only that module and its clients.
        if cached and previous == desired and not any(x in changed for x in dependencies[name]):
            continue
        changed.add(name)
        started = time.monotonic()
        try:
            log = profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=PROOFS, timeout=90).stdout
        except subprocess.CalledProcessError as error:
            (PROOFS/(name+'.check.log')).write_text(error.stdout)
            raise
        except subprocess.TimeoutExpired as error:
            output = error.stdout.decode() if isinstance(error.stdout, bytes) else error.stdout
            (PROOFS/(name+'.check.log')).write_text(output or '')
            raise ValueError('source proof '+name+' exceeded its check budget; inspect its focused log') from error
        (PROOFS/(name+'.check.log')).write_text(log)
        stamp.write_text(digest(path))
        if name == 'Slice':
            main_stamp.write_text(main_identity)
        print('Checked '+name+' ('+str(round(time.monotonic()-started, 2))+'s).', flush=True)
    (WORK/'connection-dependencies.json').write_text(json.dumps({'order': order, 'dependencies': dependencies}, indent=2)+'\n')
    return order


def compiled_inventory(signature, module):
    inventory = load(ROOT/'m4/parent/inventory.py', 'reporting_checked_inventory')
    header = re.fullmatch(r'Module\s+'+re.escape(module)+r'\s*:=\s*Struct\s+(.*)\s+End', signature.strip(), re.S)
    if not header or '...' in signature:
        raise ValueError('unsupported checked reporting module signature')
    result = []
    for field in inventory.commands(header[1]):
        field = re.sub(r'^Variant\b', 'Inductive', field)
        if field.startswith('Record '):
            field = re.sub(r'\s+as\s+'+inventory.IDENT+r'$', '', field)
        result += inventory.checked_declarations('Module '+module+' := Struct '+field+'. End', module)
    if len(result) != len(set(result)):
        raise ValueError('duplicate compiled reporting declaration')
    return result


def foundations(output):
    if output.strip() == 'Closed under the global context':
        return [], []
    if not output.startswith('Axioms:'):
        raise ValueError('unrecognized assumption report: '+output)
    axioms, uip = [], []
    for line in output.splitlines()[1:]:
        if not line.strip() or line[0].isspace():
            continue
        match = re.fullmatch(r'(\S+) relies on definitional UIP\.', line)
        if match:
            uip.append(match[1])
        else:
            axioms.append(line.split(':', 1)[0].strip())
    baseline = json.loads((ROOT/'assurance/m4-bridge-claims.json').read_text())['rocq_declarations']
    allowed = {name for row in baseline for name in row['assumption_names']}
    if set(axioms)-allowed or any(name.rsplit('.', 1)[-1] not in ['eq', 'eq_inst1', 'True', 'HEq', 'HEq_inst1'] for name in uip):
        raise ValueError('unreviewed reporting assumption: '+output)
    return sorted(axioms), sorted(uip)


def audit():
    query = ['From LeanImport Require Import Lean.', 'Require Import '+' '.join(MODULES)+'.',
             'Set Printing All.', 'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
    for index, name in enumerate(MODULES):
        query.append('Redirect "reporting-signature-'+str(index)+'" Print Module '+name+'.')
    path = PROOFS/'ReportingEnvironment.v'
    path.write_text('\n'.join(query)+'\n')
    profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=PROOFS, timeout=30)
    names = []
    for index, module in enumerate(MODULES):
        names += compiled_inventory((PROOFS/('reporting-signature-'+str(index)+'.out')).read_text(), module)
    query = query[:5]
    for index, name in enumerate(names):
        query += ['Redirect "reporting-type-'+str(index)+'" Check @'+name+'.',
                  'Redirect "reporting-axioms-'+str(index)+'" Print Assumptions '+name+'.']
    path = PROOFS/'ReportingAudit.v'
    path.write_text('\n'.join(query)+'\n')
    profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=PROOFS, timeout=60)
    records = []
    for index, name in enumerate(names):
        full_type = (PROOFS/('reporting-type-'+str(index)+'.out')).read_text().strip()
        assumptions = (PROOFS/('reporting-axioms-'+str(index)+'.out')).read_text().strip()
        axioms, uip = foundations(assumptions)
        if '...' in full_type or '⋯' in full_type:
            raise ValueError('truncated reporting proposition')
        records.append(dict(name=name, full_type=full_type, transitive_assumptions=assumptions,
                            assumption_names=axioms, definitional_uip=uip))
    query = 'import Reporting\n'+(ROOT/'scripts/m3_axiom_query.lean').read_text()+'\n#audit_module Reporting\n'
    path = WORK/'ReportingAudit.lean'
    path.write_text(query)
    output = lean(['lean', str(path)], timeout=30)
    (WORK/'ordinary-lean-audit.log').write_text(output)
    rows = [json.loads(line.split('LEANCAGE_AUDIT ', 1)[1]) for line in output.splitlines() if 'LEANCAGE_AUDIT ' in line]
    inventory = [row['declarations'] for row in rows if 'declarations' in row]
    lean_records = sorted([row for row in rows if 'name' in row], key=lambda row: row['name'])
    if len(inventory) != 1 or sorted(inventory[0]) != [row['name'] for row in lean_records]:
        raise ValueError('incomplete ordinary Lean theorem inventory')
    for row in lean_records:
        if not row['is_theorem'] or set(row['axioms'])-{'propext', 'Classical.choice', 'Quot.sound'}:
            raise ValueError('unreviewed ordinary Lean foundation')
    log = profile.run(['rocq', 'check', '-silent', *flags(checker=True), *MODULES], cwd=PROOFS, timeout=90).stdout
    (WORK/'connection-kernel-check.log').write_text(log)
    return dict(rocq_declarations=records, lean_declarations=lean_records)


def proof_identity():
    _, order, _, _ = source_plan()
    paths = [PROOFS/(name+'.vo') for name in order]
    paths += [WORK/'modules/Reporting.olean', WORK/'rebase/main/proofs/Main.vo',
              ROOT/'scripts/m3_axiom_query.lean', ROOT/'assurance/m4-bridge-claims.json',
              profile.WORK/'rocq-lean-import/src/Lean.vo',
              profile.WORK/'rocq-lean-import/src/lean_import.cmxs', profile.WORK/'opam/strict-9.3/bin/rocq']
    return {str(path.relative_to(ROOT)): digest(path) for path in paths}


def audited_result():
    identity = proof_identity()
    receipt = WORK/'audit-reuse.json'
    data = WORK/'connection-audit.json'
    if receipt.exists() and data.exists():
        saved = json.loads(receipt.read_text())
        if saved == dict(inputs=identity, result_sha256=digest(data)):
            return json.loads(data.read_text())
    result = audit()
    data.write_text(json.dumps(result, indent=2)+'\n')
    receipt.write_text(json.dumps(dict(inputs=identity, result_sha256=digest(data)), indent=2)+'\n')
    return result


def negative_controls():
    mutations = {
        'WrongFields': ('SourceConnection',
            '(imported_int32 (fr_entry r)) (imported_int32 (fr_clean r))',
            '(imported_int32 (fr_clean r)) (imported_int32 (fr_entry r))',
            ['WrongFields.v\", line 26,', 'Error: Not convertible.']),
        'WrongLoss': ('CallProjection',
            '| dead _ => LeanCage_Reporting_Status_lost',
            '| dead _ => LeanCage_Reporting_Status_published',
            ['LeanCage_Reporting_Status_lost', 'source_status (dead memory)', 'Unable to unify']),
    }
    cache_key = dict(mutations=mutations, proof_inputs=proof_identity(),
                     sources={module: digest(DIRECTORY/(module+'.v')) for module, *_ in mutations.values()})
    cache_key = json.loads(json.dumps(cache_key))
    receipt = WORK/'negative-reuse.json'
    if receipt.exists():
        saved = json.loads(receipt.read_text())
        if saved['inputs'] == cache_key and all((WORK/(name+'.log')).exists() and
                digest(WORK/(name+'.log')) == value for name, value in saved['results'].items()):
            return saved['results']
    logs = {}
    for name, (module, before, after, messages) in mutations.items():
        source = (DIRECTORY/(module+'.v')).read_text()
        if source.count(before) != 1:
            raise ValueError('negative-control mutation site changed')
        path = PROOFS/(name+'.v')
        path.write_text(source.replace(before, after))
        try:
            profile.run(['rocq', 'c', '-q', *flags(), str(path)], cwd=PROOFS, timeout=15)
        except subprocess.CalledProcessError as error:
            if not all(message in error.stdout for message in messages):
                raise ValueError('negative control failed for an unintended reason: '+name+'\n'+error.stdout)
            logs[name] = error.stdout
            (WORK/(name+'.log')).write_text(error.stdout)
        else:
            raise ValueError('invalid source/interface conversion was accepted: '+name)
    results = {name: hashlib.sha256(output.encode()).hexdigest() for name, output in logs.items()}
    receipt.write_text(json.dumps(dict(inputs=cache_key, results=results), indent=2)+'\n')
    return results


def bindings():
    texts, order, dependencies, files = source_plan()
    paths = [path for path in DIRECTORY.iterdir() if path.is_file()]
    paths += [ROOT/'docs/architecture/AR-reporting.md', ROOT/'docs/decisions/architectural/DA-reporting-connection.md',
              ROOT/'scripts/check_reporting_connection.sh', ROOT/'scripts/m3_axiom_query.lean',
              ROOT/'assurance/reporting-source.json.gz', ROOT/'assurance/reporting-connection-before.json.gz',
              ROOT/'assurance/m4-bridge-claims.json',
              ROOT/'assurance/m4-bridge-evidence.json']
    paths += [ROOT/'verification/compiler/amendment.py',
              ROOT/'assurance/reporting-compiler-before.json.gz']
    paths += [files[name] for name in order if name in files]
    sources = {str(path.relative_to(ROOT)): digest(path) for path in sorted(set(paths))}
    prior = json.loads(gzip.decompress((ROOT/'assurance/reporting-source.json.gz').read_bytes()))
    # Carry forward the source/ABI association and live Lean source identities.
    # Other milestones' navigation and planning documents are not proof inputs here.
    for name, value in prior['inputs_sha256'].items():
        path = Path(name)
        if (path.suffix in ['.c', '.h', '.lean'] or path.name in ['lean-toolchain', 'lake-manifest.json']
                or name in ['m4/toolchain-lock.json', 'm4/bridge/toolchain-lock.json',
                            'm4/main/frontend.py', 'm4/extract.py']):
            sources[name] = value
    sources['docs/functional-spec/FS-workspace.md'] = digest(ROOT/'docs/functional-spec/FS-workspace.md')
    cache = {str((PROOFS/(name+suffix)).relative_to(ROOT)): digest(PROOFS/(name+suffix))
             for name in order for suffix in ['.v', '.vo']}
    for name in ['modules/Reporting.olean', 'publication.ndjson', 'publication-extension.ndjson']:
        path = WORK/name
        cache[str(path.relative_to(ROOT))] = digest(path)
    for name in ['modules/Public.olean', 'modules/Normalized.olean', 'normalized-decoder.ndjson',
                 'rocq-lean-import/src/Lean.vo', 'rocq-lean-import/src/lean_import.cmxs',
                 'lean4export/.lake/build/bin/lean4export', 'opam/strict-9.3/bin/rocq']:
        path = profile.WORK/name
        cache[str(path.relative_to(ROOT))] = digest(path)
    cache.update(prior['dependency_sha256'])
    for name in ['Main.v', 'Main.vo']:
        path = WORK/'rebase/main/proofs'/name
        cache[str(path.relative_to(ROOT))] = digest(path)
    return dict(source_sha256=sources, cache_sha256=cache, host_inputs_sha256=prior['host_inputs_sha256'],
                source_module_order=order, source_module_dependencies=dependencies)


def verify_metadata_amendment():
    path = ROOT/'assurance/reporting-connection-before.json.gz'
    before = json.loads(gzip.decompress(path.read_bytes()))
    allowed = ['scripts/check_reporting.sh', 'verification/reporting/README.md']
    record = 'assurance/reporting-source.json.gz'
    if set(before) != set(allowed+[record]):
        raise ValueError('reporting metadata amendment scope differs')
    old = json.loads(gzip.decompress(base64.b64decode(before[record])))
    for name in allowed:
        previous = hashlib.sha256(base64.b64decode(before[name])).hexdigest()
        if old['inputs_sha256'][name] != previous:
            raise ValueError('reporting metadata preimage differs')
        old['inputs_sha256'][name] = digest(ROOT/name)
    old = load(ROOT/'verification/compiler/amendment.py',
               'reporting_compiler_gate_amendment').adjust_source(old)
    if old != json.loads(gzip.decompress((ROOT/record).read_bytes())):
        raise ValueError('reporting amendment changes more than the gate and its documentation fingerprints')


def collect():
    verify_metadata_amendment()
    evidence = dict(schema_version=1,
        claim='Current helper reporting call refines the ordinary Lean decoder through a checked call interface',
        spec_ids=['FS-workspace.results', 'FS-assurance.native', 'AR-reporting.interface', 'AR-reporting.proof'],
        full_m4_complete=False, original_obligations_closed=[],
        implementation='native/leancage_m3.c:send_frame, actual complete Main.prog',
        source_producer=['SenderProgram.sender_all_prefixes', 'SenderProgram.sender_all_returns',
                         'CallProjection.source_call_interface', 'SourceConnection.source_frame_view'],
        ordinary_consumer='LeanCage.Reporting.live_publication',
        imported_proof='ReportingImport.LeanCage_Reporting_normalized_publication',
        current_source_result='CurrentSource.current_sender_decodes',
        source_witnesses=['CurrentSource.current_sender_nonvacuous', 'CurrentSource.current_sender_failure',
                          'CurrentSource.current_sender_partial_loss'],
        interface='Exact emitted byte prefix, remaining suffix, raw header/tags/fields and running/published/failed/lost status',
        logical_foundations='Full per-declaration assumptions and SProp definitional UIP appear below',
        premises='Owned source result/digest, selector/TLS storage, byte-aware library effects and a retained source execution',
        source_scope='Clight source calls; InputWitnesses constructs inhabited source inputs, not a full-process startup producer',
        residual_connections=['Physical descriptors/global-state provenance', 'Pinned Linux I/O and partial user-copy relation',
                              'Controller/supervision/capture/export composition', 'Compiler/runtime/linker/loader realization'],
        kernel_runtime_hardware='Not supplied by this source call theorem; retained deployment identities are test evidence only',
        lean_toolchain=(ROOT/'m3/lean-toolchain').read_text().strip(),
        compiler_semantics='Pinned CompCert 3.17 Clight plus the retained byte-aware/loss library machine',
        replay='./scripts/check_reporting_connection.sh')
    evidence.update(audited_result())
    evidence['negative_controls'] = negative_controls()
    evidence.update(bindings())
    for group in ['source_sha256', 'cache_sha256']:
        for name, value in evidence[group].items():
            if digest(ROOT/name) != value:
                raise ValueError('current reporting association differs: '+name)
    for name, value in evidence['host_inputs_sha256'].items():
        if digest(name) != value:
            raise ValueError('current reporting host ABI input differs: '+name)
    return evidence


def check():
    if not RECORD.exists():
        raise ValueError('no reviewed reporting connection record; use --collect to propose one')
    expected = json.loads(gzip.decompress(RECORD.read_bytes()))
    if expected['schema_version'] != 1 or expected['full_m4_complete'] is not False or expected['original_obligations_closed'] != []:
        raise ValueError('reporting connection scope differs')
    verify_metadata_amendment()
    for name, value in expected['source_sha256'].items():
        if digest(ROOT/name) != value:
            raise ValueError('reporting connection source/dependency changed: '+name)
    for name, value in expected['host_inputs_sha256'].items():
        if not Path(name).is_absolute() or digest(name) != value:
            raise ValueError('reporting source ABI/header/tool input changed: '+name)
    if any(not (ROOT/name).exists() for name in expected['cache_sha256']):
        build_lean()
        build_sources()
        actual = collect()
        if actual != expected:
            raise ValueError('replayed reporting statement/foundation/binding differs')
    for name, value in expected['cache_sha256'].items():
        if digest(ROOT/name) != value:
            raise ValueError('reporting connection artifact changed: '+name)
    texts, order, dependencies, files = source_plan()
    if order != expected['source_module_order'] or dependencies != expected['source_module_dependencies']:
        raise ValueError('source consumer dependency graph changed')
    for name in order:
        if (PROOFS/(name+'.v')).read_text() != texts[name]:
            raise ValueError('adapted source proof changed: '+name)
    print('Current helper call and ordinary Lean decoder connection checked; matching proof artifacts reused.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', action='store_true', help='check changed proof sources without refreshing expectations')
    parser.add_argument('--audit', action='store_true', help='audit full statements and recheck their kernels')
    parser.add_argument('--collect', action='store_true', help='write an ignored proposed assurance record')
    args = parser.parse_args()
    if args.build or args.audit or args.collect:
        build_lean()
        build_sources()
        if args.collect:
            report = collect()
            (WORK/'connection-proposed.json').write_text(json.dumps(report, indent=2)+'\n')
            print('Wrote the proposed reporting record; reviewed expectations were not changed.')
        elif args.audit:
            (WORK/'connection-audit.json').write_text(json.dumps(audit(), indent=2)+'\n')
            print('Audited full types, foundations and independent kernel replay.')
    else:
        check()



if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(error.stdout or error.stderr, file=sys.stderr)
        sys.exit(1)
