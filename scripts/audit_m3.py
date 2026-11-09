#!/usr/bin/env python3
"""Audit every M3 theorem, its full type and transitive axioms, plus native byte identity and VM evidence."""
# §AR-workspace.proofs: Normal checking never regenerates reviewed expectations.
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile

PROJECT=Path(__file__).resolve().parents[1]
PACKAGE=PROJECT/'m3'
MANIFEST=PROJECT/'assurance/workspace-claims.json'

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result);return result
M1=module('m3_m1_audit',PROJECT/'scripts/audit_axioms.py')
M2=module('m3_m2_audit',PROJECT/'scripts/audit_m2.py')
VM=module('m3_vm_audit',PROJECT/'scripts/run_m3_vm.py')


def modules():
    # §AR-workspace.proofs: Preserve the reviewed model/decoder inventory exactly.
    # New maintained runtime modules keep their own functional evidence gate;
    # VM/source identities still include every translated dependency.
    return {name:PACKAGE/(name.replace('.','/')+'.lean') for name in predecessor_claims()['modules']}


def required_sources():
    if MANIFEST.is_file():
        preserved_claims(json.loads(MANIFEST.read_text()))
    hashes=VM.source_identities()
    for name in ['scripts/check.sh',str(VM.EVIDENCE.relative_to(PROJECT)),str(VM.TRANSCRIPT.relative_to(PROJECT)),
                 str(VM.INVENTORY.relative_to(PROJECT)),'assurance/m2-claims.json','assurance/m1-reviewed-baseline.json',
                 'docs/functional-spec/FS-assurance.md','docs/requirements/REQ-proof-integrity.md','docs/reviews/M3-handoff.md',
                 'docs/reviews/M3-acceptance.md','scripts/audit_axioms.py','scripts/audit_m2.py',
                 'scripts/m2_axiom_query.lean','m2/Main.lean','docs/functional-spec/FS-compatibility.md']:
        hashes[name]=M1.sha256(PROJECT/name)
    return dict(sorted(hashes.items()))


def query_environment(names=(), declarations=(), extra_source=''):
    for name in [*names,*declarations]:
        if not M1.NAME.fullmatch(name):raise M1.AuditError('Invalid Lean declaration/module name')
    source=(PROJECT/'scripts/m3_axiom_query.lean').read_text()+'\n'+extra_source+'\n'
    source+=''.join(f'#audit_module {name}\n' for name in names)
    source+=''.join(f'#audit_decl {name}\n' for name in declarations)
    cache=PROJECT/'.tools/assurance';cache.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='m3-query-',dir=cache) as directory:
        probe=Path(directory)/'Query.lean';probe.write_text(source)
        result=subprocess.run(['lake','env','lean',str(probe)],cwd=PACKAGE,capture_output=True,text=True,timeout=M1.QUERY_TIMEOUT_SECONDS)
    if result.returncode:raise M1.AuditError('M3 declaration query failed:\n'+result.stdout+result.stderr)
    return [json.loads(line.split('LEANCAGE_AUDIT ',1)[1]) for line in result.stdout.splitlines() if 'LEANCAGE_AUDIT ' in line]


def check_filter():
    header=(PROJECT/'native/m3_filter.h').read_text()
    rows=re.findall(r'\{(0x[0-9a-f]+),(0x[0-9a-f]+),(0x[0-9a-f]+),(0x[0-9a-f]+)\}',header)
    native=b''.join(struct.pack('<HBBI',*(int(value,16) for value in row)) for row in rows)
    if not native or len(native)//8>4096:raise M1.AuditError('Missing/oversize native filter')
    path=PROJECT/'.tools/assurance/m3-filter.bin'
    subprocess.run([str(PACKAGE/'.lake/build/bin/leancage'),'emit-filter',str(path)],check=True)
    if path.read_bytes()!=native or header!=VM.filter_header(path.read_bytes()):raise M1.AuditError('Native filter differs from universally proved Lean program')
    syscall_list=json.loads((PROJECT/'profiles/m3/syscalls.json').read_text())
    table=[int(n) for n in re.search(r'def allowed : List UInt32 :=\s*\[([^]]+)\]',(PACKAGE/'LeanCageM3/Filter.lean').read_text()).group(1).split(',')]
    if [row['number'] for row in syscall_list['allow']]!=table or len(set(table))!=len(table):raise M1.AuditError('Reviewed syscall enumeration differs')
    return M1.sha256(path)


def predecessor_claims():
    return json.loads(VM.PREDECESSOR.read_baseline()['assurance/m3-claims.json'])


def preserved_claims(manifest):
    expected={'schema_version','scope','modules','claims','declarations','source_sha256','toolchain','predecessor'}
    if set(manifest)!=expected or manifest['schema_version']!=2:
        raise M1.AuditError('Unsupported/incomplete current workspace theorem manifest')
    if manifest['predecessor']!=VM.PREDECESSOR.binding():
        raise M1.AuditError('Workspace theorem predecessor binding differs')
    previous=predecessor_claims()
    for field in ('scope','modules','claims','declarations','toolchain'):
        if manifest[field]!=previous[field]:
            raise M1.AuditError('Preserved workspace theorem inventory/type/axiom field differs: '+field)


def audit(propose=False):
    toolchain=(PROJECT/'lean-toolchain').read_text().strip()
    if propose:
        manifest=copy.deepcopy(predecessor_claims())
        manifest.update(schema_version=2,predecessor=VM.PREDECESSOR.binding(),source_sha256=required_sources())
        manifest_hash=None
    else:
        manifest_hash=M1.sha256(MANIFEST);manifest=json.loads(MANIFEST.read_text())
    preserved_claims(manifest)
    if set(manifest['modules'])!=set(modules()) or manifest['toolchain']!=toolchain or (PACKAGE/'lean-toolchain').read_text().strip()!=toolchain:
        raise M1.AuditError('M3 modules/toolchain differ')
    sources=required_sources()
    if manifest['source_sha256']!=sources:raise M1.AuditError('M3 source/dependency/evidence identities differ')
    subprocess.run(['lake','build','LeanCageM3','leancage'],cwd=PACKAGE,check=True)
    records=query_environment(names=sorted(modules()))
    declarations=M2.validate_inventory(manifest['declarations'],records,modules())
    if not manifest['claims'] or len(set(manifest['claims']))!=len(manifest['claims']) or not set(manifest['claims'])<={r['name'] for r in declarations}:
        raise M1.AuditError('Missing/duplicate/non-theorem M3 claim')
    # Preserve the separately reviewed M2 environment, including its executable Main module.
    baseline=json.loads((PROJECT/'assurance/m2-claims.json').read_text())
    if baseline['source_sha256'] != M2.required_sources():raise M1.AuditError('M2 baseline sources differ')
    subprocess.run(['lake','build','LeanCageM2','leancage-m2'],cwd=PROJECT/'m2',check=True)
    preserved=M2.query_environment(names=baseline['modules'])
    m2_declarations=M2.validate_inventory(baseline['declarations'],preserved,baseline['modules'])
    filter_digest=check_filter();VM.check_evidence()
    if sources!=required_sources() or (not propose and manifest_hash!=M1.sha256(MANIFEST)):raise M1.AuditError('M3 sources changed during audit')
    artifacts={}
    for name in modules():
        base=PACKAGE/'.lake/build/lib/lean'/name.replace('.','/')
        if not base.with_suffix('.olean').is_file():raise M1.AuditError('Missing M3 checked module: '+name)
        for suffix in ('.olean','.olean.private','.olean.server'):
            path=base.with_suffix(suffix)
            if path.is_file():artifacts[str(path.relative_to(PROJECT))]=M1.sha256(path)
    if propose:
        proposal=PROJECT/'.tools/assurance/workspace-claims-proposal.json'
        proposal.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
        manifest_hash=M1.sha256(proposal)
        print('Current workspace theorem proposal written: '+str(proposal))
    report={'schema_version':2,'scope':manifest['scope'],'manifest_sha256':manifest_hash,'source_sha256':sources,
            'theorems':len(declarations),'claims':len(manifest['claims']),'preserved_m2_theorems':len(m2_declarations),
            'filter_sha256':filter_digest,'toolchain':toolchain,'checked_artifacts':artifacts}
    path=PROJECT/'.tools/assurance/workspace-audit.json';path.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(f'Workspace assurance audit passed: {len(declarations)} theorem declarations, {len(manifest["claims"])} claims; all {len(m2_declarations)} M2 declarations preserved.')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--propose',action='store_true',help='write an ignored current-input proposal; preserve reviewed records')
    args=parser.parse_args()
    try:audit(args.propose)
    except (M1.AuditError,ValueError,OSError,subprocess.SubprocessError) as error:
        print(f'M3 audit failed: {error}',file=sys.stderr);sys.exit(1)
