#!/usr/bin/env python3
"""Check M2 statements/axioms/artifacts and preserve the entire reviewed M1 theorem baseline."""
# §AR-lifecycle.proofs: No expectation regeneration in normal checks; all modules inventoried.
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

PROJECT=Path(__file__).resolve().parents[1]
PACKAGE=PROJECT/'m2'
MANIFEST=PROJECT/'assurance/m2-claims.json'
BASELINE=PROJECT/'assurance/m1-reviewed-baseline.json'
SPEC=importlib.util.spec_from_file_location('m1_audit',PROJECT/'scripts/audit_axioms.py')
M1=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(M1)
SPEC=importlib.util.spec_from_file_location('m2_vm',PROJECT/'scripts/run_m2_vm.py')
VM=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(VM)


def modules():
    paths=[PACKAGE/'LeanCageM2.lean',PACKAGE/'Main.lean',*sorted((PACKAGE/'LeanCageM2').rglob('*.lean'))]
    return {str(p.relative_to(PACKAGE).with_suffix('')).replace('/','.'):p for p in paths}


# §AR-lifecycle.proofs: A dependent package must not silently select a different Lean kernel.
def check_toolchain():
    toolchain=(PROJECT/'lean-toolchain').read_text().strip()
    if (PACKAGE/'lean-toolchain').read_text().strip()!=toolchain:
        raise M1.AuditError('M2 toolchain differs from the preserved root pin')
    return toolchain


def required_sources():
    hashes=VM.source_identities()
    paths=[BASELINE,PROJECT/'scripts/audit_axioms.py',PROJECT/'scripts/axiom_query.lean',
        PROJECT/'scripts/check.sh',PROJECT/'assurance/m2-vm-evidence.json',PROJECT/'assurance/m2-vm-transcript.log',
        PROJECT/'docs/functional-spec/FS-lifecycle.md',PROJECT/'docs/functional-spec/FS-assurance.md',
        PROJECT/'docs/architecture/AR-lifecycle.md',PROJECT/'docs/decisions/architectural/DA-m2-profile.md',
        PROJECT/'docs/requirements/REQ-proof-integrity.md',PROJECT/'docs/reviews/M2-handoff.md']
    hashes.update({str(p.relative_to(PROJECT)):M1.sha256(p) for p in paths})
    return dict(sorted(hashes.items()))


def query_environment(names=(),declarations=(),extra_source=''):
    for name in [*names,*declarations]:
        if not M1.NAME.fullmatch(name):raise M1.AuditError(f'Invalid Lean name: {name}')
    source=(PROJECT/'scripts/m2_axiom_query.lean').read_text()+'\n'+extra_source+'\n'
    source+=''.join(f'#audit_module {name}\n' for name in names)
    source+=''.join(f'#audit_decl {name}\n' for name in declarations)
    cache=PROJECT/'.tools/assurance';cache.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='m2-query-',dir=cache) as directory:
        probe=Path(directory)/'Query.lean';probe.write_text(source)
        result=subprocess.run(['lake','env','lean',str(probe)],cwd=PACKAGE,capture_output=True,text=True,timeout=90)
    if result.returncode:raise M1.AuditError('M2 Lean query failed:\n'+result.stdout+result.stderr)
    records=[json.loads(line.split('LEANCAGE_AUDIT ',1)[1]) for line in result.stdout.splitlines() if 'LEANCAGE_AUDIT ' in line]
    if not records:raise M1.AuditError('Empty M2 theorem evidence')
    return records


def validate_inventory(expected,records,names):
    inventories=[r for r in records if 'module' in r]
    declarations=[r for r in records if 'name' in r]
    if len(inventories)!=len(names) or {r['module'] for r in inventories}!=set(names):
        raise M1.AuditError('Missing/duplicate M2 module inventory')
    listed=[n for r in inventories for n in r['declarations']]
    if sorted(listed)!=sorted(r['name'] for r in declarations):raise M1.AuditError('Missing M2 declaration evidence')
    M1.validate_declarations(expected,declarations)
    return declarations


def audit():
    toolchain=check_toolchain()
    manifest_hash=M1.sha256(MANIFEST);manifest=json.loads(MANIFEST.read_text())
    if set(manifest)!={'schema_version','scope','modules','claims','declarations','source_sha256','toolchain'} or manifest['schema_version']!=1:
        raise M1.AuditError('Unsupported/incomplete M2 theorem manifest')
    if set(manifest['modules'])!=set(modules()):raise M1.AuditError('M2 module inventory differs')
    sources=required_sources()
    if manifest['source_sha256']!=sources:raise M1.AuditError('M2 source/dependency/evidence identities differ')
    if manifest['toolchain']!=toolchain:raise M1.AuditError('M2 toolchain differs')
    subprocess.run(['lake','build','LeanCageM2','leancage-m2'],cwd=PACKAGE,check=True)
    records=query_environment(names=sorted(modules()))
    declarations=validate_inventory(manifest['declarations'],records,modules())
    claims=manifest['claims']
    if not claims or len(set(claims))!=len(claims) or not set(claims)<={r['name'] for r in declarations}:
        raise M1.AuditError('Missing/duplicate/non-theorem M2 claim')
    baseline=json.loads(BASELINE.read_text())
    preserved=query_environment(names=sorted(baseline['modules']))
    m1_declarations=validate_inventory(baseline['declarations'],preserved,baseline['modules'])
    VM.check_evidence()
    if sources!=required_sources() or manifest_hash!=M1.sha256(MANIFEST):raise M1.AuditError('M2 sources changed during audit')
    artifacts={}
    for module in modules():
        base=PACKAGE/'.lake/build/lib/lean'/module.replace('.','/')
        if not base.with_suffix('.olean').is_file():raise M1.AuditError(f'Missing M2 checked artifact: {module}')
        for suffix in ('.olean','.olean.private','.olean.server'):
            path=base.with_suffix(suffix)
            if path.is_file():artifacts[str(path.relative_to(PROJECT))]=M1.sha256(path)
    report={'schema_version':1,'scope':manifest['scope'],'manifest_sha256':manifest_hash,'source_sha256':sources,
        'declarations':sorted(declarations,key=lambda r:r['name']),'artifacts_sha256':artifacts,
        'preserved_m1_theorems':len(m1_declarations),'native_linux_correspondence':'Open M4 obligations; not certified by this proof audit'}
    output=PROJECT/'.tools/assurance/m2-report.json';output.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(f'M2 audit passed: {len(declarations)} theorems; {len(claims)} named claims; {len(sources)} identities; all {len(m1_declarations)} M1 theorem statements/axioms preserved.')

if __name__=='__main__':
    try:audit()
    except (M1.AuditError,ValueError,KeyError,OSError,subprocess.SubprocessError) as error:
        print(f'M2 audit failed: {error}',file=sys.stderr);sys.exit(1)
