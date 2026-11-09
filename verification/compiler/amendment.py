"""Preserve proof evidence across reviewed gate and foundation-input amendments."""
# SPDX-License-Identifier: Apache-2.0
# §AR-compiled-reporting.certificate: Check the exact operational fingerprint amendment.
import base64
import copy
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
ARCHIVE = 'assurance/reporting-compiler-before.json.gz'
AGGREGATE = 'scripts/check_m4_all.sh'
CHECKER = 'verification/reporting/connection.py'
SOURCE = 'assurance/reporting-source.json.gz'
CONNECTION = 'assurance/reporting-connection.json.gz'
ADAPTER = 'verification/compiler/amendment.py'
COMPILER = 'verification/compiler/check.py'
COMPILER_RECORD = 'assurance/reporting-compiler.json.gz'
HISTORICAL_METADATA = 'verification/reporting/README.md'
HISTORICAL_HOST_SOURCE = 'native/leancage_m3.c'
PATHS_BEFORE = "    paths += [files[name] for name in order if name in files]"
PATHS_AFTER = ("    paths += [ROOT/'verification/compiler/amendment.py',\n"
               "              ROOT/'assurance/reporting-compiler-before.json.gz']\n"+PATHS_BEFORE)
VERIFY_BEFORE = "    if old != json.loads(gzip.decompress((ROOT/record).read_bytes())):"
VERIFY_AFTER = ("    old = load(ROOT/'verification/compiler/amendment.py',\n"
                "               'reporting_compiler_gate_amendment').adjust_source(old)\n"+VERIFY_BEFORE)
SOURCE_CHECK_BEFORE = """    for name, value in expected['source_sha256'].items():
        if digest(ROOT/name) != value:
            raise ValueError('reporting connection source/dependency changed: '+name)"""
SOURCE_CHECK_AFTER = """    preserved = load(ROOT/'verification/compiler/amendment.py',
                     'reporting_preserved_inputs').PreservedInputs()
    for name, value in expected['source_sha256'].items():
        preserved.verify('assurance/reporting-connection.json.gz', 'source_sha256', name, value)"""
CACHE_CHECK_BEFORE = """    for name, value in expected['cache_sha256'].items():
        if digest(ROOT/name) != value:
            raise ValueError('reporting connection artifact changed: '+name)"""
CACHE_CHECK_AFTER = """    for name, value in expected['cache_sha256'].items():
        preserved.verify('assurance/reporting-connection.json.gz', 'cache_sha256', name, value)"""
HOST_CHECK_BEFORE = """    for name, value in expected['host_inputs_sha256'].items():
        if not Path(name).is_absolute() or digest(name) != value:
            raise ValueError('reporting source ABI/header/tool input changed: '+name)"""
HOST_CHECK_AFTER = """    for name, value in expected['host_inputs_sha256'].items():
        if not Path(name).is_absolute():
            raise ValueError('reporting source ABI/header/tool input changed: '+name)
        preserved.verify('assurance/reporting-connection.json.gz', 'host_inputs_sha256', name, value)"""
REPORT_BEFORE = "    print('Current helper call and ordinary Lean decoder connection checked; matching proof artifacts reused.')"
REPORT_AFTER = """    if preserved.used:
        print('Preserved historical helper/decoder connection checked; exact archived inputs and proof artifacts verified.')
    else:
        print('Current helper call and ordinary Lean decoder connection checked; matching proof artifacts reused.')"""
COMPILER_BINDINGS_BEFORE = """    return {str(path.relative_to(ROOT))if path.is_relative_to(ROOT)else str(path):profile.sha(path)
            for path in sorted(set(paths))}"""
COMPILER_BINDINGS_AFTER = """    current = {str(path.relative_to(ROOT))if path.is_relative_to(ROOT)else str(path):profile.sha(path)
               for path in sorted(set(paths))}
    expected = json.loads(gzip.decompress(RECORD.read_bytes()))['inputs_sha256'] if RECORD.exists() else {}
    preserved = amendment.PreservedInputs()
    for name, value in expected.items():
        if name in current and current[name] != value:
            preserved.verify('assurance/reporting-compiler.json.gz', 'inputs_sha256', name, value)
            current[name] = value
    return current"""

# §AR-tooling.checks: Exact reviewed CI repair; other source or claim edits still fail.
FOUNDATION_INPUTS = {
    'assurance/filter-decoder.json': (
        '31a86bf372affd26c59064289021b31c3d520b585528ed60f9fd1ccb6d671dde',
        'c66ee0b5543aa6a7fbb80b59738471ece4fa6c5ed35ef7bd9a573d19022fbb8d'),
    'assurance/m2-claims.json': (
        'ff2ad12ac93f30dc7e644d1bcbd7c813dcf20b425cedc8f001c4ab1c87807922',
        '50168b4d89615359ec49fdd32c181658675881746c5bdb4955e6c2755022676f'),
    'assurance/m3-claims.json': (
        'b8cb6e5302e4b62816861e064906a80e706612b696f0792f8a226b6777a2900e',
        'cffcf981d41fd5e21a8ee67b9aafb30342dbfdd23b0d9cc70369e5074c4bd0e7'),
    'tests/integration/test_output_capture.py': (
        '67bafa3ba3213f658134f7b7c82406cf9db82e83849efba9ed72d9820b4085a4',
        'd52f0393ac2ee6f9f55c19541ebeb03beb37f68a8dbc05b5390f821d894aab05'),
    'scripts/check_foundation_inputs.py': (
        None, '3b63d186cffef3e0de262ce0c25b26c1881154d8a399ef44b3c6394287b09f38'),
    'tests/integration/test_foundation_inputs.py': (
        None, '23c0a2f0c7b16526a62bfc96677837575213e283aebabce8e245ce551dcddf6a'),
}
FOUNDATION_PAYLOADS = {
    'assurance/filter-decoder.json': '0052ba0e1c2435fc65326fa604a19d875115b2463254d8c2866d17e04ac59d5b',
    'assurance/m2-claims.json': '197ab4d902493f8c2c390f7d34905bf86f3d8777cc0e3e0020f1abf0a910b8c0',
    'assurance/m3-claims.json': '9c2816b985d3ad13babc0ba56563a65c50273b83b11e816e2decd3137e107855',
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


# §AR-workspace-vm.migration: Compose the later product-status amendment with this exact preimage.
def product_evidence():
    path = ROOT/'scripts/rebind_product_evidence.py'
    spec = importlib.util.spec_from_file_location('product_evidence_amendment', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def preimages():
    saved = json.loads(gzip.decompress((ROOT/ARCHIVE).read_bytes()))
    if set(saved)!={AGGREGATE,CHECKER,SOURCE,CONNECTION}:
        raise ValueError('compiler gate amendment preimage scope differs')
    return {name:base64.b64decode(value,validate=True)for name,value in saved.items()}


def replace_once(text,before,after):
    if text.count(before)!=1:
        raise ValueError('compiler gate amendment site differs')
    return text.replace(before,after)


def verify_code(saved):
    aggregate = saved[AGGREGATE].decode()
    for marker in ['  run_check ./scripts/check_reporting.sh\n','run_check ./scripts/check_m4_types.sh\n']:
        indent = '  ' if marker.startswith('  ')else''
        aggregate = replace_once(aggregate,marker,marker+indent+'run_check ./scripts/check_reporting_compiler.sh\n')
    marker = 'if python3 verification/reporting/check.py --current-profile; then\n'
    aggregate = replace_once(aggregate, marker,
                             marker+'  run_check python3 scripts/check_foundation_inputs.py\n')
    if (ROOT/AGGREGATE).read_text()!=aggregate:
        raise ValueError('aggregate amendment exceeds the compiler and foundation input checks')
    checker = replace_once(saved[CHECKER].decode(),PATHS_BEFORE,PATHS_AFTER)
    checker = replace_once(checker,VERIFY_BEFORE,VERIFY_AFTER)
    for before, after in [(SOURCE_CHECK_BEFORE, SOURCE_CHECK_AFTER),
                          (CACHE_CHECK_BEFORE, CACHE_CHECK_AFTER), (HOST_CHECK_BEFORE, HOST_CHECK_AFTER),
                          (REPORT_BEFORE, REPORT_AFTER)]:
        checker = replace_once(checker, before, after)
    if (ROOT/CHECKER).read_text()!=checker:
        raise ValueError('reporting checker amendment exceeds the fingerprint adapter')
    migration = product_evidence()
    compiler = subprocess.run(['git', 'show', migration.BASELINE+':'+COMPILER], cwd=ROOT,
                              check=True, capture_output=True).stdout
    _, original = migration.original_record(COMPILER_RECORD)
    if sha(compiler)!=original['inputs_sha256'][COMPILER]:
        raise ValueError('compiler checker preimage differs from its accepted identity')
    compiler = replace_once(compiler.decode(), COMPILER_BINDINGS_BEFORE, COMPILER_BINDINGS_AFTER)
    if (ROOT/COMPILER).read_text()!=compiler:
        raise ValueError('compiler checker amendment exceeds the archived input verifier')


# §AR-workspace-vm.migration: A mismatch requires the sealed baseline and full migration check.
class PreservedInputs:
    def __init__(self):
        self.migration = None
        self.used = False
        self.originals = {}

    def verify(self, record, group, name, expected):
        actual = sha((ROOT/name).read_bytes())
        if actual == expected:
            return False
        path = Path(name)
        key = name
        if (record==CONNECTION and group=='host_inputs_sha256'
                and name==str(ROOT/HISTORICAL_HOST_SOURCE)):
            key = HISTORICAL_HOST_SOURCE
        elif path.is_absolute() or str(path)!=name or '..' in path.parts:
            raise ValueError('historical input is not an exact repository key: '+name)
        if self.migration is None:
            migration = product_evidence()
            migration.check()
            self.bindings = json.loads(migration.RECORD.read_text())
            self.sources, _ = migration.preserved_inputs()
            self.caches, _ = migration.preserved_caches()
            self.migration = migration
        if record not in (CONNECTION, COMPILER_RECORD):
            raise ValueError('unapproved historical evidence record: '+record)
        if record not in self.originals:
            _, self.originals[record] = self.migration.original_record(record)
        if self.originals[record].get(group, {}).get(name)!=expected:
            raise ValueError('historical input differs from the accepted baseline: '+name)
        binding = dict(preserved_sha256=expected, current_sha256=actual)
        source_binding = self.bindings['historical_inputs'].get(record, {}).get(key)
        cache_binding = self.bindings['historical_caches'].get(self.migration.CACHE_RECORD, {}).get(key)
        source_group = group in ('source_sha256', 'inputs_sha256') or (
            record==CONNECTION and group=='host_inputs_sha256' and key==HISTORICAL_HOST_SOURCE)
        if source_group and source_binding is not None:
            valid = (key in self.migration.HISTORICAL and key in self.sources
                     and sha(self.sources[key])==expected and source_binding==binding)
        elif ((record, group) in ((CONNECTION, 'cache_sha256'), (COMPILER_RECORD, 'inputs_sha256'))
              and name in self.migration.CACHE_INPUTS):
            valid = (self.migration.CACHE_INPUTS[name]==expected
                     and sha(self.caches[name])==expected and cache_binding==binding)
        else:
            valid = False
        if not valid:
            raise ValueError('input has no exact validated historical binding: '+name)
        self.used = True
        return True


def source_after(saved):
    result = json.loads(gzip.decompress(saved[SOURCE]))
    if result['inputs_sha256'][AGGREGATE]!=sha(saved[AGGREGATE]):
        raise ValueError('aggregate preimage differs from the accepted source record')
    result['inputs_sha256'][AGGREGATE]=sha((ROOT/AGGREGATE).read_bytes())
    for name, (before, after) in FOUNDATION_INPUTS.items():
        current = sha((ROOT/name).read_bytes())
        if current != after and name in FOUNDATION_PAYLOADS:
            current = product_evidence().original_file_hash(name)
        if result['inputs_sha256'].get(name)!=before or current!=after:
            raise ValueError('foundation input amendment bytes differ: '+name)
        result['inputs_sha256'][name]=after
    for name, expected in FOUNDATION_PAYLOADS.items():
        payload = json.loads((ROOT/name).read_text())
        del payload['source_sha256']
        if sha(json.dumps(payload, sort_keys=True, separators=(',', ':')).encode())!=expected:
            raise ValueError('foundation amendment changes theorem evidence: '+name)
    return product_evidence().replay(SOURCE, result)


def adjust_source(previous):
    saved = preimages()
    verify_code(saved)
    expected = json.loads(gzip.decompress(saved[SOURCE]))
    normalized = copy.deepcopy(previous)
    # §AR-workspace-vm.migration: Undo only the earlier adapter's current README fingerprint.
    if normalized['inputs_sha256'].get(HISTORICAL_METADATA)!=expected['inputs_sha256'][HISTORICAL_METADATA]:
        migration = product_evidence()
        migration.check()
        preserved, _ = migration.preserved_inputs()
        current = sha((ROOT/HISTORICAL_METADATA).read_bytes())
        historical = sha(preserved[HISTORICAL_METADATA])
        bindings = json.loads(migration.RECORD.read_text())['historical_inputs'].get(SOURCE, {})
        if (normalized['inputs_sha256'].get(HISTORICAL_METADATA)!=current
                or expected['inputs_sha256'][HISTORICAL_METADATA]!=historical
                or bindings.get(HISTORICAL_METADATA)!=dict(preserved_sha256=historical, current_sha256=current)):
            raise ValueError('historical reporting README preimage differs')
        normalized['inputs_sha256'][HISTORICAL_METADATA] = historical
    if normalized!=expected:
        raise ValueError('earlier reporting metadata amendment preimage differs')
    return source_after(saved)


def connection_after(saved):
    result = copy.deepcopy(json.loads(gzip.decompress(saved[CONNECTION])))
    for name in [CHECKER,SOURCE]:
        if result['source_sha256'][name]!=sha(saved[name]):
            raise ValueError('reporting connection metadata preimage differs '+name)
        result['source_sha256'][name]=sha((ROOT/name).read_bytes())
    for name in [ARCHIVE,ADAPTER]:
        if name in result['source_sha256']:
            raise ValueError('compiler gate adapter is already in the preimage')
        result['source_sha256'][name]=sha((ROOT/name).read_bytes())
    return result


def verify():
    saved = preimages()
    verify_code(saved)
    if source_after(saved)!=json.loads(gzip.decompress((ROOT/SOURCE).read_bytes())):
        raise ValueError('source record differs beyond the reviewed gate/input fingerprints')
    if connection_after(saved)!=json.loads(gzip.decompress((ROOT/CONNECTION).read_bytes())):
        raise ValueError('compiler amendment changes reporting statements, foundations or artifacts')
    return True
