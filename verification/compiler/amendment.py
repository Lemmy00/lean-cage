"""Preserve accepted proof evidence while extending the aggregate check command."""
# SPDX-License-Identifier: Apache-2.0
# §AR-compiled-reporting.certificate: Check the exact operational fingerprint amendment.
import base64
import copy
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ARCHIVE = 'assurance/reporting-compiler-before.json.gz'
AGGREGATE = 'scripts/check_m4_all.sh'
CHECKER = 'verification/reporting/connection.py'
SOURCE = 'assurance/reporting-source.json.gz'
CONNECTION = 'assurance/reporting-connection.json.gz'
ADAPTER = 'verification/compiler/amendment.py'
PATHS_BEFORE = "    paths += [files[name] for name in order if name in files]"
PATHS_AFTER = ("    paths += [ROOT/'verification/compiler/amendment.py',\n"
               "              ROOT/'assurance/reporting-compiler-before.json.gz']\n"+PATHS_BEFORE)
VERIFY_BEFORE = "    if old != json.loads(gzip.decompress((ROOT/record).read_bytes())):"
VERIFY_AFTER = ("    old = load(ROOT/'verification/compiler/amendment.py',\n"
                "               'reporting_compiler_gate_amendment').adjust_source(old)\n"+VERIFY_BEFORE)


def sha(data):
    return hashlib.sha256(data).hexdigest()


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
    if (ROOT/AGGREGATE).read_text()!=aggregate:
        raise ValueError('aggregate amendment changes more than the additional compiler gate')
    checker = replace_once(saved[CHECKER].decode(),PATHS_BEFORE,PATHS_AFTER)
    checker = replace_once(checker,VERIFY_BEFORE,VERIFY_AFTER)
    if (ROOT/CHECKER).read_text()!=checker:
        raise ValueError('reporting checker amendment exceeds the fingerprint adapter')


def source_after(saved):
    result = json.loads(gzip.decompress(saved[SOURCE]))
    if result['inputs_sha256'][AGGREGATE]!=sha(saved[AGGREGATE]):
        raise ValueError('aggregate preimage differs from the accepted source record')
    result['inputs_sha256'][AGGREGATE]=sha((ROOT/AGGREGATE).read_bytes())
    return result


def adjust_source(previous):
    saved = preimages()
    verify_code(saved)
    if previous!=json.loads(gzip.decompress(saved[SOURCE])):
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
        raise ValueError('compiler amendment changes more than one source-record fingerprint')
    if connection_after(saved)!=json.loads(gzip.decompress((ROOT/CONNECTION).read_bytes())):
        raise ValueError('compiler amendment changes reporting statements, foundations or artifacts')
    return True
