#!/usr/bin/env python3
"""Extract the actual native decimal parser without changing its tokens."""
# §AR-m4-controller.extraction: The wrapper states the selected LP64 type assumptions.
import hashlib
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('controller_native_extract', ROOT / 'm4/extract.py')
legacy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(legacy)

PREFIX = '''// SPDX-License-Identifier: Apache-2.0
// Extracted for the bounded controller source proof; no native workload is executed.
typedef unsigned long uint64_t;
#define UINT64_MAX 18446744073709551615UL
_Static_assert(sizeof(int)==4 && sizeof(long)==8 && sizeof(void*)==8,"LP64");
'''
SUFFIX = '\nvoid(*controller_roots[])(void)={(void(*)(void))number};\n'


def extract(source):
    original = legacy.function(source, 'number')
    formatted = legacy.readable(original)
    if legacy.tokens(original) != legacy.tokens(formatted):
        raise ValueError('decimal extraction changed source tokens')
    return PREFIX + formatted + SUFFIX


def identity(source, generated):
    original = legacy.function(source, 'number')
    copied = legacy.function(generated, 'number')
    if generated != extract(source) or legacy.tokens(original) != legacy.tokens(copied):
        raise ValueError('decimal source wrapper or function differs')
    start = source.index(original)
    return {
        'name': 'number',
        'source': 'native/leancage_m3.c',
        'first_line': source[:start].count('\n') + 1,
        'last_line': source[:start + len(original)].count('\n') + 1,
        'exact_source_sha256': hashlib.sha256(original.encode()).hexdigest(),
        'tokens_sha256': hashlib.sha256(''.join(legacy.tokens(original)).encode()).hexdigest(),
        'wrapper_sha256': hashlib.sha256(generated.encode()).hexdigest(),
        'abi': 'x86_64-linux, LP64, unsigned-long uint64_t, signed plain char',
        'boundary': 'Exact maintained function tokens; wrapper types and frontend provenance do not certify a deployed executable.',
    }
