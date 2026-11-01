#!/usr/bin/env python3
"""Complete-helper provenance and the one explicitly reviewed parser-name adaptation."""
# §AR-m4-controller.main-inputs: Preserve actual tokens, headers, ABI and kernel-checked identity.
import hashlib
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
SOURCE_SHA256 = 'fe20ad61706bb8e8463d32e5c9a1a9f3bf038ff52cc9f2ac40ba14c1a010d82c'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def header_inputs(preprocessed):
    paths = set(re.findall(r'^#\s+\d+\s+"([^"\n]+)"', preprocessed, re.M))
    result = {}
    for raw in sorted(paths):
        if raw in {'<built-in>', '<command-line>'}:
            continue
        path = Path(raw)
        if not path.is_absolute() or not path.is_file():
            raise ValueError('unresolved complete-helper header: ' + raw)
        key = str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else raw
        result[key] = digest(path)
    if 'native/leancage_m3.c' not in result or len(result) < 100:
        raise ValueError('incomplete complete-helper preprocessor provenance')
    return result


def verify_inputs(inputs):
    for name, expected in inputs.items():
        path = Path(name) if Path(name).is_absolute() else ROOT / name
        if digest(path) != expected:
            raise ValueError('complete-helper header/source changed: ' + name)


def function(ast, name):
    matches = re.findall(r'^Definition f_' + re.escape(name) + r' :=.*?^\|\}\.', ast, re.M | re.S)
    if len(matches) != 1:
        raise ValueError('missing or duplicate complete-helper function: ' + name)
    return matches[0]


def number_adapter(original):
    if original.count('Module Info.') != 1:
        raise ValueError('unexpected decimal AST metadata')
    header = original[:original.index('Module Info.')]
    identifiers = re.findall(r'^Definition _[^\n]+ : ident :=[^\n]+\n', original, re.M)
    renamed = 'Definition _result : ident := $"result".\n'
    if identifiers.count(renamed) != 1:
        raise ValueError('unreviewed decimal identifier adaptation')
    identifiers = [('Definition _result : ident := Main._result__1.\n' if line == renamed else line)
                   for line in identifiers]
    return (header + 'From LeanCageMain Require Import Main.\n' + ''.join(identifiers) + '\n' +
            function(original, 'number') + '\nTheorem full_number_ast : f_number=Main.f_number.\n'
            'Proof. reflexivity. Qed.\n')


def adapt_proof(source):
    return source.replace('LeanCageController', 'LeanCageMainNumber')


def mutated_number(ast):
    original = function(ast, 'number')
    token = 'Econst_int (Int.repr 10) tint'
    if token not in original:
        raise ValueError('missing negative-identity mutation site')
    return ast.replace(original, original.replace(token, 'Econst_int (Int.repr 11) tint', 1), 1)
