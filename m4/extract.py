#!/usr/bin/env python3
"""Generate the bounded experiment directly from the maintained helper."""
# §AR-m4-native.slice: Preserve tokens and branches; reject stale or ambiguous extraction.
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
NAMES = ['fault', 'error_number', 'write_all', 'put32', 'put64', 'get32', 'get64',
         'send_frame', 'decode_frame', 'result_of', 'fail_child', 'finish']
TOKEN = re.compile(r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|//[^\n]*|/\*.*?\*/|\s+|.', re.S)


def function(source, name):
    matches = list(re.finditer(r'^static [^\n]*?\b' + name + r'\([^\n]*?\)\s*\{', source, re.M))
    if len(matches) != 1:
        raise ValueError(f'expected one definition: {name}')
    start = matches[0].start()
    opening = matches[0].end() - 1
    depth = 0
    for match in TOKEN.finditer(source, opening):
        if match.group() == '{':
            depth += 1
        elif match.group() == '}':
            depth -= 1
            if depth == 0:
                return source[start:match.end()]
    raise ValueError(f'unclosed definition: {name}')


def terminal_receiver(source):
    start = source.index('    unsigned char failure_bytes[9];size_t used=0;')
    end = source.index('\nreport:', start)
    if source.count('unsigned char failure_bytes[9];size_t used=0;') != 1:
        raise ValueError('ambiguous terminal receiver')
    return source[start:end]


def readable(source):
    """Only insert whitespace; preserve strings, comments and all C tokens."""
    lines = []
    current = ''
    depth = 0
    parens = 0
    def emit():
        nonlocal current
        if current.strip():
            lines.append('    ' * depth + current.strip())
        current = ''
    for match in TOKEN.finditer(source):
        token = match.group()
        if token.isspace():
            if current and not current.endswith(' '):
                current += ' '
        elif token == '(':
            parens += 1
            current += token
        elif token == ')':
            parens -= 1
            current += token
            if parens == 0 and len(current) > 90:
                emit()
        elif token == '{':
            current += ' {'
            emit()
            depth += 1
        elif token == '}':
            emit()
            depth -= 1
            current = '}'
            emit()
        elif token in ('&', '|') and current.endswith(token) and len(current) > 70:
            current += token
            emit()
        elif token == ',' and (parens == 0 or len(current) > 80):
            current += token
            emit()
        elif token == ';':
            current += token
            if parens == 0:
                emit()
        else:
            current += token
    emit()
    return re.sub(r'\n\s*;\n', ';\n', '\n'.join(lines) + '\n')


def tokens(source):
    return [m.group() for m in TOKEN.finditer(source) if not m.group().isspace()]


def extract(source):
    declarations = [line for line in source.splitlines() if
                    line.startswith(('enum { EXITED', 'struct result {', 'static uint64_t run_id;',
                                     'static const char *mode=', 'enum { FRAME_SIZE='))]
    if len(declarations) != 5:
        raise ValueError('source dependency declarations changed')
    # The helper shares these globals with excluded setup; initialize independently in harnesses.
    declarations += ['static int preflight;', 'static unsigned run_uid;']
    pieces = declarations + [function(source, name) for name in NAMES]
    receiver = ('struct result m4_collect_failure(int fd,int bad,int entered,'
                'int leader_done,int leader_status) {\n'
                'int pipefd[1]={fd};struct result result;\n' +
                terminal_receiver(source) + '\nreturn result;\n}')
    raw = '\n'.join(pieces) + '\n' + receiver + '\n'
    formatted = readable(raw)
    if tokens(raw) != tokens(formatted):
        raise ValueError('formatting changed source tokens')
    if len(formatted.splitlines()) > 300:
        raise ValueError('readable slice exceeds 300 authored C lines')
    roots = 'void (*m4_roots[])(void) = {' + ','.join('(void (*)(void))' + n for n in NAMES) + '};\n'
    result = '/* SPDX-License-Identifier: Apache-2.0 */\n#include "abi.h"\n' + formatted + readable(roots)
    if len(result.splitlines()) + len((ROOT / 'm4/abi.h').read_text().splitlines()) > 300:
        raise ValueError('slice including ABI/adapters exceeds 300 authored C lines')
    return result


def identities(source):
    return {**{name: hashlib.sha256(function(source, name).encode()).hexdigest() for name in NAMES},
            'namespace_init.terminal_receiver': hashlib.sha256(terminal_receiver(source).encode()).hexdigest()}


if __name__ == '__main__':
    source = (ROOT / 'native/leancage_m3.c').read_text()
    output = ROOT / '.tools/m4/input'
    output.mkdir(parents=True, exist_ok=True)
    (output / 'slice.c').write_text(extract(source))
    (output / 'functions.json').write_text(json.dumps(identities(source), indent=2) + '\n')
