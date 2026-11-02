"""Checked Rocq module signatures plus a conservative source-command restriction."""
# SPDX-License-Identifier: Apache-2.0
# §AR-m4-parent.audit: Enumerate checked constants independently of source syntax.
import re


def commands(source):
    """Split vernacular commands, respecting nested comments and quoted strings."""
    output, current, depth, quoted, i = [], [], 0, False, 0
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if depth:
            if pair == '(*':
                depth += 1
                i += 2
            elif pair == '*)':
                depth -= 1
                i += 2
                if not depth:
                    current.append(' ')
            else:
                i += 1
            continue
        if quoted:
            current.append(char)
            if pair == '""':
                current.append('"')
                i += 2
                continue
            if char == '"':
                quoted = False
            i += 1
            continue
        if pair == '(*':
            depth = 1
            i += 2
        elif char == '"':
            quoted = True
            current.append(char)
            i += 1
        elif char == '.' and (i + 1 == len(source) or source[i + 1].isspace() or source[i + 1:i + 3] == '(*'):
            output.append(''.join(current).strip())
            current = []
            i += 1
        else:
            current.append(char)
            i += 1
    if depth or quoted or ''.join(current).strip():
        raise ValueError('unterminated Rocq command, comment or string')
    return output


PROOFS = {'Theorem', 'Lemma', 'Example', 'Corollary', 'Fact', 'Remark', 'Proposition'}
DEFINITIONS = {'Definition', 'Fixpoint'}
STRUCTURES = {'Inductive', 'Record'}
FORBIDDEN = re.compile(r'\b(?:Axiom|Axioms|Parameter|Parameters|Conjecture|Admitted|admit|Abort|'
                       r'vm_cast_no_check|native_cast_no_check|bypass_check|Load|Redirect)\b')


def declarations(source, prefix):
    """Reject unsupported top-level syntax, including attributes/qualifiers.

    Every supported Definition and Fixpoint is included regardless of its sort;
    a proof-valued definition cannot evade type/foundation comparison. Inductive
    constructors are checked by Rocq and their consumers' transitive foundation
    audit. Local/nested/mutual/program declarations and notations are unsupported.
    """
    result, in_proof, awaiting = [], False, False
    for command in commands(source):
        if FORBIDDEN.search(command) or re.search(r'\b(?:Unset|Set)\s+.*(?:Checking|Type\s+in\s+Type)', command):
            raise ValueError('unchecked Rocq proof or altered kernel checking')
        if re.match(r'(?:#|Local\b|Global\b|Polymorphic\b|Monomorphic\b|Program\b|Module\b|Section\b)', command):
            raise ValueError('unsupported qualified/attributed/scoped Rocq command')
        if in_proof:
            if command == 'Qed':
                in_proof = False
            elif re.search(r'\b(?:Definition|Fixpoint|Inductive|Record|Theorem|Lemma|Example|Corollary|Fact|Remark|Proposition|Let)\b', command):
                raise ValueError('nested Rocq declaration is unsupported')
            continue
        if awaiting:
            if command != 'Proof':
                raise ValueError('Rocq theorem must have an explicit Proof and Qed')
            in_proof, awaiting = True, False
            continue
        match = re.match(r'([A-Za-z]+)\s+([A-Za-z_][A-Za-z0-9_\']*)(?=\s|[:(])', command)
        kind = match[1] if match else ''
        if kind in PROOFS | DEFINITIONS | STRUCTURES:
            if ((kind in STRUCTURES and re.search(r'\bwith\s+[A-Za-z_]', command))
                    or (kind == 'Fixpoint' and re.search(
                        r"\bwith\s+[A-Za-z_][A-Za-z0-9_']*\s*(?:\([^)]*\)\s*)*:", command))):
                raise ValueError('mutual Rocq declaration is unsupported')
            if kind in PROOFS:
                result.append(prefix + match[2])
                awaiting = True
            elif kind in DEFINITIONS:
                if ':=' not in command:
                    raise ValueError('proof-mode Rocq definition is unsupported')
                result.append(prefix + match[2])
            continue
        if (re.fullmatch(r'(?:From\s+[\w.]+\s+)?Require\s+Import\s+[\w.\s]+', command)
                or re.fullmatch(r'Import\s+[\w.\s]+', command)
                or re.fullmatch(r'Open\s+Scope\s+\w+', command)
                or re.match(r'Ltac\s+[A-Za-z_]\w*\b.*:=', command, re.S)):
            continue
        raise ValueError('unsupported top-level Rocq command: ' + command[:90])
    if awaiting or in_proof or not result or len(set(result)) != len(result):
        raise ValueError('unfinished, empty or duplicate Rocq declaration inventory')
    return result


IDENT = r"[A-Za-z_][A-Za-z0-9_']*"


def outer_split(text, separator):
    """Split printed signature fields only outside all binders and strings."""
    result, stack, start, i, quoted = [], [], 0, 0, False
    pairs = {')': '(', ']': '[', '}': '{'}
    while i < len(text):
        char = text[i]
        if quoted:
            if text[i:i + 2] == '""':
                i += 2
                continue
            if char == '"':
                quoted = False
        elif char == '"':
            quoted = True
        elif char in '([{':
            stack.append(char)
        elif char in ')]}':
            if not stack or stack.pop() != pairs[char]:
                raise ValueError('unbalanced checked Rocq signature')
        elif not stack and text.startswith(separator, i):
            result.append(text[start:i].strip())
            i += len(separator)
            start = i
            continue
        i += 1
    if stack or quoted:
        raise ValueError('truncated checked Rocq signature')
    return result + [text[start:].strip()]


def checked_declarations(signature, module):
    """Enumerate every constant/type/constructor in a compiled module signature.

    Rocq's Print Module reads the checked environment, including opaque and Local
    constants and definitions introduced through vernacular control commands.
    Printing All disables notation; each supported signature field is consumed in
    full. Nested/functor/mutual-inductive signature forms fail explicitly.
    """
    short = module.rsplit('.', 1)[-1]
    header = re.fullmatch(r'Module\s+' + re.escape(short) + r'\s*:=\s*Struct\s+(.*)\s+End',
                          signature.strip(), re.S)
    if not header or '...' in signature:
        raise ValueError('unsupported or truncated checked Rocq module signature')
    result = []
    for field in commands(header[1]):
        constant = re.fullmatch(r'(?:Definition|Parameter)\s+(' + IDENT + r')\s*:\s*(.+)', field, re.S)
        if constant:
            # Check balanced complete types even when no constructor parsing is needed.
            outer_split(constant[2], '\0')
            result.append(module + '.' + constant[1])
            continue
        structured = re.fullmatch(r'(Inductive|Record)\s+(' + IDENT + r')\b(.*)', field, re.S)
        if not structured:
            raise ValueError('unsupported checked Rocq signature field: ' + field[:90])
        pieces = outer_split(structured[3], ':=')
        if len(pieces) != 2 or len(outer_split(pieces[1], ' with ')) != 1:
            raise ValueError('unsupported checked Rocq inductive signature')
        result.append(module + '.' + structured[2])
        if structured[1] == 'Inductive':
            constructors = outer_split(pieces[1], '|')
            for constructor in constructors:
                match = re.fullmatch(r'(' + IDENT + r')\s*:\s*(.+)', constructor, re.S)
                if not match:
                    raise ValueError('unsupported checked Rocq constructor signature')
                result.append(module + '.' + match[1])
        else:
            match = re.fullmatch(r'(' + IDENT + r')\s*\{.*\}', pieces[1], re.S)
            if not match:
                raise ValueError('unsupported checked Rocq record signature')
            result.append(module + '.' + match[1])
            # Field projections appear as separate Definition fields, too.
    if not result or len(set(result)) != len(result):
        raise ValueError('empty or duplicate checked Rocq module inventory')
    return result
