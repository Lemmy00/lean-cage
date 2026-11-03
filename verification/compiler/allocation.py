"""Instantiate CompCert's existing validated allocator with an explicit oracle.

The generated module retains the upstream proof and notice. Its oracle is an
ordinary universally quantified argument, not a new logical or compiler axiom.
"""
# SPDX-License-Identifier: Apache-2.0
# §AR-compiled-reporting.certificate: Preserve the entire allocation validator and proof.
from pathlib import Path
import re


def proof(source: Path) -> str:
    upstream = (source / 'backend/Allocproof.v').read_text()
    allocation = (source / 'backend/Allocation.v').read_text()
    start = allocation.index('Definition transf_function (f: RTL.function)')
    end = allocation.index('\n', allocation.index('  transform_partial_program transf_fundef p.', start))
    definitions = allocation[start:end]
    boundary = 'Definition match_prog (p: RTL.program) (tp: LTL.program) :='
    if upstream.count(boundary) != 1:
        raise ValueError('upstream allocator proof boundary changed')
    # These aliases depend only on Allocation's equation sets, not the oracle.
    # Rocq prohibits module declarations inside sections; keep them at top level.
    aliases = re.findall(r'^Module ES[FPD]2? := [^\n]+\n', upstream, re.M)
    if len(aliases) != 6:
        raise ValueError('upstream equation-set aliases changed')
    for alias in aliases:
        upstream = upstream.replace(alias, '')
    before = 'unfold analyze; intros. exploit DS.fixpoint_allnodes_solution; eauto.'
    if upstream.count(before) != 1:
        raise ValueError('upstream dataflow proof application changed')
    upstream = upstream.replace(before, '''unfold analyze; intros.
  generalize (@DS.fixpoint_allnodes_solution block_shape bsh successors_block_shape
    (transfer f env bsh) an pc bs s H H0 H1).''')
    declarations = ''.join(aliases)+'''Local Open Scope error_monad_scope.
Section EXPLICIT_ALLOCATION_ORACLE.
Variable allocation_oracle : RTL.function -> res LTL.function.
Local Definition regalloc := allocation_oracle.

'''+definitions+'\n\n'
    return upstream.replace(boundary, declarations+boundary)+'\nEnd EXPLICIT_ALLOCATION_ORACLE.\n'
