"""Recheck reporting at the helper/runtime program boundary, reusing pure proofs."""
# SPDX-License-Identifier: Apache-2.0
# §AR-compiled-reporting.runtime: Keep the actual helper bodies and the runtime root explicit.
import hashlib
import json
from pathlib import Path
import shutil
import time

import profile

ROOT = profile.ROOT
DIRECTORY = Path(__file__).resolve().parent
WORK = ROOT/'.tools/reporting/compiler-source'
connection = profile.connection


def flags(checker=False):
    original = profile.flags(checker)
    result,index = [],0
    while index<len(original):
        if original[index]=='-Q' and original[index+1]==str(connection.PROOFS):
            index+=3
        else:
            result.append(original[index]);index+=1
    return result+['-Q',str(WORK),'']


def plan():
    texts,_,_,_ = connection.source_plan()
    marker = 'From LeanCageMain Require Export Main.\nDefinition prog := Main.prog.'
    texts['Slice'] = profile.replace_once(texts['Slice'],marker,
        'From LeanCageMain Require Export Main.\nRequire Import RuntimeProgram.\nDefinition prog := RuntimeProgram.program.')
    for function in ['get32','get64']:
        previous = '  change (In (_'+function+', Gfun (Internal f_'+function+')) global_definitions).'
        texts['Codec'] = profile.replace_once(texts['Codec'],previous,
            '  unfold Slice.prog;rewrite RuntimeProgram.helper_definitions_retained;apply in_or_app;left.\n'+previous)
    texts['RuntimeProgram'] = (DIRECTORY/'RuntimeProgram.v').read_text()
    if (DIRECTORY/'RuntimeInputs.v').exists():
        texts['RuntimeInputs'] = (DIRECTORY/'RuntimeInputs.v').read_text()
    roots = ['SourceConnection','InputWitnesses']+(['RuntimeInputs'] if 'RuntimeInputs' in texts else [])
    order,dependencies,seen = [],{},set()
    def visit(name):
        if name in seen:
            return
        if name not in texts:
            raise ValueError('unreviewed source dependency '+name)
        seen.add(name)
        dependencies[name] = connection.imports(texts[name])
        for dep in dependencies[name]:
            visit(dep)
        order.append(name)
    for name in roots:
        visit(name)
    return texts,order,dependencies


def build():
    WORK.mkdir(exist_ok=True)
    texts,order,dependencies = plan()
    accepted = json.loads(__import__('gzip').decompress(connection.RECORD.read_bytes()))['cache_sha256']
    pure = {}
    for name in order:
        pure[name] = name not in ['RuntimeProgram','RuntimeInputs','Slice'] and all(pure[x] for x in dependencies[name])
        path = WORK/(name+'.v')
        if not path.exists() or path.read_text()!=texts[name]:
            path.write_text(texts[name])
        artifact = path.with_suffix('.vo')
        stamp = path.with_suffix('.inputs.json')
        identity = dict(source=profile.sha(path),dependencies={dep:profile.sha(WORK/(dep+'.vo'))
            for dep in dependencies[name]},main=profile.sha(connection.WORK/'rebase/main/proofs/Main.vo'))
        if artifact.exists() and stamp.exists() and json.loads(stamp.read_text())==identity:
            continue
        if pure[name]:
            old = connection.PROOFS/(name+'.vo')
            key = str(old.relative_to(ROOT))
            if old.with_suffix('.v').read_text()!=texts[name] or profile.sha(old)!=accepted[key]:
                raise ValueError('pure source cache differs: '+name)
            shutil.copy2(old,artifact)
        else:
            started = time.monotonic()
            output = profile.run(['rocq','c','-q',*flags(),str(path)],timeout=60)
            path.with_suffix('.log').write_text(output)
            print('Checked helper/runtime source consumer '+name+' ('+
                  str(round(time.monotonic()-started,2))+'s)',flush=True)
        stamp.write_text(json.dumps(identity,sort_keys=True)+'\n')
    (WORK/'dependencies.json').write_text(json.dumps(dict(order=order,dependencies=dependencies),indent=2)+'\n')
    return order


if __name__=='__main__':
    build()
