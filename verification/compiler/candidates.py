"""Build the untrusted candidate generator by reusing pinned compiled tools."""
# SPDX-License-Identifier: Apache-2.0
# §AR-compiled-reporting.certificate: The output is data for the checked backend, never proof.
import importlib.util
import os
from pathlib import Path
import re
import shutil
import subprocess

DIRECTORY = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('reporting_certificate_profile',DIRECTORY/'profile.py')
profile = importlib.util.module_from_spec(spec)
spec.loader.exec_module(profile)
spec = importlib.util.spec_from_file_location('reporting_candidate_quote',DIRECTORY/'quote.py')
quote = importlib.util.module_from_spec(spec)
spec.loader.exec_module(quote)
BASE = profile.ROOT/'.tools/m4/CompCert'
WORK = profile.WORK/'candidate-tool'
MODULES = ['SelectOp','SplitLong','SelectLong','SelectDiv','Selection','RTLgen','Linearize']


def replay_source(name):
    text = (BASE/'extraction'/(name+'.ml')).read_text()
    for old in MODULES:
        text = re.sub(r'\b'+old+r'\b','Replay'+old,text)
    replacements = {
        'SelectOp': [('symbol_is_relocatable','fun _ -> false')],
        'RTLgen': [('more_likely','fun _ _ _ -> false')],
        'Selection': [
            ('compile_switch', '''fun _ default cases ->
  List.fold_right (fun (key,action) rest -> Switch.CTifeq(key,action,rest)) cases (Switch.CTaction default)'''),
            ('if_conversion_heuristic','fun _ _ _ _ _ _ -> false')],
        'Linearize': [('enumerate_aux','fun f _ -> List.map fst (Maps.PTree.elements f.LTL.fn_code)')],
    }
    for symbol, body in replacements.get(name,[]):
        if name=='SelectOp':
            pattern = r'let '+symbol+r' =.*?\n(?=\(\*\* val )'
            flags = re.S
        else:
            pattern = r'^let '+symbol+r' =[^\n]*'
            flags = re.M
        text, count = re.subn(pattern,'let '+symbol+' = '+body+'\n',text,flags=flags)
        if count != 1:
            raise ValueError('pinned extraction choice differs: '+name+'.'+symbol)
    originals = list(BASE.rglob(name+'.v'))
    if len(originals)!=1:
        raise ValueError('ambiguous upstream candidate-tool notice '+name)
    original = originals[0].read_text()
    notice = original[:original.index('\n\n')]
    if 'Copyright' not in notice or 'License' not in notice:
        raise ValueError('missing upstream candidate-tool notice '+name)
    return notice+'\n\n'+text


def build():
    WORK.mkdir(exist_ok=True)
    # Use the compiler's existing local OCaml toolchain and compiled modules.
    spec = importlib.util.spec_from_file_location('reporting_original_tools',profile.ROOT/'m4/bootstrap.py')
    bootstrap = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(bootstrap)
    environment = bootstrap.environment()
    environment['COMPCERT_CONFIG'] = str(BASE/'compcert.ini')
    directories = ['extraction','lib','common','x86','backend','cfrontend','cparser','driver','export','debug']
    includes = ['-I',str(WORK)]
    for directory in directories:
        includes += ['-I',str(BASE/directory)]
    menhir = profile.ROOT/'.tools/m4/root/usr/lib/ocaml/menhirLib'
    includes += ['-I',str(menhir)]
    compiler = 'ocamlopt'
    files = {('Replay'+name+'.ml'):replay_source(name) for name in MODULES}
    files['QuoteLTL.ml'] = quote.printer(BASE)
    files['CandidateDriver.ml'] = (DIRECTORY/'CandidateDriver.ml').read_text()
    for name,text in files.items():
        path = WORK/name
        if not path.exists() or path.read_text()!=text:
            path.write_text(text)
    # ocamldep supplies an order including the unchanged baseline modules.
    args = ['ocamldep',*includes,*[str(WORK/name) for name in files]]
    dependency_text = subprocess.check_output(args,cwd=BASE,env=environment,text=True)
    (WORK/'dependencies.log').write_text(dependency_text)
    order = []
    deps = {}
    for line in dependency_text.replace('\\\n',' ').splitlines():
        if ':' in line and line.split(':',1)[0].strip().endswith('.cmx'):
            target,values = line.split(':',1)
            deps[Path(target.strip())]=[Path(x) for x in values.split() if x.endswith('.cmx')]
    baseline_order = subprocess.check_output([str(BASE/'tools/modorder'),'.depend.extr','driver/Driver.cmx',
        'export/ExportDriver.cmx'],cwd=BASE,env=environment,text=True).split()
    original = [BASE/name for name in baseline_order
                if name not in ['driver/Driver.cmx','export/ExportDriver.cmx']]
    # Keep shared modules once; the replay copies have distinct names.
    original = list(dict.fromkeys(original))
    seen = set()
    def visit(path):
        if path in seen:
            return
        seen.add(path)
        for dep in deps.get(path,[]):
            if dep.parent==WORK:
                visit(dep)
        order.append(path)
    for name in files:
        visit(WORK/Path(name).with_suffix('.cmx'))
    for path in order:
        source = path.with_suffix('.ml')
        stamp = path.with_suffix('.inputs')
        identity = profile.sha(source)+'\n'+ '\n'.join(profile.sha(dep) for dep in deps.get(path,[]) if dep.exists())
        if path.exists() and stamp.exists() and stamp.read_text()==identity:
            continue
        result = subprocess.run([compiler,'-c',*includes,str(source)],cwd=BASE,env=environment,
                                text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(result.stdout)
        stamp.write_text(identity)
    executable = WORK/'reporting-candidates'
    args = [compiler,'-I',str(menhir),'-o',str(executable),'str.cmxa','unix.cmxa','menhirLib.cmxa',
            *includes,*[str(x) for x in original+order]]
    result = subprocess.run(args,cwd=BASE,env=environment,text=True,
                            stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (WORK/'link.log').write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return executable,environment


if __name__=='__main__':
    executable,environment = build()
    subprocess.run([str(executable),str(profile.ROOT/'.tools/reporting/current/leancage_m3.i'),
        str(profile.WORK/'CandidateData.v'),str(profile.WORK/'helper-candidate.s')],
        cwd=profile.ROOT,env=environment,check=True)
    print('Generated untrusted allocation candidates and assembly for kernel replay.')
