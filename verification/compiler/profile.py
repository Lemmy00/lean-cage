"""Concrete choices for a kernel-replayable instance of the pinned backend.

The retained tools and their compiled proofs are read-only. Only clients of a
changed choice are rebuilt, into this separate local directory.
"""
# SPDX-License-Identifier: Apache-2.0
# §AR-compiled-reporting.certificate: Instantiate compiler choices without trusting their output.
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / '.tools/reporting/compiler'
TREE = ROOT / '.tools/reporting/compiler-backend'
spec = importlib.util.spec_from_file_location('compiler_reporting_connection',
    ROOT / 'verification/reporting/connection.py')
connection = importlib.util.module_from_spec(spec)
spec.loader.exec_module(connection)
base = connection.profile


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError('pinned compiler choice differs: '+old)
    return text.replace(old, new)


def choices():
    source = base.WORK / 'CompCert'
    result = {}
    path = 'driver/Compopts.v'
    text = (source/path).read_text()
    pattern = r'Parameter (\w+): unit -> bool\.'
    names = re.findall(pattern, text)
    if len(names) != 10:
        raise ValueError('pinned compiler option set differs')
    result[path] = re.sub(pattern,
        lambda m: 'Definition '+m[1]+' (_:unit) := false.\nGlobal Opaque '+m[1]+'.', text)
    substitutions = {
        'x86/SelectOp.v': [('Parameter symbol_is_relocatable: ident -> bool.',
            'Definition symbol_is_relocatable (_:ident) := false.\nGlobal Opaque symbol_is_relocatable.')],
        'backend/RTLgen.v': [('Parameter more_likely: condexpr -> stmt -> stmt -> bool.',
            'Definition more_likely (_:condexpr) (_ _:stmt) := false.\nGlobal Opaque more_likely.')],
        'backend/Selection.v': [
            ('Parameter compile_switch: Z -> nat -> table -> comptree.',
             '''Fixpoint linear_switch (default:nat) (cases:table) : comptree :=
  match cases with
  | nil => CTaction default
  | (key,action)::rest => CTifeq key action (linear_switch default rest)
  end.
Definition compile_switch (_:Z) := linear_switch.
Global Opaque compile_switch.'''),
            ('''Parameter if_conversion_heuristic:
  ident -> Cminor.expr -> Cminor.expr -> Cminor.expr -> AST.typ -> CminorSel.stmt -> bool.''',
             '''Definition if_conversion_heuristic (_:ident) (_ _ _:Cminor.expr)
  (_:AST.typ) (_:CminorSel.stmt) := false.
Global Opaque if_conversion_heuristic.''')],
        'backend/Linearize.v': [('Parameter enumerate_aux: LTL.function -> PMap.t bool -> list node.',
            '''Definition enumerate_aux (f:LTL.function) (_:PMap.t bool) :=
  List.map fst (PTree.elements (LTL.fn_code f)).
Global Opaque enumerate_aux.''')],
    }
    for path, replacements in substitutions.items():
        text = (source/path).read_text()
        for old, new in replacements:
            text = replace_once(text, old, new)
        result[path] = text
    path = 'common/Unityping.v'
    text = (source/path).read_text()
    start = text.index('Function solve_constraints ')
    end = text.index('\nQed.',start)
    # Preserve the termination proof. Its computational witness must remain
    # transparent for ordinary kernel conversion, rather than only extraction.
    result[path] = text[:end]+'\nDefined.'+text[end+5:]
    for path in ['x86/Conventions1.v','x86/Stacklayout.v']:
        text = (source/path).read_text()
        if 'Archi.win64' not in text:
            raise ValueError('pinned calling-convention choice differs')
        result[path] = ('Require Import CompilerPlatform.\n'+
                        text.replace('Archi.win64','CompilerPlatform.win64'))
    path = 'backend/Kildall.v'
    text = (source/path).read_text()
    text = replace_once(text,'Require Import Iteration.',
        'Require Import Iteration.\nRequire Import ExecutableIteration.')
    text = replace_once(text,
        'Module Backward_Dataflow_Solver (LAT: SEMILATTICE) (NS: NODE_SET):',
        'Module Backward_Dataflow_Solver (LAT: SEMILATTICE) (NS: NODE_SET) <:')
    # Transparent ascription retains the checked interface and its entire
    # implementation. Opaque ascription hides the solver from kernel reduction.
    result[path] = text.replace('PrimIter.','ExecutableIteration.')
    path = 'backend/Linearizeproof.v'
    text = (source/path).read_text()
    start = text.index('Theorem transf_step_correct:')
    end = text.index('\nQed.',start)
    body = text[start:end]
    def constructor_section(body,first,last,names):
        begin = body.index(first)
        finish = body.index(last,begin) if last else len(body)
        section = body[begin:finish]
        matches = list(re.finditer(r'econstructor; eauto\.',section))
        if len(matches)!=len(names):
            raise ValueError('pinned linearization proof section differs: '+first)
        choices = iter(names)
        def select(_):
            constructor = next(choices)
            if constructor=='cond_left':
                return 'eapply match_states_add_branch;[exact STACKS|exact TRF|exact REACH1|exact TAIL].'
            if constructor=='cond_right':
                return 'eapply match_states_add_branch;[exact STACKS|exact TRF|exact REACH2|exact TAIL].'
            if constructor=='cond_taken_false':
                return 'eapply match_states_cond_taken;[exact STACKS|exact TRF|exact REACH2|].'
            if constructor=='cond_taken_true':
                return 'eapply match_states_cond_taken;[exact STACKS|exact TRF|exact REACH1|exact H].'
            if constructor=='match_states_jumptable':
                return 'eapply match_states_jumptable with(n:=n);assumption.'
            return ('lazymatch goal with | |-match_states _ _ => eapply '+constructor+
                    ';try assumption | _ => econstructor;eauto end.')
        section = re.sub(r'econstructor; eauto\.',select,section)
        return body[:begin]+section+body[finish:]
    body = constructor_section(body,'  (* Lbranch *)','  (* Lcond *)',['match_states_add_branch'])
    body = constructor_section(body,'  (* Lcond *)','  (* Ljumptable *)',
        ['cond_left','cond_taken_false','cond_taken_true','cond_right'])
    body = constructor_section(body,'  (* Ljumptable *)','  (* Lreturn *)',['match_states_jumptable'])
    body = constructor_section(body,'  (* internal functions *)','  (* external function *)',['match_states_add_branch'])
    # Name the constructor determined by the source state. Generic constructor
    # search otherwise unfolds the concrete enumeration during unification.
    body = body.replace('econstructor; eauto.', '''lazymatch goal with
  | |-match_states (LTL.Block _ _ _ _ _ _) _ => eapply match_states_block;try assumption
  | |-match_states (LTL.State _ _ _ _ _ _) (Linear.State _ _ _ (add_branch _ _) _ _) =>
      eapply match_states_add_branch;try assumption
  | |-match_states (LTL.State _ _ _ _ _ _) (Linear.State _ _ _ (Linear.Lcond _ _ _ :: _) _ _) =>
      eapply match_states_cond_taken;try assumption
  | |-match_states (LTL.State _ _ _ _ _ _) (Linear.State _ _ _ (Linear.Ljumptable _ _ :: _) _ _) =>
      eapply match_states_jumptable;try assumption
  | |-match_states (LTL.Callstate _ _ _ _) _ => eapply match_states_call;try assumption
  | |-match_states (LTL.Returnstate _ _ _) _ => eapply match_states_return;try assumption
  | _ => econstructor;eauto
  end.''')
    result[path] = text[:start]+body+text[end:]
    return result


def flags(checker=False):
    return [arg.replace(str(base.WORK/'CompCert'), str(TREE))
            for arg in connection.flags(checker)] + ['-Q',str(WORK),'']


def run(args, timeout=60):
    command = [str(base.WORK/'opam-bin'),'exec','--switch='+base.SWITCH,'--',*args]
    result = subprocess.run(command, cwd=WORK, env=base.environment(), text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def prepare():
    TREE.mkdir(parents=True,exist_ok=True)
    source = base.WORK/'CompCert'
    patched = choices()
    # Never write through a retained source or compiled-artifact symlink.
    for original in source.rglob('*'):
        relative = original.relative_to(source)
        target = TREE/relative
        if original.is_dir():
            target.mkdir(exist_ok=True)
        elif original.suffix=='.v' and str(relative) not in patched and target.exists() and not target.is_symlink():
            if target.read_bytes()!=original.read_bytes():
                target.unlink()
                target.symlink_to(original)
        elif not target.exists() and not target.is_symlink():
            target.symlink_to(original)
    for relative, text in patched.items():
        target = TREE/relative
        if target.is_symlink():
            target.unlink()
        if not target.exists() or target.read_text() != text:
            target.write_text(text)
    return patched


def graph():
    directories = ['lib','common','x86_64','x86','backend','cfrontend','driver']
    files = sorted(path for directory in directories for path in (TREE/directory).glob('*.v'))
    output = run(['rocq','dep',*flags(),*[str(path) for path in files]],timeout=30)
    (WORK/'backend-dependencies.log').write_text(output)
    result = {}
    for line in output.splitlines():
        if '.vo ' not in line or ':' not in line:
            continue
        targets, deps = line.split(':',1)
        target = next((Path(x).resolve() for x in targets.split() if x.endswith('.vo')),None)
        if target is not None:
            # resolve() would follow an existing .vo symlink into the baseline.
            # Logical output paths must remain in the new tree instead.
            target = Path(next(x for x in targets.split() if x.endswith('.vo'))).absolute()
            result[target] = [Path(x).absolute() for x in deps.split() if x.endswith('.vo')]
    return result


def backend_roots():
    names = ['Cshmgenproof','Cminorgenproof','Selectionproof','RTLgenproof',
             'Allocation','Linearizeproof',
             'Stackingproof','Asmgenproof']
    result = []
    for name in names:
        files = [path for directory in ['lib','common','x86_64','x86','backend','cfrontend','driver']
                 for path in (base.WORK/'CompCert'/directory).glob(name+'.v')]
        if len(files)!=1:
            raise ValueError('ambiguous backend module '+name)
        result.append(str(files[0].relative_to(base.WORK/'CompCert').with_suffix('.vo')))
    return result


def build(roots=None):
    roots = backend_roots() if roots is None else roots
    platform = WORK/'CompilerPlatform.v'
    platform_source = Path(__file__).with_name('CompilerPlatform.v')
    if not platform.exists() or platform.read_bytes()!=platform_source.read_bytes():
        platform.write_bytes(platform_source.read_bytes())
    platform_stamp = platform.with_suffix('.inputs')
    if (not platform.with_suffix('.vo').exists() or not platform_stamp.exists() or
            platform_stamp.read_text()!=sha(platform)):
        output = run(['rocq','c','-q',*connection.flags(),'-Q',str(WORK),'',str(platform)],timeout=10)
        (WORK/'CompilerPlatform.log').write_text(output)
        platform_stamp.write_text(sha(platform))
    binary = WORK/'BinaryIteration.v'
    binary_source = Path(__file__).with_name('BinaryIteration.v')
    if not binary.exists() or binary.read_bytes()!=binary_source.read_bytes():
        binary.write_bytes(binary_source.read_bytes())
    stamp = WORK/'BinaryIteration.inputs'
    if not binary.with_suffix('.vo').exists() or not stamp.exists() or stamp.read_text()!=sha(binary):
        # This helper uses only the unchanged standard library.
        output = run(['rocq','c','-q',*connection.flags(),'-Q',str(WORK),'',str(binary)],timeout=15)
        (WORK/'BinaryIteration.log').write_text(output)
        stamp.write_text(sha(binary))
    executable = WORK/'ExecutableIteration.v'
    executable_source = Path(__file__).with_name('ExecutableIteration.v')
    if not executable.exists() or executable.read_bytes()!=executable_source.read_bytes():
        executable.write_bytes(executable_source.read_bytes())
    executable_stamp = WORK/'ExecutableIteration.inputs'
    executable_identity = sha(executable)+'\n'+sha(binary.with_suffix('.vo'))
    if (not executable.with_suffix('.vo').exists() or not executable_stamp.exists() or
            executable_stamp.read_text()!=executable_identity):
        output = run(['rocq','c','-q',*connection.flags(),'-Q',str(WORK),'',str(executable)],timeout=15)
        (WORK/'ExecutableIteration.log').write_text(output)
        executable_stamp.write_text(executable_identity)
    patched = prepare()
    dependencies = graph()
    changed = {TREE/Path(path).with_suffix('.vo') for path in patched}
    order, seen, affected = [],set(),set(changed)
    def visit(path):
        if path in seen or path not in dependencies:
            return
        seen.add(path)
        for dep in dependencies[path]:
            visit(dep)
        if any(dep in affected for dep in dependencies[path]):
            affected.add(path)
        order.append(path)
    for relative in roots:
        visit(TREE/relative)
    for path in order:
        if path not in affected:
            # Restore an unchanged baseline artifact if an earlier route trial
            # rebuilt it against a different foundation in this private tree.
            original = base.WORK/'CompCert'/path.relative_to(TREE)
            if path.exists() and not path.is_symlink() and sha(path)!=sha(original):
                path.unlink()
                path.symlink_to(original)
            continue
        source = path.with_suffix('.v')
        identity = dict(flags=flags(),source=sha(source),dependencies={str(dep):sha(dep) for dep in dependencies[path]})
        stamp = path.with_suffix('.verified-inputs.json')
        if path.exists() and not path.is_symlink() and stamp.exists() and json.loads(stamp.read_text())==identity:
            continue
        for artifact in [path,path.with_suffix('.glob'),path.with_suffix('.vos'),path.with_suffix('.vok'),
                         path.parent/('.'+path.stem+'.aux')]:
            if artifact.is_symlink():
                artifact.unlink()
        print('Checking changed backend dependency '+str(path.relative_to(TREE)),flush=True)
        log_path = path.with_suffix('.compiler.log')
        command = [str(base.WORK/'opam-bin'),'exec','--switch='+base.SWITCH,'--',
                   'rocq','c','-q','-time',*flags(),str(source)]
        with log_path.open('w')as log:
            try:
                result = subprocess.run(command,cwd=WORK,env=base.environment(),text=True,
                                         stdout=log,stderr=subprocess.STDOUT,timeout=30)
            except subprocess.TimeoutExpired as error:
                raise ValueError('inspect focused backend log '+str(log_path))from error
        if result.returncode:
            raise ValueError(log_path.read_text()[-2800:])
        stamp.write_text(json.dumps(identity,sort_keys=True)+'\n')
    return dict(changed_sources=patched,checked_modules=[str(x.relative_to(TREE)) for x in order if x in affected])


if __name__=='__main__':
    result = build()
    (WORK/'concrete-profile-build.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Concrete backend dependencies checked.')
