#!/usr/bin/env python3
"""Replay maintained native-source proofs in dependency order on one frozen input set."""
# §AR-host-boundary.acceptance: Exclusions remain explicit partial evidence.
import argparse
import concurrent.futures
import datetime
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


GATEWAY = load('host_source_replay_gateway', 'verification/host/gateway.py')


def prepare_generated():
    for name, path in [('outgoing', 'verification/host/outgoing_proofs.py'),
                       ('send_receive', 'verification/host/send_receive_proofs.py')]:
        module = load('host_replay_' + name, path)
        module.generate()
    if (HERE / 'GatewayObservationSourceRepair.v').is_file():
        old = gzip.decompress((ROOT / 'assurance/host-source-comment-program.v.gz').read_bytes())
        (GATEWAY.WORK / 'GatewayObservationBeforeSource.v').write_bytes(old)
        after = gzip.decompress((ROOT / 'assurance/host-observation-source-program.v.gz').read_bytes())
        expected = json.loads((ROOT / 'assurance/host-observation-source-amendment.json').read_text())
        if hashlib.sha256(after).hexdigest() != expected['after_clight_sha256']:
            raise ValueError('Historical observation source epoch differs')
        (GATEWAY.WORK / 'GatewayObservationAfterSource.v').write_bytes(after)
    if (HERE / 'GatewayOutcomeSourceRepair.v').is_file():
        before = gzip.decompress((ROOT / 'assurance/host-observation-source-program.v.gz').read_bytes())
        after = gzip.decompress((ROOT / 'assurance/host-outcome-source-program.v.gz').read_bytes())
        (GATEWAY.WORK / 'GatewayOutcomeBeforeSource.v').write_bytes(before)
        (GATEWAY.WORK / 'GatewayOutcomeAfterSource.v').write_bytes(after)


def snapshot(excluded):
    paths = {path.stem: path for path in HERE.glob('*.v') if path.stem not in excluded}
    needed = list(paths)
    needed.append('GatewaySource')
    while needed:
        name = needed.pop()
        if name not in paths:
            candidate = GATEWAY.WORK / (name + '.v')
            if not candidate.is_file():
                raise ValueError('Missing generated source: ' + name)
            paths[name] = candidate
        source = paths[name]
        for group in re.findall(r'From\s+HostGateway\s+Require\s+Import\s+([A-Za-z0-9_\s]+)\.', source.read_text()):
            for dependency in group.split():
                if dependency in excluded:
                    raise ValueError(name + ' depends on excluded developing source ' + dependency)
                if dependency not in paths:
                    paths[dependency] = GATEWAY.WORK / (dependency + '.v')
                    needed.append(dependency)
    for name, source in paths.items():
        destination = GATEWAY.WORK / (name + '.v')
        if source != destination:
            shutil.copyfile(source, destination)
    return paths


def graph(paths, directory):
    command = ['rocq', 'dep', *GATEWAY.flags(), *[str(GATEWAY.WORK / (name + '.v')) for name in sorted(paths)]]
    result = GATEWAY.PROFILE.run(command, cwd=GATEWAY.WORK, timeout=120)
    (directory / 'dependencies.log').write_text(result.stdout)
    dependencies = {name: [] for name in paths}
    for line in result.stdout.splitlines():
        if ':' not in line:
            continue
        left, right = line.split(':', 1)
        objects = [item for item in left.split() if item.endswith('.vo')]
        if not objects:
            continue
        name = Path(objects[0]).stem
        if name in dependencies:
            dependencies[name] = sorted({Path(item).stem for item in right.split()
                                         if item.endswith('.vo') and Path(item).stem in paths})
    return dependencies, command


def recorded_phase(command, log, timeout=120):
    try:
        result = GATEWAY.PROFILE.run(command, cwd=GATEWAY.WORK, timeout=timeout)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        output = error.stdout or ''
        if isinstance(output, bytes):
            output = output.decode(errors='replace')
        log.write_text(output)
        return dict(command=command, error=type(error).__name__,
                    return_code=getattr(error, 'returncode', None),
                    timeout_seconds=getattr(error, 'timeout', None),
                    stdout_sha256=GATEWAY.sha(log))
    log.write_text(result.stdout)
    return None


def replay(excluded, reason, workers, reuse=None):
    GATEWAY.PROFILE.verify_tools()
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    directory = ROOT / '.tools/host' / ('source-replay-' + stamp)
    directory.mkdir(parents=True)
    prepare_generated()
    sources = snapshot(excluded)
    frozen = {name: GATEWAY.sha(path) for name, path in sources.items()}
    dependencies, dependency_command = graph(sources, directory)
    inputs = dict(sources={name: str(path.relative_to(ROOT)) for name, path in sources.items()},
                  source_sha256=frozen, dependencies=dependencies, excluded=sorted(excluded), reason=reason,
                  maintained_sources=sorted(name for name, path in sources.items() if path.parent == HERE),
                  dependency_command=dependency_command, flags=GATEWAY.flags(),
                  replay_tool_sha256=GATEWAY.sha(Path(__file__)),
                  profile_sha256=GATEWAY.sha(ROOT / 'm4/bridge/profile.py'),
                  lock_sha256=GATEWAY.sha(ROOT / 'm4/bridge/toolchain-lock.json'))
    (directory / 'inputs.json').write_text(json.dumps(inputs, indent=2, sort_keys=True) + '\n')
    pending, running, completed, failures = set(sources), {}, {}, {}
    reused = set()
    if reuse is not None:
        reuse = reuse.resolve()
        previous = json.loads(reuse.read_text())
        previous_inputs = json.loads((reuse.parent / 'inputs.json').read_text())
        if previous.get('status') != 'passed' or previous['inputs_sha256'] != GATEWAY.sha(reuse.parent / 'inputs.json'):
            raise ValueError('Cannot reuse a failed or changed source replay')
        for name in ('flags', 'profile_sha256', 'lock_sha256'):
            if previous_inputs[name] != inputs[name]:
                raise ValueError('Cannot reuse different proof environment: ' + name)
        for name, row in previous['completed'].items():
            if name in frozen and row['source'] == frozen[name] and row['object'] == GATEWAY.sha(GATEWAY.WORK / (name + '.vo')):
                reused.add(name)
        while True:
            kept = {name for name in reused if set(dependencies[name]) <= reused}
            if kept == reused:
                break
            reused = kept
        for name in reused:
            completed[name] = dict(previous['completed'][name], reused_from=str(reuse.relative_to(ROOT)))
            pending.remove(name)
    started = time.monotonic()

    def one(name):
        if GATEWAY.sha(sources[name]) != frozen[name]:
            raise ValueError('Source drift before compilation: ' + name)
        GATEWAY.compile_file(name)
        log = GATEWAY.WORK / (name + '.log')
        shutil.copyfile(log, directory / (name + '.log'))
        return dict(source=frozen[name], object=GATEWAY.sha(GATEWAY.WORK / (name + '.vo')))

    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        while pending or running:
            if not failures:
                ready = sorted(name for name in pending if set(dependencies[name]) <= completed.keys())
                for name in ready[:workers - len(running)]:
                    pending.remove(name)
                    running[pool.submit(one, name)] = name
            if not running:
                break
            done, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                try:
                    completed[name] = future.result()
                except Exception as error:
                    failures[name] = repr(error)
    def input_drift():
        def digest(path):
            return GATEWAY.sha(path) if path.is_file() else None
        changed = [name for name, source in sources.items() if digest(source) != frozen[name]]
        changed += ['compiled-source:' + name for name in sources
                    if digest(GATEWAY.WORK / (name + '.v')) != frozen[name]]
        changed += ['object:' + name for name, row in completed.items()
                    if digest(GATEWAY.WORK / (name + '.vo')) != row['object']]
        maintained = {path.stem for path in HERE.glob('*.v') if path.stem not in excluded}
        changed += ['inventory-added:' + name for name in maintained - set(inputs['maintained_sources'])]
        changed += ['inventory-removed:' + name for name in set(inputs['maintained_sources']) - maintained]
        return sorted(set(changed))

    drift = input_drift()
    result = dict(schema='leancage-host-source-replay-v1', partial=bool(excluded), reason=reason,
                  excluded=sorted(excluded), completed=completed, failed=failures, blocked=sorted(pending),
                  input_drift=drift, seconds=round(time.monotonic() - started, 2),
                  reused=sorted(reused),
                  inputs_sha256=GATEWAY.sha(directory / 'inputs.json'))
    if not failures and not pending and not drift:
        aggregate_name = 'GatewaySourceReplay_' + stamp
        aggregate = GATEWAY.WORK / (aggregate_name + '.v')
        aggregate.write_text('From HostGateway Require Import ' + ' '.join(sorted(sources)) + '.\n')
        error = recorded_phase(['rocq', 'c', '-q', *GATEWAY.flags(), str(aggregate)], directory / 'aggregate.log')
        command = ['rocq', 'check', '-silent', *GATEWAY.flags(checker=True), 'HostGateway.' + aggregate_name]
        if error is None:
            error = recorded_phase(command, directory / 'kernel-check.log')
        result.update(input_drift=input_drift(), checker_command=command)
        if error is None and not result['input_drift']:
            result.update(status='passed', aggregate_object_sha256=GATEWAY.sha(aggregate.with_suffix('.vo')),
                          checker_stdout_sha256=GATEWAY.sha(directory / 'kernel-check.log'))
        else:
            result.update(status='failed', aggregate_error=error)
    else:
        result['status'] = 'failed'
    (directory / 'result.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(dict(directory=str(directory), status=result['status'], completed=len(completed),
                          failed=failures, aggregate_error=result.get('aggregate_error'),
                          input_drift=result['input_drift'], blocked=len(pending), excluded=sorted(excluded), seconds=result['seconds'])))
    if result['status'] != 'passed':
        raise SystemExit(1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exclude', action='append', default=[])
    parser.add_argument('--reason', required=True)
    parser.add_argument('--workers', type=int, choices=range(1, 5), default=4)
    parser.add_argument('--reuse', type=Path, help='reuse only an exactly matching checked source/object/dependency closure')
    args = parser.parse_args()
    replay(set(args.exclude), args.reason, args.workers, args.reuse)


if __name__ == '__main__':
    main()
