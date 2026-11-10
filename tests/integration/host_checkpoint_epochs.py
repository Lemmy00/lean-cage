#!/usr/bin/env python3
"""Reject changed source/type/archive bytes while retaining explicit native repairs."""
# §AR-host-boundary.acceptance: Negative metadata checks preserve the reviewed scope.
import importlib.util
import argparse
import copy
import gzip
import json
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("host_checkpoint_epochs", ROOT / "verification/host/checkpoint.py")
checkpoint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checkpoint)
CHAIN = [
    dict(name=name, functions=functions, amendment=f"assurance/host-{name}-source-amendment.json",
         after_source=f"assurance/host-{name}-current.c.gz", after_program=f"assurance/host-{name}-source-program.v.gz")
    for name, functions in [("observation", ["host_outcome_observation"]),
                            ("outcome", ["host_outcome_from", "host_outcome_json"])]]


def mirror(destination, record=None):
    paths = set((ROOT / "assurance").glob("host-*.json")) | set((ROOT / "assurance").glob("host-*.gz"))
    paths |= {ROOT / "linux/host_python.c", ROOT / "verification/host/GatewayObservationSourceRepair.v",
              ROOT / "verification/host/GatewayOutcomeSourceRepair.v"}
    offset = json.loads((ROOT / "assurance/host-file-copy-offset-amendment.json").read_text())
    paths |= {ROOT / name for name in offset["source_sha256"]}
    eof = json.loads((ROOT / 'assurance/host-source-eof-amendment.json').read_text())
    paths |= {ROOT / name for name in eof['sources']}
    if record is not None:
        paths |= {ROOT / name for name in record["sources"]}
        paths |= {ROOT / name for name in record["archives_and_reviews"]}
        paths |= {ROOT / "m4/bridge/profile.py", ROOT / "m4/bridge/toolchain-lock.json"}
    for path in paths:
        target = destination / path.relative_to(ROOT)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.symlink_to(path)


def changed(root, name, transform):
    path = root / name
    before = path.read_bytes()
    after = transform(before)
    assert before != after
    path.unlink()
    path.write_bytes(after)


def validate(root):
    checkpoint.verify_native_epochs(CHAIN, root)
    checkpoint.verify_copy_offsets("assurance/host-file-copy-offset-amendment.json", root)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path, help='also test the complete active checkpoint inventory/replay binding')
    args = parser.parse_args()
    tests = {
        "unreviewed gateway source": ("linux/host_python.c", lambda data: data + b"\n/* unreviewed */\n"),
        "changed retained theorem statement": (
            "verification/host/GatewayOutcomeSourceRepair.v",
            lambda data: data.replace(b"GatewayOutcomeBeforeSource.composites =", b"GatewayOutcomeBeforeSource.composites <>", 1)),
        "changed generated source archive": ("assurance/host-outcome-source-program.v.gz", lambda data: data + b"changed"),
        "unreviewed filesystem primitive": ("linux/host_primitives.c", lambda data: data + b"\n/* unreviewed */\n"),
        "body edit disguised as EOF cleanup": (
            "verification/host/GatewayOutcomeEntry.v", lambda data: b"(* unreviewed prefix *)\n" + data),
    }
    with tempfile.TemporaryDirectory(prefix="leancage-checkpoint-epochs-") as directory:
        base = Path(directory)
        good = base / "good"
        mirror(good)
        validate(good)
        for index, (label, (name, mutate)) in enumerate(tests.items()):
            root = base / str(index)
            mirror(root)
            changed(root, name, mutate)
            try:
                validate(root)
            except (ValueError, OSError) as error:
                assert str(error), label
            else:
                raise AssertionError("metadata gate admitted " + label)
        if args.record:
            record = json.loads(args.record.read_text())
            complete = base / 'complete'
            mirror(complete, record)
            checkpoint.verify_record(record, complete)
            for label in ('changed proof with updated outer hash', 'removed proof with updated outer inventory',
                          'partial replay with updated archive hash', 'changed replay tool with updated outer hash',
                          'delivery promotion'):
                root = base / label.replace(' ', '-')
                mirror(root, record)
                candidate = copy.deepcopy(record)
                proof = 'verification/host/GatewayValidationEntry.v'
                if label.startswith('changed proof'):
                    changed(root, proof, lambda data: data.replace(b'events = prefix ++', b'events <> prefix ++', 1))
                    candidate['sources'][proof] = checkpoint.digest((root / proof).read_bytes())
                elif label.startswith('removed proof'):
                    (root / proof).unlink()
                    del candidate['sources'][proof]
                elif label.startswith('partial replay'):
                    path = candidate['rocq_source_replay']['result']
                    payload = json.loads(gzip.decompress((root / path).read_bytes()))
                    payload['partial'] = True
                    changed(root, path, lambda _: gzip.compress(json.dumps(payload).encode(), mtime=0))
                    candidate['archives_and_reviews'][path] = checkpoint.digest((root / path).read_bytes())
                elif label.startswith('changed replay tool'):
                    path = 'verification/host/source_replay.py'
                    changed(root, path, lambda data: data + b'\n# changed replay algorithm\n')
                    candidate['sources'][path] = checkpoint.digest((root / path).read_bytes())
                else:
                    candidate['delivery'] = 'M5.2 complete'
                try:
                    checkpoint.verify_record(candidate, root)
                except (ValueError, OSError) as error:
                    assert str(error), label
                else:
                    raise AssertionError('active checkpoint admitted ' + label)
    print("Native epoch chain and positional-read amendment accepted; source/type/archive mutations rejected.")


if __name__ == "__main__":
    main()
