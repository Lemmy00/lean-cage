"""Public commands over the same Workspace API used by integrations."""
# §FS-linux-product.operation: Caller-owned policies, bounded snapshots and retrieved results.
import argparse
import json
from pathlib import Path
import signal
import sys

from .build import DEFAULT_BUNDLE
from .runner import Workspace, Cancellation


def main(argv=None):
    parser = argparse.ArgumentParser(prog="leancage", description="Run offline shell and Python tasks in a disposable Linux workspace.")
    parser.add_argument("--bundle", type=Path, default=DEFAULT_BUNDLE)
    parser.add_argument("--results", type=Path)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("check", "run"):
        command = commands.add_parser(name)
        command.add_argument("policy", type=Path)
        command.add_argument("--workspace", type=Path)
        command.add_argument("--stdin", type=Path)
        command.add_argument("--output", type=Path)
        command.add_argument("--timeout", type=float)
    command = commands.add_parser("validate-policy")
    command.add_argument("policy", type=Path)
    command = commands.add_parser("report")
    command.add_argument("request", help="request identity or returned result directory")
    commands.add_parser("bundle")
    args = parser.parse_args(argv)
    try:
        workspace = Workspace(args.bundle, args.results)
        if args.command == "bundle":
            print(json.dumps({"bundle_id": workspace.bundle_id, "manifest": str(workspace.bundle / "manifest.json")}, sort_keys=True))
            return 0
        if args.command == "validate-policy":
            workspace.validate(args.policy)
            print("valid policy")
            return 0
        if args.command == "report":
            print(json.dumps(workspace.report(args.request), sort_keys=True))
            return 0
        cancellation = Cancellation()
        previous = {number: signal.signal(number, lambda *_: cancellation.cancel()) for number in (signal.SIGINT, signal.SIGTERM)}
        try:
            result = getattr(workspace, args.command)(args.policy, workspace=args.workspace, stdin=args.stdin,
                                                       output=args.output, cancellation=cancellation, timeout=args.timeout)
        finally:
            for number, handler in previous.items():
                signal.signal(number, handler)
        print(json.dumps(result.json(), sort_keys=True))
        return result.exit_code
    except (OSError, ValueError, TimeoutError) as error:
        print(json.dumps({"status": "rejected", "entry": "no", "error": str(error)}, sort_keys=True))
        return 64


if __name__ == "__main__":
    sys.exit(main())
