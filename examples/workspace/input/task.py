from pathlib import Path
import json
import sys

numbers = [int(value) for value in Path("numbers.txt").read_text().split()]
answer = {"sum": sum(numbers), "stdin": sys.stdin.read().strip()}
Path("summary.json").write_text(json.dumps(answer, sort_keys=True) + "\n")
print("python-workflow")
print("python-stderr", file=sys.stderr)
