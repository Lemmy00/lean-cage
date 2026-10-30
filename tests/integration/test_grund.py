"""Exercise the project's source citation profiles with the actual pinned tool."""

# §AR-tooling.checks: Test discovery, failed resolution, and dependency exclusions.

import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


PROJECT = Path(__file__).resolve().parents[2]
MARKER = chr(167)


class GrundLeanIntegration(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="leancage-grund-")
        self.addCleanup(self.temp.cleanup)
        self.fixture = Path(self.temp.name)
        for name in ("grund.toml", "AGENTS.md", ".gitignore"):
            shutil.copy2(PROJECT / name, self.fixture / name)
        shutil.copytree(PROJECT / "docs", self.fixture / "docs")

    def grund(self, *args):
        return subprocess.run(
            [str(PROJECT / "scripts/grund.sh"), *args],
            cwd=PROJECT,
            capture_output=True,
            text=True,
            timeout=60,
        )

    def check_fixture(self):
        return self.grund("check", "--full", str(self.fixture))

    def write_probe(self, path, coordinate):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            f"-- {MARKER}{coordinate}: Check the configured Lean comment reader.\n",
            encoding="utf-8",
        )

    def test_lean_citation_is_discovered(self):
        self.write_probe(self.fixture / "Probe.lean", "AR-tooling.checks")
        check = self.check_fixture()
        self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
        refs = self.grund("refs", "AR-tooling.checks", str(self.fixture), "--format", "json")
        self.assertEqual(refs.returncode, 0, refs.stderr)
        sites = [json.loads(line) for line in refs.stdout.splitlines() if line.strip()]
        self.assertTrue(
            any(site["path"] == "Probe.lean" and site["section"] == "checks" for site in sites),
            refs.stdout,
        )

    def test_dangling_lean_citation_fails(self):
        baseline = self.check_fixture()
        self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
        self.write_probe(self.fixture / "Probe.lean", "FS-missing-fixture-contract")
        check = self.check_fixture()
        self.assertEqual(check.returncode, 1, check.stdout + check.stderr)
        self.assertIn("FS-missing-fixture-contract", check.stdout + check.stderr)
        self.assertIn("Probe.lean", check.stdout + check.stderr)

    def test_c_citations_are_discovered_and_dangling_citations_fail(self):
        probe = self.fixture / "Probe.c"
        probe.write_text(f"// {MARKER}AR-m1-launch.binding: Native boundary.\n")
        check = self.check_fixture()
        self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
        refs = self.grund("refs", "AR-m1-launch.binding", str(self.fixture), "--format", "json")
        self.assertEqual(refs.returncode, 0, refs.stderr)
        self.assertTrue(any(json.loads(line)["path"] == "Probe.c"
                            for line in refs.stdout.splitlines() if line.strip()), refs.stdout)
        probe.write_text(f"// {MARKER}AR-missing-native-fixture: Must fail.\n")
        check = self.check_fixture()
        self.assertEqual(check.returncode, 1, check.stdout + check.stderr)
        self.assertIn("AR-missing-native-fixture", check.stdout + check.stderr)

    def test_dependency_sources_are_excluded(self):
        for directory in (".lake/packages/vendor", ".tools/vendor"):
            self.write_probe(self.fixture / directory / "Probe.lean", "FS-missing-vendor-contract")
        check = self.check_fixture()
        self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
        self.assertNotIn("FS-missing-vendor-contract", check.stdout + check.stderr)


if __name__ == "__main__":
    unittest.main()
