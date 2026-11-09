"""Protect proof payloads when rebinding the product status document."""
# §AR-workspace-vm.migration: Documentation maintenance cannot approve a changed theorem or binary.
import importlib.util
import copy
import json
import gzip
import base64
import hashlib
from pathlib import Path
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("product_evidence", ROOT / "scripts/rebind_product_evidence.py")
evidence = importlib.util.module_from_spec(spec)
spec.loader.exec_module(evidence)


class EvidenceMigration(unittest.TestCase):
    def test_replayed_preimage_preserves_the_actual_reporting_proof(self):
        name = "assurance/reporting-source.json.gz"
        current = evidence.decode(name, (ROOT / name).read_bytes())
        entry = json.loads(evidence.RECORD.read_text())["entries"][name]
        previous = copy.deepcopy(current)
        for group, bindings in entry["changes"].items():
            for key, binding in bindings.items():
                previous[group][key] = binding["before"]
        self.assertEqual(evidence.replay(name, previous), current)
        changed = copy.deepcopy(previous)
        changed["full_m4_complete"] = True
        with self.assertRaises(ValueError):
            evidence.replay(name, changed)
        changed = copy.deepcopy(previous)
        group = next(iter(entry["changes"]))
        key = next(iter(entry["changes"][group]))
        changed[group][key] = "an-unreviewed-preimage"
        with self.assertRaises(ValueError):
            evidence.replay(name, changed)

    def test_only_enumerated_operational_inputs_can_change(self):
        value = {"source_sha256": {"docs/functional-spec/FS-assurance.md": "before", "linux/workspace.c": "code"},
                 "declarations": [{"type": "original proposition", "axioms": ["propext"]}]}
        result, changes = evidence.amended(value, lambda key: "after" if key.endswith("FS-assurance.md") else "code")
        self.assertEqual(result["declarations"], value["declarations"])
        self.assertEqual(evidence.mask(result, changes), evidence.mask(value, changes))
        with self.assertRaises(ValueError):
            evidence.amended(value, lambda _: "different")

    def test_theorem_axiom_scope_and_cache_changes_remain_visible(self):
        original = {"declarations": [{"type": "original", "axioms": []}], "scope": "conditional",
                    "dependency_sha256": {"checked.olean": "same"},
                    "source_sha256": {"docs/functional-spec/FS-assurance.md": "before"}}
        _, changes = evidence.amended(original, lambda _: "after")
        for altered in ({**original, "declarations": [{"type": "weaker", "axioms": []}]},
                        {**original, "declarations": [{"type": "original", "axioms": ["sorryAx"]}]},
                        {**original, "scope": "unconditional"},
                        {**original, "dependency_sha256": {"checked.olean": "different"}}):
            self.assertNotEqual(evidence.mask(original, changes), evidence.mask(altered, changes))


class CompilerAmendmentPreimage(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location("compiler_amendment_preimage", ROOT / "verification/compiler/amendment.py")
        cls.amendment = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.amendment)

    def previous(self):
        archive = json.loads(gzip.decompress((ROOT / "assurance/reporting-connection-before.json.gz").read_bytes()))
        value = json.loads(gzip.decompress(base64.b64decode(archive[self.amendment.SOURCE])))
        for name in ("scripts/check_reporting.sh", "verification/reporting/README.md"):
            self.assertEqual(value["inputs_sha256"][name], hashlib.sha256(base64.b64decode(archive[name])).hexdigest())
            value["inputs_sha256"][name] = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
        return value

    def test_exact_current_readme_composes_with_the_preserved_preimage(self):
        previous = self.previous()
        unchanged = copy.deepcopy(previous)
        expected = json.loads(gzip.decompress((ROOT / self.amendment.SOURCE).read_bytes()))
        self.assertEqual(self.amendment.adjust_source(previous), expected)
        self.assertEqual(previous, unchanged)

    def test_other_fingerprint_scope_type_axiom_and_cache_changes_fail(self):
        previous = self.previous()
        variants = []
        for field, value in (("full_m4_complete", True), ("ordinary_lean_security_claim", True)):
            changed = copy.deepcopy(previous)
            changed[field] = value
            variants.append(changed)
        for group in ("cache_sha256", "dependency_sha256"):
            changed = copy.deepcopy(previous)
            changed[group][next(iter(changed[group]))] = "changed-proof-cache"
            variants.append(changed)
        for field, value in (("full_type", "weaker proposition"), ("assumption_names", ["sorryAx"])):
            changed = copy.deepcopy(previous)
            rows = next(rows for rows in changed["declarations"].values() if rows)
            rows[0][field] = value
            variants.append(changed)
        changed = copy.deepcopy(previous)
        changed["inputs_sha256"]["scripts/check_reporting.sh"] = "unreviewed-gate"
        variants.append(changed)
        changed = copy.deepcopy(previous)
        changed["inputs_sha256"][self.amendment.HISTORICAL_METADATA] = "unreviewed-readme"
        variants.append(changed)
        for changed in variants:
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                self.amendment.adjust_source(changed)

    def test_archived_readme_must_match_the_saved_expected_preimage(self):
        migration = self.amendment.product_evidence()
        preserved, binding = migration.preserved_inputs()
        altered = dict(preserved)
        altered[self.amendment.HISTORICAL_METADATA] += b"changed"
        with patch.object(self.amendment, "product_evidence", return_value=migration), \
                patch.object(migration, "check"), \
                patch.object(migration, "preserved_inputs", return_value=(altered, binding)), \
                self.assertRaises(ValueError):
            self.amendment.adjust_source(self.previous())


class PreservedHistoricalInputs(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location("compiler_preserved_inputs", ROOT / "verification/compiler/amendment.py")
        cls.amendment = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.amendment)

    def test_exact_sources_and_both_sealed_compiled_inputs_are_checked(self):
        verifier = self.amendment.PreservedInputs()
        _, connection = evidence.original_record(self.amendment.CONNECTION)
        for name in ("native/leancage_m3.c", "verification/reporting/README.md"):
            self.assertTrue(verifier.verify(self.amendment.CONNECTION, "source_sha256", name,
                                            connection["source_sha256"][name]))
        for name in evidence.CACHE_INPUTS:
            self.assertTrue(verifier.verify(self.amendment.CONNECTION, "cache_sha256", name,
                                            connection["cache_sha256"][name]))
            self.assertTrue(verifier.verify(self.amendment.COMPILER_RECORD, "inputs_sha256", name,
                                            evidence.CACHE_INPUTS[name]))
        name = str(ROOT / self.amendment.HISTORICAL_HOST_SOURCE)
        self.assertTrue(verifier.verify(self.amendment.CONNECTION, "host_inputs_sha256", name,
                                        connection["host_inputs_sha256"][name]))
        name = next(name for name in connection["cache_sha256"] if name.endswith(".vo"))
        self.assertFalse(verifier.verify(self.amendment.CONNECTION, "cache_sha256", name,
                                         connection["cache_sha256"][name]))
        self.assertTrue(verifier.used)

    def test_unapproved_key_record_group_and_expected_hash_are_rejected(self):
        verifier = self.amendment.PreservedInputs()
        _, connection = evidence.original_record(self.amendment.CONNECTION)
        name = "native/leancage_m3.c"
        expected = connection["source_sha256"][name]
        cases = [("unreviewed-record", "source_sha256", name, expected),
                 (self.amendment.CONNECTION, "cache_sha256", name, expected),
                 (self.amendment.CONNECTION, "source_sha256", name, "unreviewed-hash"),
                 (self.amendment.CONNECTION, "source_sha256", str(ROOT / name), expected),
                 (self.amendment.CONNECTION, "host_inputs_sha256", "/usr/include/errno.h", expected),
                 (self.amendment.CONNECTION, "source_sha256", "native/../native/leancage_m3.c", expected)]
        for record, group, key, value in cases:
            with self.subTest(record=record, group=group, key=key), self.assertRaises(ValueError):
                verifier.verify(record, group, key, value)

    def test_archive_bytes_and_exact_old_current_mapping_cannot_be_substituted(self):
        verifier = self.amendment.PreservedInputs()
        _, connection = evidence.original_record(self.amendment.CONNECTION)
        name = "verification/reporting/README.md"
        expected = connection["source_sha256"][name]
        verifier.verify(self.amendment.CONNECTION, "source_sha256", name, expected)
        sources = dict(verifier.sources)
        sources[name] += b"changed"
        with patch.object(verifier, "sources", sources), self.assertRaises(ValueError):
            verifier.verify(self.amendment.CONNECTION, "source_sha256", name, expected)
        bindings = copy.deepcopy(verifier.bindings)
        bindings["historical_inputs"][self.amendment.CONNECTION][name]["current_sha256"] = "changed"
        with patch.object(verifier, "bindings", bindings), self.assertRaises(ValueError):
            verifier.verify(self.amendment.CONNECTION, "source_sha256", name, expected)

    def test_changed_proof_artifact_cannot_use_an_archived_input_binding(self):
        _, connection = evidence.original_record(self.amendment.CONNECTION)
        name = next(name for name in connection["cache_sha256"] if name.endswith(".vo"))
        read_bytes = Path.read_bytes

        def changed(path):
            value = read_bytes(path)
            return value + b"changed" if path == ROOT / name else value

        with patch.object(Path, "read_bytes", changed), self.assertRaises(ValueError):
            self.amendment.PreservedInputs().verify(self.amendment.CONNECTION, "cache_sha256", name,
                                                    connection["cache_sha256"][name])

    def test_other_reporting_and_compiler_checker_edits_fail_exact_code_guards(self):
        read_text = Path.read_text
        for name in (self.amendment.CHECKER, self.amendment.COMPILER):
            def changed(path, *args, **kwargs):
                value = read_text(path, *args, **kwargs)
                return value + "\n# unreviewed checker edit\n" if path == ROOT / name else value

            with self.subTest(checker=name), patch.object(Path, "read_text", changed), self.assertRaises(ValueError):
                self.amendment.verify_code(self.amendment.preimages())


if __name__ == "__main__":
    unittest.main()
