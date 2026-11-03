"""Protect proof payloads when rebinding the product status document."""
# §AR-workspace-vm.migration: Documentation maintenance cannot approve a changed theorem or binary.
import importlib.util
import copy
import json
from pathlib import Path
import unittest

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


if __name__ == "__main__":
    unittest.main()
