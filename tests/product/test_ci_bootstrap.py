"""Keep metadata validation usable before generated proof artifacts exist."""
# §AR-workspace-vm.migration: Freeze expected artifacts; their owning gates check actual bytes.
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('ci_bootstrap_evidence', ROOT / 'scripts/rebind_product_evidence.py')
evidence = importlib.util.module_from_spec(spec)
spec.loader.exec_module(evidence)


class MetadataBootstrap(unittest.TestCase):
    def test_missing_generated_artifacts_preserve_the_original_expected_hashes(self):
        expected = {'.tools/proof.vo': 'a' * 64, '.lake/build/lib/lean/Model.olean': 'b' * 64,
                    '/external/sdk/header.h': 'c' * 64}
        original = {'inputs_sha256': expected, 'declarations': ['original theorem']}
        with tempfile.TemporaryDirectory() as directory, patch.object(evidence, 'ROOT', Path(directory)):
            fingerprint = evidence.current_fingerprints('record', original, {}, {}, {}, {}, {})
            result, changes = evidence.amended(original, fingerprint)
        self.assertEqual(result, original)
        self.assertEqual(changes, {})

    def test_sealed_cache_observations_are_preserved_without_a_rebuilt_cache(self):
        name = next(iter(evidence.CACHE_INPUTS))
        raw = b'fixture-sealed-compiled-bytes'
        expected = hashlib.sha256(raw).hexdigest()
        binding = dict(preserved_sha256=expected, current_sha256='d' * 64)
        observations = {evidence.CACHE_RECORD: {name: binding}}
        historical = {}
        original = {'inputs_sha256': {name: expected}}
        with tempfile.TemporaryDirectory() as directory, patch.object(evidence, 'ROOT', Path(directory)):
            fingerprint = evidence.current_fingerprints(evidence.CACHE_RECORD, original, {},
                                                        {name: raw}, {}, historical, observations)
            self.assertEqual(fingerprint(name), expected)
        self.assertEqual(historical, observations)

    def test_changed_sealed_bytes_or_malformed_observations_fail(self):
        name = next(iter(evidence.CACHE_INPUTS))
        raw = b'sealed'
        expected = hashlib.sha256(raw).hexdigest()
        original = {'inputs_sha256': {name: expected}}
        for cached, observed in ((b'changed', 'd' * 64), (raw, 'not-a-sha256')):
            with self.subTest(cached=cached, observed=observed), tempfile.TemporaryDirectory() as directory, \
                    patch.object(evidence, 'ROOT', Path(directory)):
                observations = {evidence.CACHE_RECORD: {name: dict(preserved_sha256=expected,
                                                                 current_sha256=observed)}}
                fingerprint = evidence.current_fingerprints(evidence.CACHE_RECORD, original, {},
                                                            {name: cached}, {}, {}, observations)
                with self.assertRaises(ValueError):
                    fingerprint(name)

    def test_maintained_source_changes_still_fail(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(evidence, 'ROOT', Path(directory)):
            path = Path(directory) / 'maintained.v'
            path.write_bytes(b'changed source')
            original = {'inputs_sha256': {'maintained.v': hashlib.sha256(b'original source').hexdigest()}}
            fingerprint = evidence.current_fingerprints('record', original, {}, {}, {}, {}, {})
            with self.assertRaises(ValueError):
                evidence.amended(original, fingerprint)


if __name__ == '__main__':
    unittest.main()
