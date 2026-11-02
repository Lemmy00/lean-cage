"""Navigation changes cannot smuggle theorem or artifact changes into old evidence."""
# SPDX-License-Identifier: Apache-2.0
# §AR-m4-parent.audit: Preserve old statements while amending only document/dependency hashes.
import copy
import gzip
import json
from pathlib import Path
import shutil
import tempfile
import unittest
import amendment


class NavigationAmendmentTests(unittest.TestCase):
    def test_current_amendment(self):
        amendment.check()

    def test_unamended_proof_change(self):
        record = amendment.validate()
        with self.assertRaises(ValueError):
            amendment.validate_candidate_sources({'m4/parent-checkpoint/ParentMachine.v': 'a'},
                                                 {'m4/parent-checkpoint/ParentMachine.v': 'b'}, record)

    def test_changed_inventory(self):
        record = copy.deepcopy(amendment.validate())
        record['files'].pop(next(iter(record['files'])))
        with self.assertRaises(ValueError):
            amendment.validate(record=record)

    def test_forged_after_hash_does_not_allow_statement_change(self):
        record = copy.deepcopy(amendment.validate())
        original = json.loads(gzip.decompress(amendment.BEFORE.read_bytes()))
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for path in record['files']:
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(amendment.ROOT / path, target)
            path = 'assurance/m4-connection-claims.json'
            changed = json.loads((root / path).read_text())
            changed['rocq_declarations'][0]['full_type'] = 'fabricated security proposition'
            (root / path).write_text(json.dumps(changed))
            record['files'][path]['after_sha256'] = amendment.sha((root / path).read_bytes())
            with self.assertRaises(ValueError):
                amendment.validate(record=record, original=original, root=root)


if __name__ == '__main__':
    unittest.main()
