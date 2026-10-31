# §AR-m4-bridge.import: Reject altered statements, omitted inputs and unknown foundations.
import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check as gate


class BridgeGateTests(unittest.TestCase):
    def test_unreviewed_axiom_rejected(self):
        with self.assertRaisesRegex(ValueError, 'unreviewed'):
            gate.foundations('Axioms:\nInjected : False')

    def test_unreviewed_uip_rejected(self):
        with self.assertRaisesRegex(ValueError, 'unreviewed'):
            gate.foundations('Axioms:\nSneaky relies on definitional UIP.')

    def test_primed_axiom_is_not_silently_omitted(self):
        with self.assertRaisesRegex(ValueError, 'unreviewed'):
            gate.foundations("Axioms:\nInjected' : False")

    def test_unknown_report_format_is_not_treated_as_closed(self):
        with self.assertRaisesRegex(ValueError, 'unrecognized'):
            gate.foundations('Unexpected checker message')

    def test_altered_statement_rejected(self):
        expected = {key: [{'name': 'x', 'full_type': 'True'}]
                    for key in ['rocq_declarations', 'lean_declarations', 'imported_endpoint', 'export_inventory']}
        actual = copy.deepcopy(expected)
        actual['rocq_declarations'][0]['full_type'] = 'False'
        with self.assertRaisesRegex(ValueError, 'statement'):
            gate.validate_claims(expected, actual)

    def test_missing_module_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(gate, 'DIRECTORY', Path(directory)):
                with self.assertRaisesRegex(ValueError, 'unlisted'):
                    gate.inventory()

    def test_truncated_export_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'export.ndjson'
            path.write_text('{"meta": {"lean": {"version": "4.35.0"}}}\n')
            with self.assertRaisesRegex(ValueError, 'missing actual'):
                gate.export_inventory(path)


if __name__ == '__main__':
    unittest.main()
