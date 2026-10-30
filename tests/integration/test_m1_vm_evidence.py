"""Check that VM evidence requires actual successful/denied execution and failures."""

# §AR-m1-launch.vm: Malformed or incomplete execution evidence must never pass.

import importlib.util
from pathlib import Path
import unittest
from unittest import mock


PROJECT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("m1_vm", PROJECT / "scripts/run_m1_vm.py")
VM = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VM)


class M1VmEvidenceIntegration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.transcript = VM.TRANSCRIPT.read_text()

    def test_archived_observations_pass(self):
        cases = VM.validate_transcript(self.transcript, 33)
        self.assertEqual(len(cases), 13)
        self.assertEqual(sum(case["guest_observed"] for case in cases), 3)
        VM.check_evidence()

    def test_timeout_or_failed_vm_never_passes(self):
        for code in (-9, 0, 1, 35):
            with self.subTest(code=code), self.assertRaises(ValueError):
                VM.validate_transcript(self.transcript, code)

    def test_missing_allowed_or_denied_action_fails(self):
        for old, new in (("getpid_positive=1", "getpid_positive=0"),
                         ("getppid_raw=-1", "getppid_raw=110"),
                         ("nnp=1 seccomp=2", "nnp=0 seccomp=0")):
            with self.subTest(observation=old), self.assertRaises(ValueError):
                VM.validate_transcript(self.transcript.replace(old, new, 1), 33)

    def test_infrastructure_failure_is_not_denial(self):
        text = self.transcript.replace("M1_RESULT kind=1 phase=3 detail=22 receipts=3",
                                       "failed to create thread: Resource temporarily unavailable")
        with self.assertRaises(ValueError):
            VM.validate_transcript(text, 33)

    def test_wrong_errno_or_missing_receipt_fails(self):
        for old, new in (("phase=2 detail=22", "phase=2 detail=1"),
                         ("receipts=15", "receipts=3")):
            with self.subTest(observation=old), self.assertRaises(ValueError):
                VM.validate_transcript(self.transcript.replace(old, new), 33)

    def test_guest_execution_after_validation_failure_fails(self):
        text = self.transcript.replace("CASE_BEGIN name=empty\n", "CASE_BEGIN name=empty\n" + VM.GUEST + "\n")
        with self.assertRaises(ValueError):
            VM.validate_transcript(text, 33)

    def test_missing_or_duplicate_case_fails(self):
        for text in (self.transcript.replace("CASE_BEGIN name=empty\n", "", 1),
                     self.transcript + self.transcript):
            with self.assertRaises(ValueError):
                VM.validate_transcript(text, 33)

    def test_stale_source_identity_fails(self):
        with mock.patch.object(VM, "source_identities", return_value={}):
            with self.assertRaisesRegex(ValueError, "VM sources differ"):
                VM.check_evidence()


if __name__ == "__main__":
    unittest.main()
