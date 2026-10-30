"""Reject stale, weakened, forged and incomplete M2 evidence without launching a guest."""
# §AR-lifecycle.audit: Archived evidence must validate the actual observations and complete profile.
import copy
import importlib.util
import json
from pathlib import Path
import unittest
from unittest import mock

PROJECT=Path(__file__).resolve().parents[3]
SPEC=importlib.util.spec_from_file_location('m2_vm',PROJECT/'scripts/run_m2_vm.py')
VM=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(VM)


class Evidence(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.evidence=json.loads(VM.EVIDENCE.read_text())
        cls.transcript=VM.TRANSCRIPT.read_text()

    def test_complete_source_bound_record(self):
        VM.validate_evidence(self.evidence)
        self.assertEqual(len(VM.validate_transcript(self.transcript,33)),len(VM.EXPECTED))

    def test_archive_is_independent_of_current_checkout(self):
        relocated=Path('/tmp/leancage-other-checkout')
        sources=VM.source_identities()
        with mock.patch.object(VM,'PROJECT',relocated), mock.patch.object(VM,'WORK',relocated/'.tools/m2vm'), \
             mock.patch.object(VM.M1,'WORK',relocated/'.tools/m1vm'), \
             mock.patch.object(VM,'source_identities',return_value=sources):
            VM.validate_evidence(self.evidence)

    def test_mixed_recording_roots_are_rejected(self):
        for flag in ('-L','-bios','-kernel','-initrd'):
            altered=copy.deepcopy(self.evidence)
            position=altered['command'].index(flag)+1
            altered['command'][position]='/tmp/another-recording/'+Path(altered['command'][position]).name
            with self.subTest(flag=flag),self.assertRaises(ValueError):VM.validate_evidence(altered)
        altered=copy.deepcopy(self.evidence)
        altered['environment']['QEMU_MODULE_DIR']='/tmp/another-recording/modules'
        with self.assertRaises(ValueError):VM.validate_evidence(altered)

    def test_current_artifacts_resolve_to_current_checkout(self):
        relocated=Path('/tmp/leancage-other-checkout')
        recorded_project,_=VM.recorded_layout(self.evidence['command'])
        sources=VM.source_identities()
        with mock.patch.object(VM,'PROJECT',relocated), \
             mock.patch.object(VM,'source_identities',return_value=sources), \
             mock.patch.object(VM.M1,'check_hash') as check:
            VM.check_evidence(True)
        observed={args.args[0]:args.args[1] for args in check.call_args_list}
        self.assertEqual(len(observed),len(self.evidence['artifacts_sha256']))
        for path,digest in self.evidence['artifacts_sha256'].items():
            recorded=Path(path)
            expected=relocated/recorded.relative_to(recorded_project) if recorded.is_relative_to(recorded_project) else recorded
            self.assertEqual(observed[expected],digest)

    def test_missing_or_duplicate_cases_and_guest_markers(self):
        for text in (self.transcript+self.transcript,
                     self.transcript.replace('M2_CASE_BEGIN name=allowed\n','',1),
                     self.transcript.replace(VM.GUEST,'M2_GUEST check=failed',1),
                     self.transcript+VM.GUEST+'\n'):
            with self.subTest(text=text[:40]),self.assertRaises(ValueError):VM.validate_transcript(text,33)

    def test_no_guest_entry_after_rejection(self):
        for name in ('empty','permissive','handles_failure','filter_failure','error_drop','cancel_before'):
            text=self.transcript.replace(f'M2_CASE_BEGIN name={name}\n',f'M2_CASE_BEGIN name={name}\n'+VM.GUEST+'\n')
            with self.subTest(name=name),self.assertRaises(ValueError):VM.validate_transcript(text,33)

    def test_exit125_is_not_a_setup_error(self):
        text=self.transcript.replace('M2_RESULT kind=0 phase=0 detail=125 entry=1 clean=1',
                                     'M2_RESULT kind=1 phase=8 detail=125 entry=0 clean=1')
        with self.assertRaises(ValueError):VM.validate_transcript(text,33)

    def test_lost_report_never_becomes_exec_success(self):
        text=self.transcript.replace('M2_RESULT kind=4 phase=9 detail=71 entry=2 clean=1',
                                     'M2_RESULT kind=0 phase=0 detail=0 entry=1 clean=1',1)
        with self.assertRaises(ValueError):VM.validate_transcript(text,33)

    def test_cancellation_requires_observed_cleanup_and_sentinel_survival(self):
        for old,new in (('owned_gone=1','owned_gone=0'),('sentinel_alive=1','sentinel_alive=0'),
                        ('kind=3 phase=0 detail=0 entry=1 clean=1','kind=3 phase=0 detail=0 entry=1 clean=0')):
            with self.subTest(field=old),self.assertRaises(ValueError):VM.validate_transcript(self.transcript.replace(old,new,1),33)

    def test_positive_controls_are_required(self):
        for field in ('namespaces','unix','inet','sysvipc','cgroup_cpu_memory_pids'):
            with self.subTest(field=field),self.assertRaises(ValueError):
                VM.validate_transcript(self.transcript.replace(field+'=present',field+'=absent',1),33)

    def test_timeout_infrastructure_failure_or_wrong_profile_fails(self):
        for code in (0,1,35,-9):
            with self.subTest(code=code),self.assertRaises(ValueError):VM.validate_transcript(self.transcript,code)
        with self.assertRaises(ValueError):VM.validate_transcript(self.transcript.replace(VM.PROFILE,'m1-profile'),33)

    def test_every_top_level_field_is_required(self):
        for field in self.evidence:
            altered=copy.deepcopy(self.evidence);del altered[field]
            with self.subTest(field=field),self.assertRaises(ValueError):VM.validate_evidence(altered)

    def test_incomplete_profile_artifacts_and_runtime_are_rejected(self):
        changes=[('kernel',{}),('machine',{}),('guest_files',{}),('tools',{}),('artifacts_sha256',{}),
                 ('command',['qemu','-nic','none','-kernel','unrecorded','-initrd','unrecorded']),
                 ('environment',{}),('virtual_cpu',[]),('assumptions',[])]
        for key,value in changes:
            altered=copy.deepcopy(self.evidence);altered[key]=value
            with self.subTest(field=key),self.assertRaises(ValueError):VM.validate_evidence(altered)

    def test_stale_sources_fail(self):
        with mock.patch.object(VM,'source_identities',return_value={}):
            with self.assertRaises(ValueError):VM.validate_evidence(self.evidence)

    def test_artifact_mode_compares_current_files(self):
        with mock.patch.object(VM.M1,'check_hash',side_effect=ValueError('changed artifact')):
            with self.assertRaisesRegex(ValueError,'changed artifact'):VM.check_evidence(True)


if __name__=='__main__':unittest.main()
