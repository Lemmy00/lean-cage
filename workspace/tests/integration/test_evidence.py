"""Reject incomplete, forged, stale or mixed-root assurance records; never launch a workload."""
# §AR-workspace.acceptance: Historical checks must remain exact after a checkout move.
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

PROJECT=Path(__file__).resolve().parents[3]
spec=importlib.util.spec_from_file_location('m3_evidence_test',PROJECT/'scripts/run_m3_vm.py')
VM=importlib.util.module_from_spec(spec);spec.loader.exec_module(VM)

class Evidence(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.evidence=json.loads(VM.EVIDENCE.read_text())
        cls.text=VM.TRANSCRIPT.read_text()

    def test_complete_archived_record(self):
        VM.validate_evidence(self.evidence)

    def test_missing_duplicate_reordered_records_and_timeout(self):
        lines=self.text.splitlines(keepends=True)
        indices=[i for i,l in enumerate(lines) if l.startswith('M3_RESULT ')]
        variants=[lines[:indices[0]]+lines[indices[0]+1:],lines[:indices[0]]+[lines[indices[0]]]+lines[indices[0]:],lines[:-2]]
        swapped=list(lines);swapped[indices[0]],swapped[indices[1]]=swapped[indices[1]],swapped[indices[0]];variants.append(swapped)
        for text in variants:
            with self.subTest(),self.assertRaises(ValueError):VM.validate_transcript(''.join(text),33)
        with self.assertRaises(ValueError):VM.validate_transcript(self.text,0)

    def mutate_result(self,name,key,value):
        return self.mutate_fields(name,{key:value})

    def mutate_fields(self,name,fields):
        result=[]
        for line in self.text.splitlines():
            if line.startswith('M3_RESULT '):
                row=json.loads(line[len('M3_RESULT '):])
                if row['name']==name:row.update(fields);line='M3_RESULT '+json.dumps(row)
            result.append(line)
        return '\n'.join(result)+'\n'

    def test_cancel_race_keeps_observed_kill_and_required_facts(self):
        fields=dict(kind=2,detail=9,exit=137)
        VM.validate_transcript(self.mutate_fields('both_streams',fields),33)
        for changed in [dict(detail=15),dict(entry=0),dict(clean=0),dict(triggers=0),dict(exit=124)]:
            with self.subTest(changed=changed),self.assertRaises(ValueError):
                VM.validate_transcript(self.mutate_fields('both_streams',fields|changed),33)

    def test_failed_storage_still_enforces_prefix_bounds(self):
        VM.validate_transcript(self.mutate_result('fault_output_storage','out',6),33)
        cap=next(c['out_cap'] for c in VM.CASES.CASES if c['name']=='fault_output_storage')
        for fields in [dict(out=cap+2,stdout_stored=cap+1),dict(out=1,stdout_stored=2)]:
            with self.subTest(fields=fields),self.assertRaises(ValueError):
                VM.validate_transcript(self.mutate_fields('fault_output_storage',fields),33)

    def test_private_counters_and_scope_are_required(self):
        for name,key,value in [('shell','sentinel',0),('shell','extinct',0),('shell','clean',0),
            ('shell','kind',4),('shell','extra',1),('oom','oom',0),('task_limit','pids',0),
            ('cpu_budget','cpu',0),('deadline','elapsed',0),('stdout_cap','out',0)]:
            with self.subTest(name=name,key=key),self.assertRaises(ValueError):
                VM.validate_transcript(self.mutate_result(name,key,value),33)

    def test_concurrent_credentials_and_overlap_required(self):
        rows=self.evidence['observations']['cases'];a,b=rows[-2:]
        for key,value in [('uid',a['uid']),('began',a['ended']+1)]:
            with self.subTest(key=key),self.assertRaises(ValueError):VM.validate_transcript(self.mutate_result(b['name'],key,value),33)

    def test_sources_profile_and_artifact_completeness(self):
        variants=[]
        e=copy.deepcopy(self.evidence);e['source_sha256']['native/leancage_m3.c']='0'*64;variants.append(e)
        e=copy.deepcopy(self.evidence);e['command'][0]='/unrelated/qemu';variants.append(e)
        e=copy.deepcopy(self.evidence);e['machine']['network_devices']=['eth0'];variants.append(e)
        e=copy.deepcopy(self.evidence);e['environment']['overrides']['QEMU_MODULE_DIR']='/unrelated/modules';variants.append(e)
        e=copy.deepcopy(self.evidence);del e['artifacts_sha256']['qemu_accel'];variants.append(e)
        e=copy.deepcopy(self.evidence);e['artifacts_sha256']['helper']='0'*64;variants.append(e)
        e=copy.deepcopy(self.evidence);e['assumptions']=[];variants.append(e)
        e=copy.deepcopy(self.evidence);e['predecessor']['archive_sha256']='0'*64;variants.append(e)
        for e in variants:
            with self.subTest(),self.assertRaises(ValueError):VM.validate_evidence(e)

    def test_reports_and_supervisor_death_cannot_be_omitted(self):
        for prefix in ('M3_API name=report ','M3_DEATH '):
            text='\n'.join(l for l in self.text.splitlines() if not l.startswith(prefix))+'\n'
            with self.subTest(prefix=prefix),self.assertRaises(ValueError):VM.validate_transcript(text,33)

    def test_moved_checkout_without_original_artifacts(self):
        with tempfile.TemporaryDirectory(prefix='leancage-m3-relocated-') as directory:
            root=Path(directory)
            paths=set(self.evidence['source_sha256'])|{str(path.relative_to(PROJECT)) for path in (VM.EVIDENCE,VM.TRANSCRIPT,VM.INVENTORY)}
            for name in paths:
                target=root/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(PROJECT/name,target)
            result=subprocess.run(['python3',str(root/'scripts/run_m3_vm.py'),'--check-evidence'],cwd=root,capture_output=True,text=True,timeout=30)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertFalse((root/'.tools/m3vm').exists())

if __name__=='__main__':unittest.main()
