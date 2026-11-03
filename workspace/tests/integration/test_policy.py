"""Exercise the real Lean policy decoder without launching any workload."""
# §AR-workspace.interfaces: Reject ambiguous policy bytes before native profile admission.
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

PROJECT=Path(__file__).resolve().parents[3]
CLI=PROJECT/'m3/.lake/build/bin/leancage'
EXAMPLE=json.loads((PROJECT/'profiles/m3/example-policy.json').read_text())

class Policy(unittest.TestCase):
    def decode(self,data):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'request.json';path.write_bytes(data)
            r=subprocess.run([str(CLI),'validate-policy',str(path)],capture_output=True,text=True,timeout=20)
        self.assertIn(r.returncode,(0,64),r.stdout+r.stderr)
        return r.returncode==0

    def test_real_example_and_unicode_arguments(self):
        self.assertTrue(self.decode(json.dumps(EXAMPLE).encode()))
        p=copy.deepcopy(EXAMPLE);p['argv']=['/bin/sh','-c','echo é']
        self.assertTrue(self.decode(json.dumps(p,ensure_ascii=False).encode()))

    def test_reject_ambiguous_json(self):
        raw=json.dumps(EXAMPLE).encode()
        bad=[b'\xff'+raw,raw+b' {}',b'{'+raw[1:].replace(b'"schema_version": 1',b'"schema_version": 1,"schema_version": 1'),
             raw.replace(b'"schema_version": 1',b'"schema_version": 1e0'),
             raw.replace(b'"schema_version": 1',b'"schema_version": 1.0'),
             raw.replace(b'"schema_version": 1',b'"schema_version": 01'),
             raw.replace(b'"schema_version": 1',b'"schema_version": -1'),b' '*65537+raw,
             raw.replace(b'"schema_version": 1',b'"schema_version": 1,"\\u0073chema_version": 1')]
        for data in bad:
            with self.subTest(data=data[:80]):self.assertFalse(self.decode(data))

    def test_unknown_fields_profiles_digests_and_argument_bounds(self):
        changes=[('extra',0),('profile','other'),('runtime_manifest_digest','sha256:'+'0'*64),
            ('workspace_input','sha256:'+'A'*64),('stdin_input','/etc/passwd'),('export','copy-to-host'),
            ('argv',[]),('argv',['/bin/other']),('argv',['/bin/sh','']),('argv',['/bin/sh','a\0b']),
            ('argv',['/bin/sh','x'*4097]),('argv',['/bin/sh']+['x']*64),('argv',['/bin/sh']+['x'*4096]*4)]
        for key,value in changes:
            p=copy.deepcopy(EXAMPLE);p[key]=value
            with self.subTest(key=key):self.assertFalse(self.decode(json.dumps(p).encode()))

    def test_native_widths_and_resource_bounds(self):
        changes=[('memory_max_bytes',0),('memory_max_bytes',16777217),('memory_max_bytes',1073741825),
                 ('tasks_max',3),('tasks_max',257),('cpu_period_us',99999),('cpu_quota_us',100001),
                 ('cpu_budget_us',18446744073709551616),('wall_time_ms',9),('workspace_max_bytes',1048577),
                 ('workspace_max_inodes',63),('stdin_max_bytes',67108865),('stdout_max_bytes',16777217),
                 ('stderr_max_bytes',-1),('extra',0)]
        for key,value in changes:
            p=copy.deepcopy(EXAMPLE);p['limits'][key]=value
            with self.subTest(key=key,value=value):self.assertFalse(self.decode(json.dumps(p).encode()))

if __name__=='__main__':unittest.main()
