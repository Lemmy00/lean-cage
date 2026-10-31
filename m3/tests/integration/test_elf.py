"""Passive ELF header and dependency bounds checks."""
# §AR-workspace.runtime: Malformed bytes are rejected without executing or loading them.
import importlib.util
from pathlib import Path
import struct
import unittest

PROJECT=Path(__file__).resolve().parents[3]
spec=importlib.util.spec_from_file_location('m3_elf',PROJECT/'scripts/m3_elf.py')
ELF=importlib.util.module_from_spec(spec);spec.loader.exec_module(ELF)

def fixture():
    b=bytearray(1024)
    ident=b'\x7fELF\x02\x01\x01'+bytes(9)
    struct.pack_into('<16sHHIQQQIHHHHHH',b,0,ident,3,62,1,0,64,0,0,64,56,2,0,0,0)
    struct.pack_into('<IIQQQQQQ',b,64,1,5,0,0x400000,0,1024,1024,4096)
    struct.pack_into('<IIQQQQQQ',b,120,2,4,256,0x400100,0,64,64,8)
    for i,pair in enumerate([(5,0x400200),(10,12),(1,1),(0,0)]):struct.pack_into('<qQ',b,256+i*16,*pair)
    b[512:524]=b'\0libtest.so\0'
    return bytes(b)

class Elf(unittest.TestCase):
    def test_exact_needed_string(self):
        self.assertEqual(ELF.elf(fixture())['needed'],['libtest.so'])

    def test_invalid_abi_and_program_bounds(self):
        for at,data in [(4,b'\x01'),(18,b'\x03\x00'),(32,struct.pack('<Q',2**64-1))]:
            b=bytearray(fixture());b[at:at+len(data)]=data
            with self.subTest(at=at),self.assertRaises(ValueError):ELF.elf(bytes(b))

    def test_dynamic_table_must_terminate(self):
        b=bytearray(fixture());struct.pack_into('<qQ',b,304,1,1)
        with self.assertRaises(ValueError):ELF.elf(bytes(b))

    def test_string_pointer_and_offset_bounds(self):
        for at,value in [(264,2**64-1),(296,4096)]:
            b=bytearray(fixture());struct.pack_into('<Q',b,at,value)
            with self.subTest(at=at),self.assertRaises(ValueError):ELF.elf(bytes(b))

if __name__=='__main__':unittest.main()
