"""Pure artifact hashing checks; this test never runs the native guest launcher."""
# §AR-workspace.runtime: Compare padding/chunk boundaries and large inputs against an independent
# digest.
import hashlib
from pathlib import Path
import subprocess
import tempfile
import unittest

PROJECT = Path(__file__).resolve().parents[3]


class Sha256(unittest.TestCase):
    def test_vectors_and_stream_boundaries(self):
        source = '''#include <stdio.h>
#include "m3_sha256.h"
int main(void){struct m3_sha state;sha_init(&state);unsigned char buffer[37],digest[32];char hex[65];size_t n;
while((n=fread(buffer,1,sizeof(buffer),stdin)))sha_update(&state,buffer,n);
if(ferror(stdin))return 1;sha_final(&state,digest);sha_hex(digest,hex);puts(hex);return 0;}
'''
        with tempfile.TemporaryDirectory(prefix='m3-hash-') as directory:
            code = Path(directory) / 'hash.c'
            binary = Path(directory) / 'hash'
            code.write_text(source)
            subprocess.run(['cc', '-std=c11', '-O2', '-I', str(PROJECT / 'native'), str(code), '-o', str(binary)], check=True)
            for data in [b'', b'abc', *[bytes(range(256))[:n] for n in (1, 55, 56, 63, 64, 65, 119, 120, 127, 128, 255)], b'a' * 1000000]:
                with self.subTest(length=len(data)):
                    result = subprocess.run([binary], input=data, capture_output=True, check=True)
                    self.assertEqual(result.stdout.decode().strip(), hashlib.sha256(data).hexdigest())


if __name__ == '__main__':
    unittest.main()
