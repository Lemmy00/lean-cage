#!/usr/bin/env python3
"""Differential/source witnesses, not native verification or OS experiments."""
# §AR-m4-native.evidence: Replay retained source branches using only memory and scripted effects.
import ctypes as C
import json
from pathlib import Path
import random
import struct
import unittest
import tempfile
import shutil
import check as gate
from extract import ROOT, extract, function

LIB = ROOT / '.tools/m4/input/witness.so'


def frame(kind=0, stage=0, detail=0, entry=1, clean=0, elapsed=0):
    p = bytearray(160)
    p[:4] = b'LC3R'
    p[4] = 1
    p[6] = kind
    struct.pack_into('<QQI', p, 8, 1, 0, 128)
    struct.pack_into('<6I', p, 32, stage, detail, entry, clean, 0, 100000)
    struct.pack_into('<Q', p, 88, elapsed)
    return p


def accepted(p):
    """Independent executable intermediate-frame contract (not the final Lean parser)."""
    if p[:4] != b'LC3R' or p[4:6] != b'\x01\x00' or p[7]:
        return False
    if struct.unpack_from('<QQII', p, 8) != (1, 0, 128, 0) or any(p[156:]):
        return False
    kind = p[6]
    stage, detail, entry, clean, triggers, uid = struct.unpack_from('<6I', p, 32)
    if kind > 7 or entry > 2 or clean > 1 or uid != 100000 or triggers or any(p[56:88]) or any(p[96:156]):
        return False
    return {
        0: stage == 0 and detail <= 255 and entry == 1,
        1: 1 <= stage <= 8 and 1 <= detail <= 4095 and entry == 0,
        2: stage == 0 and 1 <= detail <= 64 and entry == 1,
        4: stage == 9 and 1 <= detail <= 4095,
        5: stage == detail == entry == clean == 0 and any(p[88:96]),
        6: stage == 8 and detail == 0 and entry == 1 and clean == 0,
        7: False,  # preflight is false for these witnesses
    }.get(kind, False)


class Witness(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lib = C.CDLL(str(LIB))
        cls.lib.witness_reset.argtypes = [C.c_char_p, C.c_ulong, C.c_uint, C.c_int]
        cls.lib.witness_get64.restype = C.c_ulong
        cls.lib.witness_put64.argtypes = [C.c_void_p, C.c_ulong]
        cls.lib.witness_output.restype = C.c_ulong
        cls.lib.witness_write.argtypes = [C.c_void_p, C.c_ulong]

    def setUp(self):
        self.reset()

    def reset(self, mode=b'normal'):
        self.lib.witness_reset(mode, 1, 100000, 0)

    def output(self):
        p = C.create_string_buffer(2048)
        size = self.lib.witness_output(p)
        return p.raw[:size]

    def test_source_and_stale_input(self):
        source = (ROOT / 'native/leancage_m3.c').read_text()
        original = extract(source)
        self.assertEqual(original, (LIB.parent / 'slice.c').read_text())
        changed = source.replace('count-=(size_t)n;', 'count-=(size_t)n+1;')
        self.assertNotEqual(extract(changed), original)
        with self.assertRaises(ValueError):
            function(source + '\n' + function(source, 'get32'), 'get32')

    def test_arbitrary_byte_codecs(self):
        rng = random.Random(41)
        for _ in range(1000):
            raw = rng.randbytes(8)
            self.assertEqual(self.lib.witness_get32(raw) & 0xffffffff, int.from_bytes(raw[:4], 'little'))
            self.assertEqual(self.lib.witness_get64(raw), int.from_bytes(raw, 'little'))
            out = C.create_string_buffer(8)
            self.lib.witness_put64(out, int.from_bytes(raw, 'little'))
            self.assertEqual(out.raw, raw)
            self.lib.witness_put32(out, int.from_bytes(raw[:4], 'little'))
            self.assertEqual(out.raw[:4], raw[:4])

    def test_short_interrupted_write(self):
        for n, error in [(2, 0), (-1, 4), (1, 0), (3, 0)]:
            self.lib.witness_effect(n, error)
        self.assertEqual(self.lib.witness_write(b'abcdef', 6), 0)
        self.assertEqual(self.output(), b'abcdef')

    def test_zero_error_and_loss(self):
        for n, error, result in [(0, 0, -1), (-1, 5, -1), (-2, 0, 10002)]:
            self.reset()
            self.lib.witness_effect(2, 0)
            self.lib.witness_effect(n, error)
            self.assertEqual(self.lib.witness_write(b'abcdef', 6), result)
            self.assertEqual(self.output(), b'ab')
        self.reset()
        self.assertEqual(self.lib.witness_write(b'', 0), 0)

    def test_decoder_samples_and_invalid_tags(self):
        rng = random.Random(42)
        for _ in range(4000):
            p = frame()
            for _ in range(rng.randrange(1, 5)):
                p[rng.randrange(160)] = rng.randrange(256)
            self.assertEqual(self.lib.witness_decode(bytes(p), 0) == 0, bool(accepted(p)))
        for tag in range(256):
            p = frame(kind=tag)
            self.assertEqual(self.lib.witness_decode(bytes(p), 0) == 0, bool(accepted(p)))

    def test_success_setup_admission_and_rejection(self):
        for p in [frame(), frame(kind=1, stage=8, detail=4, entry=0),
                  frame(kind=5, entry=0, elapsed=1), frame(kind=6, stage=8)]:
            self.assertEqual(self.lib.witness_decode(bytes(p), 0), 0)
        for i in [0, 4, 5, 7, 8, 16, 24, 28, 156, 159]:
            p = frame()
            p[i] ^= 1
            self.assertEqual(self.lib.witness_decode(bytes(p), 0), -1)

    def test_frame_faults(self):
        for mode, length, valid in [(b'normal', 160, True), (b'report_short', 17, False),
                                   (b'report_drop', 0, False), (b'report_duplicate', 320, False),
                                   (b'report_wrong_seq', 160, False), (b'report_bad_reserved', 160, False)]:
            self.reset(mode)
            self.assertEqual(self.lib.witness_send(0, 0, 0, 1), 0)
            raw = self.output()
            self.assertEqual(len(raw), length)
            if length == 160:
                self.assertEqual(self.lib.witness_decode(raw, 0) == 0, valid)

    def test_terminal_error_reporting_can_fail(self):
        for mode, size in [(b'normal', 8), (b'error_short', 3), (b'error_drop', 0)]:
            self.reset(mode)
            self.assertEqual(self.lib.witness_failure(8, -1), 1125)
            self.assertEqual(self.output(), struct.pack('<II', 8, 0xffffffff)[:size])
        self.reset()
        self.lib.witness_effect(-1, 5)
        self.assertEqual(self.lib.witness_failure(8, 5), 1125)
        self.assertEqual(self.output(), b'')
        self.reset()
        self.lib.witness_effect(-1, 5)
        self.assertEqual(self.lib.witness_finish(0, 42), 42)
        self.assertEqual(self.output(), b'')
        for error in [-2147483648, -1, 0, 1, 4, 4095, 4096, 2147483647]:
            self.assertEqual(self.lib.witness_errno(error), error if 0 < error <= 4095 else 5)

    def test_tampered_ast_and_preprocessor_input(self):
        expected = {key: gate.digest(LIB.parent / name) for name, key in
                    [('slice.c', 'slice_sha256'), ('slice.i', 'preprocessed_sha256'),
                     ('Slice.v', 'clight_ast_sha256')]}
        for changed in ['slice.c', 'slice.i', 'Slice.v']:
            with tempfile.TemporaryDirectory(dir=ROOT / '.tools/m4') as tmp:
                directory = Path(tmp)
                for name in ['slice.c', 'slice.i', 'Slice.v']:
                    shutil.copyfile(LIB.parent / name, directory / name)
                gate.validate_input_artifacts(expected, directory)
                with (directory / changed).open('a') as out:
                    out.write('tampered')
                with self.assertRaisesRegex(ValueError, 'stale or tampered'):
                    gate.validate_input_artifacts(expected, directory)

    def test_authored_proof_drift_rejected_before_tools(self):
        original_root, original_manifest, original_evidence = gate.ROOT, gate.MANIFEST, gate.EVIDENCE
        with tempfile.TemporaryDirectory(dir=ROOT / '.tools/m4') as tmp:
            directory = Path(tmp)
            expected_sources = gate.sources()
            for name in [*expected_sources, 'assurance/m4-claims.json', 'assurance/m4-evidence.json']:
                destination = directory / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                source = ROOT / name
                if source.exists():
                    shutil.copyfile(source, destination)
            # An isolated fixture works during initial recording as well as replay.
            (directory / 'assurance/m4-claims.json').write_text(json.dumps({'source_sha256': expected_sources}))
            (directory / 'assurance/m4-evidence.json').write_text('{}')
            with (directory / 'm4/Codec.v').open('a') as out:
                out.write('\n(* Changed proof input. *)\n')
            try:
                gate.ROOT = directory
                gate.MANIFEST = directory / 'assurance/m4-claims.json'
                gate.EVIDENCE = directory / 'assurance/m4-evidence.json'
                with self.assertRaisesRegex(ValueError, 'authored source identities'):
                    gate.check()
            finally:
                gate.ROOT, gate.MANIFEST, gate.EVIDENCE = original_root, original_manifest, original_evidence

    def test_terminal_receiver_short_eintr_eof_errors_loss(self):
        setup = struct.pack('<II', 8, 4)
        self.lib.witness_effect(3, 0)
        self.lib.witness_effect(-1, 4)
        self.lib.witness_effect(5, 0)
        self.lib.witness_effect(0, 0)
        self.assertEqual(self.lib.witness_receive(setup, 8, 0, 0, 0, 0), 10800040)
        for raw in [setup[:3], setup + b'x', struct.pack('<II', 9, 4),
                    struct.pack('<II', 8, 0), struct.pack('<II', 8, 4096)]:
            self.reset()
            self.lib.witness_effect(len(raw), 0)
            self.assertEqual(self.lib.witness_receive(raw, len(raw), 0, 0, 0, 0), 40900712)
        self.reset()
        self.lib.witness_effect(-1, 5)
        self.assertEqual(self.lib.witness_receive(b'', 0, 0, 0, 0, 0), 40900712)
        self.reset()
        self.lib.witness_effect(-2, 0)
        self.assertEqual(self.lib.witness_receive(b'', 0, 0, 0, 0, 0), 10002)
        self.reset()
        self.assertEqual(self.lib.witness_receive(b'', 0, 0, 1, 1, 42 << 8), 421)
        self.reset()
        self.assertEqual(self.lib.witness_receive(b'', 0, 0, 1, 1, 9), 20000091)


if __name__ == '__main__':
    unittest.main(verbosity=2)
