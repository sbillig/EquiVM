#!/usr/bin/env python3
"""Regression checks for Attester's generated-summary coverage."""

import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))


def load_generator():
    spec = importlib.util.spec_from_file_location(
        "attester_blocks_test", ROOT / "Benchmarks/EAS/Attester/generate_blocks.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class AttesterCoverageTests(unittest.TestCase):
    def test_patched_jump_checks_metadata_suffix_for_missing_steps(self):
        generator = load_generator()
        prefix = bytes.fromhex("7f" + "00" * 32 + "5600")
        runtime = prefix + bytes.fromhex("a1005bef0000000000000000000b")
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            (directory / "runtime.hex").write_text(runtime.hex())
            (directory / "creation.hex").write_text((b"\x00" + runtime).hex())
            with (patch.object(generator, "ROOT", directory),
                  patch.object(generator.tempfile, "TemporaryDirectory",
                               return_value=SimpleNamespace(name=temporary, cleanup=lambda: None)),
                  patch.object(generator.blocks, "read_lean_layout", return_value={1: (32, "target")}),
                  patch.object(sys, "argv", ["generate_blocks.py"])):
                with self.assertRaisesRegex(ValueError, "unsupported_ef"):
                    generator.main()


if __name__ == "__main__":
    unittest.main()
