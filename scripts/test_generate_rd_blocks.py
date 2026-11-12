#!/usr/bin/env python3
"""Focused checks for primitive RD summaries and the return-data copy rule."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
import sys
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_all_benchmark_blocks as benchmarks
import generate_rd_blocks as rd


def units(hex_code: str, **kwargs: object) -> str:
    return "\n".join(rd.generate_units(
        bytes.fromhex(hex_code), "sample", "sampleCode", keep_metadata=True, **kwargs
    ))


class GeneratorTests(unittest.TestCase):
    def test_unrelated_sequences_use_primitive_steps(self) -> None:
        rendered = units("60806040525f3560e01c")
        self.assertIn(".push1", rendered)
        self.assertIn("RD.genMstore", rendered)
        self.assertIn(".calldataload", rendered)
        self.assertIn(".shr", rendered)
        self.assertNotIn("solcSummary", rendered)

    def test_cursor_uses_current_account_map_interface(self) -> None:
        rendered = units("5b00")
        self.assertIn("{σ : AccountMap}", rendered)
        self.assertIn("rdata σ k C", rendered)
        self.assertIn("RDret sampleCode g s0 σ ByteArray.empty", rendered)
        self.assertNotIn("cA", rendered)

    def test_sload_uses_current_map_operations(self) -> None:
        rendered = units("54")
        self.assertIn("σ.get? ee.codeOwner", rendered)
        self.assertIn("ac.storage.getD", rendered)

    def test_new_local_opcodes_and_transient_storage(self) -> None:
        rendered = units("600160025d60015c434445600360020553")
        for step in (".tstore", ".tload", ".number", ".prevrandao",
                     ".gaslimit", ".sdiv", "RD.genMstore8"):
            self.assertIn(step, rendered)
        self.assertIn("tstoreAccountMap ee.codeOwner", rendered)
        self.assertIn("ac.tstorage.getD", rendered)
        self.assertIn("(hperm : ee.perm = true)", rendered)
        self.assertNotIn("Unsupported instruction boundary", rendered)

    def test_cancun_arith_and_account_opcodes(self) -> None:
        rendered = units(
            "600360021d" "6001" "60ff1a" "600060800b"
            "60036002600108" "60036002600109"
            "600131" "60013f" "600140" "48"
            "6020600060405e" "60206000a0")
        for step in (".sar", ".byte", ".signextend", ".addmod", ".mulmod",
                     ".balance", ".extcodehash", ".blockhash", ".basefee",
                     "RD.genMcopy", "RD.genLog0"):
            self.assertIn(step, rendered)
        self.assertIn("balanceWord", rendered)
        self.assertIn("extCodeHashWord", rendered)
        self.assertIn("blockHashWord ee", rendered)
        self.assertIn("Mmcopy aw", rendered)
        self.assertIn("(hperm : ee.perm = true)", rendered)
        self.assertNotIn("Unsupported instruction boundary", rendered)
        # Without warm/cold operations the block keeps exact counters, so the MCOPY cost shows.
        rendered = units("6020600060405e")
        self.assertIn("RD.genMcopy", rendered)
        self.assertIn("mcopyExpansionCost aw", rendered)

    def test_immutable_mode_uses_deployed_code_and_symbolic_push(self) -> None:
        code = bytes([0x7F, *([0] * 32), 0x56])
        sites = rd.validate_immutable_sites(
            [{"offset": 1, "length": 32, "key": "owner"}], code)
        rendered = rd.generate(code, "imm", "template", ["Contract.Immutables"],
                               immutable_sites=sites, layout_term="Contract.layout")
        self.assertIn("RD (Contract.layout.runtime template immWords) ee g s0", rendered)
        self.assertNotIn("def immutableLayout", rendered)
        self.assertIn('immWords "owner"', rendered)
        self.assertIn("Layout.decodeSite", rendered)
        self.assertIn("immutable_decode(", rendered)
        self.assertIn("theorem immutableLayout_inBounds", rendered)
        self.assertIn("theorem immutableTemplate_size64", rendered)
        self.assertIn("theorem immutableDecode_0", rendered)
        self.assertNotIn("theorem immutableDecode_33", rendered)
        self.assertIn("(D_J (Contract.layout.runtime template immWords) 0)", rendered)
        self.assertIn("immutableRuntime_size", rendered)

    def test_immutable_mode_requires_imported_layout_term(self) -> None:
        with self.assertRaisesRegex(ValueError, "imported Lean layout term"):
            rd.generate(bytes.fromhex("5b00"), "imm", "template", [],
                        immutable_sites={})

    def test_runtime_suffix_reads_appended_data_symbolically(self) -> None:
        # CODECOPY reads 32 bytes starting at the end of the 10-byte template.
        code = bytes.fromhex("6020600a600039600051")
        rendered = rd.generate(code, "suffix", "template", [],
                               runtime_suffix=True)
        self.assertIn("{suffix : ByteArray}", rendered)
        self.assertIn("RD (template ++ suffix) ee g s0", rendered)
        self.assertIn("(template ++ suffix).write", rendered)
        self.assertIn("append_decode(template, suffix,", rendered)
        self.assertNotIn("immWords", rendered)
        self.assertNotIn("Layout.runtime", rendered)

    def test_runtime_suffix_covers_codesize(self) -> None:
        rendered = rd.generate(bytes.fromhex("38"), "suffix", "template", [],
                               runtime_suffix=True)
        self.assertIn("(template ++ suffix).size", rendered)
        self.assertIn("(suffix := suffix)", rendered)

    def test_runtime_suffix_is_exclusive_with_splicing(self) -> None:
        with self.assertRaisesRegex(ValueError, "separate"):
            rd.generate(bytes.fromhex("5b00"), "suffix", "template", [],
                        runtime_suffix=True, immutable_sites={},
                        layout_term="Contract.layout")

    def test_immutable_layout_rejects_non_push_payload(self) -> None:
        with self.assertRaisesRegex(ValueError, "not a PUSH32 payload"):
            rd.validate_immutable_sites(
                [{"offset": 2, "length": 32, "key": "owner"}],
                bytes([0x7F, *([0] * 32)]))

    def test_immutable_layout_rejects_width_mismatched_to_opcode(self) -> None:
        with self.assertRaisesRegex(ValueError, "not a PUSH20 payload"):
            rd.validate_immutable_sites(
                [{"offset": 1, "length": 20, "key": "owner"}],
                bytes([0x7F, *([0] * 32)]))
        with self.assertRaisesRegex(ValueError, "length 20 or 32"):
            rd.validate_immutable_sites(
                [{"offset": 1, "length": 21, "key": "owner"}],
                bytes([0x74, *([0] * 21)]))

    def test_immutable_layout_accepts_push20(self) -> None:
        code = bytes([0x73, *([0] * 20), 0x50, 0x00])
        sites = rd.validate_immutable_sites(
            [{"offset": 1, "length": 20, "key": "owner"}], code)
        rendered = rd.generate(code, "imm20", "template", ["Contract.Immutables"],
                               immutable_sites=sites, layout_term="Contract.layout")
        self.assertIn("RD (Contract.layout.runtimeN template immWords)", rendered)
        self.assertIn('Layout.siteWord 20 (immWords "owner")', rendered)
        self.assertIn("Layout.decodeSite20", rendered)
        self.assertIn("immutable_decode_n(", rendered)

    def test_full_copy_variants_discharge_guard(self) -> None:
        variants = (
            "3d5f5f3e", "3d5f803e", "3d5f60003e", "3d60005f3e",
            "3d6000803e", "3d600060003e", "3d6100005f3e",
            "3d5f6100003e", "3d610000803e", "3d610000620000003e",
        )
        for code in variants:
            with self.subTest(code=code):
                rendered = units(code)
                self.assertIn(".returndatasize", rendered)
                self.assertIn("RD.genReturndatacopy", rendered)
                self.assertIn("returnDataCopyFullGuard rdata", rendered)
                self.assertNotIn("genReturndatacopyFull", rendered)
                self.assertNotIn("hguard", rendered)

    def test_generic_copy_keeps_semantic_guard(self) -> None:
        rendered = units("3e")
        self.assertIn("(hguard0 :", rendered)
        self.assertIn("RD.genReturndatacopy", rendered)

    def test_every_push_width_has_a_generator_step(self) -> None:
        for width in range(1, 33):
            with self.subTest(width=width):
                code = bytes([0x5F + width, *([width] * width)])
                rendered = "\n".join(rd.generate_units(
                    code, "push", "pushCode", keep_metadata=True,
                    fail_on_unsupported=True,
                ))
                step = f".push{width} " if width in {1, 2, 4, 20} else ".pushConst "
                self.assertIn(step, rendered)
                self.assertNotIn("Unsupported instruction boundary", rendered)

    def test_incomplete_push_is_explicit_boundary(self) -> None:
        rendered = units("7f01")
        self.assertIn("Unsupported instruction boundary at pc 0: push32", rendered)

    def test_reachable_metadata_jumpdest_gets_a_summary(self) -> None:
        # CALLDATALOAD supplies 6 to JUMP; pc 6 is inside a CBOR-shaped suffix.
        code = bytes.fromhex("5f355600a1005b0000000000000000000b")
        self.assertEqual([ins.pc for ins in rd.disassemble(code) if ins.opcode == 0x5B], [6])
        for creation in (False, True):
            with self.subTest(creation=creation):
                records = rd.generate_unit_records(code, "sample", "sampleCode",
                                                   creation_code=creation)
                self.assertTrue(any(6 in unit.pcs for unit in records))

    def test_metadata_is_removed_only_when_control_flow_stays_in_prefix(self) -> None:
        metadata = bytes.fromhex("a1005b0000000000000000000b")
        safe = ("00", "600456005b00")
        for prefix in safe:
            with self.subTest(prefix=prefix):
                code = bytes.fromhex(prefix) + metadata
                self.assertEqual(rd.strip_solidity_metadata(code), bytes.fromhex(prefix))
        uncertain = ("5f355600", "60065600", "5b5f600057", "5b", "61ab", "ef00")
        for prefix in uncertain:
            with self.subTest(prefix=prefix):
                code = bytes.fromhex(prefix) + metadata
                self.assertEqual(rd.strip_solidity_metadata(code), code)

    def test_patched_jump_target_keeps_metadata(self) -> None:
        prefix = bytes.fromhex("7f" + "00" * 32 + "5600")
        metadata = bytes.fromhex("a1005b0000000000000000000b")
        code = prefix + metadata
        sites = {1: (32, "target")}
        self.assertEqual(rd.strip_solidity_metadata(code), prefix)
        self.assertEqual(rd.strip_solidity_metadata(code, sites), code)
        records = rd.generate_unit_records(code, "sample", "sampleCode",
                                           immutable_sites=sites, layout_term="layout")
        self.assertTrue(any(len(prefix) + 2 in unit.pcs for unit in records))

    def test_copy_is_not_split_by_small_bound(self) -> None:
        rendered = units("3d5f5f3e", max_summary_instructions=2)
        self.assertEqual(1, rendered.count("/-- Automatically generated RD summary"))
        self.assertIn("returnDataCopyFullGuard rdata", rendered)

    def test_creation_mode_lifts_concrete_decodes(self) -> None:
        rendered = rd.generate(bytes.fromhex("600100"), "sample", "sampleCode",
                               ["Sample.Bytecode"], keep_metadata=True,
                               creation_code=True)
        self.assertIn("decode_append_left_of_decode", rendered)
        self.assertIn("RD (sampleCode ++ tail)", rendered)

    def test_creation_runtime_omits_unreachable_suffix(self) -> None:
        # Both paths stay in the prefix; pc 8 is a runtime-only JUMPDEST.
        constructor = bytes.fromhex("5f6006575b005b00")
        runtime = bytes.fromhex("5b00")
        code = constructor + runtime
        records = rd.generate_unit_records(code, "sample", "sampleCode",
                                           keep_metadata=True, creation_code=True,
                                           creation_runtime=runtime)
        self.assertTrue(records)
        self.assertTrue(all(pc < len(constructor) for unit in records for pc in unit.pcs))
        self.assertIn("sampleCode.size = 10", "\n".join(unit.text for unit in records))
        self.assertTrue(any(pc == len(constructor) for unit in rd.generate_unit_records(
            code, "sample", "sampleCode", keep_metadata=True, creation_code=True)
                            for pc in unit.pcs))

    def test_creation_runtime_keeps_uncertain_control_flow(self) -> None:
        runtime = bytes.fromhex("5b00")
        cases = {
            "dynamic jump": "5f355600",
            "jump into runtime": "60045600",
            "jump into arbitrary tail": "60ff5600",
            "conditional fallthrough": "5b5f600057",
            "ordinary fallthrough": "5b",
            "push crossing boundary": "61ab",
            "unknown opcode": "ef00",
        }
        for label, constructor in cases.items():
            with self.subTest(label=label):
                code = bytes.fromhex(constructor) + runtime
                self.assertEqual(rd.creation_constructor_code(code, runtime), code)

    def test_creation_runtime_ignores_push_payload_bytes(self) -> None:
        constructor = bytes.fromhex("61565b5000")
        runtime = bytes.fromhex("5b00")
        self.assertEqual(rd.creation_constructor_code(constructor + runtime, runtime), constructor)

    def test_uncertain_creation_keeps_metadata_like_suffix(self) -> None:
        # The suffix resembles solc metadata, but a dynamic jump could enter it.
        constructor = bytes.fromhex("5f355600")
        runtime = bytes.fromhex("a00001")
        records = rd.generate_unit_records(constructor + runtime, "sample", "sampleCode",
                                           creation_code=True, creation_runtime=runtime)
        self.assertTrue(any(pc == len(constructor) for unit in records for pc in unit.pcs))

    def test_creation_runtime_requires_exact_nonempty_suffix(self) -> None:
        code = bytes.fromhex("005b00")
        for runtime in (b"", bytes.fromhex("5b01")):
            with self.subTest(runtime=runtime), self.assertRaisesRegex(ValueError, "nonempty suffix"):
                rd.generate_unit_records(code, "sample", "sampleCode", creation_code=True,
                                         creation_runtime=runtime)
        with self.assertRaisesRegex(ValueError, "requires creation code"):
            rd.generate_unit_records(code, "sample", "sampleCode", creation_runtime=bytes.fromhex("5b00"))

    def test_creation_jump_destination_substitutes_codecopy_source(self) -> None:
        from bytecode_io import read_bytecode
        creation = read_bytecode(Path(__file__).resolve().parent.parent /
                                 "Examples/VyperImmutable/creation.hex")
        rendered = "\n".join(rd.generate_units(
            creation, "sample", "sampleCode", creation_code=True))
        self.assertIn("(j tail (memLoad", rendered)
        self.assertNotIn("__CODE__", rendered)

    def test_index_covers_generated_theorems(self) -> None:
        records = rd.generate_unit_records(bytes.fromhex("6001"), "sample", "sampleCode",
                                           keep_metadata=True)
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "Blocks.lean"
            rd.write_outputs(output, "sample", ["Sample.Bytecode"], records, None)
            index = output.with_suffix(".index").read_text()
            self.assertIn("sample_block_0\tBlocks.lean:", index)
            self.assertIn("sample_block_0_packed\tBlocks.lean:", index)

    def test_shards_and_index_refer_to_same_files(self) -> None:
        records = rd.generate_unit_records(bytes.fromhex("5b5b"), "sample", "sampleCode",
                                           keep_metadata=True)
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "Blocks.lean"
            shards = rd.write_outputs(output, "sample", ["Sample.Bytecode"], records, 1)
            self.assertEqual(2, len(shards))
            index = output.with_suffix(".index").read_text()
            for shard in shards:
                self.assertIn(shard.name + ":", index)

    def test_branch_prefix_sharing_keeps_summary_names_and_shards(self) -> None:
        code = bytes.fromhex("5b6001506001505f35600057")
        records = rd.generate_unit_records(code, "sample", "sampleCode", keep_metadata=True,
                                           prepare_branch_prefixes=True)
        self.assertEqual(len(records), 2)
        names = [unit.theorem_names for unit in records]
        shared = rd.share_branch_units(records)
        self.assertEqual([unit.theorem_names for unit in shared], names)
        self.assertEqual(sum(unit.text.count("private def sample_block_0_shared") for unit in shared), 1)
        self.assertTrue(all("sample_block_0_shared hstack h" in unit.text for unit in shared))
        self.assertLess(sum(unit.text.count("native_decide") for unit in shared),
                        sum(unit.text.count("native_decide") for unit in records))
        self.assertEqual(rd.share_branch_units(records, {99}), records)
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "Blocks.lean"
            shards = rd.write_outputs(output, "sample", ["Sample.Bytecode"], records, 1,
                                      share_branch_prefixes=True)
            self.assertEqual(len(shards), 2)
            self.assertTrue(all("sample_block_0_shared" not in f.read_text() for f in shards))
            index = output.with_suffix(".index").read_text()
            self.assertTrue(all(name in index for unit in records for name in unit.theorem_names))

    def test_branch_prefix_creation_and_static_controls(self) -> None:
        code = bytes.fromhex("5b6001506001505f35600057")
        records = rd.generate_unit_records(code, "sample", "sampleCode", keep_metadata=True,
                                           creation_code=True, prepare_branch_prefixes=True)
        shared = rd.share_branch_units(records)
        self.assertIn("(hcreationCodeSize : sampleCode.size = 12)", shared[0].text)
        self.assertTrue(all("sample_block_0_shared hstack hcreationCodeSize h" in u.text
                            for u in shared))
        store = bytes.fromhex("5b60006000556000506000600057")
        static = rd.generate_unit_records(store, "sample", "sampleCode", keep_metadata=True,
                                          prepare_branch_prefixes=True)
        self.assertTrue(all(unit.branch_prefix is None for unit in static))
        # JUMPI consumes a pre-existing condition, so the prefix has a different stack input.
        different_stack = bytes.fromhex("5b600150600150600050600057")
        mismatch = rd.generate_unit_records(different_stack, "sample", "sampleCode",
                                           keep_metadata=True, prepare_branch_prefixes=True)
        self.assertTrue(all(unit.branch_prefix is None for unit in mismatch))
        patched = rd.generate_unit_records(code, "sample", "sampleCode", keep_metadata=True,
                                           immutable_sites={}, layout_term="Sample.layout",
                                           prepare_branch_prefixes=True)
        self.assertTrue(all(unit.branch_prefix is None for unit in patched))

    def test_contract_variants_can_share_summary_prefix(self) -> None:
        records = rd.generate_unit_records(bytes.fromhex("5b5b"), "sample", "sampleCode",
                                           keep_metadata=True)
        for shard_size in (None, 1):
            with self.subTest(shard_size=shard_size), tempfile.TemporaryDirectory() as tmp:
                for variant in ("Main", "Alternate"):
                    namespace = f"Sample.{variant}.RuntimeBlocks"
                    output = Path(tmp) / f"{variant}.lean"
                    paths = rd.write_outputs(output, "sample", ["Sample.Bytecode"], records,
                                             shard_size, namespace=namespace)
                    for path in paths:
                        rendered = path.read_text()
                        self.assertIn(f"namespace {namespace}\n", rendered)
                        self.assertIn(f"end {namespace}\n", rendered)
                        self.assertIn("theorem sample_block_", rendered)
                        self.assertNotIn("namespace sampleBlocks\n", rendered)


class BenchmarkInputTests(unittest.TestCase):
    def test_discovery_is_independent_of_temporary_scaffolds(self) -> None:
        for with_scaffolds in (False, True):
            with self.subTest(with_scaffolds=with_scaffolds), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp) / "Benchmarks"
                expected = [root / "Dss/End/Bytecode.lean",
                            root / "UniswapV3/Pool/Bytecode.lean"]
                paths = expected + ([root / "Scaffolds/Temporary/Bytecode.lean"]
                                    if with_scaffolds else [])
                for path in reversed(paths):
                    path.parent.mkdir(parents=True)
                    path.touch()
                self.assertEqual(benchmarks.benchmark_paths(root), expected)

    def test_layout_module_supports_both_benchmark_formats(self) -> None:
        for files, expected in (((), None),
                                (("Immutables.lean",), "Immutables.lean"),
                                (("Immutables.lean", "ImmutableCode.lean"), "ImmutableCode.lean")):
            with self.subTest(files=files), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                path = root / "Benchmarks/Sample/Bytecode.lean"
                path.parent.mkdir(parents=True)
                path.write_text("namespace Sample\ndef sampleBytecode : ByteArray := ⟨#[0]⟩\n",
                                encoding="utf-8")
                for name in files:
                    path.with_name(name).touch()
                with patch.object(benchmarks, "ROOT", root):
                    self.assertEqual(
                        benchmarks.benchmark_inputs(path),
                        ("Sample.sampleBytecode", "Benchmarks.Sample.Bytecode",
                         path.with_name(expected) if expected else None),
                    )


if __name__ == "__main__":
    unittest.main()
