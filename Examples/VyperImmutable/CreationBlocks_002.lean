import Reasoning.Reach
import Reasoning.Initcode
import Examples.VyperImmutable.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace immutableCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Examples.VyperImmutable.immutableCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Examples.VyperImmutable.immutableCreationBytecode

/-- Final stack for bytecode block summary `immutableCreation_block_26_taken`. -/
def immutableCreation_block_26_taken_stack {tail : ByteArray} {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 299).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) :: R)

/-- Final memory for bytecode block summary `immutableCreation_block_26_taken`. -/
def immutableCreation_block_26_taken_memory {tail : ByteArray} {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 299).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)

/-- Automatically generated RD summary for bytecode block at pc 26. -/
theorem immutableCreation_block_26_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftLeft (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 299).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Examples.VyperImmutable.immutableCreationBytecode 0).contains (UInt256.ofNat 88) = true)
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 26) (x0 :: R) mem aw rdata σ k C)
    : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 88) (immutableCreation_block_26_taken_stack (tail := tail) (mem := mem) (x0 := x0) (R := R)) (immutableCreation_block_26_taken_memory (tail := tail) (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((41) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Examples.VyperImmutable.immutableCreationBytecode.size = 235 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMstore r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 299) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genCodecopy r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMload r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 88) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 88) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 88)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutableCreation_block_26_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftLeft (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 299).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) (UInt256.ofNat 32)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Examples.VyperImmutable.immutableCreationBytecode 0).contains (UInt256.ofNat 88) = true)
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 26) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 88) (immutableCreation_block_26_taken_stack (tail := tail) (mem := mem) (x0 := x0) (R := R)) (immutableCreation_block_26_taken_memory (tail := tail) (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutableCreation_block_26_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `immutableCreation_block_26_fallthrough`. -/
def immutableCreation_block_26_fallthrough_stack {tail : ByteArray} {mem : ByteArray} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 299).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) :: R)

/-- Final memory for bytecode block summary `immutableCreation_block_26_fallthrough`. -/
def immutableCreation_block_26_fallthrough_memory {tail : ByteArray} {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 299).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)

/-- Automatically generated RD summary for bytecode block at pc 26. -/
theorem immutableCreation_block_26_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftLeft (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 299).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 26) (x0 :: R) mem aw rdata σ k C)
    : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 46) (immutableCreation_block_26_fallthrough_stack (tail := tail) (mem := mem) (x0 := x0) (R := R)) (immutableCreation_block_26_fallthrough_memory (tail := tail) (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 13) (C + ((41) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Examples.VyperImmutable.immutableCreationBytecode.size = 235 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMstore r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 299) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genCodecopy r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := RD.genMload r7 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.shl (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 88) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 46)) r13 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutableCreation_block_26_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftLeft (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 299).toNat (x0.toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) (UInt256.ofNat 32)) = (UInt256.ofNat 0))
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 26) (x0 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 46) (immutableCreation_block_26_fallthrough_stack (tail := tail) (mem := mem) (x0 := x0) (R := R)) (immutableCreation_block_26_fallthrough_memory (tail := tail) (mem := mem) (x0 := x0)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutableCreation_block_26_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 46. -/
theorem immutableCreation_block_46 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 46) (x0 :: R) mem aw rdata σ k C)
    : RDret (Examples.VyperImmutable.immutableCreationBytecode ++ tail) g s0 σ (((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 92).toNat ((memLoad (UInt256.ofNat 96) ((memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 267).toNat ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 143).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)).toByteArray.write 0 ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 267).toNat ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 143).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) (UInt256.ofNat 175).toNat 32)).toByteArray.write 0 ((memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 267).toNat ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 143).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)).toByteArray.write 0 ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 267).toNat ((memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32)).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 96).toNat 32) (UInt256.ofNat 143).toNat 32) (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat) (UInt256.ofNat 175).toNat 32) (UInt256.ofNat 207).toNat 32) (UInt256.ofNat 0).toNat (UInt256.ofNat 143).toNat).readWithPadding (UInt256.ofNat 0).toNat (UInt256.ofNat 239).toNat) := by
  let r0 := h
  have hcreationCodeSize : Examples.VyperImmutable.immutableCreationBytecode.size = 235 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMstore r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genMload r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 143) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMstore r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 267) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := RD.genCodecopy r9 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r12 := RD.genMload r11 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 175) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r14 := RD.genMstore r13 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 96) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r16 := RD.genMload r15 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 207) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r18 := RD.genMstore r17 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 143) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 92) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r22 := RD.genCodecopy r21 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 239) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 0) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRet r24 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 88. -/
theorem immutableCreation_block_88 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 88) R mem aw rdata σ k C)
    : RDrev (Examples.VyperImmutable.immutableCreationBytecode ++ tail) g s0 := by
  let r0 := h
  have hcreationCodeSize : Examples.VyperImmutable.immutableCreationBytecode.size = 235 := by native_decide
  have r1 := r0.jumpdest (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  exact RD.genRev r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)

end immutableCreationBlocks
