import Reasoning.Reach
import Reasoning.Initcode
import Examples.VyperImmutable.Bytecode

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace immutableCreationBlocks

private abbrev d := Reasoning.Theory.decode_append_left_of_decode Examples.VyperImmutable.immutableCreationBytecode
private abbrev j := Reasoning.Theory.D_J_contains_append_left Examples.VyperImmutable.immutableCreationBytecode

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem immutableCreation_block_0_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Examples.VyperImmutable.immutableCreationBytecode 0).contains (UInt256.ofNat 88) = true)
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 88) R mem (M aw (UInt256.ofNat 207) (⟨32⟩ : UInt256)) rdata σ (k + 6) (C + ((23) + (memExpansionCost aw (UInt256.ofNat 207) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Examples.VyperImmutable.immutableCreationBytecode.size = 235 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 207) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 88) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 88) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 88)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutableCreation_block_0_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Examples.VyperImmutable.immutableCreationBytecode 0).contains (UInt256.ofNat 88) = true)
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 88) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutableCreation_block_0_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem immutableCreation_block_0_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 9) R mem (M aw (UInt256.ofNat 207) (⟨32⟩ : UInt256)) rdata σ (k + 6) (C + ((23) + (memExpansionCost aw (UInt256.ofNat 207) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Examples.VyperImmutable.immutableCreationBytecode.size = 235 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 207) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := RD.genMload r1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.pop (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := r3.callvalue (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 88) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := r5.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 9)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutableCreation_block_0_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : ee.weiValue = (UInt256.ofNat 0))
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 0) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 9) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutableCreation_block_0_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `immutableCreation_block_9_taken`. -/
def immutableCreation_block_9_taken_stack {tail : ByteArray} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 235).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) :: R)

/-- Final memory for bytecode block summary `immutableCreation_block_9_taken`. -/
def immutableCreation_block_9_taken_memory {tail : ByteArray} {mem : ByteArray} : ByteArray :=
  ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 235).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)

/-- Automatically generated RD summary for bytecode block at pc 9. -/
theorem immutableCreation_block_9_taken {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 235).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Examples.VyperImmutable.immutableCreationBytecode 0).contains (UInt256.ofNat 88) = true)
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 9) R mem aw rdata σ k C)
    : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 88) (immutableCreation_block_9_taken_stack (tail := tail) (mem := mem) (R := R)) (immutableCreation_block_9_taken_memory (tail := tail) (mem := mem)) (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((35) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Examples.VyperImmutable.immutableCreationBytecode.size = 235 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 235) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genCodecopy r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMload r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 88) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (j tail (UInt256.ofNat 88) hvalid) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 88)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutableCreation_block_9_taken_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 235).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) (UInt256.ofNat 160)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Examples.VyperImmutable.immutableCreationBytecode 0).contains (UInt256.ofNat 88) = true)
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 9) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 88) (immutableCreation_block_9_taken_stack (tail := tail) (mem := mem) (R := R)) (immutableCreation_block_9_taken_memory (tail := tail) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutableCreation_block_9_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `immutableCreation_block_9_fallthrough`. -/
def immutableCreation_block_9_fallthrough_stack {tail : ByteArray} {mem : ByteArray} {R : List UInt256} : List UInt256 :=
  ((memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 235).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) :: R)

/-- Final memory for bytecode block summary `immutableCreation_block_9_fallthrough`. -/
def immutableCreation_block_9_fallthrough_memory {tail : ByteArray} {mem : ByteArray} : ByteArray :=
  ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 235).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)

/-- Automatically generated RD summary for bytecode block at pc 9. -/
theorem immutableCreation_block_9_fallthrough {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 235).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 9) R mem aw rdata σ k C)
    : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 26) (immutableCreation_block_9_fallthrough_stack (tail := tail) (mem := mem) (R := R)) (immutableCreation_block_9_fallthrough_memory (tail := tail) (mem := mem)) (M (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)) rdata σ (k + 11) (C + ((35) + (memExpansionCost aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) + (3 + 3 * (((UInt256.ofNat 32).toNat + 31) / 32)) + (memExpansionCost (M aw (⟨0⟩ : UInt256) (UInt256.ofNat 32)) (⟨0⟩ : UInt256) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have hcreationCodeSize : Examples.VyperImmutable.immutableCreationBytecode.size = 235 := by native_decide
  have r1 := r0.push1 (UInt256.ofNat 32) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 235) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r3 := r2.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r4 := RD.genCodecopy r3 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r5 := r4.push0 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r6 := RD.genMload r5 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r7 := r6.dup1 (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 160) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r9 := r8.shr (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 88) (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) (by evm_ov)
  have r11 := r10.jumpiNT (by exact d tail _ _ _ (by native_decide) (by rw [hcreationCodeSize]; native_decide) (by native_decide)) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 26)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem immutableCreation_block_9_fallthrough_packed {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.shiftRight (memLoad (⟨0⟩ : UInt256) ((Examples.VyperImmutable.immutableCreationBytecode ++ tail).write (UInt256.ofNat 235).toNat mem (⟨0⟩ : UInt256).toNat (UInt256.ofNat 32).toNat)) (UInt256.ofNat 160)) = (UInt256.ofNat 0))
    (h : RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 9) R mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD (Examples.VyperImmutable.immutableCreationBytecode ++ tail) ee g s0 (UInt256.ofNat 26) (immutableCreation_block_9_fallthrough_stack (tail := tail) (mem := mem) (R := R)) (immutableCreation_block_9_fallthrough_memory (tail := tail) (mem := mem)) aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (immutableCreation_block_9_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

end immutableCreationBlocks
