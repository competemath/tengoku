import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionBlockEigenbasis
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms scaled_block_equations` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms blocks_eq_of_pivot_eq` (it only prints; the queue checks the axioms of every declaration). -/

/-! The linear block reduction consumed by the actual weighted-projector
coordinates. All nine blocks are affine expressions in the one block B₀₁.
The hypotheses are the row and weighted-column equations of that gauge. -/
noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedBlockEquations

open AlbertLean.Generic.QuaternionRow.BlockEigenbasis
variable {K : Type*} [Field K] [CharZero K]

/-- Clearing the overlap denominators first keeps the block calculation
linear over an arbitrary coefficient field.
@isnad1 id=and.3h4v.s11.63d50ab6d8f7 from=translated src=- shape=27af9487 vocab=3ab26084
-/
theorem scaled_block_equations (B : Fin 3 → Fin 3 → Mat2 K)
    (p q : Fin 3 → K)
    (hd : ∀ i, B i i = q i • (1 : Mat2 K))
    (hr : ∀ i, B i 0 + B i 1 + B i 2 = 0)
    (hc : ∀ j, p 0 • B 0 j + p 1 • B 1 j + p 2 • B 2 j = 0) :
    B 0 2 = -q 0 • (1 : Mat2 K) - B 0 1 ∧
    p 2 • B 2 1 = -p 0 • B 0 1 - (p 1 * q 1) • (1 : Mat2 K) ∧
    p 2 • B 2 0 = p 0 • B 0 1 + (p 1 * q 1 - p 2 * q 2) • (1 : Mat2 K) ∧
    p 1 • B 1 0 = -p 0 • B 0 1 +
      (-p 0 * q 0 - p 1 * q 1 + p 2 * q 2) • (1 : Mat2 K) ∧
    p 1 • B 1 2 = p 0 • B 0 1 +
      (p 0 * q 0 - p 2 * q 2) • (1 : Mat2 K) := by
  have h02 := hr 0
  rw [hd 0] at h02
  have h21 := hc 1
  rw [hd 1] at h21
  have h20 := hr 2
  rw [hd 2] at h20
  have h10 := hc 0
  rw [hd 0] at h10
  have h12 := hr 1
  rw [hd 1] at h12
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (norm := module) h02
  · linear_combination (norm := module) h21
  · linear_combination (norm := module) p 2 • h20 - h21
  · linear_combination (norm := module) h10 - p 2 • h20 + h21
  · linear_combination (norm := module) p 1 • h12 - h10 + p 2 • h20 - h21

/-- One block and the six overlap scalars determine the entire matrix in the
weighted gauge; no eigenvalue choice is needed for this uniqueness step.
@isnad1 id=eq.9h5v.s10.a2eed87e54c5 from=translated src=- shape=d50af96b vocab=160993b4
-/
theorem blocks_eq_of_pivot_eq (B C : Fin 3 → Fin 3 → Mat2 K)
    (p q : Fin 3 → K) (hp1 : p 1 ≠ 0) (hp2 : p 2 ≠ 0)
    (hdB : ∀ i, B i i = q i • (1 : Mat2 K))
    (hrB : ∀ i, B i 0 + B i 1 + B i 2 = 0)
    (hcB : ∀ j, p 0 • B 0 j + p 1 • B 1 j + p 2 • B 2 j = 0)
    (hdC : ∀ i, C i i = q i • (1 : Mat2 K))
    (hrC : ∀ i, C i 0 + C i 1 + C i 2 = 0)
    (hcC : ∀ j, p 0 • C 0 j + p 1 • C 1 j + p 2 • C 2 j = 0)
    (hX : B 0 1 = C 0 1) : B = C := by
  obtain ⟨hb02, hb21, hb20, hb10, hb12⟩ := scaled_block_equations B p q hdB hrB hcB
  obtain ⟨hc02, hc21, hc20, hc10, hc12⟩ := scaled_block_equations C p q hdC hrC hcC
  rw [hX] at hb02 hb21 hb20 hb10 hb12
  have h02 : B 0 2 = C 0 2 := hb02.trans hc02.symm
  have cancel1 {X Y : Mat2 K} (h : p 1 • X = p 1 • Y) : X = Y := by
    exact (smul_right_injective _ hp1) h
  have cancel2 {X Y : Mat2 K} (h : p 2 • X = p 2 • Y) : X = Y := by
    exact (smul_right_injective _ hp2) h
  have h21 := cancel2 (hb21.trans hc21.symm)
  have h20 := cancel2 (hb20.trans hc20.symm)
  have h10 := cancel1 (hb10.trans hc10.symm)
  have h12 := cancel1 (hb12.trans hc12.symm)
  funext i j
  fin_cases i <;> fin_cases j
  · exact (hdB 0).trans (hdC 0).symm
  · exact hX
  · exact h02
  · exact h10
  · exact (hdB 1).trans (hdC 1).symm
  · exact h12
  · exact h20
  · exact h21
  · exact (hdB 2).trans (hdC 2).symm

end AlbertLean.Generic.QuaternionRow.WeightedBlockEquations
