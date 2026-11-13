import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.SimultaneousAbsorption
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.BlockAssembly
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.CoreTheorem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/WuProver/lean-commutator@2f197491d436, `CommutatorTheorem/NoEpsilon/AbsorptionCore.lean`: removed 12 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# A bounded identity corner absorbs finitely many smaller outside blocks

The coordinate space is the dependent disjoint union of one two-by-two core and an
arbitrary finite family of outside blocks. No padding or enlargement is performed.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace NoEpsilon.Absorption

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (r : ℕ) (d : ι → Type) [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

/-- The core is indexed by none; the outside blocks are indexed by some i.-/
def blockShape : Option ι → Type
  | none => Fin r ⊕ Fin r
  | some i => d i

instance blockShapeFintype (i : Option ι) : Fintype (blockShape r d i) := by
  cases i <;> dsimp [blockShape] <;> infer_instance

instance blockShapeDecidableEq (i : Option ι) : DecidableEq (blockShape r d i) := by
  cases i <;> dsimp [blockShape] <;> infer_instance

abbrev Ambient := Sigma (blockShape r d)

def firstIndex (j : Fin r) : Ambient r d := ⟨none, Sum.inl j⟩

def secondIndex (j : Fin r) : Ambient r d := ⟨none, Sum.inr j⟩

def outsideIndex (i : ι) (j : d i) : Ambient r d := ⟨some i, j⟩

-- Preserve the existing parameter list for downstream callers.
theorem firstIndex_injective : Function.Injective (firstIndex r d) := by
  intro x y h
  exact Sum.inl_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

-- Preserve the existing parameter list for downstream callers.
theorem secondIndex_injective : Function.Injective (secondIndex r d) := by
  intro x y h
  exact Sum.inr_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

-- Preserve the existing parameter list for downstream callers.
theorem outsideIndex_injective (i : ι) : Function.Injective (outsideIndex r d i) := by
  intro x y h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

variable {r d}

-- Preserve the existing parameter list for downstream callers.
theorem coordinateInclusion_orthogonal {α β γ : Type*}
    [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → γ) (g : β → γ) (h : ∀ a b, f a ≠ g b) :
    (coordinateInclusion f)ᴴ * coordinateInclusion g = 0 := by
  ext a b
  simpa [Matrix.mul_apply, coordinateInclusion, Matrix.conjTranspose_apply]
    using (h a b).symm

-- Preserve the existing parameter list for downstream callers.
/-- The trace of the full matrix is the sum of the traces of its diagonal blocks.-/
theorem trace_eq_sum_blocks (A : Matrix (Ambient r d) (Ambient r d) ℂ) :
    trace A = trace (BlockAssembly.block A none none) +
      ∑ i, trace (BlockAssembly.block A (some i) (some i)) := by
  simp only [Matrix.trace, Matrix.diag, BlockAssembly.block, Matrix.submatrix_apply]
  rw [Fintype.sum_sigma, Fintype.sum_option]

/-- The explicit norm budget depends only on the initial norm and the number of
outside blocks, and is independent of their individual dimensions.-/
noncomputable def absorptionBudget (a : ℝ) (m : ℕ) : ℝ :=
  let b := simultaneousBudget a m
  (b / a) ^ 2 *
    (4 * (m + 1) * identityCornerNormBudget b + 2 * (m + 1) ^ 2 * b)

end NoEpsilon.Absorption
