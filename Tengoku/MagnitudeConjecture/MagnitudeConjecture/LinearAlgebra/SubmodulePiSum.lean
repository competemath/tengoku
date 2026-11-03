import Tengoku.Seed.LinearAlgebra.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Summing a single coordinate in a family of submodules -/

set_option autoImplicit false

namespace Submodule

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [Fintype ι] [DecidableEq ι]

/-- The ambient sum of a family supported in one submodule is its nonzero
coordinate.
@isnad1 id=eq.0h6v.s7.3c5113dceb1e from=translated src=- shape=42ccedfd vocab=170fd9d3
-/
theorem sum_coe_single (p : ι → Submodule R M) (i : ι) (x : p i) :
    (∑ j, ((Pi.single i x : ∀ j, p j) j : M)) = (x : M) := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    rfl
  · simp

end Submodule
