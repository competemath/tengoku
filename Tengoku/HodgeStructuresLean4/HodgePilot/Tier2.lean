import Tengoku.HodgeStructuresLean4.HodgePilot.Tier1

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tier 2: `σ` is an involution and is `starRingEnd ℂ`-semilinear; package it
as a semilinear map. This is the referee-flagged hardest design step. -/

open scoped TensorProduct

noncomputable section

namespace HodgePilot

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

/--
@isnad1 id=eq.0h2v.s10.1df60f8389e6 from=translated src=- shape=f1d3ebae vocab=7869a438
-/
theorem sigmaR_involutive (x : ℂ ⊗[ℝ] V) : sigmaR V (sigmaR V x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/--
@isnad1 id=eq.0h3v.s10.a2f6e7bbd58a from=translated src=- shape=75c60031 vocab=fb279438
-/
theorem sigmaR_smul (c : ℂ) (x : ℂ ⊗[ℝ] V) :
    sigmaR V (c • x) = (starRingEnd ℂ) c • sigmaR V x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c' v =>
      rw [TensorProduct.smul_tmul', sigmaR_tmul, sigmaR_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy =>
      rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- Conjugation on `ℂ ⊗[ℝ] V` as a `starRingEnd ℂ`-semilinear map.-/
def sigma : (ℂ ⊗[ℝ] V) →ₛₗ[starRingEnd ℂ] (ℂ ⊗[ℝ] V) where
  toFun := sigmaR V
  map_add' := map_add (sigmaR V)
  map_smul' := sigmaR_smul V

/--
@isnad1 id=eq.0h2v.s10.67c0183fecb7 from=translated src=- shape=1b22459c vocab=31559931
-/
@[simp] theorem sigma_apply (x : ℂ ⊗[ℝ] V) : sigma V x = sigmaR V x := rfl

/--
@isnad1 id=eq.0h2v.s10.96bee62649dd from=translated src=- shape=0fb1eb48 vocab=f01a0554
-/
theorem sigma_sigma (x : ℂ ⊗[ℝ] V) : sigma V (sigma V x) = x := by
  simp [sigmaR_involutive]

end HodgePilot
