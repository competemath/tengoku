/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.ThreeGap.SimultaneousApprox
import Tengoku.LeanPool.LeanPool.ThreeGap.ModTwoGrowth

/-!
# The Euclidean growth inequality (instantiating the any-norm mod-2 theorem)

Instantiating `SimApprox.growth_additive_modTwo` at the **Euclidean (L²) norm** gives the growth
inequality for best simultaneous approximations in the Euclidean norm:

  `q_{n + 2^{d+1}} ≥ 2 q_{n+1} + q_n`.

For `d = 2` this is `q_{n+8} ≥ 2 q_{n+1} + q_n`, the denominator-growth input behind the Euclidean
five-distance theorem on `𝕋²`. The Euclidean norm on `Fin d → ℝ` is obtained by transporting the
`EuclideanSpace ℝ (Fin d)` norm along `EuclideanSpace.equiv`; its triangle inequality and
homogeneity come for free from that being a (continuous) linear equivalence.

Axiom-clean.
-/

@[expose] public section

namespace ThreeGap.SimApprox

variable {d : ℕ}

/-- The **Euclidean (L²) norm** on `Fin d → ℝ`, transported from `EuclideanSpace ℝ (Fin d)` along
`EuclideanSpace.equiv`. Concretely `euclNorm x = √(∑ i, (x i)²)`. -/
noncomputable def euclNorm (d : ℕ) (x : Fin d → ℝ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin d) ℝ).symm x‖

/--
@isnad1 id=le.0h2v.s4.1b679b04e9d8 from=translated src=- shape=42a2b5ba vocab=d7e18fc6
-/
theorem euclNorm_nonneg (x : Fin d → ℝ) : 0 ≤ euclNorm d x := norm_nonneg _

/--
@isnad1 id=le.0h3v.s5.21cb30e8a79e from=translated src=- shape=10558f34 vocab=51f3b9ff
-/
theorem euclNorm_tri (x y : Fin d → ℝ) : euclNorm d (x + y) ≤ euclNorm d x + euclNorm d y := by
  unfold euclNorm
  rw [map_add]
  exact norm_add_le _ _

/--
@isnad1 id=eq.0h3v.s5.5a69b03dcc08 from=translated src=- shape=b6ea3dc1 vocab=e3ca75a2
-/
theorem euclNorm_smul (c : ℝ) (x : Fin d → ℝ) : euclNorm d (c • x) = |c| * euclNorm d x := by
  unfold euclNorm
  rw [map_smul, norm_smul, Real.norm_eq_abs]

end ThreeGap.SimApprox
