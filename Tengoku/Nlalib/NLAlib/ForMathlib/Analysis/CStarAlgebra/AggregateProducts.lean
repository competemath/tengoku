import Tengoku.Seed.Analysis.CStarAlgebra.Module.Constructions
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NoncommRing
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Aggregate product bounds in a C⋆-algebra

Finite Hilbert C⋆-module Cauchy--Schwarz retains both aggregate Gram
matrices in a sum of products. Uniformly bounded middle factors yield
an arithmetic-mean bound with explicit constant `1/2`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CStarAlgebra

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

/-- Operator Cauchy--Schwarz for a finite sum of products retains the norms
of the two aggregate Gram matrices.
@isnad1 id=le.0h4v.s8.d2ca3bd39364 from=translated src=- shape=a901360f vocab=a1ff3fda
-/
theorem norm_sum_mul_sq_le (a b : ι → A) :
    ‖∑ i, a i * b i‖ ^ 2 ≤
      ‖∑ i, a i * star (a i)‖ * ‖∑ i, star (b i) * b i‖ := by
  let x : WithCStarModule A (ι → A) :=
    (WithCStarModule.equiv A (ι → A)).symm (fun i => star (b i))
  let y : WithCStarModule A (ι → A) :=
    (WithCStarModule.equiv A (ι → A)).symm a
  have h := CStarModule.norm_inner_le (A := A) (WithCStarModule A (ι → A)) (x := x) (y := y)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [mul_pow, WithCStarModule.pi_norm_sq, WithCStarModule.pi_inner,
    WithCStarModule.inner_def, x, y, WithCStarModule.equiv_symm_pi_apply,
    star_star, mul_comm (‖∑ i, star (b i) * b i‖)] using hsq

/-- The Gram matrix of a sum is at most twice the sum of its two Gram
matrices in the positive order.
@isnad1 id=le.0h3v.s8.6824f847a042 from=translated src=- shape=6afd0666 vocab=017bed24
-/
theorem add_mul_star_add_le (a b : A) :
    (a + b) * star (a + b) ≤
      (2 : ℝ) • (a * star a) + (2 : ℝ) • (b * star b) := by
  rw [← sub_nonneg]
  convert mul_star_self_nonneg (a - b) using 1
  simp only [two_smul, star_add, star_sub]
  noncomm_ring

end CStarAlgebra
