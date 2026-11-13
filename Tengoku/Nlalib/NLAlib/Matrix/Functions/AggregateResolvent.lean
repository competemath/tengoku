import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.CStarAlgebra.AggregateProducts
import Tengoku.Nlalib.NLAlib.Matrix.Functions.HermitianResolvent
import Tengoku.Seed.Analysis.Matrix.Order
import Tengoku.Seed.Tactic.Abel
import Tengoku.Seed.Tactic.GCongr
import Tengoku.Seed.Tactic.NoncommRing
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Aggregate cubic resolvent words

Restoring a common Hermitian resolvent before summation retains the actual
squared sums of the endpoint directions and perturbations. Distinct endpoint
perturbations are allowed; the cubic specialization has the explicit constants
`R / eta^4` and `2 alpha^2 R^3 / eta^6`.

Source: Tatiana Brailovskaya and Ramon van Handel, *Universality and sharp
matrix concentration inequalities*, arXiv:2201.05142v3 (2024), §6.4, proof
of Lemma 6.11. These deterministic bounds support the atlas result
`matrix-resolvent-gaussian-universality`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
local notation "M" => Matrix n n ℂ

end NLAlib

namespace NLAlib
open scoped Matrix MatrixOrder ComplexOrder
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
local notation "M" => Matrix n n ℂ

/-- The first resolvent identity restores the common unperturbed resolvent
at the left end of a real Hermitian perturbation.
@isnad1 id=eq.3h5v.s8.b2ef240c7780 from=translated src=- shape=b33561c6 vocab=6a5a690f
-/
theorem resolvent_sub_smul_eq_sub_mul_resolvent (A Z : M) (α : ℝ) (ζ : ℂ)
    (hA : A.IsHermitian) (hZ : Z.IsHermitian) (hζ : ζ.im ≠ 0) :
    resolvent (A - α • Z) ζ = resolvent A ζ -
      α • (resolvent A ζ * Z * resolvent (A - α • Z) ζ) := by
  have hB := hA.sub (hZ.smul (isSelfAdjoint_iff.mpr (star_trivial α)))
  have h := Matrix.inv_sub_inv (A := ζ • (1 : M) - A)
    (B := ζ • (1 : M) - (A - α • Z))
    ⟨fun _ => hB.isUnit_smul_one_sub_of_im_ne_zero hζ,
      fun _ => hA.isUnit_smul_one_sub_of_im_ne_zero hζ⟩
  have he : (ζ • (1 : M) - (A - α • Z)) - (ζ • (1 : M) - A) = α • Z := by abel
  rw [he, Matrix.mul_smul, Matrix.smul_mul,
    ← resolvent_matrix_eq_inv, ← resolvent_matrix_eq_inv] at h
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm

/-- The first resolvent identity restores the common unperturbed resolvent
at the right end of a real Hermitian perturbation.
@isnad1 id=eq.3h5v.s8.01b7de214867 from=translated src=- shape=f412f230 vocab=6a5a690f
-/
theorem resolvent_sub_smul_eq_sub_resolvent_mul (A Z : M) (α : ℝ) (ζ : ℂ)
    (hA : A.IsHermitian) (hZ : Z.IsHermitian) (hζ : ζ.im ≠ 0) :
    resolvent (A - α • Z) ζ = resolvent A ζ -
      α • (resolvent (A - α • Z) ζ * Z * resolvent A ζ) := by
  have hB := hA.sub (hZ.smul (isSelfAdjoint_iff.mpr (star_trivial α)))
  have h := Matrix.inv_sub_inv (A := ζ • (1 : M) - (A - α • Z))
    (B := ζ • (1 : M) - A)
    ⟨fun _ => hA.isUnit_smul_one_sub_of_im_ne_zero hζ,
      fun _ => hB.isUnit_smul_one_sub_of_im_ne_zero hζ⟩
  have he : (ζ • (1 : M) - A) - (ζ • (1 : M) - (A - α • Z)) = (-α) • Z := by
    simp only [neg_smul]
    abel
  rw [he, Matrix.mul_smul, Matrix.smul_mul,
    ← resolvent_matrix_eq_inv, ← resolvent_matrix_eq_inv, neg_smul] at h
  exact sub_eq_iff_eq_add.mp h |>.trans (by abel)

end NLAlib
