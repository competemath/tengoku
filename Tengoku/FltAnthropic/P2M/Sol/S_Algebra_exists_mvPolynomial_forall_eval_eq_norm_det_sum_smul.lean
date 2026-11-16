import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul

set_option autoImplicit false

open MvPolynomial

namespace P2mPoly

variable (E : Type) [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
  (m : Type) [Fintype m] [DecidableEq m] (n : ℕ) (e : Fin n → Matrix m m E)

noncomputable def genMat : Matrix m m (MvPolynomial (Fin n) E) :=
  ∑ a, (X a : MvPolynomial (Fin n) E) • (e a).map (C : E → MvPolynomial (Fin n) E)

noncomputable def genDet : MvPolynomial (Fin n) E := (genMat E m n e).det

noncomputable def evE (c : Fin n → ℝ) : MvPolynomial (Fin n) E →+* E :=
  MvPolynomial.eval fun a => algebraMap ℝ E (c a)

/--
@isnad1 id=eq.0h5v.s8.f75929227f01 from=translated src=- shape=b47b56e9 vocab=aed0f139
-/
theorem evE_genMat (c : Fin n → ℝ) :
    (evE E n c).mapMatrix (genMat E m n e) = ∑ a, c a • e a := by
  ext p q
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  simp only [genMat, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, evE, MvPolynomial.eval_X, MvPolynomial.eval_C, Algebra.smul_def]

/--
@isnad1 id=eq.0h5v.s8.d3dbab7e5410 from=translated src=- shape=fcc0165c vocab=2c345a66
-/
theorem evE_genDet (c : Fin n → ℝ) : evE E n c (genDet E m n e) = (∑ a, c a • e a).det := by
  rw [genDet, RingHom.map_det, evE_genMat]

/--
@isnad1 id=eq.0h4v.s8.40f68cfe7003 from=translated src=- shape=809704aa vocab=91074b71
-/
theorem evE_eq_sum (c : Fin n → ℝ) (D : MvPolynomial (Fin n) E) :
    evE E n c D = ∑ s ∈ D.support, (s.prod fun a k => c a ^ k) • MvPolynomial.coeff s D := by
  conv_lhs => rw [MvPolynomial.as_sum D]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [evE, MvPolynomial.eval_monomial, Algebra.smul_def, mul_comm]
  congr 1
  rw [Finsupp.prod, Finsupp.prod, map_prod]
  exact Finset.prod_congr rfl fun a _ => by rw [map_pow]

variable {κ : Type} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℝ E)

noncomputable def lmPoly : Matrix κ κ (MvPolynomial (Fin n) ℝ) :=
  ∑ s ∈ (genDet E m n e).support,
    (Algebra.leftMulMatrix b (MvPolynomial.coeff s (genDet E m n e))).map fun r => MvPolynomial.monomial s r

/--
@isnad1 id=eq.0h7v.s8.66c6a6dc1105 from=translated src=- shape=bd2d3096 vocab=e2529598
-/
theorem eval_lmPoly (c : Fin n → ℝ) :
    (MvPolynomial.eval c).mapMatrix (lmPoly E m n e b) =
      Algebra.leftMulMatrix b (evE E n c (genDet E m n e)) := by
  rw [evE_eq_sum, map_sum]
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, lmPoly, Matrix.sum_apply, map_sum,
    MvPolynomial.eval_monomial, map_smul, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

end P2mPoly

open P2mPoly in
/--
@isnad1 id=ex.0h4v.s8.ba3054614c50 from=translated src=- shape=fb815832 vocab=d9a8106d
-/
theorem solution
    (E : Type) [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
    (m : Type) [Fintype m] [DecidableEq m]
    (n : ℕ) (e : Fin n → Matrix m m E) :
    ∃ P : MvPolynomial (Fin n) ℝ, ∀ c : Fin n → ℝ,
      MvPolynomial.eval c P = Algebra.norm ℝ (Matrix.det (∑ a, c a • e a)) := by
  classical
  let b := Module.Free.chooseBasis ℝ E
  refine ⟨(lmPoly E m n e b).det, fun c => ?_⟩
  rw [RingHom.map_det, eval_lmPoly, ← Algebra.norm_eq_matrix_det b, evE_genDet]

