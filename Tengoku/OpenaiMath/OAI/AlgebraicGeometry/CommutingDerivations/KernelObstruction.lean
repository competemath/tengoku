import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.AbhyankarSathaye.Stabilization
import Tengoku

namespace OAI

/-! Every element of the proposed common kernel has a critical point.
This proves the coordinate obstruction for all such elements, independently
of whether they generate that subalgebra. It does not assert kernel equality. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

/--
@isnad1 id=eq.1h6v.s10.8256108506c5 from=translated src=- shape=22c19a4c vocab=24911554
-/
theorem critical_aeval {σ B : Type*} [CommRing B]
    (f : MvPolynomial σ B) (point : σ → B)
    (hc : ∀ i, eval point (pderiv i f) = 0) (q : Polynomial B) (i : σ) :
    eval point (pderiv i (Polynomial.aeval f q)) = 0 := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => simp only [map_add, hq, hr, add_zero]
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp [Polynomial.aeval_C, MvPolynomial.algebraMap_eq, hc]

/--
@isnad1 id=not.1h5v.s10.dc1f312a1cb0 from=translated src=- shape=acfe3c49 vocab=d50f6868
-/
theorem no_coordinate_aeval_of_critical {σ B : Type*} [Fintype σ] [CommRing B]
    [Nontrivial B] (f : MvPolynomial σ B) (point : σ → B)
    (hc : ∀ i, eval point (pderiv i f) = 0) (q : Polynomial B) :
    ¬ ∃ (e : MvPolynomial σ B ≃ₐ[B] MvPolynomial σ B) (i : σ),
      e (X i) = Polynomial.aeval f q :=
  no_coordinate_of_critical _ point (critical_aeval f point hc q)

/--
@isnad1 id=not.1h2v.s9.b1cca95bd582 from=translated src=- shape=d90735b2 vocab=f1bed3e1
-/
theorem polynomial_in_extendedF_not_coordinate {n : ℕ} (hn : 4 ≤ n)
    (q : Polynomial ℂ) :
    ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (i : Fin n),
      e (X i) = Polynomial.aeval (extendedF hn) q :=
  no_coordinate_aeval_of_critical (extendedF hn) (extendedPoint hn)
    (extendedF_critical hn) q

/-- In particular, no generator of a common kernel equal to `C[F_n]` can
be a coordinate. The explicit polynomial-expression hypothesis suffices.
@isnad1 id=not.2h2v.s9.a4e281e3aff6 from=translated src=- shape=2173809c vocab=f1bed3e1
-/
theorem element_of_extendedF_subring_not_coordinate {n : ℕ} (hn : 4 ≤ n)
    (g : MvPolynomial (Fin n) ℂ)
    (hg : ∃ q : Polynomial ℂ, g = Polynomial.aeval (extendedF hn) q) :
    ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (i : Fin n),
      e (X i) = g := by
  obtain ⟨q, rfl⟩ := hg
  exact polynomial_in_extendedF_not_coordinate hn q

end AbhyankarSathaye.CommutingDerivations

end

end OAI
