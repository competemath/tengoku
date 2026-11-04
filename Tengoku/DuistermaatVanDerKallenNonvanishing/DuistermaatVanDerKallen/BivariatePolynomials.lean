import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicSets
import Tengoku.Seed.Algebra.MvPolynomial.Equiv
import Tengoku.Seed.Algebra.Polynomial.Roots
import Tengoku.Seed.Topology.Algebra.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact conversion from coordinate-polynomial scalar graphs to polynomials
in an output variable with polynomial input coefficients. Nonzero bivariate
polynomials preserve their output degree outside a finite input set. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set

def scalarTargetPolynomialEquiv (ι : Type*) :
    MvPolynomial (ι ⊕ Unit) ℝ ≃ₐ[ℝ] Polynomial (MvPolynomial ι ℝ) :=
  (MvPolynomial.renameEquiv ℝ (Equiv.optionEquivSumPUnit ι).symm).trans
    (MvPolynomial.optionEquivLeft ℝ ι)

theorem eval_scalarTargetPolynomialEquiv {ι : Type*}
    (p : MvPolynomial (ι ⊕ Unit) ℝ) (x : ι → ℝ) (y : ℝ) :
    ((scalarTargetPolynomialEquiv ι p).map (MvPolynomial.eval x)).eval y =
      MvPolynomial.eval (Sum.elim x (fun _ => y)) p := by
  rw [scalarTargetPolynomialEquiv, AlgEquiv.trans_apply,
    ← MvPolynomial.optionEquivLeft_elim_eval]
  simp only [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename]
  congr 1
  congr 1
  funext i
  cases i <;> rfl

def bivariatePolynomialEquiv :
    MvPolynomial (Unit ⊕ Unit) ℝ ≃+* Polynomial (Polynomial ℝ) :=
  (scalarTargetPolynomialEquiv Unit).toRingEquiv.trans
    (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv ℝ Unit).toRingEquiv)

theorem eval_bivariatePolynomialEquiv (p : MvPolynomial (Unit ⊕ Unit) ℝ)
    (x y : ℝ) :
    ((bivariatePolynomialEquiv p).map (Polynomial.evalRingHom x)).eval y =
      MvPolynomial.eval (Sum.elim (fun _ => x) (fun _ => y)) p := by
  rw [bivariatePolynomialEquiv, RingEquiv.trans_apply, Polynomial.mapEquiv_apply,
    Polynomial.map_map]
  have he : (Polynomial.evalRingHom x).comp
      (↑(MvPolynomial.uniqueAlgEquiv ℝ Unit).toRingEquiv :
        MvPolynomial Unit ℝ →+* Polynomial ℝ) =
      MvPolynomial.eval (fun _ : Unit => x) := by
    apply RingHom.ext
    intro q
    exact MvPolynomial.eval₂_uniqueAlgEquiv (σ := Unit) (f := q)
      (φ := RingHom.id ℝ) (a := fun _ => x)
  rw [he]
  exact eval_scalarTargetPolynomialEquiv p _ y

theorem polynomial_specialization_nonzero_outside_finite
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x ∉ E,
      P.map (Polynomial.evalRingHom x) ≠ 0 ∧
      (P.map (Polynomial.evalRingHom x)).natDegree = P.natDegree := by
  refine ⟨{x | P.leadingCoeff.eval x = 0},
    Polynomial.finite_setOfPred_isRoot (Polynomial.leadingCoeff_ne_zero.mpr hP), ?_⟩
  intro x hx
  have hc : (Polynomial.evalRingHom x) P.leadingCoeff ≠ 0 := hx
  refine ⟨?_, Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hc⟩
  intro hz
  have hcoef := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero
    (Polynomial.evalRingHom x) hc
  rw [hz, Polynomial.leadingCoeff_zero] at hcoef
  exact hc hcoef.symm

end
end DuistermaatVanDerKallen
