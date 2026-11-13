import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTRealStabilityClosure
import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTDeterminantStability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/WuProver/lean-commutator@2f197491d436, `CommutatorTheorem/Epsilon/BTRSStabilityBridge.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Ravichandran--Srivastava stability bridge

This file connects the definite-determinant stability theorem to the minimal
stable-or-zero closure API.  It packages repeated coordinate differentiation
without making any assertion about the subsequent finite determinant
expansion into coloring polynomials.

Thus the only analytic hypothesis in this layer is the explicitly named
multivariate Gauss--Lucas/Hurwitz closure proposition.  All product,
complexification, differentiation, and diagonal-specialization steps below
are proved theorems.
-/

namespace CommutatorTheorem.BTRSStabilityBridge

open scoped BigOperators Polynomial
open Polynomial Finset
open CommutatorTheorem.BTRealStabilityClosure
open CommutatorTheorem.BTDeterminantStability

/-- A genuinely stable polynomial belongs to the stable-or-zero class.-/
theorem mvStableOrZero_of_complexStable {σ : Type*}
    {p : MvPolynomial σ ℂ} (hp : ComplexStable p) :
    MvStableOrZero p :=
  Or.inr hp

/-- Repeated coordinate partial differentiation, in the order recorded by a
list.-/
noncomputable def iteratedPDeriv {σ R : Type*} [CommSemiring R] :
    List σ → MvPolynomial σ R → MvPolynomial σ R
  | [], p => p
  | i :: is, p => iteratedPDeriv is (MvPolynomial.pderiv i p)

@[simp] theorem iteratedPDeriv_nil {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) :
    iteratedPDeriv [] p = p := rfl

@[simp] theorem iteratedPDeriv_cons {σ R : Type*} [CommSemiring R]
    (i : σ) (is : List σ) (p : MvPolynomial σ R) :
    iteratedPDeriv (i :: is) p =
      iteratedPDeriv is (MvPolynomial.pderiv i p) := rfl

/-- Repeated partial differentiation commutes with coefficient maps.-/
theorem iteratedPDeriv_map {σ R S : Type*}
    [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (is : List σ) (p : MvPolynomial σ R) :
    iteratedPDeriv is (MvPolynomial.map φ p) =
      MvPolynomial.map φ (iteratedPDeriv is p) := by
  induction is generalizing p with
  | nil => rfl
  | cons i is ih =>
      change iteratedPDeriv is
          (MvPolynomial.pderiv i (MvPolynomial.map φ p)) =
        MvPolynomial.map φ
          (iteratedPDeriv is (MvPolynomial.pderiv i p))
      rw [MvPolynomial.pderiv_map, ih]

-- Preserve the existing parameter list for downstream callers.
/-- The multivariate Gauss--Lucas/Hurwitz statement propagates stability
through any finite sequence of coordinate derivatives.-/
theorem mvStableOrZero_iteratedPDeriv
    (H : MultivariateGaussLucasHurwitz)
    {σ : Type} [Fintype σ] [DecidableEq σ]
    (is : List σ) (p : MvPolynomial σ ℂ) (hp : MvStableOrZero p) :
    MvStableOrZero (iteratedPDeriv is p) := by
  induction is generalizing p with
  | nil => exact hp
  | cons i is ih =>
      exact ih (MvPolynomial.pderiv i p)
        (mvStableOrZero_pderiv_of_gaussLucasHurwitz H p i hp)

/-- Real diagonal specialization of a multivariate polynomial.-/
noncomputable def diagonalizeReal {σ : Type*}
    (p : MvPolynomial σ ℝ) : ℝ[X] :=
  MvPolynomial.eval₂ Polynomial.C (fun _ : σ ↦ Polynomial.X) p

/-- Complexification commutes with diagonal specialization.-/
theorem map_diagonalizeReal {σ : Type*} (p : MvPolynomial σ ℝ) :
    (diagonalizeReal p).map Complex.ofRealHom =
      diagonalize (MvPolynomial.map Complex.ofRealHom p) := by
  unfold diagonalizeReal diagonalize
  change Polynomial.mapRingHom Complex.ofRealHom
      (MvPolynomial.eval₂ Polynomial.C (fun _ : σ ↦ Polynomial.X) p) =
    MvPolynomial.eval₂ Polynomial.C (fun _ : σ ↦ Polynomial.X)
      (MvPolynomial.map Complex.ofRealHom p)
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_map]
  congr 1
  · ext x
    simp
  · funext i
    simp

/-- A nonzero stable-or-zero complexification has a real-rooted real
diagonal specialization.-/
theorem realRooted_diagonalizeReal_of_stable
    {σ : Type*} {p : MvPolynomial σ ℝ}
    (hp : MvStableOrZero (MvPolynomial.map Complex.ofRealHom p))
    (hdiag : diagonalize (MvPolynomial.map Complex.ofRealHom p) ≠ 0) :
    CommutatorTheorem.RealRooted (diagonalizeReal p) := by
  apply realRooted_of_map_upperStable
  rw [map_diagonalizeReal]
  rcases (MvStableOrZero.diagonalize hp) with hzero | hstable
  · exact (hdiag hzero).elim
  · exact hstable

end CommutatorTheorem.BTRSStabilityBridge
