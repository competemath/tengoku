/-
Coefficienti canonici della riduzione H4.

Ogni polinomio intero viene ridotto modulo `X²-5X+5`; i coefficienti
costante e lineare della riduzione sono quindi definiti nel kernel, non
affidati a uno script esterno. In particolare questo vale per
`Φₘ(γ)`. La seconda forma `γᵏ-γ'` è espressa dalla ricorrenza `gammaU`.
-/
import Tengoku.AgrawalR5.AgrawalCore.QuadraticGamma
import Tengoku.Seed.Algebra.Polynomial.Degree.IsMonicOfDegree
import Tengoku.Seed.RingTheory.Polynomial.Cyclotomic.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

/-- Il polinomio minimo quadratico di `γ=(5+√5)/2`.-/
noncomputable def gammaMinPoly : Polynomial ℤ :=
  X ^ 2 - C 5 * X + C 5

theorem gammaMinPoly_monic : gammaMinPoly.Monic := by
  unfold gammaMinPoly
  exact (Polynomial.isMonicOfDegree_sub_add_two (5 : ℤ) 5).monic

theorem gammaMinPoly_natDegree : gammaMinPoly.natDegree = 2 := by
  unfold gammaMinPoly
  exact (Polynomial.isMonicOfDegree_sub_add_two (5 : ℤ) 5).natDegree_eq

theorem gammaMinPoly_ne_one : gammaMinPoly ≠ 1 := by
  intro h
  have := congrArg Polynomial.natDegree h
  rw [gammaMinPoly_natDegree] at this
  norm_num at this

/-- Coefficiente costante della riduzione quadratica.-/
noncomputable def gammaCoeff0 (P : Polynomial ℤ) : ℤ :=
  (P %ₘ gammaMinPoly).coeff 0

/-- Coefficiente lineare della riduzione quadratica.-/
noncomputable def gammaCoeff1 (P : Polynomial ℤ) : ℤ :=
  (P %ₘ gammaMinPoly).coeff 1

/-- La riduzione modulo il polinomio quadratico ha esattamente i due
coefficienti dichiarati.-/
theorem gamma_remainder_eq (P : Polynomial ℤ) :
    P %ₘ gammaMinPoly =
      C (gammaCoeff1 P) * X + C (gammaCoeff0 P) := by
  apply Polynomial.eq_X_add_C_of_natDegree_le_one
  have hlt :=
    Polynomial.natDegree_modByMonic_lt P gammaMinPoly_monic gammaMinPoly_ne_one
  rw [gammaMinPoly_natDegree] at hlt
  omega

/-- Valutazione del polinomio minimo in una radice astratta.-/
theorem eval₂_gammaMinPoly {R : Type*} [CommRing R] (f : ℤ →+* R)
    (γ : R) (hγ : γ ^ 2 = 5 * γ - 5) :
    Polynomial.eval₂ f γ gammaMinPoly = 0 := by
  simp [gammaMinPoly]
  linear_combination hγ

/-- Ogni valutazione in `γ` è la valutazione dei due coefficienti
canonici della riduzione.-/
theorem eval₂_eq_gamma_coeffs {R : Type*} [CommRing R] (f : ℤ →+* R)
    (γ : R) (hγ : γ ^ 2 = 5 * γ - 5) (P : Polynomial ℤ) :
    Polynomial.eval₂ f γ P =
      f (gammaCoeff0 P) + f (gammaCoeff1 P) * γ := by
  have hroot := eval₂_gammaMinPoly f γ hγ
  have hmod :
      Polynomial.eval₂ f γ (P %ₘ gammaMinPoly) =
        Polynomial.eval₂ f γ P :=
    Polynomial.eval₂_modByMonic_eq_self_of_root hroot
  rw [gamma_remainder_eq] at hmod
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X] at hmod
  simpa [add_comm, mul_comm] using hmod.symm

/-- I coefficienti interi canonici di `Φₘ(γ)`.-/
noncomputable def cyclotomicGammaCoeffs (m : ℕ) : ℤ × ℤ :=
  (gammaCoeff0 (Polynomial.cyclotomic m ℤ),
    gammaCoeff1 (Polynomial.cyclotomic m ℤ))

/-- Valutazione kernel-pura del polinomio ciclotomico nella base
`1,γ`.-/
theorem eval₂_cyclotomic_gamma_coeffs {R : Type*} [CommRing R]
    (f : ℤ →+* R) (γ : R) (hγ : γ ^ 2 = 5 * γ - 5) (m : ℕ) :
    Polynomial.eval₂ f γ (Polynomial.cyclotomic m ℤ) =
      f (cyclotomicGammaCoeffs m).1 +
        f (cyclotomicGammaCoeffs m).2 * γ := by
  exact eval₂_eq_gamma_coeffs f γ hγ (Polynomial.cyclotomic m ℤ)

/-- La seconda forma del risultante primitivo:
`γᵏ-γ' = -5(U_{k-1}+1) + (U_k+1)γ`.-/
theorem gamma_pow_sub_conj {R : Type*} [CommRing R] (γ : R)
    (hγ : γ ^ 2 = 5 * γ - 5) {k : ℕ} (hk : 1 ≤ k) :
    γ ^ k - (5 - γ) =
      ((-5 * (gammaU (k - 1) + 1) : ℤ) : R) +
        ((gammaU k + 1 : ℤ) : R) * γ := by
  rw [gamma_pow_formula γ hγ hk]
  push_cast
  ring

end AgrawalCore
