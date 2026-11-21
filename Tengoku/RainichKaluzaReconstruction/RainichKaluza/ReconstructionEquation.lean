import Tengoku.RainichKaluzaReconstruction.RainichKaluza.LorentzianScalarBlock
import Tengoku.Seed.Algebra.Algebra.Basic
import Tengoku.Seed.Tactic.Abel
import Tengoku.Seed.Tactic.NoncommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinate-free reconstruction equation

This file derives the Sylvester-type equation used by the eigenbasis analysis.
The proof is valid in any associative real algebra, so matrices and linear
endomorphisms are special cases. The geometric work still has to establish the
premises from the convention-fixed EMD equations.
-/

namespace RainichKaluza

/-- **Exact noncommutative algebra theorem.** If `R = S + V`, the Maxwell part
squares to a scalar multiple of the identity, and the rank-one scalar part
squares to its trace times itself, then `V` satisfies the reconstruction
equation used throughout the project.-/
theorem reconstructionEquation_of_decomposition
    {A : Type*} [Ring A] [Algebra ℝ A]
    (S V : A) (traceV qSq : ℝ)
    (hS : S * S = qSq • (1 : A))
    (hV : V * V = traceV • V) :
    let R := S + V
    R * V + V * R - traceV • V = R * R - qSq • (1 : A) := by
  dsimp
  calc
    (S + V) * V + V * (S + V) - traceV • V =
        S * V + V * S + V * V := by
      simp only [add_mul, mul_add, hV]
      abel
    _ = (S + V) * (S + V) - qSq • (1 : A) := by
      simp only [add_mul, mul_add, hS, hV]
      abel

/-- The same identity with the Ricci-like element supplied explicitly.-/
theorem reconstructionEquation_of_eq_add
    {A : Type*} [Ring A] [Algebra ℝ A]
    (R S V : A) (traceV qSq : ℝ)
    (hR : R = S + V)
    (hS : S * S = qSq • (1 : A))
    (hV : V * V = traceV • V) :
    R * V + V * R - traceV • V = R * R - qSq • (1 : A) := by
  subst R
  exact reconstructionEquation_of_decomposition S V traceV qSq hS hV

/-- **Centralizer invariance.** An involution commuting with `R` sends every
solution of the reconstruction equation to another solution by conjugation.
Thus uniqueness can hold only modulo the involutive centralizer of the Ricci
endomorphism unless additional geometric data break that symmetry.-/
theorem reconstructionEquation_conjugation_invariant
    {A : Type*} [Ring A] [Algebra ℝ A]
    (R V C : A) (traceV qSq : ℝ)
    (hC : C * C = 1)
    (hCR : C * R = R * C)
    (hV : R * V + V * R - traceV • V =
      R * R - qSq • (1 : A)) :
    R * (C * V * C) + (C * V * C) * R -
        traceV • (C * V * C) =
      R * R - qSq • (1 : A) := by
  have htrace : (algebraMap ℝ A traceV) * C =
      C * algebraMap ℝ A traceV := Algebra.commutes traceV C
  have hq : (algebraMap ℝ A qSq) * C =
      C * algebraMap ℝ A qSq := Algebra.commutes qSq C
  simp only [Algebra.smul_def] at hV ⊢
  have hleft : R * (C * V * C) = C * (R * V) * C := by
    calc
      R * (C * V * C) = (R * C) * V * C := by ac_rfl
      _ = (C * R) * V * C := by rw [← hCR]
      _ = C * (R * V) * C := by ac_rfl
  have hright : (C * V * C) * R = C * (V * R) * C := by
    calc
      (C * V * C) * R = C * V * (C * R) := by ac_rfl
      _ = C * V * (R * C) := by rw [hCR]
      _ = C * (V * R) * C := by ac_rfl
  have hscalar : algebraMap ℝ A traceV * (C * V * C) =
      C * (algebraMap ℝ A traceV * V) * C := by
    calc
      algebraMap ℝ A traceV * (C * V * C) =
          (algebraMap ℝ A traceV * C) * V * C := by ac_rfl
      _ = (C * algebraMap ℝ A traceV) * V * C := by rw [htrace]
      _ = C * (algebraMap ℝ A traceV * V) * C := by ac_rfl
  have hRicciConj : C * (R * R) * C = R * R := by
    calc
      C * (R * R) * C = (C * R) * R * C := by ac_rfl
      _ = (R * C) * R * C := by rw [hCR]
      _ = R * (C * R) * C := by ac_rfl
      _ = R * (R * C) * C := by rw [hCR]
      _ = R * R * (C * C) := by ac_rfl
      _ = R * R := by rw [hC, mul_one]
  have hqConj : C * (algebraMap ℝ A qSq * 1) * C =
      algebraMap ℝ A qSq * 1 := by
    calc
      C * (algebraMap ℝ A qSq * 1) * C =
          (C * algebraMap ℝ A qSq) * 1 * C := by ac_rfl
      _ = (algebraMap ℝ A qSq * C) * 1 * C := by rw [← hq]
      _ = algebraMap ℝ A qSq * 1 * (C * C) := by ac_rfl
      _ = algebraMap ℝ A qSq * 1 := by rw [hC, mul_one]
  calc
    R * (C * V * C) + (C * V * C) * R -
        algebraMap ℝ A traceV * (C * V * C) =
      C * (R * V + V * R - algebraMap ℝ A traceV * V) * C := by
        rw [hleft, hright, hscalar]
        noncomm_ring
    _ = C * (R * R - algebraMap ℝ A qSq * 1) * C := by rw [hV]
    _ = R * R - algebraMap ℝ A qSq * 1 := by
      rw [mul_sub, sub_mul, hRicciConj, hqConj]

end RainichKaluza
