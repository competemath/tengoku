/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Tengoku
import Tengoku.LeanPool.LeanPool.LeanModularForms.Modularforms.SlashActionAuxil

/-! # E2 -/

@[expose] public section

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups
open ArithmeticFunction

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
open scoped ArithmeticFunction.sigma

noncomputable section

/-- Compatibility alias for Mathlib's `EisensteinSeries.G2`. -/
def G₂ : ℍ → ℂ := EisensteinSeries.G2

/-- Compatibility alias for Mathlib's `EisensteinSeries.E2`. -/
def E₂ : ℍ → ℂ := EisensteinSeries.E2

/-- Compatibility alias for Mathlib's `EisensteinSeries.D2`. -/
def D₂ (γ : SL(2, ℤ)) : ℍ → ℂ := EisensteinSeries.D2 γ

/--
@isnad1 id=eq.0h2v.s8.37ab535566e8 from=translated src=- shape=bb8a48bc vocab=11a691d9
-/
lemma D₂_apply (γ : SL(2, ℤ)) (z : ℍ) :
    D₂ γ z = (2 * π * Complex.I * γ 1 0) / (γ 1 0 * z + γ 1 1) := by rfl

/--
@isnad1 id=eq.0h0v.s4.d0ef2ffae168 from=translated src=- shape=35dee393 vocab=ca27a0ef
-/
lemma D2_T : D₂ ModularGroup.T = 0 := by simpa [D₂] using (EisensteinSeries.D2_T)

/--
@isnad1 id=eq.0h1v.s5.5be45f18d0c3 from=translated src=- shape=f4829966 vocab=10c7a262
-/
lemma D2_S (z : ℍ) : D₂ ModularGroup.S z = 2 * (π : ℂ) * Complex.I / z :=
  EisensteinSeries.D2_S z

/--
@isnad1 id=eq.0h1v.s7.c5fa6f06f666 from=translated src=- shape=908884a8 vocab=9eb45143
-/
lemma G2_q_exp (z : ℍ) : G₂ z = (2 * riemannZeta 2) - 8 * π ^ 2 *
    ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * n * z) := by
  calc
    G₂ z = (2 * riemannZeta 2) - 8 * π ^ 2 *
        ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * z) ^ (n : ℕ) := by
          simpa [G₂] using (EisensteinSeries.G2_eq_tsum_cexp z)
    _ = (2 * riemannZeta 2) - 8 * π ^ 2 *
        ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * n * z) := by
          congr 2
          apply tsum_congr
          intro n
          rw [← Complex.exp_nat_mul]
          ring_nf

/--
@isnad1 id=eq.0h0v.s6.68e2b6871dc7 from=translated src=- shape=656092e4 vocab=d37c571e
-/
lemma G2_periodic : (G₂ ∣[(2 : ℤ)] ModularGroup.T) = G₂ := by
  simpa [G₂] using (EisensteinSeries.G2_T_transform)

/--
@isnad1 id=eq.0h1v.s6.e3d9ff073130 from=translated src=- shape=ef0a7578 vocab=964e6c82
-/
lemma G₂_transform (γ : SL(2, ℤ)) : (G₂ ∣[(2 : ℤ)] γ) = G₂ - (D₂ γ) := by
  simpa [G₂, D₂] using (EisensteinSeries.G2_slash_action γ)

/-- E₂ is 1-periodic: E₂(z + 1) = E₂(z).
@isnad1 id=eq.0h1v.s5.6ee11c207b79 from=translated src=- shape=ba65eac2 vocab=906674ed
-/
lemma E₂_periodic (z : ℍ) : E₂ ((1 : ℝ) +ᵥ z) = E₂ z := by
  have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.T) z
  rw [modular_slash_T_apply] at h
  simpa [E₂, EisensteinSeries.D2_T] using h

/--
@isnad1 id=eq.0h1v.s6.f57bcdb77f36 from=translated src=- shape=745bca21 vocab=2d801ce1
-/
lemma E₂_transform (z : ℍ) : (E₂ ∣[(2 : ℤ)] ModularGroup.S) z =
    E₂ z + 6 / (π * Complex.I * z) := by
  have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.S) z
  have h' : (E₂ ∣[(2 : ℤ)] ModularGroup.S) z =
      E₂ z - (1 / (2 * riemannZeta 2)) * (2 * π * Complex.I / z) := by
    simpa [E₂, EisensteinSeries.D2_S, smul_eq_mul] using h
  rw [riemannZeta_two] at h'
  have hpi : (π : ℂ) ≠ 0 := by simp
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  calc
    (E₂ ∣[(2 : ℤ)] ModularGroup.S) z =
        E₂ z - 1 / (2 * (π ^ 2 / (6 : ℂ))) * (2 * π * Complex.I / z) := h'
    _ = E₂ z + 6 / (π * Complex.I * z) := by
      field_simp [hpi, hI, hz]
      ring_nf
      simp [Complex.I_sq, add_comm]

/-- E₂ transforms under SL(2,ℤ) as: E₂ ∣[2] γ = E₂ - α • D₂ γ where α = 1/(2ζ(2)).
@isnad1 id=eq.0h1v.s7.e8c11c7781b1 from=translated src=- shape=0dee3394 vocab=ababa0a7
-/
lemma E₂_slash_transform (γ : SL(2, ℤ)) :
    (E₂ ∣[(2 : ℤ)] γ) = E₂ - (1 / (2 * riemannZeta 2)) • D₂ γ := by
  simpa [E₂, D₂] using (EisensteinSeries.E2_slash_action γ)

/-- E₂ transforms under S as: E₂(-1/z) = z² · (E₂(z) + 6/(πIz)).
@isnad1 id=eq.0h1v.s7.34e90380038b from=translated src=- shape=bfe14996 vocab=bd0758ab
-/
lemma E₂_S_transform (z : ℍ) :
    E₂ (ModularGroup.S • z) = z ^ 2 * (E₂ z + 6 / (π * Complex.I * z)) := by
  have h := E₂_transform z
  rw [SL_slash_apply, ModularGroup.denom_S, zpow_neg, zpow_two] at h
  have hz2 : (z : ℂ) * (z : ℂ) ≠ 0 := mul_ne_zero (ne_zero z) (ne_zero z)
  rw [sq, mul_comm]
  -- `only` is required here; without it simp rewrites the congrArg term structure
  simpa only [mul_assoc, inv_mul_cancel₀ hz2, mul_one] using congrArg (· * ((z : ℂ) * (z : ℂ))) h

private lemma cexp_succ_eq_pow (z : ℍ) (n : ℕ) :
    cexp (2 * π * Complex.I * (n + 1) * z) = cexp (2 * π * Complex.I * z) ^ (n + 1) := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/--
@isnad1 id=eq.0h1v.s8.6d79ae829a6f from=translated src=- shape=89e532c8 vocab=c14d33ec
-/
lemma tsum_eq_tsum_sigma (z : ℍ) : ∑' n : ℕ, (n + 1) *
    cexp (2 * π * Complex.I * (n + 1) * z) / (1 - cexp (2 * π * Complex.I * (n + 1) * z)) =
    ∑' n : ℕ, sigma 1 (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) := by
  let q : ℂ := cexp (2 * π * Complex.I * z)
  let f : ℕ → ℂ := fun n => (n : ℂ) ^ 1 * q ^ n / (1 - q ^ n)
  let g : ℕ → ℂ := fun n => sigma 1 n * q ^ n
  have h :
      ∑' n : ℕ+, f n = ∑' n : ℕ+, g n := by
    simpa [f, g, q] using
      (tsum_pow_div_one_sub_eq_tsum_sigma (r := q) (UpperHalfPlane.norm_exp_two_pi_I_lt_one z) 1)
  have hf := tsum_pnat_eq_tsum_succ (f := f)
  have hg := tsum_pnat_eq_tsum_succ (f := g)
  rw [hf, hg] at h
  calc
    ∑' n : ℕ, (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) /
        (1 - cexp (2 * π * Complex.I * (n + 1) * z))
      = ∑' n : ℕ, f (n + 1) := tsum_congr fun n => by simp [f, pow_one, cexp_succ_eq_pow z n, q]
    _ = ∑' n : ℕ, g (n + 1) := h
    _ = ∑' n : ℕ, sigma 1 (n + 1) * cexp (2 * π * Complex.I * (n + 1) * z) :=
        tsum_congr fun n => by simp [g, cexp_succ_eq_pow z n, q]

/--
@isnad1 id=eq.0h1v.s7.894e5a19f905 from=translated src=- shape=656dae2e vocab=ebe3e3b7
-/
lemma E₂_eq (z : UpperHalfPlane) : E₂ z =
    1 - 24 * ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * n * z) /
                        (1 - cexp (2 * π * Complex.I * n * z)) := by
  have hpi : (π : ℂ) ≠ 0 := by simp
  rw [E₂, EisensteinSeries.E2]
  simp only [one_div, mul_inv_rev, Pi.smul_apply, smul_eq_mul]
  rw [EisensteinSeries.G2_eq_tsum_cexp, mul_sub]
  congr 1
  · rw [riemannZeta_two]; field_simp
  · rw [← mul_assoc]
    congr 1
    · rw [riemannZeta_two]; grind
    · calc
        ∑' n : ℕ+, sigma 1 n * cexp (2 * π * Complex.I * z) ^ (n : ℕ)
            = ∑' n : ℕ+, (n : ℂ) ^ 1 * cexp (2 * π * Complex.I * z) ^ (n : ℕ) /
                (1 - cexp (2 * π * Complex.I * z) ^ (n : ℕ)) := by
                  simpa [pow_one] using
                    (tsum_pow_div_one_sub_eq_tsum_sigma
                      (r := cexp (2 * π * Complex.I * z))
                        (UpperHalfPlane.norm_exp_two_pi_I_lt_one z) 1).symm
        _ = ∑' n : ℕ+, ↑n * cexp (2 * π * Complex.I * n * z) /
            (1 - cexp (2 * π * Complex.I * n * z)) :=
              tsum_congr fun n => by
                simp [pow_one, show cexp (2 * π * Complex.I * ↑n * z) =
                    cexp (2 * π * Complex.I * z) ^ (n : ℕ) from
                  by rw [← Complex.exp_nat_mul]; ring_nf]
