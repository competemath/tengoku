import Tengoku.Seed.Analysis.Fourier.FourierTransformDeriv
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv

set_option autoImplicit false

open MeasureTheory Complex FourierTransform

theorem solution (j : ℕ) (ξ : ℝ) :
    ∫ x : ℝ, ((x : ℝ) : ℂ) ^ j * (Real.exp (-(Real.pi * x ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ)) =
      (2 * Real.pi * Complex.I)⁻¹ ^ j * iteratedDeriv j (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) ξ := by
  set G : ℝ → ℂ := fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ) with hGdef

  have hGc : (fun x : ℝ => cexp (-Real.pi * (1 : ℂ) * (x : ℂ) ^ 2)) = G := by
    funext x
    simp only [hGdef, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hFG : 𝓕 G = G := by
    have h := fourier_gaussian_pi (b := 1) (by simp)
    rw [hGc] at h
    rw [h]
    funext t
    simp only [one_cpow, div_one, one_mul, hGdef, Complex.ofReal_exp]
    push_cast
    ring_nf

  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (⊤ : ℕ∞) → Integrable (fun x : ℝ => x ^ n • G x) := by
    intro n _
    have h0 := (integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := n)
      (by have := n.cast_nonneg (α := ℝ); linarith)).ofReal (𝕜 := ℂ)
    have h : Integrable (fun x : ℝ => (((x ^ (n : ℝ) * Real.exp (-Real.pi * x ^ 2) : ℝ)) : ℂ)) := h0
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [hGdef, Real.rpow_natCast, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow, neg_mul]

  have hD := Real.iteratedDeriv_fourier (N := ⊤) (n := j) hint le_top
  rw [hFG] at hD

  have h1 : iteratedDeriv j G (-ξ) =
      (-2 * Real.pi * Complex.I) ^ j * ∫ x : ℝ, ((x : ℝ) : ℂ) ^ j * G x * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ)) := by
    rw [hD, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [smul_eq_mul, mul_pow]
    have : cexp (((-2 * Real.pi * x * -ξ : ℝ) : ℂ) * I) = cexp (2 * Real.pi * I * (ξ : ℂ) * (x : ℂ)) := by
      congr 1; push_cast; ring
    rw [this]
    ring

  have h2 : iteratedDeriv j G (-ξ) = (-1 : ℂ) ^ j * iteratedDeriv j G ξ := by
    have hev : (fun x : ℝ => G (-x)) = G := by funext x; simp only [hGdef, neg_sq]
    have h := iteratedDeriv_comp_neg j G ξ
    rw [hev] at h

    rw [h, Complex.real_smul]
    push_cast
    rw [← mul_assoc, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_mul]

  have hne : ((-2 * Real.pi * Complex.I : ℂ) ^ j) ≠ 0 :=
    pow_ne_zero _ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])
  have hkey := h1.symm.trans h2

  calc (∫ x : ℝ, ((x : ℝ) : ℂ) ^ j * G x * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ)))
      = ((-2 * Real.pi * Complex.I) ^ j)⁻¹ * ((-2 * Real.pi * Complex.I) ^ j *
          ∫ x : ℝ, ((x : ℝ) : ℂ) ^ j * G x * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))) := by
        rw [inv_mul_cancel_left₀ hne]
    _ = ((-2 * Real.pi * Complex.I) ^ j)⁻¹ * ((-1 : ℂ) ^ j * iteratedDeriv j G ξ) := by rw [hkey]
    _ = (2 * Real.pi * Complex.I)⁻¹ ^ j * iteratedDeriv j G ξ := by
        rw [← inv_pow, ← mul_assoc, ← mul_pow]
        congr 2
        rw [show (-2 * (Real.pi : ℂ) * Complex.I) = -(2 * Real.pi * Complex.I) by ring, inv_neg]
        ring

