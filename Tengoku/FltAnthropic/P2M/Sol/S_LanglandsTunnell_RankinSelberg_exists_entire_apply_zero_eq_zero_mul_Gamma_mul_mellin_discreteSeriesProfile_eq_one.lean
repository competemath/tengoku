import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv
import Tengoku.FltAnthropic.Theorems.Thm_Complex_mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_discreteSeriesProfile_eq_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_entire_apply_zero_eq_zero_mul_Gamma_mul_mellin_discreteSeriesProfile_eq_one

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=ex.2h2v.s8.571e5de4eec5 from=translated src=- shape=37c67d55 vocab=0d8e4558
-/
theorem solution
    (C k : ℝ) (hC : 0 < C) (hk : 0 < k) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ H 0 = 0 ∧
      ∀ s : ℂ, 1 - k < s.re → 0 < s.re →
        H s * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
          ∫ y : ℝ, (((if 0 < y then C * y ^ k * Real.exp (-(4 * Real.pi * y)) else 0 : ℝ) : ℝ) : ℂ) *
            ((|y| : ℝ) : ℂ) ^ (s - 2)) = 1 := by
  have hπ0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have h4π : (0 : ℝ) < 4 * Real.pi := by positivity
  have h4π0 : ((4 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h4π.ne'
  have hC0 : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'

  refine ⟨fun s => 2 * (C : ℂ)⁻¹ * (Real.pi : ℂ) ^ s * ((4 * Real.pi : ℝ) : ℂ) ^ (s - 1 + (k : ℂ)) *
      (Complex.Gamma s)⁻¹ * (Complex.Gamma (s - 1 + (k : ℂ)))⁻¹, ?_, ?_, ?_⟩
  ·
    intro s
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ z) s :=
      differentiableAt_id.const_cpow (Or.inl hπ0)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => ((4 * Real.pi : ℝ) : ℂ) ^ (z - 1 + (k : ℂ))) s :=
      ((differentiableAt_id.sub_const 1).add_const (k : ℂ)).const_cpow (Or.inl h4π0)
    have h3 : DifferentiableAt ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) s :=
      Complex.differentiable_one_div_Gamma s
    have h4 : DifferentiableAt ℂ (fun z : ℂ => (Complex.Gamma (z - 1 + (k : ℂ)))⁻¹) s := by
      have hg : DifferentiableAt ℂ (fun w : ℂ => (Complex.Gamma w)⁻¹) (s - 1 + (k : ℂ)) :=
        Complex.differentiable_one_div_Gamma _
      have hf : DifferentiableAt ℂ (fun z : ℂ => z - 1 + (k : ℂ)) s :=
        (differentiableAt_id.sub_const 1).add_const _
      have hcomp := hg.comp s hf
      exact hcomp
    exact ((((differentiableAt_const _).mul h1).mul h2).mul h3).mul h4
  ·
    simp [Complex.Gamma_zero]
  · intro s hs1 hs0

    have hmel := Complex.mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq k (4 * Real.pi) h4π (s - 1)
      (by simp; linarith)
    obtain ⟨-, hmel⟩ := hmel
    have hint : ∫ y : ℝ, (((if 0 < y then C * y ^ k * Real.exp (-(4 * Real.pi * y)) else 0 : ℝ) : ℝ) : ℂ) *
          ((|y| : ℝ) : ℂ) ^ (s - 2) =
        (C : ℂ) * ((1 / ((4 * Real.pi : ℝ) : ℂ)) ^ (s - 1 + (k : ℂ)) * Complex.Gamma (s - 1 + (k : ℂ))) := by
      rw [← hmel, ← smul_eq_mul (a := (C : ℂ)), ← mellin_const_smul]
      unfold mellin
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi (0 : ℝ))
        (fun y hy => by
          have hy' : ¬ (0 < y) := hy
          simp [hy'])]
      refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
      have hy : 0 < y := hy
      simp only [ite_eq_left hy, abs_of_pos hy, smul_eq_mul]
      push_cast
      rw [Complex.ofReal_cpow hy.le]
      have e : (y : ℂ) ^ (s - 2) = (y : ℂ) ^ (s - 1 - 1) := by congr 1; ring
      rw [e]
      ring
    rw [hint]

    have hG1 : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
    have hG2 : Complex.Gamma (s - 1 + (k : ℂ)) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hP1 : (Real.pi : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hπ0)
    have hP2 : ((4 * Real.pi : ℝ) : ℂ) ^ (s - 1 + (k : ℂ)) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h4π0)
    have hinv : (1 / ((4 * Real.pi : ℝ) : ℂ)) ^ (s - 1 + (k : ℂ)) = (((4 * Real.pi : ℝ) : ℂ) ^ (s - 1 + (k : ℂ)))⁻¹ := by
      rw [one_div, Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg h4π.le]; exact Real.pi_ne_zero.symm)]
    rw [hinv, Complex.cpow_neg]
    field_simp

