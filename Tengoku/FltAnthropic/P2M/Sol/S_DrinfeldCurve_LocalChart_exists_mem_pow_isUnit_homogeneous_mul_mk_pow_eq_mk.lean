import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_DrinfeldCurve_LocalChart
import Tengoku.FltAnthropic.Theorems.Thm_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow
import Tengoku.FltAnthropic.Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_mul_mk_pow_eq_mk.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_DrinfeldCurve_LocalChart_exists_mem_pow_isUnit_homogeneous_mul_mk_pow_eq_mk

set_option autoImplicit false

open IsLocalRing

namespace DrinfeldCurve
export _root_.DrinfeldCurve (LocalChart.drinfeldForm mk mk_surjective)
namespace LocalChart
export _root_.DrinfeldCurve.LocalChart (drinfeldForm)
namespace PowPureChartAux
open _root_.DrinfeldCurve.LocalChart open _root_.DrinfeldCurve

open MvPowerSeries

/--
@isnad1 id=isunit.3h6v.s12.23636b4039ab from=translated src=- shape=7746fb32 vocab=540511d2
-/
theorem isUnit_constantCoeff_of_isUnit_mk {W : Type} [CommRing W] [IsLocalRing W] (π : W) (hπ : π ∈ maximalIdeal W)
    (f u v : MvPowerSeries (Fin 2) W) (hf : constantCoeff f = 0) (g : MvPowerSeries (Fin 2) W)
    (hg : IsUnit (Ideal.Quotient.mk (Ideal.span {C π * v - f * u}) g)) : IsUnit (constantCoeff g) := by
  set φ : MvPowerSeries (Fin 2) W →+* ResidueField W := (residue W).comp constantCoeff with hφ
  have hker : ∀ a ∈ Ideal.span {C π * v - f * u}, φ a = 0 := by
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp only [hφ, RingHom.coe_comp, Function.comp_apply, map_mul, map_sub, constantCoeff_C, hf, zero_mul, sub_zero]
    rw [(residue_eq_zero_iff π).mpr hπ]; simp
  have h1 := hg.map (Ideal.Quotient.lift _ φ hker)
  rw [Ideal.Quotient.lift_mk] at h1
  simp only [hφ, RingHom.coe_comp, Function.comp_apply] at h1
  by_contra hnu
  have hm : constantCoeff g ∈ maximalIdeal W := (mem_maximalIdeal _).mpr hnu
  rw [(residue_eq_zero_iff _).mpr hm] at h1
  exact not_isUnit_zero h1

/--
@isnad1 id=eq.0h2v.s8.36b00da68850 from=translated src=- shape=6353e1a6 vocab=745a8f1c
-/
theorem coeff_drinfeldForm_zero {W : Type} [CommRing W] (q : ℕ) [Fact q.Prime] :
    coeff (0 : Fin 2 →₀ ℕ) (DrinfeldCurve.LocalChart.drinfeldForm q W) = 0 := by
  classical
  have e1 : (X 0 : MvPowerSeries (Fin 2) W) * X 1 ^ q = monomial (Finsupp.single 0 1 + Finsupp.single 1 q) 1 := by
    rw [X_pow_eq, X_def, monomial_mul_monomial, one_mul]
  have e2 : (X 0 : MvPowerSeries (Fin 2) W) ^ q * X 1 = monomial (Finsupp.single 0 q + Finsupp.single 1 1) 1 := by
    rw [X_pow_eq, X_def, monomial_mul_monomial, one_mul]
  unfold DrinfeldCurve.LocalChart.drinfeldForm
  rw [e1, e2, map_sub, coeff_monomial, coeff_monomial, ite_eq_right, ite_eq_right, sub_zero]
  · intro hn; have := congrArg (fun n : Fin 2 →₀ ℕ => n 1) hn; simp at this
  · intro hn; have := congrArg (fun n : Fin 2 →₀ ℕ => n 0) hn; simp at this

end DrinfeldCurve.LocalChart.PowPureChartAux

open DrinfeldCurve.LocalChart.PowPureChartAux in
/--
@isnad1 id=ex.5h10v.s14.85efc3dd1d35 from=translated src=- shape=91ef0545 vocab=12048122
-/
theorem solution
    (q : ℕ) [Fact q.Prime] (W : Type) [CommRing W] [IsLocalRing W]
    (π : W) (hπ : π ∈ maximalIdeal W)
    (f u v : MvPowerSeries (Fin 2) W)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (s : MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u}) (hs : IsUnit s)
    (d k : ℕ) (h : MvPowerSeries (Fin 2) W)
    (hh : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ d)
    (hunit : ∀ a b : W, (a ∉ maximalIdeal W ∨ b ∉ maximalIdeal W) →
        a ^ q * b - a * b ^ q ∈ maximalIdeal W →
        IsUnit (∑ i ∈ Finset.range (d + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i)) h
              * a ^ i * b ^ (d - i))) :
    ∃ (h' : MvPowerSeries (Fin 2) W)
      (_ : h' ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (d * k)),
      (∀ a b : W, (a ∉ maximalIdeal W ∨ b ∉ maximalIdeal W) →
          a ^ q * b - a * b ^ q ∈ maximalIdeal W →
          IsUnit (∑ i ∈ Finset.range (d * k + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d * k - i)) h'
              * a ^ i * b ^ (d * k - i))) ∧
      s * (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) h) ^ k =
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π * v - f * u}) h' := by
  classical
  have hf0 : MvPowerSeries.constantCoeff f = 0 := by
    have h1 := (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W (q + 2) _).mp hf 0 (by simp)
    rw [map_sub, coeff_drinfeldForm_zero q, sub_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h1
    exact h1
  obtain ⟨G, hG⟩ := Ideal.Quotient.mk_surjective s
  have hGu : IsUnit (MvPowerSeries.constantCoeff G) :=
    isUnit_constantCoeff_of_isUnit_mk π hπ f u v hf0 G (by rw [hG]; exact hs)
  refine ⟨G * h ^ k, (MvPowerSeries.mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow W G h d k hh 0 0).1, ?_, ?_⟩
  · intro a b hab hdir
    rw [(MvPowerSeries.mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow W G h d k hh a b).2]
    exact hGu.mul ((hunit a b hab hdir).pow k)
  · rw [← hG, map_mul, map_pow]
