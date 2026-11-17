import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow

set_option autoImplicit false

namespace MvPowerSeries
export _root_.MvPowerSeries (coeff coeff_monomial X_dvd_iff subst C subst_mul X constantCoeff monomial_zero_eq_C_apply subst_pow hasSubst_of_constantCoeff_zero X_pow_dvd_iff monomial_mul_monomial coeff_zero_eq_constantCoeff_apply coe_substAlgHom monomial coeff_subst X_pow_eq ext HasSubst subst_C mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt)
namespace PowPureAux
open _root_.MvPowerSeries

section Graded

variable (W : Type) [CommRing W]

noncomputable abbrev nd (e i : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e - i)

omit W in
@[scoped simp] theorem nd_zero (e i : ℕ) : nd e i 0 = i := by simp [nd]

omit W in
@[scoped simp] theorem nd_one (e i : ℕ) : nd e i 1 = e - i := by simp [nd]

omit W in
theorem eq_nd (n : Fin 2 →₀ ℕ) : n = nd (n 0 + n 1) (n 0) := by
  ext j
  fin_cases j <;> simp [nd]

omit W in
theorem nd_injOn (e : ℕ) : Set.InjOn (nd e) ↑(Finset.range (e + 1)) := by
  intro i _ j _ h
  have := congrArg (fun n : Fin 2 →₀ ℕ => n 0) h
  simpa using this

theorem coeff_eq_zero_of_mem_pow (e : ℕ) (g : MvPowerSeries (Fin 2) W)
    (hg : g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e)
    (n : Fin 2 →₀ ℕ) (hn : n 0 + n 1 < e) : MvPowerSeries.coeff n g = 0 :=
  (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W e g).mp hg n hn

noncomputable def low (e : ℕ) (g : MvPowerSeries (Fin 2) W) : MvPowerSeries (Fin 2) W :=
  ∑ i ∈ Finset.range (e + 1), MvPowerSeries.monomial (nd e i) (MvPowerSeries.coeff (nd e i) g)

end Graded

section Line

variable (W : Type) [CommRing W]

noncomputable def lineSubst (a b : W) : Fin 2 → PowerSeries W :=
  fun s => PowerSeries.C (if s = 0 then a else b) * PowerSeries.X

theorem hasSubst_lineSubst (a b : W) : MvPowerSeries.HasSubst (lineSubst W a b) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  show PowerSeries.constantCoeff (PowerSeries.C (if s = 0 then a else b) * PowerSeries.X) = 0
  simp

noncomputable def lineEval (a b : W) (G : MvPowerSeries (Fin 2) W) : PowerSeries W :=
  MvPowerSeries.subst (lineSubst W a b) G

theorem lineEval_mul (a b : W) (G H : MvPowerSeries (Fin 2) W) :
    lineEval W a b (G * H) = lineEval W a b G * lineEval W a b H :=
  MvPowerSeries.subst_mul (hasSubst_lineSubst W a b) G H

theorem lineEval_pow (a b : W) (G : MvPowerSeries (Fin 2) W) (n : ℕ) :
    lineEval W a b (G ^ n) = lineEval W a b G ^ n :=
  MvPowerSeries.subst_pow (hasSubst_lineSubst W a b) G n

theorem mvcoeff_C_mul_X_pow (c : W) (e m : ℕ) :
    MvPowerSeries.coeff (Finsupp.single () e) (PowerSeries.C c * PowerSeries.X ^ m) = if e = m then c else 0 :=
  PowerSeries.coeff_C_mul_X_pow c m e

theorem coeff_lineEval (a b : W) (G : MvPowerSeries (Fin 2) W) (e : ℕ) :
    PowerSeries.coeff e (lineEval W a b G) =
      ∑ i ∈ Finset.range (e + 1), MvPowerSeries.coeff (nd e i) G * a ^ i * b ^ (e - i) := by
  classical
  show MvPowerSeries.coeff (Finsupp.single () e) (MvPowerSeries.subst (lineSubst W a b) G) = _
  rw [MvPowerSeries.coeff_subst (hasSubst_lineSubst W a b)]
  have hterm : ∀ d : Fin 2 →₀ ℕ,
      MvPowerSeries.coeff d G • MvPowerSeries.coeff (Finsupp.single () e)
          (d.prod fun s n => lineSubst W a b s ^ n) =
        if d 0 + d 1 = e then MvPowerSeries.coeff d G * a ^ d 0 * b ^ d 1 else 0 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    have : lineSubst W a b 0 ^ d 0 * lineSubst W a b 1 ^ d 1 =
        PowerSeries.C (a ^ d 0 * b ^ d 1) * PowerSeries.X ^ (d 0 + d 1) := by
      simp only [lineSubst, ite_true, ite_eq_right (by decide : (1 : Fin 2) ≠ 0), map_mul, map_pow]
      ring
    rw [this, mvcoeff_C_mul_X_pow, smul_eq_mul]
    by_cases h : d 0 + d 1 = e
    · rw [ite_eq_left h.symm, ite_eq_left h, mul_assoc]
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h, mul_zero]
  simp only [hterm]
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (e + 1)).image (nd e)) ?_]
  · rw [Finset.sum_image (nd_injOn e)]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [nd_zero, nd_one, ite_eq_left (by omega)]
  · intro d hd
    rw [Function.mem_support] at hd
    have h : d 0 + d 1 = e := by
      by_contra h; exact hd (ite_eq_right h)
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨d 0, by omega, by rw [(eq_nd d), h, nd_zero]⟩

theorem constantCoeff_lineEval (a b : W) (G : MvPowerSeries (Fin 2) W) :
    PowerSeries.constantCoeff (lineEval W a b G) = MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) G := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lineEval]
  simp [nd]

end Line

end MvPowerSeries.PowPureAux
open scoped _root_.P2MW.S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow.MvPowerSeries _root_.P2MW.S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow.MvPowerSeries.PowPureAux
open scoped _root_.P2MW.S_MvPowerSeries_mul_pow_mem_span_X_pow_and_sum_coeff_mul_pow_eq_constantCoeff_mul_pow.MvPowerSeries

open MvPowerSeries.PowPureAux in
theorem solution
    (W : Type) [CommRing W] (G h : MvPowerSeries (Fin 2) W) (d k : ℕ)
    (hh : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ d) (a b : W) :
    G * h ^ k ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (d * k) ∧
      (∑ i ∈ Finset.range (d * k + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d * k - i)) (G * h ^ k)
              * a ^ i * b ^ (d * k - i)) =
        MvPowerSeries.constantCoeff G *
          (∑ i ∈ Finset.range (d + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i)) h
              * a ^ i * b ^ (d - i)) ^ k := by
  classical
  refine ⟨?_, ?_⟩
  · have h1 := Ideal.pow_mem_pow hh k
    rw [← pow_mul] at h1
    exact Ideal.mul_mem_left _ _ h1
  ·
    have eL : (∑ i ∈ Finset.range (d * k + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d * k - i)) (G * h ^ k)
              * a ^ i * b ^ (d * k - i)) = PowerSeries.coeff (d * k) (lineEval W a b (G * h ^ k)) := by
      rw [coeff_lineEval]
    have eR : (∑ i ∈ Finset.range (d + 1),
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i)) h
              * a ^ i * b ^ (d - i)) = PowerSeries.coeff d (lineEval W a b h) := by
      rw [coeff_lineEval]
    rw [eL, eR, lineEval_mul, lineEval_pow]

    have hdiv : (PowerSeries.X : PowerSeries W) ^ d ∣ lineEval W a b h := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [coeff_lineEval]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [coeff_eq_zero_of_mem_pow W d h hh (nd m i) (by
        simp only [Finset.mem_range] at hi; rw [nd_zero, nd_one]; omega), zero_mul, zero_mul]
    obtain ⟨ψ, hψ⟩ := hdiv
    have hψ0 : PowerSeries.coeff d (lineEval W a b h) = PowerSeries.constantCoeff ψ := by
      rw [hψ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      have := PowerSeries.coeff_X_pow_mul ψ d 0
      rwa [zero_add] at this
    rw [hψ0, hψ]
    have e1 : lineEval W a b G * (PowerSeries.X ^ d * ψ) ^ k = PowerSeries.X ^ (d * k) * (lineEval W a b G * ψ ^ k) := by
      rw [mul_pow, ← pow_mul]; ring
    rw [e1]
    have h2 := PowerSeries.coeff_X_pow_mul (lineEval W a b G * ψ ^ k) (d * k) 0
    rw [zero_add] at h2
    rw [h2, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, constantCoeff_lineEval,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
