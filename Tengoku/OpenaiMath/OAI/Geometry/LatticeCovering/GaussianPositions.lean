import Tengoku.OpenaiMath.OAI.Geometry.LatticeCovering.GaussianRates

namespace OAI

namespace SingleLatticeCovering.FinalRates
open Real Filter Topology Asymptotics

noncomputable def localScale (C : ℝ) (n : ℕ) : ℕ := ⌈sectionRadius C n⌉₊+2

lemma sectionRadius_le_localScale (C : ℝ) (n : ℕ) :
    sectionRadius C n ≤ (localScale C n : ℝ) := by
  have H := Nat.le_ceil (sectionRadius C n)
  dsimp [localScale]
  push_cast
  linarith

lemma dimension_le_localScale {C : ℝ} (hC : 0 < C) {n D : ℕ}
    (hD : (D:ℝ) ≤ C*((firstSize n:ℝ)+1)) : D ≤ localScale C n := by
  have _ := hC
  have hc := sectionRadius_le_localScale C n
  have hh : (D:ℝ) ≤ (localScale C n:ℝ) := by
    dsimp [sectionRadius] at hc
    nlinarith [show (0:ℝ) ≤ (firstSize n:ℝ) by positivity]
  exact_mod_cast hh

lemma localScale_tendsto {C : ℝ} (hC : 0 < C) : Tendsto (localScale C) atTop atTop := by
  apply tendsto_atTop_mono _ firstSize_tendsto
  intro n
  have H := sectionRadius_le_localScale C n
  dsimp [sectionRadius] at H
  exact_mod_cast (show (firstSize n:ℝ) ≤ (localScale C n:ℝ) by
    nlinarith [show (0:ℝ) ≤ (firstSize n:ℝ) by positivity])

lemma eventually_localScale_root {C : ℝ} (hC : 0 < C) : ∀ᶠ n : ℕ in atTop,
    Real.exp ((localScale C n:ℝ)^30) ≤ Real.sqrt (Real.sqrt (n:ℝ)) := by
  let H : ℝ := 3*(C+2)
  have hH : 0 < H := by dsimp [H]; positivity
  have hsmall : (fun n : ℕ => (Real.log (Real.log (n:ℝ)))^60) =o[atTop]
      (fun n => Real.log (n:ℝ)) := by
    simpa only [Function.comp_def,Real.rpow_natCast,Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop ((60:ℕ):ℝ) (by norm_num : (0:ℝ) < 1)).comp_tendsto log_nat_atTop
  filter_upwards [hsmall.bound (by positivity : 0 < 1/(4*H^30)),
    loglog_nat_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop (1:ℕ)] with n hbound hs hn
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 ≤ Real.log (Real.log (n:ℝ)) := le_trans zero_le_one hs
  have hs2 : 1 ≤ (Real.log (Real.log (n:ℝ)))^2 := one_le_pow₀ hs
  have hceil := Nat.ceil_lt_add_one (sq_nonneg (Real.log (Real.log (n:ℝ))))
  change (firstSize n:ℝ) < (Real.log (Real.log (n:ℝ)))^2+1 at hceil
  have hlceil := Nat.ceil_lt_add_one (sectionRadius_pos hC n).le
  have hl : (localScale C n:ℝ) ≤ H*(Real.log (Real.log (n:ℝ)))^2 := by
    dsimp [localScale,sectionRadius]
    push_cast
    dsimp [sectionRadius] at hlceil
    have hh := mul_le_mul_of_nonneg_left hceil.le (show 0 ≤ C+1 by linarith)
    dsimp [H]
    nlinarith [mul_nonneg (show 0 ≤ 2*C+5 by linarith) (sub_nonneg.mpr hs2)]
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hs0 _),
    abs_of_nonneg (Real.log_natCast_nonneg n)] at hbound
  have hpow : (localScale C n:ℝ)^30 ≤ H^30*(Real.log (Real.log (n:ℝ)))^60 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (localScale C n)) hl 30
    simpa only [mul_pow,←pow_mul] using hh
  have hexp : 4*(localScale C n:ℝ)^30 ≤ Real.log (n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 4*H^30)
    have he : (4*H^30)*(1/(4*H^30)*Real.log (n:ℝ))=Real.log (n:ℝ) := by field_simp
    rw [he] at hh
    nlinarith
  have hlog : Real.log (Real.sqrt (Real.sqrt (n:ℝ)))=Real.log (n:ℝ)/4 := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _),Real.log_sqrt hnp.le]
    ring
  rw [←Real.exp_log (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hnp))]
  apply Real.exp_le_exp.mpr
  rw [hlog]
  linarith

end SingleLatticeCovering.FinalRates

namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory MeasureTheory.Measure Set Filter Topology GaussianDensity CanonicalDensity Sections
open scoped ENNReal

lemma normalizer_half (D : ℕ) : normalizer D (1/2)=(Real.sqrt (2*Real.pi))^D := by
  unfold normalizer
  rw [show Real.pi/(1/2)=2*Real.pi by ring,Real.sqrt_eq_rpow,
    ←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0 ≤ 2*Real.pi)]
  congr 1
  ring

lemma density_half_gaussian {D : ℕ} (y : E D) :
    GaussianDensity.density (1/2) y=Sections.gaussian (E D) y := by
  unfold GaussianDensity.density Sections.gaussian
  rw [normalizer_half,finrank_euclideanSpace_fin,zpow_neg,zpow_natCast]
  congr 1
  congr 1
  ring

end SingleLatticeCovering.GaussianNumerics

noncomputable section

end

end OAI
