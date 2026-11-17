/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.EquivalentUltrametric
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Base
import Tengoku.Seed.Analysis.Normed.Module.Seminorm.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rounding an ultrametric seminorm to a discrete value group

For `e > 1`, round a positive number up to the least integral power of `e` above it.
Applied to an ultrametric seminorm, this gives an equivalent ultrametric seminorm with
values in `e ^ ℤ`, homogeneous when nonzero scalar norms are powers of `e`. This is the
first step in the proof of Corollary 4.3.
-/

namespace AlternatingAnalytic

/-- Round a nonnegative real number upwards to an integral power of `e`, fixing zero.-/
noncomputable def discreteRound (e x : ℝ) : ℝ :=
  if x = 0 then 0 else e ^ ⌈Real.logb e x⌉

/--
@isnad1 id=eq.0h1v.s4.fa5f121d5cac from=translated src=- shape=1d838610 vocab=5c7872ad
-/
@[simp]
theorem discreteRound_zero (e : ℝ) : discreteRound e 0 = 0 := by
  simp [discreteRound]

/--
@isnad1 id=lt.2h2v.s5.10e324e03ec0 from=translated src=- shape=6c67d60b vocab=0e47e7c6
-/
theorem discreteRound_pos {e x : ℝ} (he : 1 < e) (hx : 0 < x) :
    0 < discreteRound e x := by
  simp only [discreteRound, ite_eq_right hx.ne']
  exact zpow_pos (zero_lt_one.trans he) _

/--
@isnad1 id=le.1h2v.s4.f5e7fdae15b9 from=translated src=- shape=1852429d vocab=13a6624a
-/
theorem discreteRound_nonneg {e : ℝ} (he : 1 < e) (x : ℝ) :
    0 ≤ discreteRound e x := by
  unfold discreteRound
  split_ifs
  · exact le_rfl
  · exact (zpow_pos (zero_lt_one.trans he) _).le

/--
@isnad1 id=le.2h2v.s5.a7614b6af300 from=translated src=- shape=20f62a73 vocab=13a6624a
-/
theorem le_discreteRound {e x : ℝ} (he : 1 < e) (hx : 0 ≤ x) :
    x ≤ discreteRound e x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rw [discreteRound, ite_eq_right hx.ne', ← Real.rpow_intCast]
  exact (Real.logb_le_iff_le_rpow he hx).mp (Int.le_ceil _)

/--
@isnad1 id=le.2h2v.s5.fa8e600aa63c from=translated src=- shape=e54d2011 vocab=22e08311
-/
theorem discreteRound_le_mul {e x : ℝ} (he : 1 < e) (hx : 0 ≤ x) :
    discreteRound e x ≤ e * x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rw [discreteRound, ite_eq_right hx.ne', ← Real.rpow_intCast]
  calc
    _ ≤ e ^ (Real.logb e x + 1) :=
      Real.rpow_le_rpow_of_exponent_le he.le (Int.ceil_lt_add_one _).le
    _ = e * x := by
      rw [Real.rpow_add (zero_lt_one.trans he), Real.rpow_one,
        Real.rpow_logb (zero_lt_one.trans he) he.ne' hx, mul_comm]

/--
@isnad1 id=le.3h3v.s5.2234a5f18df2 from=translated src=- shape=02be2863 vocab=13a6624a
-/
theorem discreteRound_mono {e x y : ℝ} (he : 1 < e) (hx : 0 ≤ x) (hxy : x ≤ y) :
    discreteRound e x ≤ discreteRound e y := by
  by_cases hx0 : x = 0
  · simpa [hx0] using discreteRound_nonneg he y
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hypos : 0 < y := hxpos.trans_le hxy
  simp only [discreteRound, ite_eq_right hx0, ite_eq_right hypos.ne']
  exact zpow_le_zpow_right₀ he.le (Int.ceil_mono (Real.logb_le_logb_of_le he hxpos hxy))

/--
@isnad1 id=eq.3h3v.s5.63455653a6c2 from=translated src=- shape=9c4a2dd2 vocab=9b47b05d
-/
theorem discreteRound_max {e x y : ℝ} (he : 1 < e) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    discreteRound e (max x y) = max (discreteRound e x) (discreteRound e y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (discreteRound_mono he hx h)]
  · rw [max_eq_left h, max_eq_left (discreteRound_mono he hy h)]

/--
@isnad1 id=eq.1h3v.s6.7ce246d4fc9f from=translated src=- shape=a6d9457f vocab=713212b3
-/
theorem discreteRound_zpow_mul {e : ℝ} (he : 1 < e) (m : ℤ) (x : ℝ) :
    discreteRound e (e ^ m * x) = e ^ m * discreteRound e x := by
  by_cases hx : x = 0
  · simp [hx]
  have he0 : 0 < e := zero_lt_one.trans he
  have hlog : Real.logb e (e ^ m) = (m : ℝ) := by
    rw [← Real.rpow_intCast]
    exact Real.logb_rpow he0 he.ne'
  simp only [discreteRound, ite_eq_right hx, ite_eq_right (mul_ne_zero (zpow_ne_zero _ he0.ne') hx)]
  rw [Real.logb_mul (zpow_ne_zero _ he0.ne') hx, hlog, Int.ceil_intCast_add,
    zpow_add₀ he0.ne']

/--
@isnad1 id=ex.1h2v.s5.4720c01c7268 from=translated src=- shape=b7639e79 vocab=07c2ac05
-/
theorem discreteRound_mem_zpowers {e x : ℝ} (hx : x ≠ 0) :
    ∃ n : ℤ, discreteRound e x = e ^ n := by
  exact ⟨⌈Real.logb e x⌉, by simp only [discreteRound, ite_eq_right hx]⟩

section Seminorm

variable {K F : Type*} [NormedField K] [AddCommGroup F] [Module K F]

/-- The rounded ultrametric seminorm.-/
noncomputable def roundedSeminorm (p : Seminorm K F)
    (hp : ∀ x y, p (x + y) ≤ max (p x) (p y)) {e : ℝ} (he : 1 < e)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = e ^ n) : Seminorm K F :=
  Seminorm.of (fun x => discreteRound e (p x))
    (fun x y => by
      apply (discreteRound_mono he (apply_nonneg p (x + y)) (hp x y)).trans
      rw [discreteRound_max he (apply_nonneg p x) (apply_nonneg p y)]
      exact max_le (le_add_of_nonneg_right (discreteRound_nonneg he _))
        (le_add_of_nonneg_left (discreteRound_nonneg he _)))
    (fun c x => by
      rw [map_smul_eq_mul]
      by_cases hc : c = 0
      · simp [hc]
      obtain ⟨n, hn⟩ := hval c hc
      rw [hn]
      exact discreteRound_zpow_mul he n (p x))

/--
@isnad1 id=eq.3h5v.s10.0c77ecd4bab1 from=translated src=- shape=de5732cc vocab=25ba6f5b
-/
@[simp]
theorem roundedSeminorm_apply (p : Seminorm K F)
    (hp : ∀ x y, p (x + y) ≤ max (p x) (p y)) {e : ℝ} (he : 1 < e)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = e ^ n) (x : F) :
    roundedSeminorm p hp he hval x = discreteRound e (p x) := rfl

/--
@isnad1 id=le.3h6v.s10.f11a8a100137 from=translated src=- shape=849e5e1e vocab=52063588
-/
theorem roundedSeminorm_ultrametric (p : Seminorm K F)
    (hp : ∀ x y, p (x + y) ≤ max (p x) (p y)) {e : ℝ} (he : 1 < e)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = e ^ n) (x y : F) :
    roundedSeminorm p hp he hval (x + y) ≤
      max (roundedSeminorm p hp he hval x) (roundedSeminorm p hp he hval y) := by
  change discreteRound e (p (x + y)) ≤ max (discreteRound e (p x)) (discreteRound e (p y))
  rw [← discreteRound_max he (apply_nonneg p x) (apply_nonneg p y)]
  exact discreteRound_mono he (apply_nonneg p _) (hp x y)

/--
@isnad1 id=le.3h5v.s10.587682e08332 from=translated src=- shape=16e65bee vocab=52063588
-/
theorem le_roundedSeminorm (p : Seminorm K F)
    (hp : ∀ x y, p (x + y) ≤ max (p x) (p y)) {e : ℝ} (he : 1 < e)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = e ^ n) (x : F) :
    p x ≤ roundedSeminorm p hp he hval x :=
  le_discreteRound he (apply_nonneg p x)

/--
@isnad1 id=le.3h5v.s10.ef33dde81985 from=translated src=- shape=1f792512 vocab=3a0cd896
-/
theorem roundedSeminorm_le_mul (p : Seminorm K F)
    (hp : ∀ x y, p (x + y) ≤ max (p x) (p y)) {e : ℝ} (he : 1 < e)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = e ^ n) (x : F) :
    roundedSeminorm p hp he hval x ≤ e * p x :=
  discreteRound_le_mul he (apply_nonneg p x)

end Seminorm

/-- If nonzero scalar norms lie in `e ^ ℤ`, an equivalent ultrametric norm can be chosen
with nonzero values in `e ^ ℤ`.
@isnad1 id=ex.3h3v.s10.5a9310bbb15d from=translated src=- shape=9c27f35b vocab=cb71c6a0
-/
theorem HasEquivalentUltrametricNorm.exists_discrete
    {K F : Type*} [NormedField K] [NormedAddCommGroup F] [NormedSpace K F]
    (h : HasEquivalentUltrametricNorm K F) {e : ℝ} (he : 1 < e)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = e ^ n) :
    ∃ q : Seminorm K F,
      (∀ x y, q (x + y) ≤ max (q x) (q y)) ∧
      (∃ A : ℝ, 0 < A ∧ ∀ x, ‖x‖ ≤ A * q x) ∧
      (∃ B : ℝ, 0 < B ∧ ∀ x, q x ≤ B * ‖x‖) ∧
      (∀ x : F, x ≠ 0 → ∃ n : ℤ, q x = e ^ n) := by
  rcases h with ⟨p, hp, ⟨A, hA, hlower⟩, ⟨B, hB, hupper⟩⟩
  refine ⟨roundedSeminorm p hp he hval, roundedSeminorm_ultrametric p hp he hval,
    ⟨A, hA, fun x => (hlower x).trans
      (mul_le_mul_of_nonneg_left (le_roundedSeminorm p hp he hval x) hA.le)⟩,
    ⟨e * B, mul_pos (zero_lt_one.trans he) hB, fun x => ?_⟩, ?_⟩
  · exact (roundedSeminorm_le_mul p hp he hval x).trans
      ((mul_le_mul_of_nonneg_left (hupper x) (zero_lt_one.trans he).le).trans_eq
        (mul_assoc e B ‖x‖).symm)
  · intro x hx
    have hpx : p x ≠ 0 := by
      intro hz
      have hh := hlower x
      rw [hz, mul_zero] at hh
      exact hx (norm_le_zero_iff.mp hh)
    exact discreteRound_mem_zpowers hpx

end AlternatingAnalytic
