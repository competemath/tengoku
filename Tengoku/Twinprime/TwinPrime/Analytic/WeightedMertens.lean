import Tengoku.Twinprime.TwinPrime.Analytic.SelbergMoebiusError
import Tengoku.Twinprime.TwinPrime.Analytic.SupremumContraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A locally bounded weighted Mertens supremum and the hyperbola head

The running supremum is finite on every interval `[2,x]` by the trivial
Möbius estimate. No uniform bound is assumed. Its pointwise control and the
unconditional absolute coefficient mass bound give the short hyperbola head
estimate needed before contraction.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

def weightedMertens (x : ℝ) : ℝ := |mertensReal x| * (Real.log x) ^ 6 / x

def mertensSup (x : ℝ) : ℝ := initialIntervalSup weightedMertens 2 x

/--
@isnad1 id=le.1h1v.s4.42e7a28d721f from=translated src=- shape=35bd48ee vocab=cd3e33d7
-/
theorem weightedMertens_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ weightedMertens x := by
  unfold weightedMertens
  exact div_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) hx

/--
@isnad1 id=le.1h1v.s5.1310f71e06be from=translated src=- shape=daa6252f vocab=3c18ac21
-/
theorem weightedMertens_le_log_pow (x : ℝ) (hx : 0 < x) :
    weightedMertens x ≤ (Real.log x) ^ 6 := by
  unfold weightedMertens
  apply (div_le_iff₀ hx).mpr
  have h := mul_le_mul_of_nonneg_right (abs_mertensReal_le x hx.le)
    (show 0 ≤ (Real.log x) ^ 6 by positivity)
  simpa only [mul_comm] using h

/-- Local boundedness uses only `|M(t)| ≤ t`, with a bound depending on x.
@isnad1 id=bddabove.1h1v.s5.531df1a5c907 from=translated src=- shape=ceec3c47 vocab=4e550787
-/
theorem weightedMertens_bddAbove (x : ℝ) (_hx : 2 ≤ x) :
    BddAbove (weightedMertens '' Set.Icc 2 x) := by
  refine ⟨(Real.log x) ^ 6, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have ht0 : 0 < t := by linarith [ht.1]
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith [ht.1])
  exact (weightedMertens_le_log_pow t ht0).trans
    (pow_le_pow_left₀ hlogt (Real.log_le_log ht0 ht.2) 6)

/--
@isnad1 id=islub.1h1v.s5.ce5ecfbf402e from=translated src=- shape=4dc81713 vocab=0cf230bd
-/
theorem mertensSup_isLUB (x : ℝ) (hx : 2 ≤ x) :
    IsLUB (weightedMertens '' Set.Icc 2 x) (mertensSup x) :=
  initialIntervalSup_isLUB weightedMertens hx (weightedMertens_bddAbove x hx)

/--
@isnad1 id=le.2h2v.s4.ad0918409d80 from=translated src=- shape=994278ac vocab=5e4c1b96
-/
theorem weightedMertens_le_sup {t x : ℝ} (ht : 2 ≤ t) (htx : t ≤ x) :
    weightedMertens t ≤ mertensSup x :=
  le_initialIntervalSup weightedMertens (weightedMertens_bddAbove x (ht.trans htx)) ⟨ht, htx⟩

/--
@isnad1 id=le.1h1v.s4.b27b982cf24b from=translated src=- shape=35bd48ee vocab=0bd16f11
-/
theorem mertensSup_nonneg (x : ℝ) (hx : 2 ≤ x) : 0 ≤ mertensSup x :=
  (weightedMertens_nonneg 2 (by norm_num)).trans (weightedMertens_le_sup le_rfl hx)

/--
@isnad1 id=le.1h1v.s5.81d64a00e224 from=translated src=- shape=076044b8 vocab=c4efc89c
-/
theorem mertensSup_le_log_pow (x : ℝ) (hx : 2 ≤ x) :
    mertensSup x ≤ (Real.log x) ^ 6 := by
  apply (mertensSup_isLUB x hx).2
  rintro _ ⟨t, ht, rfl⟩
  have ht0 : 0 < t := by linarith [ht.1]
  exact (weightedMertens_le_log_pow t ht0).trans
    (pow_le_pow_left₀ (Real.log_nonneg (by linarith [ht.1])) (Real.log_le_log ht0 ht.2) 6)

/--
@isnad1 id=le.2h2v.s4.7d7b1868d8cf from=translated src=- shape=994278ac vocab=0bd16f11
-/
theorem mertensSup_mono {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    mertensSup x ≤ mertensSup y :=
  initialIntervalSup_mono weightedMertens hx hxy (weightedMertens_bddAbove y (hx.trans hxy))

/--
@isnad1 id=monotone.0h0v.s4.f50e6858a9b6 from=translated src=- shape=f2a09be3 vocab=18ef7b2c
-/
theorem mertensSup_monotoneOn : MonotoneOn mertensSup (Set.Ici 2) := by
  intro x hx y _hy hxy
  exact mertensSup_mono hx hxy

/-- Every actual Möbius sum in the initial interval is controlled by its
finite weighted supremum.
@isnad1 id=le.2h2v.s6.8875abe106dc from=translated src=- shape=c9766e64 vocab=e5a4d1c9
-/
theorem abs_mertensReal_le_sup {t x : ℝ} (ht : 2 ≤ t) (htx : t ≤ x) :
    |mertensReal t| ≤ mertensSup x * t / (Real.log t) ^ 6 := by
  have ht0 : 0 < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  apply (le_div_iff₀ (pow_pos hlog 6)).mpr
  exact (div_le_iff₀ ht0).mp (weightedMertens_le_sup ht htx)

/-- The actual short hyperbola head with arbitrary real rectangular cutoffs.
@isnad1 id=le.4h4v.s7.8660b2a5b5bd from=translated src=- shape=ef0acd17 vocab=e5f279f3
-/
theorem selberg_head_le_mertensSup (c x y z : ℝ)
    (hx : 2 ≤ x) (_hy : 1 ≤ y) (hz : 2 ≤ z) (hyz : y * z = x) :
    (∑ k ∈ Ioc 0 ⌊y⌋₊, |centeredSelbergCoefficient c k| * |mertensReal (x / k)|) ≤
      mertensSup x * x / (Real.log z) ^ 6 * centeredSelbergReciprocalMass c ⌊y⌋₊ := by
  have hx0 : 0 < x := by linarith
  have hz0 : 0 < z := by linarith
  have hy0 : 0 ≤ y := by nlinarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hW : 0 ≤ mertensSup x := mertensSup_nonneg x hx
  unfold centeredSelbergReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Ioc.mp hk).1
  have hk0 : (0 : ℝ) < k := by linarith
  have hky : (k : ℝ) ≤ y :=
    (show (k : ℝ) ≤ ⌊y⌋₊ by exact_mod_cast (mem_Ioc.mp hk).2).trans (Nat.floor_le hy0)
  have hzt : z ≤ x / k := (le_div_iff₀ hk0).mpr (by nlinarith)
  have htx : x / k ≤ x := (div_le_iff₀ hk0).mpr (by nlinarith)
  have hlogle : Real.log z ≤ Real.log (x / k) := Real.log_le_log hz0 hzt
  calc
    _ ≤ |centeredSelbergCoefficient c k| *
        (mertensSup x * (x / k) / (Real.log (x / k)) ^ 6) :=
      mul_le_mul_of_nonneg_left (abs_mertensReal_le_sup (hz.trans hzt) htx) (abs_nonneg _)
    _ ≤ |centeredSelbergCoefficient c k| *
        (mertensSup x * (x / k) / (Real.log z) ^ 6) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left
        (mul_nonneg hW (div_pos hx0 hk0).le) (pow_pos hlogz 6)
        (pow_le_pow_left₀ hlogz.le hlogle 6)) (abs_nonneg _)
    _ = _ := by ring

/-- The fixed-power head estimate, with the real quotient retained.
@isnad1 id=le.4h3v.s8.4e527d8c7ec5 from=translated src=- shape=4ac75860 vocab=be2f9a19
-/
theorem selberg_power_head_le_mertensSup (c x δ : ℝ)
    (hx : 2 ≤ x) (hδ : 0 < δ) (_hδ1 : δ < 1) (hz : 2 ≤ x ^ (1 - δ)) :
    (∑ k ∈ Ioc 0 ⌊x ^ δ⌋₊, |centeredSelbergCoefficient c k| * |mertensReal (x / k)|) ≤
      mertensSup x * x / ((1 - δ) ^ 6 * (Real.log x) ^ 6) *
        centeredSelbergReciprocalMass c ⌊x ^ δ⌋₊ := by
  have hx0 : 0 < x := by linarith
  have hy : 1 ≤ x ^ δ := Real.one_le_rpow (by linarith) hδ.le
  have hyz : x ^ δ * x ^ (1 - δ) = x := by
    rw [← Real.rpow_add hx0, show δ + (1 - δ) = 1 by ring, Real.rpow_one]
  simpa only [Real.log_rpow hx0, mul_pow] using
    selberg_head_le_mertensSup c x (x ^ δ) (x ^ (1 - δ)) hx hy hz hyz

/-- The unconditional coefficient mass gives the explicit quadratic
logarithmic factor in the hyperbola head.
@isnad1 id=le.4h3v.s8.293e222f7e5f from=translated src=- shape=0b8d231c vocab=c3df816f
-/
theorem selberg_power_head_le_mertensSup_log_sq (c x δ : ℝ)
    (hx : 2 ≤ x) (hδ : 0 < δ) (hδ1 : δ < 1) (hz : 2 ≤ x ^ (1 - δ)) :
    (∑ k ∈ Ioc 0 ⌊x ^ δ⌋₊, |centeredSelbergCoefficient c k| * |mertensReal (x / k)|) ≤
      mertensSup x * x / ((1 - δ) ^ 6 * (Real.log x) ^ 6) *
        (selbergReciprocalMassConstant c * (2 + δ * Real.log x) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hW := mertensSup_nonneg x hx
  have hy : 1 ≤ x ^ δ := Real.one_le_rpow (by linarith) hδ.le
  apply (selberg_power_head_le_mertensSup c x δ hx hδ hδ1 hz).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Real.log_rpow hx0] using centeredSelbergReciprocalMass_floor_le c (x ^ δ) hy

/-- After the normalization used in the Mertens contraction, the head
coefficient approaches `D(c) δ² / (1-δ)⁶`.
@isnad1 id=le.4h3v.s8.d502d45f13c6 from=translated src=- shape=c3d02a63 vocab=c3df816f
-/
theorem normalized_selberg_power_head_le (c x δ : ℝ)
    (hx : 2 ≤ x) (hδ : 0 < δ) (hδ1 : δ < 1) (hz : 2 ≤ x ^ (1 - δ)) :
    (∑ k ∈ Ioc 0 ⌊x ^ δ⌋₊, |centeredSelbergCoefficient c k| * |mertensReal (x / k)|) *
        (Real.log x) ^ 4 / x ≤
      mertensSup x * (selbergReciprocalMassConstant c * (δ + 2 / Real.log x) ^ 2 /
        (1 - δ) ^ 6) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (selberg_power_head_le_mertensSup_log_sq c x δ hx hδ hδ1 hz)
      (show 0 ≤ (Real.log x) ^ 4 by positivity)) hx0.le
  calc
    _ ≤ (mertensSup x * x / ((1 - δ) ^ 6 * (Real.log x) ^ 6) *
        (selbergReciprocalMassConstant c * (2 + δ * Real.log x) ^ 2)) *
        (Real.log x) ^ 4 / x := h
    _ = _ := by field_simp; ring

end TwinPrime.Analytic
