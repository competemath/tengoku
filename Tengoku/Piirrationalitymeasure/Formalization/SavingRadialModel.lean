import Tengoku.Piirrationalitymeasure.Formalization.GeneralSavingPeriodBounds
import Tengoku.Piirrationalitymeasure.Formalization.PeriodErrorSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! From an exact local measure formula to the uniform logarithmic main term. -/

namespace PiIrrationality

structure SavingRadialModel (a b c : ℝ) where
  domain : Set (ℝ × ℝ)
  scale_mem : ∀ h ∈ domain, ∀ t : ℝ, 0 ≤ t → t • h ∈ domain
  variation : ℝ × ℝ → ℝ
  variation_smul : ∀ h ∈ domain, ∀ t : ℝ, 0 ≤ t → variation (t • h) = t * variation h
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  variation_bound : ∀ h ∈ domain, |variation h| ≤ bound * parameterNormOne h
  radius : ℝ
  radius_pos : 0 < radius
  measure_eq : ∀ h ∈ domain, parameterNormOne h ≤ radius →
    translatedSavingMeasure a b c h - translatedSavingMeasure a b c 0 = variation h

namespace SavingRadialModel

/--
@isnad1 id=ex.3h4v.s7.f4433489bab6 from=translated src=- shape=1359ac8d vocab=dbb88b4f
-/
theorem period_main_error {a b c : ℝ} (M : SavingRadialModel a b c)
    (ha : 0 < a) (hb : 0 < b) (hq : a + 2 * b - c ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ savingPerturbationRadius a b ∧
      ∀ h ∈ M.domain, ∀ k : ℝ, 0 < k → parameterNormOne h ≤ r →
        k * parameterNormOne h ≤ r →
        |savingPeriodDifference a b c h k - M.variation h / k| ≤
          3 * savingTranslationConstant a b c * parameterNormOne h / k ^ 2 := by
  let r := min M.radius (savingPerturbationRadius a b)
  have hr : 0 < r := lt_min M.radius_pos (savingPerturbationRadius_pos ha hb)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (savingPerturbationRadius_le_one a b)
  refine ⟨r, hr, min_le_right _ _, ?_⟩
  intro h hmem k hk hh hkh
  have hn : parameterNormOne (k • h) = k * parameterNormOne h := by
    rw [parameterNormOne_smul, abs_of_pos hk]
  have he := savingPeriodDifference_error h ha.ne' hb.ne' hq hk (hh.trans hr1)
    (by rw [hn]; exact hkh.trans hr1)
  rw [M.measure_eq (k • h) (M.scale_mem h hmem k hk.le)
      (by rw [hn]; exact hkh.trans (min_le_left _ _)),
    M.variation_smul h hmem k hk.le] at he
  have hcancel : k * M.variation h / k ^ 2 = M.variation h / k := by field_simp
  simpa only [hcancel] using he

/--
@isnad1 id=ex.3h4v.s7.900d7486122d from=translated src=- shape=91f0e086 vocab=fc076910
-/
theorem truncated_log {a b c : ℝ} (M : SavingRadialModel a b c)
    (ha : 0 < a) (hb : 0 < b) (hq : a + 2 * b - c ≠ 0) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ savingPerturbationRadius a b ∧ 0 ≤ C ∧
      ∀ h ∈ M.domain, 0 < parameterNormOne h → parameterNormOne h ≤ r →
        |(∑ k ∈ Finset.Icc 1 ⌊r / parameterNormOne h⌋₊,
          savingPeriodDifference a b c h k) -
          M.variation h * Real.log (1 / parameterNormOne h)| ≤ C * parameterNormOne h := by
  obtain ⟨r, hr, hrr, herr⟩ := M.period_main_error ha hb hq
  let L := savingTranslationConstant a b c
  have hL : 0 ≤ L := savingTranslationConstant_nonneg _ _ _
  refine ⟨r, 6 * L + M.bound * (1 + |Real.log r|), hr, hrr,
    by positivity [M.bound_nonneg], ?_⟩
  intro h hmem hd hdr
  let K := ⌊r / parameterNormOne h⌋₊
  have hsum : |(∑ k ∈ Finset.Icc 1 K, savingPeriodDifference a b c h k) -
      M.variation h * (harmonic K : ℝ)| ≤ 2 * (3 * L * parameterNormOne h) := by
    apply sum_Icc_inverse_square_error K (by positivity)
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    apply herr h hmem k hk0 hdr
    have hk_le : (k : ℝ) ≤ r / parameterNormOne h :=
      (Nat.cast_le.mpr hkK).trans (Nat.floor_le (by positivity))
    exact (le_div_iff₀ hd).mp hk_le
  have hlog : |M.variation h * (harmonic K : ℝ) -
      M.variation h * Real.log (1 / parameterNormOne h)| ≤
      M.bound * (1 + |Real.log r|) * parameterNormOne h := by
    rw [← mul_sub, abs_mul]
    calc
      _ ≤ (M.bound * parameterNormOne h) * (1 + |Real.log r|) :=
        mul_le_mul (M.variation_bound h hmem) (harmonic_floor_log_scale hr hd hdr)
          (abs_nonneg _) (mul_nonneg M.bound_nonneg hd.le)
      _ = _ := by ring
  have ht := (abs_sub_le
    (∑ k ∈ Finset.Icc 1 K, savingPeriodDifference a b c h k)
    (M.variation h * (harmonic K : ℝ))
    (M.variation h * Real.log (1 / parameterNormOne h))).trans (add_le_add hsum hlog)
  dsimp only [K] at ht
  nlinarith only [ht]

/--
@isnad1 id=ex.4h4v.s8.21c4b2ba9a93 from=translated src=- shape=d08e8c61 vocab=5b67ed88
-/
theorem omega_log_variation {a b c : ℤ} (M : SavingRadialModel a b c)
    (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ)) (hc : 0 ≤ (c : ℝ))
    (hq : (a : ℝ) + 2 * b - c ≠ 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ h ∈ M.domain,
      0 < parameterNormOne h → parameterNormOne h ≤ r →
      |savingOmega ((a : ℝ) + h.1) ((b : ℝ) + h.2) c - savingOmega a b c -
        M.variation h * Real.log (1 / parameterNormOne h)| ≤ C * parameterNormOne h := by
  obtain ⟨r, C, hr, hrr, hC, hmain⟩ := M.truncated_log ha hb hq
  let B := (4 * ((a : ℝ) + b + c + 2)) ^ 2 * savingTranslationConstant a b c
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg _) (savingTranslationConstant_nonneg _ _ _)
  refine ⟨r, C + B + 2 / r, hr, by positivity, ?_⟩
  intro h hmem hd hdr
  let K := ⌊r / parameterNormOne h⌋₊
  have hsum := hmain h hmem hd hdr
  have hfirst := savingPeriodDifference_zero_bound_general ha hb hc hq (hdr.trans hrr)
  have htail := savingOmega_period_remainder_general a b c ha hb hc (hdr.trans hrr) K
  have htailBound : 2 / ((K : ℝ) + 1) ≤ (2 / r) * parameterNormOne h := by
    calc
      _ ≤ 2 / (r / parameterNormOne h) :=
        div_le_div_of_nonneg_left (by norm_num) (div_pos hr hd)
          (Nat.lt_floor_add_one (r / parameterNormOne h)).le
      _ = _ := by field_simp
  have htail' := htail.trans htailBound
  have he : savingOmega ((a : ℝ) + h.1) ((b : ℝ) + h.2) c - savingOmega a b c -
      M.variation h * Real.log (1 / parameterNormOne h) =
      (savingOmega ((a : ℝ) + h.1) ((b : ℝ) + h.2) c - savingOmega a b c -
        savingPeriodDifference a b c h 0 -
        ∑ k ∈ Finset.Icc 1 K, savingPeriodDifference a b c h k) +
      savingPeriodDifference a b c h 0 +
      ((∑ k ∈ Finset.Icc 1 K, savingPeriodDifference a b c h k) -
        M.variation h * Real.log (1 / parameterNormOne h)) := by ring
  rw [he]
  calc
    _ ≤ (|savingOmega ((a : ℝ) + h.1) ((b : ℝ) + h.2) c - savingOmega a b c -
        savingPeriodDifference a b c h 0 -
        ∑ k ∈ Finset.Icc 1 K, savingPeriodDifference a b c h k| +
      |savingPeriodDifference a b c h 0|) +
      |(∑ k ∈ Finset.Icc 1 K, savingPeriodDifference a b c h k) -
        M.variation h * Real.log (1 / parameterNormOne h)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ((2 / r) * parameterNormOne h + B * parameterNormOne h) + C * parameterNormOne h :=
      add_le_add (add_le_add htail' hfirst) hsum
    _ = _ := by ring

end SavingRadialModel

end PiIrrationality
