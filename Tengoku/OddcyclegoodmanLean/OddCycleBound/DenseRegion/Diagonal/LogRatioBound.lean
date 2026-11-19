import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv
import Tengoku.Seed.Analysis.Complex.ExponentialBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Real
open scoped Topology

namespace OddCycleBound.DenseRegion

noncomputable def Aexpr (t : ℝ) : ℝ := 3 * t * (5 + 8 * t) / (2 * (1 + t) * (1 + 4 * t))

noncomputable def Bexpr (t : ℝ) : ℝ := (1 + 4 * t) * (5 + 8 * t) / (3 * (1 + t))

noncomputable def Cexpr (t : ℝ) : ℝ := (32 * t ^ 2 + 25 * t + 2) / (3 * (1 + 4 * t))

noncomputable def Lexpr (t : ℝ) : ℝ := 2 * t * Real.log (Aexpr t) + Real.log (Bexpr t) - Cexpr t

lemma Aexpr_pos {t : ℝ} (ht : 0 < t) : 0 < Aexpr t := by unfold Aexpr; positivity

lemma Bexpr_pos {t : ℝ} (ht : 0 < t) : 0 < Bexpr t := by unfold Bexpr; positivity

lemma Cexpr_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt Cexpr ((128 * t ^ 2 + 64 * t + 17) / (3 * (1 + 4 * t) ^ 2)) t := by
  have hden0 : (3 : ℝ) * (1 + 4 * t) ≠ 0 := by positivity
  have hnum : HasDerivAt (fun s : ℝ => 32 * s ^ 2 + 25 * s + 2) (32 * (2 * t) + 25) t := by
    simpa using (((hasDerivAt_pow 2 t).const_mul (32 : ℝ)).add
      ((hasDerivAt_id t).const_mul (25 : ℝ))).add_const (2 : ℝ)
  have hden : HasDerivAt (fun s : ℝ => 3 * (1 + 4 * s)) (3 * 4) t := by
    simpa using (((hasDerivAt_id t).const_mul (4 : ℝ)).const_add (1 : ℝ)).const_mul (3 : ℝ)
  have hquot := hnum.div hden hden0
  have hkey : (32 * (2 * t) + 25) * (3 * (1 + 4 * t)) - (32 * t ^ 2 + 25 * t + 2) * (3 * 4)
      = 3 * (128 * t ^ 2 + 64 * t + 17) := by ring
  have hkey2 : (3 * (1 + 4 * t)) ^ 2 = 3 * (3 * (1 + 4 * t) ^ 2) := by ring
  rw [hkey, hkey2, mul_div_mul_left _ _ (by norm_num : (3 : ℝ) ≠ 0)] at hquot
  exact hquot

lemma Aexpr_log {t : ℝ} (ht : 0 < t) :
    Real.log (Aexpr t) = Real.log 3 + Real.log t + Real.log (5 + 8 * t)
      - Real.log 2 - Real.log (1 + t) - Real.log (1 + 4 * t) := by
  unfold Aexpr
  rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  ring

lemma Bexpr_log {t : ℝ} (ht : 0 < t) :
    Real.log (Bexpr t) = Real.log (1 + 4 * t) + Real.log (5 + 8 * t)
      - Real.log 3 - Real.log (1 + t) := by
  unfold Bexpr
  rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  ring

lemma Lexpr_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt Lexpr
      (2 * (Real.log 3 + Real.log t + Real.log (5 + 8 * t) - Real.log 2 - Real.log (1 + t)
            - Real.log (1 + 4 * t))
        + 2 * t * (1 / t + 8 / (5 + 8 * t) - 1 / (1 + t) - 4 / (1 + 4 * t))
        + (4 / (1 + 4 * t) + 8 / (5 + 8 * t) - 1 / (1 + t))
        - (128 * t ^ 2 + 64 * t + 17) / (3 * (1 + 4 * t) ^ 2)) t := by
  have h58 : (5 : ℝ) + 8 * t ≠ 0 := by positivity
  have h1t : (1 : ℝ) + t ≠ 0 := by positivity
  have h14 : (1 : ℝ) + 4 * t ≠ 0 := by positivity
  have dlogt : HasDerivAt Real.log (1 / t) t := by
    rw [one_div]; exact Real.hasDerivAt_log (ne_of_gt ht)
  have dlog58 : HasDerivAt (fun s => Real.log (5 + 8 * s)) (8 / (5 + 8 * t)) t :=
    (show HasDerivAt (fun s : ℝ => 5 + 8 * s) 8 t by
      simpa using ((hasDerivAt_id t).const_mul 8).const_add 5).log h58
  have dlog1t : HasDerivAt (fun s => Real.log (1 + s)) (1 / (1 + t)) t := by
    simpa using (show HasDerivAt (fun s : ℝ => 1 + s) 1 t by
      simpa using (hasDerivAt_id t).const_add 1).log h1t
  have dlog14 : HasDerivAt (fun s => Real.log (1 + 4 * s)) (4 / (1 + 4 * t)) t :=
    (show HasDerivAt (fun s : ℝ => 1 + 4 * s) 4 t by
      simpa using ((hasDerivAt_id t).const_mul 4).const_add 1).log h14
  have dsumA : HasDerivAt (fun s => Real.log 3 + Real.log s + Real.log (5 + 8 * s) - Real.log 2
        - Real.log (1 + s) - Real.log (1 + 4 * s))
      (0 + 1 / t + 8 / (5 + 8 * t) - 0 - 1 / (1 + t) - 4 / (1 + 4 * t)) t :=
    ((((((hasDerivAt_const t (Real.log 3)).add dlogt).add dlog58).sub
      (hasDerivAt_const t (Real.log 2))).sub dlog1t).sub dlog14)
  have d2t : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by simpa using (hasDerivAt_id t).const_mul 2
  have dsumB : HasDerivAt (fun s => Real.log (1 + 4 * s) + Real.log (5 + 8 * s) - Real.log 3
        - Real.log (1 + s))
      (4 / (1 + 4 * t) + 8 / (5 + 8 * t) - 0 - 1 / (1 + t)) t :=
    (((dlog14.add dlog58).sub (hasDerivAt_const t (Real.log 3))).sub dlog1t)
  have hcomb := ((d2t.mul dsumA).add dsumB).sub (Cexpr_hasDerivAt ht)
  have hLraw : HasDerivAt Lexpr
      (2 * (Real.log 3 + Real.log t + Real.log (5 + 8 * t) - Real.log 2 - Real.log (1 + t)
            - Real.log (1 + 4 * t))
        + 2 * t * (0 + 1 / t + 8 / (5 + 8 * t) - 0 - 1 / (1 + t) - 4 / (1 + 4 * t))
        + (4 / (1 + 4 * t) + 8 / (5 + 8 * t) - 0 - 1 / (1 + t))
        - (128 * t ^ 2 + 64 * t + 17) / (3 * (1 + 4 * t) ^ 2)) t := by
    apply hcomb.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [Set.mem_Ioi] at hs
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    unfold Lexpr; rw [Aexpr_log hs, Bexpr_log hs]
  have key : (2 * (Real.log 3 + Real.log t + Real.log (5 + 8 * t) - Real.log 2 - Real.log (1 + t)
            - Real.log (1 + 4 * t))
        + 2 * t * (0 + 1 / t + 8 / (5 + 8 * t) - 0 - 1 / (1 + t) - 4 / (1 + 4 * t))
        + (4 / (1 + 4 * t) + 8 / (5 + 8 * t) - 0 - 1 / (1 + t))
        - (128 * t ^ 2 + 64 * t + 17) / (3 * (1 + 4 * t) ^ 2))
      = (2 * (Real.log 3 + Real.log t + Real.log (5 + 8 * t) - Real.log 2 - Real.log (1 + t)
            - Real.log (1 + 4 * t))
        + 2 * t * (1 / t + 8 / (5 + 8 * t) - 1 / (1 + t) - 4 / (1 + 4 * t))
        + (4 / (1 + 4 * t) + 8 / (5 + 8 * t) - 1 / (1 + t))
        - (128 * t ^ 2 + 64 * t + 17) / (3 * (1 + 4 * t) ^ 2)) := by ring
  rw [← key]; exact hLraw

lemma Lexpr_hasDerivAt' {t : ℝ} (ht : 0 < t) :
    HasDerivAt Lexpr (2 * Real.log (Aexpr t)
      - ((32 * t ^ 2 + 16 * t - 7) * (32 * t ^ 2 + 25 * t + 2))
          / (3 * (1 + t) * (1 + 4 * t) ^ 2 * (5 + 8 * t))) t := by
  have heq : 2 * Real.log (Aexpr t)
        - ((32 * t ^ 2 + 16 * t - 7) * (32 * t ^ 2 + 25 * t + 2))
            / (3 * (1 + t) * (1 + 4 * t) ^ 2 * (5 + 8 * t))
      = 2 * (Real.log 3 + Real.log t + Real.log (5 + 8 * t) - Real.log 2 - Real.log (1 + t)
            - Real.log (1 + 4 * t))
        + 2 * t * (1 / t + 8 / (5 + 8 * t) - 1 / (1 + t) - 4 / (1 + 4 * t))
        + (4 / (1 + 4 * t) + 8 / (5 + 8 * t) - 1 / (1 + t))
        - (128 * t ^ 2 + 64 * t + 17) / (3 * (1 + 4 * t) ^ 2) := by
    have ht0 : t ≠ 0 := ne_of_gt ht
    have h58 : (5 : ℝ) + 8 * t ≠ 0 := by positivity
    have h1t : (1 : ℝ) + t ≠ 0 := by positivity
    have h14 : (1 : ℝ) + 4 * t ≠ 0 := by positivity
    rw [Aexpr_log ht]; field_simp; ring
  rw [heq]; exact Lexpr_hasDerivAt ht

lemma Lprime_neg_of_ge_threehalf {t : ℝ} (ht : 3 / 2 ≤ t) : deriv Lexpr t < 0 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have h14 : (0 : ℝ) < 1 + 4 * t := by linarith
  have h58 : (0 : ℝ) < 5 + 8 * t := by linarith
  rw [(Lexpr_hasDerivAt' ht0).deriv]
  have hA0 : 0 < Aexpr t := Aexpr_pos ht0
  have htan : 2 * Real.log (Aexpr t) ≤ 7 / 5 + (Aexpr t - 2) := by
    have hsplit : Real.log (Aexpr t) = Real.log 2 + Real.log (Aexpr t / 2) := by
      rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hA0 (by norm_num))),
          show (2 : ℝ) * (Aexpr t / 2) = Aexpr t from by ring]
    have hle := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Aexpr t / 2 from div_pos hA0 (by norm_num))
    have h2 := Real.log_two_lt_d9
    rw [hsplit]; nlinarith [hle, h2]
  have hrat : 7 / 5 + (Aexpr t - 2)
      - (32 * t ^ 2 + 16 * t - 7) * (32 * t ^ 2 + 25 * t + 2)
          / (3 * (1 + t) * (1 + 4 * t) ^ 2 * (5 + 8 * t)) < 0 := by
    have heq : 7 / 5 + (Aexpr t - 2)
        - (32 * t ^ 2 + 16 * t - 7) * (32 * t ^ 2 + 25 * t + 2)
            / (3 * (1 + t) * (1 + 4 * t) ^ 2 * (5 + 8 * t))
        = (-1024 * t ^ 4 - 736 * t ^ 3 + 2244 * t ^ 2 + 1601 * t + 50)
            / (30 * (1 + t) * (1 + 4 * t) ^ 2 * (5 + 8 * t)) := by
      unfold Aexpr; field_simp [ne_of_gt h1t, ne_of_gt h14, ne_of_gt h58]; ring
    rw [heq]
    apply div_neg_of_neg_of_pos _
      (mul_pos (mul_pos (mul_pos (by norm_num) h1t) (pow_pos h14 2)) h58)
    nlinarith [ht, mul_nonneg (sub_nonneg.mpr ht) (mul_nonneg ht0.le ht0.le),
      mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg t), sq_nonneg (t - 3 / 2), mul_pos ht0 ht0,
      mul_pos (mul_pos ht0 ht0) ht0]
  linarith [htan, hrat]

lemma log_thirteen_lt : Real.log 13 < 13 / 5 := by
  have h13 : Real.log 13 = 4 * Real.log 2 + Real.log (13 / 16) := by
    rw [show (13 : ℝ) = 2 ^ 4 * (13 / 16) from by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring_nf
  have hle : Real.log (13 / 16) ≤ 13 / 16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h2 := Real.log_two_lt_d9
  rw [h13]; nlinarith [hle, h2]

lemma Lexpr_neg_on_Icc {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 3 / 2) : Lexpr t < 0 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hA0 : 0 < Aexpr t := Aexpr_pos ht0
  have hB0 : 0 < Bexpr t := Bexpr_pos ht0
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have h14 : (0 : ℝ) < 1 + 4 * t := by linarith
  have h58 : (0 : ℝ) < 5 + 8 * t := by linarith
  have htanA : Real.log (Aexpr t) ≤ Real.log 2 + (Aexpr t - 2) / 2 := by
    rw [show Real.log (Aexpr t) = Real.log 2 + Real.log (Aexpr t / 2) from by
      rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hA0 (by norm_num))),
          show (2 : ℝ) * (Aexpr t / 2) = Aexpr t from by ring]]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Aexpr t / 2 from div_pos hA0 (by norm_num))]
  have htanB : Real.log (Bexpr t) ≤ Real.log 13 + (Bexpr t - 13) / 13 := by
    rw [show Real.log (Bexpr t) = Real.log 13 + Real.log (Bexpr t / 13) from by
      rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hB0 (by norm_num))),
          show (13 : ℝ) * (Bexpr t / 13) = Bexpr t from by ring]]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Bexpr t / 13 from div_pos hB0 (by norm_num))]
  have h2 := Real.log_two_lt_d9
  have h13 := log_thirteen_lt
  have hLbound : Lexpr t
      < 7 * t / 5 + t * (Aexpr t - 2) + (13 / 5 + (Bexpr t - 13) / 13) - Cexpr t := by
    unfold Lexpr
    have hkA : 0 ≤ Real.log 2 + (Aexpr t - 2) / 2 - Real.log (Aexpr t) := by linarith [htanA]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t) hkA, htanB, h13,
      mul_pos ht0 (show (0 : ℝ) < 7 / 10 - Real.log 2 by linarith)]
  have hcubic : 7 * t / 5 + t * (Aexpr t - 2) + (13 / 5 + (Bexpr t - 13) / 13) - Cexpr t
      = 3 * (96 * t ^ 3 - 191 * t ^ 2 - 16 * t + 46) / (130 * (1 + t) * (1 + 4 * t)) := by
    unfold Aexpr Bexpr Cexpr; field_simp [ne_of_gt h1t, ne_of_gt h14, ne_of_gt h58]; ring
  rw [hcubic] at hLbound
  have hcneg : 3 * (96 * t ^ 3 - 191 * t ^ 2 - 16 * t + 46) / (130 * (1 + t) * (1 + 4 * t)) < 0 := by
    apply div_neg_of_neg_of_pos _ (mul_pos (mul_pos (by norm_num) h1t) h14)
    nlinarith [ht1, ht2, mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ht2), sq_nonneg (t - 1),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ht2)) ht0.le]
  linarith [hLbound, hcneg]

lemma Lexpr_neg_of_ge_threehalf {t : ℝ} (ht : 3 / 2 ≤ t) : Lexpr t < 0 := by
  have hanti : AntitoneOn Lexpr (Set.Ici (3 / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun s hs => (Lexpr_hasDerivAt (by have := Set.mem_Ici.mp hs; linarith)).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici, Set.mem_Ioi] at hs
      exact (Lexpr_hasDerivAt (by linarith)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici, Set.mem_Ioi] at hs
      exact (Lprime_neg_of_ge_threehalf (le_of_lt hs)).le
  exact lt_of_le_of_lt (hanti Set.self_mem_Ici (Set.mem_Ici.mpr ht) ht)
    (Lexpr_neg_on_Icc (by norm_num) (le_refl _))

lemma Lexpr_neg_on_half_one {t : ℝ} (ht1 : 1 / 2 ≤ t) (ht2 : t ≤ 1) : Lexpr t < 0 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hA0 : 0 < Aexpr t := Aexpr_pos ht0
  have hB0 : 0 < Bexpr t := Bexpr_pos ht0
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have h14 : (0 : ℝ) < 1 + 4 * t := by linarith
  have h58 : (0 : ℝ) < 5 + 8 * t := by linarith
  have htanA : Real.log (Aexpr t) ≤ Real.log 2 + (Aexpr t - 2) / 2 := by
    rw [show Real.log (Aexpr t) = Real.log 2 + Real.log (Aexpr t / 2) from by
      rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hA0 (by norm_num))),
          show (2 : ℝ) * (Aexpr t / 2) = Aexpr t from by ring]]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Aexpr t / 2 from div_pos hA0 (by norm_num))]
  have htanB : Real.log (Bexpr t) ≤ 3 * Real.log 2 + (Bexpr t - 8) / 8 := by
    rw [show Real.log (Bexpr t) = Real.log 8 + Real.log (Bexpr t / 8) from by
          rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hB0 (by norm_num))),
              show (8 : ℝ) * (Bexpr t / 8) = Bexpr t from by ring],
        show Real.log 8 = 3 * Real.log 2 from by
          rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, Real.log_pow]; push_cast; ring]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Bexpr t / 8 from div_pos hB0 (by norm_num))]
  have h2 := Real.log_two_lt_d9
  have hLbound : Lexpr t < 7 * t / 5 + t * (Aexpr t - 2) + (21 / 10 + (Bexpr t - 8) / 8) - Cexpr t := by
    unfold Lexpr
    have hkA : 0 ≤ Real.log 2 + (Aexpr t - 2) / 2 - Real.log (Aexpr t) := by linarith [htanA]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t) hkA, htanB,
      mul_pos ht0 (show (0 : ℝ) < 7 / 10 - Real.log 2 by linarith), h2]
  have hcubic : 7 * t / 5 + t * (Aexpr t - 2) + (21 / 10 + (Bexpr t - 8) / 8) - Cexpr t
      = (512 * t ^ 3 - 492 * t ^ 2 - 252 * t + 77) / (120 * (1 + t) * (1 + 4 * t)) := by
    unfold Aexpr Bexpr Cexpr; field_simp [ne_of_gt h1t, ne_of_gt h14, ne_of_gt h58]; ring
  rw [hcubic] at hLbound
  have hcneg : (512 * t ^ 3 - 492 * t ^ 2 - 252 * t + 77) / (120 * (1 + t) * (1 + 4 * t)) < 0 := by
    apply div_neg_of_neg_of_pos _ (mul_pos (mul_pos (by norm_num) h1t) h14)
    nlinarith [ht1, ht2, mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ht2), sq_nonneg (t - 1),
      sq_nonneg (2 * t - 1)]
  linarith [hLbound, hcneg]

lemma Lexpr_neg_on_quarter_half {t : ℝ} (ht1 : 1 / 4 ≤ t) (ht2 : t ≤ 1 / 2) : Lexpr t < 0 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hA0 : 0 < Aexpr t := Aexpr_pos ht0
  have hB0 : 0 < Bexpr t := Bexpr_pos ht0
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have h14 : (0 : ℝ) < 1 + 4 * t := by linarith
  have h58 : (0 : ℝ) < 5 + 8 * t := by linarith
  have htanA : Real.log (Aexpr t) ≤ Aexpr t - 1 := Real.log_le_sub_one_of_pos hA0
  have htanB : Real.log (Bexpr t) ≤ 2 * Real.log 2 + (Bexpr t - 4) / 4 := by
    rw [show Real.log (Bexpr t) = Real.log 4 + Real.log (Bexpr t / 4) from by
          rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hB0 (by norm_num))),
              show (4 : ℝ) * (Bexpr t / 4) = Bexpr t from by ring],
        show Real.log 4 = 2 * Real.log 2 from by
          rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; push_cast; ring]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Bexpr t / 4 from div_pos hB0 (by norm_num))]
  have h2 := Real.log_two_lt_d9
  have hLbound : Lexpr t < 2 * t * (Aexpr t - 1) + (7 / 5 + (Bexpr t - 4) / 4) - Cexpr t := by
    unfold Lexpr
    have hkA : 0 ≤ Aexpr t - 1 - Real.log (Aexpr t) := by linarith [htanA]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t) hkA, htanB, h2]
  have hcubic : 2 * t * (Aexpr t - 1) + (7 / 5 + (Bexpr t - 4) / 4) - Cexpr t
      = (960 * t ^ 3 - 24 * t ^ 2 - 300 * t + 9) / (60 * (1 + t) * (1 + 4 * t)) := by
    unfold Aexpr Bexpr Cexpr; field_simp [ne_of_gt h1t, ne_of_gt h14, ne_of_gt h58]; ring
  rw [hcubic] at hLbound
  have hcneg : (960 * t ^ 3 - 24 * t ^ 2 - 300 * t + 9) / (60 * (1 + t) * (1 + 4 * t)) < 0 := by
    apply div_neg_of_neg_of_pos _ (mul_pos (mul_pos (by norm_num) h1t) h14)
    nlinarith [ht1, ht2, mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ht2), sq_nonneg (4 * t - 1),
      sq_nonneg (2 * t - 1)]
  linarith [hLbound, hcneg]

lemma Lexpr_neg_on_zero_quarter {t : ℝ} (ht0 : 0 < t) (ht2 : t ≤ 1 / 4) : Lexpr t < 0 := by
  have hA0 : 0 < Aexpr t := Aexpr_pos ht0
  have hB0 : 0 < Bexpr t := Bexpr_pos ht0
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have h14 : (0 : ℝ) < 1 + 4 * t := by linarith
  have h58 : (0 : ℝ) < 5 + 8 * t := by linarith
  have htanA : Real.log (Aexpr t) ≤ Aexpr t - 1 := Real.log_le_sub_one_of_pos hA0
  have htanB : Real.log (Bexpr t) ≤ Real.log 2 + (Bexpr t - 2) / 2 := by
    rw [show Real.log (Bexpr t) = Real.log 2 + Real.log (Bexpr t / 2) from by
      rw [← Real.log_mul (by norm_num) (ne_of_gt (div_pos hB0 (by norm_num))),
          show (2 : ℝ) * (Bexpr t / 2) = Bexpr t from by ring]]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < Bexpr t / 2 from div_pos hB0 (by norm_num))]
  have h2 := Real.log_two_lt_d9
  have hLbound : Lexpr t < 2 * t * (Aexpr t - 1) + (7 / 10 + (Bexpr t - 2) / 2) - Cexpr t := by
    unfold Lexpr
    have hkA : 0 ≤ Aexpr t - 1 - Real.log (Aexpr t) := by linarith [htanA]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * t) hkA, htanB, h2]
  have hcubic : 2 * t * (Aexpr t - 1) + (7 / 10 + (Bexpr t - 2) / 2) - Cexpr t
      = (800 * t ^ 3 + 264 * t ^ 2 - 135 * t - 4) / (30 * (1 + t) * (1 + 4 * t)) := by
    unfold Aexpr Bexpr Cexpr; field_simp [ne_of_gt h1t, ne_of_gt h14, ne_of_gt h58]; ring
  rw [hcubic] at hLbound
  have hcneg : (800 * t ^ 3 + 264 * t ^ 2 - 135 * t - 4) / (30 * (1 + t) * (1 + 4 * t)) < 0 := by
    apply div_neg_of_neg_of_pos _ (mul_pos (mul_pos (by norm_num) h1t) h14)
    nlinarith [ht0, ht2, mul_nonneg (sub_nonneg.mpr ht2) (mul_nonneg ht0.le ht0.le),
      mul_nonneg (sub_nonneg.mpr ht2) ht0.le]
  linarith [hLbound, hcneg]

theorem Lexpr_neg {t : ℝ} (ht : 0 < t) : Lexpr t < 0 := by
  rcases le_total t (1 / 4) with h | h
  · exact Lexpr_neg_on_zero_quarter ht h
  rcases le_total t (1 / 2) with h2 | h2
  · exact Lexpr_neg_on_quarter_half h h2
  rcases le_total t 1 with h3 | h3
  · exact Lexpr_neg_on_half_one h2 h3
  rcases le_total t (3 / 2) with h4 | h4
  · exact Lexpr_neg_on_Icc h3 h4
  · exact Lexpr_neg_of_ge_threehalf h4

end OddCycleBound.DenseRegion
