import Tengoku.Piirrationalitymeasure.Formalization.RootIsolation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The real root and the conjugate pair of the stationary cubic, following
Appendix A.1--A.2.
-/

namespace PiIrrationality

noncomputable def stationaryRoot : ℝ :=
  Classical.choose stationaryCubic_unique_root

theorem stationaryRoot_mem : stationaryRoot ∈ Set.Icc (66 : ℝ) 67 := by
  simpa [stationaryRoot] using (Classical.choose_spec stationaryCubic_unique_root).1.1

theorem stationaryRoot_eq_zero : stationaryCubic stationaryRoot = 0 := by
  simpa [stationaryRoot] using (Classical.choose_spec stationaryCubic_unique_root).1.2

theorem stationaryCubic_at_663_10 : stationaryCubic ((663 : ℝ) / 10) < 0 := by
  norm_num [stationaryCubic]

theorem stationaryCubic_at_664_10 : 0 < stationaryCubic ((664 : ℝ) / 10) := by
  norm_num [stationaryCubic]

theorem stationaryRoot_gt_663_10 : (663 : ℝ) / 10 < stationaryRoot := by
  by_contra h
  have hle : stationaryRoot ≤ (663 : ℝ) / 10 := le_of_not_gt h
  have hlt : stationaryRoot < (663 : ℝ) / 10 := lt_of_le_of_ne hle (by
    intro heq
    have hzero := stationaryRoot_eq_zero
    rw [heq] at hzero
    norm_num [stationaryCubic] at hzero)
  have hmono := stationaryCubic_strictMono (a := stationaryRoot) (b := (663 : ℝ) / 10)
    stationaryRoot_mem
    ⟨by norm_num, by norm_num⟩ hlt
  linarith [stationaryRoot_eq_zero, stationaryCubic_at_663_10]

theorem stationaryRoot_lt_664_10 : stationaryRoot < (664 : ℝ) / 10 := by
  by_contra h
  have hle : (664 : ℝ) / 10 ≤ stationaryRoot := le_of_not_gt h
  have hlt : (664 : ℝ) / 10 < stationaryRoot := lt_of_le_of_ne hle (by
    intro heq
    have hzero := stationaryRoot_eq_zero
    rw [← heq] at hzero
    norm_num [stationaryCubic] at hzero)
  have hmono := stationaryCubic_strictMono (a := (664 : ℝ) / 10) (b := stationaryRoot)
    ⟨by norm_num, by norm_num⟩ stationaryRoot_mem hlt
  linarith [stationaryRoot_eq_zero, stationaryCubic_at_664_10]

theorem stationaryCubic_at_6632_100 : stationaryCubic ((6632 : ℝ) / 100) < 0 := by
  norm_num [stationaryCubic]

theorem stationaryCubic_at_6633_100 : 0 < stationaryCubic ((6633 : ℝ) / 100) := by
  norm_num [stationaryCubic]

theorem stationaryRoot_gt_6632_100 : (6632 : ℝ) / 100 < stationaryRoot := by
  by_contra h
  have hle : stationaryRoot ≤ (6632 : ℝ) / 100 := le_of_not_gt h
  have hlt : stationaryRoot < (6632 : ℝ) / 100 := lt_of_le_of_ne hle (by
    intro heq
    have hzero := stationaryRoot_eq_zero
    rw [heq] at hzero
    norm_num [stationaryCubic] at hzero)
  have hmono := stationaryCubic_strictMono (a := stationaryRoot) (b := (6632 : ℝ) / 100)
    stationaryRoot_mem ⟨by norm_num, by norm_num⟩ hlt
  linarith [stationaryRoot_eq_zero, stationaryCubic_at_6632_100]

theorem stationaryRoot_lt_6633_100 : stationaryRoot < (6633 : ℝ) / 100 := by
  by_contra h
  have hle : (6633 : ℝ) / 100 ≤ stationaryRoot := le_of_not_gt h
  have hlt : (6633 : ℝ) / 100 < stationaryRoot := lt_of_le_of_ne hle (by
    intro heq
    have hzero := stationaryRoot_eq_zero
    rw [← heq] at hzero
    norm_num [stationaryCubic] at hzero)
  have hmono := stationaryCubic_strictMono (a := (6633 : ℝ) / 100) (b := stationaryRoot)
    ⟨by norm_num, by norm_num⟩ stationaryRoot_mem hlt
  linarith [stationaryRoot_eq_zero, stationaryCubic_at_6633_100]

noncomputable def rhoLower : ℝ := (66321017380598567172217731240 : ℝ) / 10 ^ 27

noncomputable def rhoUpper : ℝ := (66321017380598567172217731241 : ℝ) / 10 ^ 27

theorem stationaryCubic_at_rhoLower : stationaryCubic rhoLower < 0 := by
  norm_num [stationaryCubic, rhoLower]

theorem stationaryCubic_at_rhoUpper : 0 < stationaryCubic rhoUpper := by
  norm_num [stationaryCubic, rhoUpper]

theorem rhoLower_mem : rhoLower ∈ Set.Icc (66 : ℝ) 67 := by
  constructor <;> norm_num [rhoLower]

theorem rhoUpper_mem : rhoUpper ∈ Set.Icc (66 : ℝ) 67 := by
  constructor <;> norm_num [rhoUpper]

theorem stationaryRoot_gt_rhoLower : rhoLower < stationaryRoot := by
  by_contra h
  have hle : stationaryRoot ≤ rhoLower := le_of_not_gt h
  have hlt : stationaryRoot < rhoLower := lt_of_le_of_ne hle (by
    intro heq
    have hzero := stationaryRoot_eq_zero
    rw [heq] at hzero
    norm_num [stationaryCubic, rhoLower] at hzero)
  have hmono := stationaryCubic_strictMono (a := stationaryRoot) (b := rhoLower)
    stationaryRoot_mem rhoLower_mem hlt
  linarith [stationaryRoot_eq_zero, stationaryCubic_at_rhoLower]

theorem stationaryRoot_lt_rhoUpper : stationaryRoot < rhoUpper := by
  by_contra h
  have hle : rhoUpper ≤ stationaryRoot := le_of_not_gt h
  have hlt : rhoUpper < stationaryRoot := lt_of_le_of_ne hle (by
    intro heq
    have hzero := stationaryRoot_eq_zero
    rw [← heq] at hzero
    norm_num [stationaryCubic, rhoUpper] at hzero)
  have hmono := stationaryCubic_strictMono (a := rhoUpper) (b := stationaryRoot)
    rhoUpper_mem stationaryRoot_mem hlt
  linarith [stationaryRoot_eq_zero, stationaryCubic_at_rhoUpper]

noncomputable def saddleULower : ℝ :=
  -(1919728071187574299433227 : ℝ) / 10 ^ 24

noncomputable def saddleUUpper : ℝ :=
  -(1919728071187574299433226 : ℝ) / 10 ^ 24

theorem stationaryRoot_pos : 0 < stationaryRoot := by
  linarith [stationaryRoot_mem.1]

noncomputable def saddleU : ℝ :=
  ((232119 : ℝ) / 3715 - stationaryRoot) / 2

theorem saddleU_paper_bounds : saddleULower < saddleU ∧ saddleU < saddleUUpper := by
  unfold saddleULower saddleUUpper saddleU
  have hL := stationaryRoot_gt_rhoLower
  have hU := stationaryRoot_lt_rhoUpper
  unfold rhoLower at hL
  unfold rhoUpper at hU
  constructor <;> nlinarith [hL, hU]

noncomputable def saddleNormSq : ℝ := (232125 : ℝ) / (743 * stationaryRoot)

noncomputable def saddleVSq : ℝ := saddleNormSq - saddleU ^ 2

theorem saddleNormSq_pos : 0 < saddleNormSq := by
  unfold saddleNormSq
  exact div_pos (by norm_num) (mul_pos (by norm_num) stationaryRoot_pos)

theorem saddleU_bounds : -(2 : ℝ) < saddleU ∧ saddleU < 0 := by
  unfold saddleU
  constructor <;> nlinarith [stationaryRoot_gt_663_10,
    stationaryRoot_lt_664_10]

theorem saddleU_tight_bounds : -(193 : ℝ) / 100 < saddleU ∧ saddleU < -(19 : ℝ) / 10 := by
  unfold saddleU
  constructor <;> nlinarith [stationaryRoot_gt_6632_100,
    stationaryRoot_lt_6633_100]

theorem saddleNormSq_gt : (47 : ℝ) / 10 < saddleNormSq := by
  unfold saddleNormSq
  have hr : 0 < 743 * stationaryRoot := mul_pos (by norm_num) stationaryRoot_pos
  apply (lt_div_iff₀ hr).2
  nlinarith [stationaryRoot_lt_664_10]

theorem saddleNormSq_lt : saddleNormSq < (24 : ℝ) / 5 := by
  unfold saddleNormSq
  have hr : 0 < 743 * stationaryRoot := mul_pos (by norm_num) stationaryRoot_pos
  apply (div_lt_iff₀ hr).2
  nlinarith [stationaryRoot_gt_6632_100]

theorem saddleVSq_pos : 0 < saddleVSq := by
  unfold saddleVSq
  have hu : saddleU ^ 2 < (4 : ℝ) := by
    rcases saddleU_bounds with ⟨hu0, hu1⟩
    nlinarith [sq_nonneg (saddleU + 2), sq_nonneg saddleU]
  nlinarith [saddleNormSq_gt]

noncomputable def saddleV : ℝ := Real.sqrt saddleVSq

theorem saddleV_pos : 0 < saddleV := by
  unfold saddleV
  exact Real.sqrt_pos.2 saddleVSq_pos

theorem saddleV_sq : saddleV ^ 2 = saddleVSq := by
  exact Real.sq_sqrt saddleVSq_pos.le

theorem saddleV_gt : (49 : ℝ) / 50 < saddleV := by
  have hv := saddleV_sq
  unfold saddleVSq at hv
  have hv2 : ((49 : ℝ) / 50) ^ 2 < saddleV ^ 2 := by
    have hu := saddleU_tight_bounds
    nlinarith [saddleNormSq_gt, hv]
  nlinarith [saddleV_pos]

noncomputable def saddleNormSqLower : ℝ :=
  (4710661776618520503155596336 : ℝ) / 10 ^ 27

noncomputable def saddleNormSqUpper : ℝ :=
  (4710661776618520503155596337 : ℝ) / 10 ^ 27

theorem saddleNormSq_paper_bounds :
    saddleNormSqLower < saddleNormSq ∧ saddleNormSq < saddleNormSqUpper := by
  unfold saddleNormSqLower saddleNormSqUpper saddleNormSq
  have hL := stationaryRoot_gt_rhoLower
  have hU := stationaryRoot_lt_rhoUpper
  unfold rhoLower at hL
  unfold rhoUpper at hU
  have hr : 0 < 743 * stationaryRoot :=
    mul_pos (by norm_num) stationaryRoot_pos
  constructor
  · apply (lt_div_iff₀ hr).2
    nlinarith [hU]
  · apply (div_lt_iff₀ hr).2
    nlinarith [hL]

noncomputable def saddleVLower : ℝ :=
  (1012573903136435847419597 : ℝ) / 10 ^ 24

noncomputable def saddleVUpper : ℝ :=
  (1012573903136435847419598 : ℝ) / 10 ^ 24

noncomputable def saddleUTightLower : ℝ :=
  -(19197280711875742994332264 : ℝ) / 10 ^ 25

noncomputable def saddleUTightUpper : ℝ :=
  -(19197280711875742994332263 : ℝ) / 10 ^ 25

theorem saddleU_tight_paper_bounds :
    saddleUTightLower < saddleU ∧ saddleU < saddleUTightUpper := by
  unfold saddleUTightLower saddleUTightUpper saddleU
  have hL := stationaryRoot_gt_rhoLower
  have hU := stationaryRoot_lt_rhoUpper
  unfold rhoLower at hL
  unfold rhoUpper at hU
  have hsum : (-(19197280711875742994332264 : ℝ) / 10 ^ 25) +
      (232119 / 3715 - stationaryRoot) / 2 < 0 := by
    nlinarith [hL, hU]
  constructor <;> nlinarith [hL, hU, hsum]

theorem saddleV_paper_bounds :
    saddleVLower < saddleV ∧ saddleV < saddleVUpper := by
  have hv := saddleV_sq
  unfold saddleVSq at hv
  have hm := saddleNormSq_paper_bounds
  have hu := saddleU_paper_bounds
  dsimp [saddleNormSqLower, saddleNormSqUpper] at hm
  have hULneg : saddleULower < 0 := by norm_num [saddleULower]
  have hUUneg : saddleUUpper < 0 := by norm_num [saddleUUpper]
  have hsq_lower : saddleU ^ 2 < saddleULower ^ 2 := by
    have hprod : 0 < (saddleULower - saddleU) * (saddleULower + saddleU) := by
      apply mul_pos_of_neg_of_neg
      · linarith [hu.1]
      · linarith [hu.1, hULneg, hu.2]
    nlinarith [hprod]
  have hsq_upper : saddleUUpper ^ 2 < saddleU ^ 2 := by
    have hprod : 0 < (saddleU - saddleUUpper) * (saddleU + saddleUUpper) := by
      apply mul_pos_of_neg_of_neg
      · linarith [hu.2]
      · linarith [hu.1, hUUneg, hu.2]
    nlinarith [hprod]

  have hlow : saddleVLower ^ 2 < saddleV ^ 2 := by
    unfold saddleVLower
    norm_num
    have hnum :
        ((1012573903136435847419597 : ℝ) / 10 ^ 24) ^ 2 <
          (4710661776618520503155596336 : ℝ) / 10 ^ 27 -
            saddleUTightLower ^ 2 := by
      norm_num [saddleUTightLower]
    have ht := saddleU_tight_paper_bounds
    have hsq : saddleU ^ 2 < saddleUTightLower ^ 2 := by
      have hprod : 0 < (saddleUTightLower - saddleU) *
          (saddleUTightLower + saddleU) := by
        apply mul_pos_of_neg_of_neg
        · linarith [ht.1]
        · have hneg : saddleUTightLower < 0 := by norm_num [saddleUTightLower]
          linarith [ht.1, ht.2, hneg]
      nlinarith [hprod]
    nlinarith [hv, hm.1, hsq, hnum]
  have hupp : saddleV ^ 2 < saddleVUpper ^ 2 := by
    unfold saddleVUpper
    norm_num
    have hnum :
        (4710661776618520503155596337 : ℝ) / 10 ^ 27 -
            saddleUTightUpper ^ 2 <
          ((1012573903136435847419598 : ℝ) / 10 ^ 24) ^ 2 := by
      norm_num [saddleUTightUpper]
    have ht := saddleU_tight_paper_bounds
    have hsq : saddleUTightUpper ^ 2 < saddleU ^ 2 := by
      have hprod : 0 < (saddleU - saddleUTightUpper) *
          (saddleU + saddleUTightUpper) := by
        apply mul_pos_of_neg_of_neg
        · linarith [ht.2]
        · have hneg : saddleUTightUpper < 0 := by norm_num [saddleUTightUpper]
          linarith [ht.1, ht.2, hneg]
      nlinarith [hprod]
    nlinarith [hv, hm.2, hsq, hnum]
  have hvLpos : 0 < saddleVLower := by norm_num [saddleVLower]
  have hvUpos : 0 < saddleVUpper := by norm_num [saddleVUpper]
  constructor <;> nlinarith [saddleV_pos, hvLpos, hvUpos]

noncomputable def saddleUpper : ℂ := (saddleU : ℂ) + (saddleV : ℂ) * Complex.I

theorem stationaryCubic_complex_factorization (z : ℂ) :
    (3715 : ℂ) * z ^ 3 - 232119 * z ^ 2 - 928475 * z - 1160625 =
      (3715 : ℂ) * (z - (stationaryRoot : ℂ)) *
        (z ^ 2 - 2 * (saddleU : ℂ) * z + (saddleNormSq : ℂ)) := by
  have hr := stationaryRoot_eq_zero
  unfold stationaryCubic at hr
  have hsum : (3715 : ℝ) * (2 * saddleU + stationaryRoot) = 232119 := by
    unfold saddleU
    ring
  have hpair : (3715 : ℝ) * (saddleNormSq + 2 * stationaryRoot * saddleU) = -928475 := by
    unfold saddleU saddleNormSq
    field_simp [ne_of_gt stationaryRoot_pos]
    nlinarith [hr]
  have hprod : (3715 : ℝ) * stationaryRoot * saddleNormSq = 1160625 := by
    unfold saddleNormSq
    field_simp [ne_of_gt stationaryRoot_pos]
    ring
  have hsumC : (3715 : ℂ) * (2 * (saddleU : ℂ) + stationaryRoot) = 232119 := by
    exact_mod_cast hsum
  have hpairC : (3715 : ℂ) * ((saddleNormSq : ℂ) +
      2 * stationaryRoot * (saddleU : ℂ)) = -928475 := by
    exact_mod_cast hpair
  have hprodC : (3715 : ℂ) * stationaryRoot * (saddleNormSq : ℂ) = 1160625 := by
    exact_mod_cast hprod
  calc
    (3715 : ℂ) * z ^ 3 - 232119 * z ^ 2 - 928475 * z - 1160625 =
        (3715 : ℂ) * z ^ 3 -
          (3715 : ℂ) * (2 * (saddleU : ℂ) + stationaryRoot) * z ^ 2 +
          (3715 : ℂ) * ((saddleNormSq : ℂ) + 2 * stationaryRoot * (saddleU : ℂ)) * z -
          (3715 : ℂ) * stationaryRoot * (saddleNormSq : ℂ) := by
            rw [hsumC, hpairC, hprodC]
            ring
    _ = (3715 : ℂ) * (z - (stationaryRoot : ℂ)) *
        (z ^ 2 - 2 * (saddleU : ℂ) * z + (saddleNormSq : ℂ)) := by ring

theorem saddleUpper_quadratic_eq_zero :
    saddleUpper ^ 2 - 2 * (saddleU : ℂ) * saddleUpper +
        (saddleNormSq : ℂ) = 0 := by
  apply Complex.ext <;>
    simp [saddleUpper, pow_two, Complex.mul_re, Complex.mul_im]
  · have hv := saddleV_sq
    unfold saddleVSq at hv
    nlinarith [hv]
  · ring

theorem stationaryCubic_saddleUpper :
    (3715 : ℂ) * saddleUpper ^ 3 - 232119 * saddleUpper ^ 2 -
        928475 * saddleUpper - 1160625 = 0 := by
  rw [stationaryCubic_complex_factorization, saddleUpper_quadratic_eq_zero]
  ring

end PiIrrationality
