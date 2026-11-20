/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.CyclicAngles
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.CayleyCardinal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The literal Lebesgue sum on every open node gap

The coefficients below are explicit products of signs determined solely by the
ordered node indices and the gap cut. Their validity is proved from positivity
of the sine on `(0, π)` and negativity on `(-π, 0)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

/-- The predecessor of a positive cut index.-/
def gapPredecessor (cut : Fin n) : Fin n :=
  ⟨cut.val - 1, (Nat.sub_le _ _).trans_lt cut.isLt⟩

/-- The ordinary gap ending at `cut`; the cut must be positive.-/
def ordinaryGap (angles : CyclicAngles n hn) (cut : Fin n) (_hcut : 0 < cut.val) :
    Set ℝ :=
  Set.Ioo (angles.angle (gapPredecessor cut)) (angles.angle cut)

/-- A one-node family has no ordinary gap cut.
@isnad1 id=not.0h1v.s4.2770ed5a26a8 from=translated src=- shape=68e96a26 vocab=9435b42f
-/
lemma no_positive_cut_one (cut : Fin 1) : ¬0 < cut.val := by
  omega

/--
@isnad1 id=lt.4h5v.s6.bd05466dac0a from=translated src=- shape=0e535de5 vocab=cef6a98f
-/
lemma angle_lt_of_mem_ordinaryGap (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) {t : ℝ} (ht : t ∈ ordinaryGap angles cut hcut)
    {k : Fin n} (hk : k < cut) : angles.angle k < t := by
  have hkle : k ≤ gapPredecessor cut := Nat.le_sub_one_of_lt hk
  exact (angles.strictMono.monotone hkle).trans_lt ht.1

/--
@isnad1 id=lt.4h5v.s6.374f668aa23f from=translated src=- shape=e6821752 vocab=cef6a98f
-/
lemma lt_angle_of_mem_ordinaryGap (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) {t : ℝ} (ht : t ∈ ordinaryGap angles cut hcut)
    {k : Fin n} (hk : ¬k < cut) : t < angles.angle k :=
  ht.2.trans_le (angles.strictMono.monotone (le_of_not_gt hk))

/--
@isnad1 id=mem.3h4v.s6.a6d03b1c9b43 from=translated src=- shape=7cacc70c vocab=dc3ce219
-/
lemma ordinaryGap_mem_Ioo (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) {t : ℝ} (ht : t ∈ ordinaryGap angles cut hcut) :
    t ∈ Set.Ioo 0 (2 * Real.pi) :=
  ⟨(angles.nonneg _).trans_lt ht.1, ht.2.trans (angles.lt_two_pi _)⟩

private lemma sin_half_sub_pos {a b : ℝ} (ha : a < 2 * Real.pi) (hb : 0 ≤ b)
    (hba : b < a) : 0 < Real.sin ((a - b) / 2) := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> linarith

private lemma sin_half_sub_neg {a b : ℝ} (ha : 0 ≤ a) (hb : b < 2 * Real.pi)
    (hab : a < b) : Real.sin ((a - b) / 2) < 0 := by
  apply Real.sin_neg_of_neg_of_neg_pi_lt <;> linarith

/-- Numerator sign on the gap, determined by which side of the cut the node occupies.-/
def gapIndexSign (cut k : Fin n) : ℝ := if k < cut then 1 else -1

/-- Denominator sign, determined by the relative order of two distinct nodes.-/
def nodeIndexSign (j k : Fin n) : ℝ := if k < j then 1 else -1

/-- The nodal coefficient is a finite explicit product of `1` and `-1`.-/
def gapCoefficient (cut j : Fin n) : ℝ :=
  ∏ k ∈ Finset.univ.erase j, gapIndexSign cut k * nodeIndexSign j k

/--
@isnad1 id=eq.0h3v.s4.b442d520c456 from=translated src=- shape=4ffe586d vocab=e1cf43a3
-/
lemma abs_gapIndexSign (cut k : Fin n) : |gapIndexSign cut k| = 1 := by
  unfold gapIndexSign
  split_ifs <;> norm_num

/--
@isnad1 id=eq.0h3v.s4.cfed786a26bb from=translated src=- shape=4ffe586d vocab=35389c37
-/
lemma abs_nodeIndexSign (j k : Fin n) : |nodeIndexSign j k| = 1 := by
  unfold nodeIndexSign
  split_ifs <;> norm_num

/--
@isnad1 id=eq.0h3v.s4.7afa8c1f891d from=translated src=- shape=4ffe586d vocab=3f551287
-/
lemma abs_gapCoefficient (cut j : Fin n) : |gapCoefficient cut j| = 1 := by
  unfold gapCoefficient
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro k hk
  rw [abs_mul, abs_gapIndexSign, abs_nodeIndexSign, one_mul]

/--
@isnad1 id=or.0h3v.s5.192655b045a7 from=translated src=- shape=2f9848a9 vocab=47d026c1
-/
lemma gapCoefficient_eq_one_or_neg_one (cut j : Fin n) :
    gapCoefficient cut j = 1 ∨ gapCoefficient cut j = -1 :=
  abs_eq_abs.mp (by simpa only [abs_one] using abs_gapCoefficient cut j)

/--
@isnad1 id=eq.0h2v.s4.752a9648d695 from=translated src=- shape=48892474 vocab=55fc1fe7
-/
lemma gapCoefficient_at_cut (cut : Fin n) : gapCoefficient cut cut = 1 := by
  unfold gapCoefficient
  apply Finset.prod_eq_one
  intro k hk
  by_cases h : k < cut <;> simp [gapIndexSign, nodeIndexSign, h]

private lemma nodeIndexSign_consecutive {j l k : Fin n} (hjl : j.val + 1 = l.val)
    (hkj : k ≠ j) : nodeIndexSign j k = nodeIndexSign l k := by
  have hside : k < j ↔ k < l := by
    constructor
    · intro h
      show k.val < l.val
      omega
    · intro h
      have hkval : k.val ≠ j.val := fun heq => hkj (Fin.ext heq)
      show k.val < j.val
      omega
  simp only [nodeIndexSign, hside]

/-- Passing between two adjacent nodal indices changes only the two omitted factors.
@isnad1 id=eq.1h4v.s6.64c9c300f522 from=translated src=- shape=baf1ebfe vocab=e3d7201a
-/
lemma gapCoefficient_consecutive (cut j l : Fin n) (hjl : j.val + 1 = l.val) :
    gapCoefficient cut l =
      -(gapIndexSign cut j * gapIndexSign cut l) * gapCoefficient cut j := by
  have hjlt : j < l := by show j.val < l.val; omega
  have hjne : j ≠ l := ne_of_lt hjlt
  let P : ℝ := ∏ k ∈ (Finset.univ.erase j).erase l,
    gapIndexSign cut k * nodeIndexSign j k
  have hprod : (∏ k ∈ (Finset.univ.erase l).erase j,
      gapIndexSign cut k * nodeIndexSign l k) = P := by
    rw [Finset.erase_right_comm]
    apply Finset.prod_congr rfl
    intro k hk
    rw [← nodeIndexSign_consecutive hjl (Finset.mem_erase.mp
      (Finset.mem_erase.mp hk).2).1]
  have hjfactor : gapCoefficient cut j = -gapIndexSign cut l * P := by
    unfold gapCoefficient
    rw [← Finset.mul_prod_erase (Finset.univ.erase j)
      (fun k => gapIndexSign cut k * nodeIndexSign j k)
      (Finset.mem_erase.mpr ⟨hjne.symm, Finset.mem_univ l⟩)]
    have hsign : nodeIndexSign j l = -1 := by
      simp [nodeIndexSign, not_lt.mpr hjlt.le]
    rw [hsign]
    change (gapIndexSign cut l * -1) * P = -gapIndexSign cut l * P
    ring
  have hlfactor : gapCoefficient cut l = gapIndexSign cut j * P := by
    unfold gapCoefficient
    rw [← Finset.mul_prod_erase (Finset.univ.erase l)
      (fun k => gapIndexSign cut k * nodeIndexSign l k)
      (Finset.mem_erase.mpr ⟨hjne, Finset.mem_univ j⟩)]
    rw [show nodeIndexSign l j = 1 by simp [nodeIndexSign, hjlt], hprod, mul_one]
  rw [hjfactor, hlfactor]
  unfold gapIndexSign
  split_ifs <;> ring

/-- All adjacent nodal coefficients flip sign except across the selected gap.
@isnad1 id=eq.2h4v.s5.36a1ec8f3921 from=translated src=- shape=63ad48da vocab=47149e8d
-/
theorem gapCoefficient_consecutive_flip (cut j l : Fin n) (hjl : j.val + 1 = l.val)
    (hlcut : l ≠ cut) : gapCoefficient cut l = -gapCoefficient cut j := by
  have hside : j < cut ↔ l < cut := by
    have hlval : l.val ≠ cut.val := fun heq => hlcut (Fin.ext heq)
    change j.val < cut.val ↔ l.val < cut.val
    omega
  have hsign : gapIndexSign cut j * gapIndexSign cut l = 1 := by
    unfold gapIndexSign
    by_cases h : j < cut
    · simp [h, hside.mp h]
    · have hl : ¬l < cut := fun hl => h (hside.mpr hl)
      simp [h, hl]
  rw [gapCoefficient_consecutive cut j l hjl, hsign, neg_one_mul]

/--
@isnad1 id=eq.1h2v.s4.9a2edee4e14a from=translated src=- shape=07c8cc19 vocab=6b6e20e6
-/
lemma gapCoefficient_at_predecessor (cut : Fin n) (hcut : 0 < cut.val) :
    gapCoefficient cut (gapPredecessor cut) = 1 := by
  have hpred : (gapPredecessor cut).val + 1 = cut.val := by
    change cut.val - 1 + 1 = cut.val
    omega
  have hp : gapPredecessor cut < cut := by
    show cut.val - 1 < cut.val
    omega
  have h := gapCoefficient_consecutive cut (gapPredecessor cut) cut hpred
  simpa [gapIndexSign, hp, gapCoefficient_at_cut] using h.symm

/--
@isnad1 id=injectiv.1h2v.s4.6f8cf66f52c7 from=translated src=- shape=b3bf864c vocab=496c78f5
-/
lemma CyclicAngles.phaseNodes_injective (angles : CyclicAngles n hn) :
    Function.Injective (phaseNodes angles.angle) := by
  intro i j hij
  apply angles.strictMono.injective
  apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
    ⟨angles.nonneg i, angles.lt_two_pi i⟩ ⟨angles.nonneg j, angles.lt_two_pi j⟩
  exact Circle.coe_injective hij

/--
@isnad1 id=eq.1h4v.s5.185f00b97f13 from=translated src=- shape=b7e2ceca vocab=1a77a312
-/
lemma gapInterpolant_at_node (angles : CyclicAngles n hn) (cut j : Fin n) :
    sineInterpolant angles.angle (gapCoefficient cut) (angles.angle j) =
      gapCoefficient cut j :=
  sineInterpolant_at_node angles.angle angles.phaseNodes_injective (gapCoefficient cut) j

/--
@isnad1 id=ne.3h5v.s6.35cce40944cb from=translated src=- shape=c7c60bd7 vocab=6c1ba580
-/
lemma sin_numerator_ne_zero_on_gap (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) {t : ℝ} (ht : t ∈ ordinaryGap angles cut hcut) (k : Fin n) :
    Real.sin ((t - angles.angle k) / 2) ≠ 0 := by
  have htturn := ordinaryGap_mem_Ioo angles cut hcut ht
  by_cases hk : k < cut
  · exact (sin_half_sub_pos htturn.2 (angles.nonneg k)
      (angle_lt_of_mem_ordinaryGap angles cut hcut ht hk)).ne'
  · exact (sin_half_sub_neg htturn.1.le (angles.lt_two_pi k)
      (lt_angle_of_mem_ordinaryGap angles cut hcut ht hk)).ne

/--
@isnad1 id=ne.3h5v.s6.0b7b172abc6a from=translated src=- shape=0aa2d335 vocab=c4c484a2
-/
lemma sineCardinal_ne_zero_on_gap (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) {t : ℝ} (ht : t ∈ ordinaryGap angles cut hcut) (j : Fin n) :
    sineCardinal angles.angle j t ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact div_ne_zero (sin_numerator_ne_zero_on_gap angles cut hcut ht k)
    (sine_denominator_ne_zero angles.angle angles.phaseNodes_injective
      (Finset.mem_erase.mp hk).1.symm)

/--
@isnad1 id=eq.3h5v.s7.b4f9521dc4e2 from=translated src=- shape=7fd23d7d vocab=90f32d31
-/
lemma abs_sin_numerator_on_gap (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) {t : ℝ} (ht : t ∈ ordinaryGap angles cut hcut) (k : Fin n) :
    |Real.sin ((t - angles.angle k) / 2)| =
      gapIndexSign cut k * Real.sin ((t - angles.angle k) / 2) := by
  have htturn := ordinaryGap_mem_Ioo angles cut hcut ht
  by_cases hk : k < cut
  · rw [gapIndexSign, ite_eq_left hk, one_mul]
    exact abs_of_pos (sin_half_sub_pos htturn.2 (angles.nonneg k)
      (angle_lt_of_mem_ordinaryGap angles cut hcut ht hk))
  · rw [gapIndexSign, ite_eq_right hk, neg_one_mul]
    exact abs_of_neg (sin_half_sub_neg htturn.1.le (angles.lt_two_pi k)
      (lt_angle_of_mem_ordinaryGap angles cut hcut ht hk))

/--
@isnad1 id=eq.2h4v.s6.a214c262072e from=translated src=- shape=9e4f111d vocab=2d7d06be
-/
lemma abs_sin_denominator_ordered (angles : CyclicAngles n hn)
    {j k : Fin n} (hjk : j ≠ k) :
    |Real.sin ((angles.angle j - angles.angle k) / 2)| =
      nodeIndexSign j k * Real.sin ((angles.angle j - angles.angle k) / 2) := by
  by_cases hk : k < j
  · rw [nodeIndexSign, ite_eq_left hk, one_mul]
    exact abs_of_pos (sin_half_sub_pos (angles.lt_two_pi j) (angles.nonneg k)
      (angles.strictMono hk))
  · have hjlt : j < k := lt_of_le_of_ne (le_of_not_gt hk) hjk
    rw [nodeIndexSign, ite_eq_right hk, neg_one_mul]
    exact abs_of_neg (sin_half_sub_neg (angles.nonneg j) (angles.lt_two_pi k)
      (angles.strictMono hjlt))

/--
@isnad1 id=eq.4h6v.s7.e4fe804c9cb1 from=translated src=- shape=43ee2086 vocab=be59bbd7
-/
lemma abs_sine_ratio_on_gap (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) {t : ℝ} (ht : t ∈ ordinaryGap angles cut hcut)
    {j k : Fin n} (hjk : j ≠ k) :
    |Real.sin ((t - angles.angle k) / 2) /
        Real.sin ((angles.angle j - angles.angle k) / 2)| =
      (gapIndexSign cut k * nodeIndexSign j k) *
        (Real.sin ((t - angles.angle k) / 2) /
          Real.sin ((angles.angle j - angles.angle k) / 2)) := by
  rw [abs_div, abs_sin_numerator_on_gap angles cut hcut ht k,
    abs_sin_denominator_ordered angles hjk]
  by_cases hc : k < cut <;> by_cases hj : k < j <;>
    simp [gapIndexSign, nodeIndexSign, hc, hj, neg_div, div_neg]

/-- Each entire cardinal has a fixed, explicit sign throughout the ordinary gap.
@isnad1 id=eq.3h5v.s6.8522e1511c73 from=translated src=- shape=50605a7c vocab=5eb50579
-/
theorem abs_sineCardinal_on_gap (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) {t : ℝ} (ht : t ∈ ordinaryGap angles cut hcut) (j : Fin n) :
    |sineCardinal angles.angle j t| =
      gapCoefficient cut j * sineCardinal angles.angle j t := by
  unfold sineCardinal gapCoefficient
  rw [Finset.abs_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  exact abs_sine_ratio_on_gap angles cut hcut ht (Finset.mem_erase.mp hk).1.symm

/--
@isnad1 id=lt.3h5v.s6.dd391d07bea0 from=translated src=- shape=5674f1bd vocab=a42b758e
-/
lemma gapCoefficient_mul_sineCardinal_pos (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) {t : ℝ} (ht : t ∈ ordinaryGap angles cut hcut) (j : Fin n) :
    0 < gapCoefficient cut j * sineCardinal angles.angle j t := by
  rw [← abs_sineCardinal_on_gap angles cut hcut ht j]
  exact abs_pos.mpr (sineCardinal_ne_zero_on_gap angles cut hcut ht j)

/-- The actual absolute-value Lebesgue sum equals one signed interpolant on this gap.
@isnad1 id=eq.3h4v.s6.6356facb3cd6 from=translated src=- shape=e2ddcc96 vocab=edf54e79
-/
theorem sineLebesgueFunction_on_gap (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) {t : ℝ} (ht : t ∈ ordinaryGap angles cut hcut) :
    (∑ j, |sineCardinal angles.angle j t|) =
      sineInterpolant angles.angle (gapCoefficient cut) t := by
  unfold sineInterpolant
  apply Finset.sum_congr rfl
  intro j hj
  exact abs_sineCardinal_on_gap angles cut hcut ht j

/-- The same gap formula for the literal complex Lebesgue function.
@isnad1 id=eq.3h4v.s7.3780a33b9aec from=translated src=- shape=ea6b7f20 vocab=daddf7e3
-/
theorem lebesgueFunction_on_gap (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) {t : ℝ} (ht : t ∈ ordinaryGap angles cut hcut) :
    lebesgueFunction (phaseNodes angles.angle) (Circle.exp t : ℂ) =
      sineInterpolant angles.angle (gapCoefficient cut) t := by
  rw [lebesgueFunction_phase]
  exact sineLebesgueFunction_on_gap angles cut hcut ht

/-- The last ordered index of a positive-size node family.-/
def lastNodeIndex (hn : 0 < n) : Fin n :=
  ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩

/-- The final gap reaches the copy of the first node at `2π`.-/
def wrapGap (angles : CyclicAngles n hn) : Set ℝ :=
  Set.Ioo (angles.angle (lastNodeIndex hn)) (2 * Real.pi)

/-- All numerator sines are positive on the final gap, so only denominator signs remain.-/
def wrapCoefficient (j : Fin n) : ℝ :=
  ∏ k ∈ Finset.univ.erase j, nodeIndexSign j k

/--
@isnad1 id=lt.2h4v.s5.03b0c0810167 from=translated src=- shape=2f54eab9 vocab=e1651a96
-/
lemma angle_lt_of_mem_wrapGap (angles : CyclicAngles n hn) {t : ℝ}
    (ht : t ∈ wrapGap angles) (k : Fin n) : angles.angle k < t := by
  have hkle : k ≤ lastNodeIndex hn := Nat.le_sub_one_of_lt k.isLt
  exact (angles.strictMono.monotone hkle).trans_lt ht.1

/--
@isnad1 id=mem.2h3v.s5.4425f2cee800 from=translated src=- shape=40beffef vocab=6a94d74d
-/
lemma wrapGap_mem_Ioo (angles : CyclicAngles n hn) {t : ℝ}
    (ht : t ∈ wrapGap angles) : t ∈ Set.Ioo 0 (2 * Real.pi) :=
  ⟨(angles.nonneg _).trans_lt ht.1, ht.2⟩

/--
@isnad1 id=eq.0h2v.s4.da6424505614 from=translated src=- shape=b07e26e0 vocab=25a466bc
-/
lemma abs_wrapCoefficient (j : Fin n) : |wrapCoefficient j| = 1 := by
  unfold wrapCoefficient
  rw [Finset.abs_prod]
  exact Finset.prod_eq_one fun k _hk => abs_nodeIndexSign j k

/--
@isnad1 id=or.0h2v.s4.1efee04cf751 from=translated src=- shape=93c5e8d7 vocab=1b8b2673
-/
lemma wrapCoefficient_eq_one_or_neg_one (j : Fin n) :
    wrapCoefficient j = 1 ∨ wrapCoefficient j = -1 :=
  abs_eq_abs.mp (by simpa only [abs_one] using abs_wrapCoefficient j)

private lemma gapCoefficient_zero (hn : 0 < n) (j : Fin n) :
    gapCoefficient ⟨0, hn⟩ j = (-1 : ℝ) ^ (n - 1) * wrapCoefficient j := by
  unfold gapCoefficient
  have hsign (k : Fin n) : gapIndexSign ⟨0, hn⟩ k = -1 := by
    simp only [gapIndexSign, Fin.lt_def, Nat.not_lt_zero, ite_false]
  simp_rw [hsign]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
    Fintype.card_fin, wrapCoefficient]

/-- The final gap differs from the zero-cut coefficient by the full-turn phase sign.
This factor is essential when the number of nodes is even.
@isnad1 id=eq.1h2v.s6.ee9475f183f9 from=translated src=- shape=4165b425 vocab=8a4c5076
-/
lemma wrapCoefficient_eq_phaseSign_mul_gapCoefficient (hn : 0 < n) (j : Fin n) :
    wrapCoefficient j = (-1 : ℝ) ^ (n - 1) * gapCoefficient ⟨0, hn⟩ j := by
  have heps : (-1 : ℝ) ^ (n - 1) * (-1 : ℝ) ^ (n - 1) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [gapCoefficient_zero hn, ← mul_assoc, heps, one_mul]

/--
@isnad1 id=eq.1h1v.s5.47b70a5271ec from=translated src=- shape=ee38f69a vocab=f2ada345
-/
lemma wrapCoefficient_at_first (hn : 0 < n) :
    wrapCoefficient (⟨0, hn⟩ : Fin n) = (-1 : ℝ) ^ (n - 1) := by
  rw [wrapCoefficient_eq_phaseSign_mul_gapCoefficient hn, gapCoefficient_at_cut, mul_one]

/--
@isnad1 id=eq.1h1v.s4.7d64cb0210f3 from=translated src=- shape=56d4aa0f vocab=ea1d9eb6
-/
lemma wrapCoefficient_at_last (hn : 0 < n) : wrapCoefficient (lastNodeIndex hn) = 1 := by
  unfold wrapCoefficient
  apply Finset.prod_eq_one
  intro k hk
  have hkne : k ≠ lastNodeIndex hn := (Finset.mem_erase.mp hk).1
  have hkval : k.val ≠ n - 1 := fun heq => hkne (Fin.ext heq)
  have hklt : k < lastNodeIndex hn := by
    show k.val < n - 1
    omega
  simp [nodeIndexSign, hklt]

/--
@isnad1 id=eq.0h3v.s5.f6d9e357c587 from=translated src=- shape=bef8530a vocab=8bdb2cf8
-/
lemma gapCoefficient_eq_prod_mul_wrapCoefficient (cut j : Fin n) :
    gapCoefficient cut j =
      (∏ k ∈ Finset.univ.erase j, gapIndexSign cut k) * wrapCoefficient j := by
  unfold gapCoefficient wrapCoefficient
  exact Finset.prod_mul_distrib

/-- For an ordinary selected gap, its interpolant changes sign across the other,
final gap after transporting the first nodal value through one full turn.
@isnad1 id=eq.2h2v.s6.049568a2341d from=translated src=- shape=7259dda4 vocab=01aa8e8a
-/
theorem gapCoefficient_wrap_flip (hn : 0 < n) (cut : Fin n) (hcut : 0 < cut.val) :
    (-1 : ℝ) ^ (n - 1) * gapCoefficient cut (⟨0, hn⟩ : Fin n) =
      -gapCoefficient cut (lastNodeIndex hn) := by
  have hfirstlt : (⟨0, hn⟩ : Fin n) < cut := hcut
  have hfirst : gapIndexSign cut (⟨0, hn⟩ : Fin n) = 1 := by
    simp [gapIndexSign, hfirstlt]
  have hlastle : cut ≤ lastNodeIndex hn := Nat.le_sub_one_of_lt cut.isLt
  have hlast : gapIndexSign cut (lastNodeIndex hn) = -1 := by
    simp [gapIndexSign, not_lt.mpr hlastle]
  have hfirstprod := Finset.prod_erase (Finset.univ : Finset (Fin n)) hfirst
  have hlastprod := Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
    (gapIndexSign cut) (Finset.mem_univ (lastNodeIndex hn))
  rw [hlast, neg_one_mul] at hlastprod
  have heps : (-1 : ℝ) ^ (n - 1) * (-1 : ℝ) ^ (n - 1) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [gapCoefficient_eq_prod_mul_wrapCoefficient,
    gapCoefficient_eq_prod_mul_wrapCoefficient,
    wrapCoefficient_at_first, wrapCoefficient_at_last, mul_one, hfirstprod]
  calc
    (-1 : ℝ) ^ (n - 1) * ((∏ k, gapIndexSign cut k) * (-1 : ℝ) ^ (n - 1)) =
        (∏ k, gapIndexSign cut k) *
          ((-1 : ℝ) ^ (n - 1) * (-1 : ℝ) ^ (n - 1)) := by ring
    _ = ∏ k, gapIndexSign cut k := by rw [heps, mul_one]
    _ = -(∏ k ∈ Finset.univ.erase (lastNodeIndex hn), gapIndexSign cut k) := hlastprod.symm

/-- Every pair of consecutive nodal coefficients flips on the final gap.
@isnad1 id=eq.2h3v.s5.51b4e679ff96 from=translated src=- shape=7ec47a98 vocab=ad6bd8c1
-/
theorem wrapCoefficient_consecutive_flip (hn : 0 < n) (j l : Fin n)
    (hjl : j.val + 1 = l.val) : wrapCoefficient l = -wrapCoefficient j := by
  have hlzero : l ≠ (⟨0, hn⟩ : Fin n) := by
    intro h
    have := congrArg Fin.val h
    change l.val = 0 at this
    omega
  rw [wrapCoefficient_eq_phaseSign_mul_gapCoefficient hn l,
    wrapCoefficient_eq_phaseSign_mul_gapCoefficient hn j,
    gapCoefficient_consecutive_flip ⟨0, hn⟩ j l hjl hlzero, mul_neg]

/--
@isnad1 id=lt.2h4v.s6.beafa5378dc1 from=translated src=- shape=51a9a126 vocab=a7df08ca
-/
lemma sin_numerator_pos_on_wrapGap (angles : CyclicAngles n hn) {t : ℝ}
    (ht : t ∈ wrapGap angles) (k : Fin n) :
    0 < Real.sin ((t - angles.angle k) / 2) :=
  sin_half_sub_pos ht.2 (angles.nonneg k) (angle_lt_of_mem_wrapGap angles ht k)

/--
@isnad1 id=ne.2h4v.s5.c8ec81830373 from=translated src=- shape=04c51ff8 vocab=adb6204e
-/
lemma sineCardinal_ne_zero_on_wrapGap (angles : CyclicAngles n hn) {t : ℝ}
    (ht : t ∈ wrapGap angles) (j : Fin n) : sineCardinal angles.angle j t ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact div_ne_zero (sin_numerator_pos_on_wrapGap angles ht k).ne'
    (sine_denominator_ne_zero angles.angle angles.phaseNodes_injective
      (Finset.mem_erase.mp hk).1.symm)

/--
@isnad1 id=eq.3h5v.s7.34a0e1851ab3 from=translated src=- shape=34d15eb7 vocab=8b84ec9a
-/
lemma abs_sine_ratio_on_wrapGap (angles : CyclicAngles n hn) {t : ℝ}
    (ht : t ∈ wrapGap angles) {j k : Fin n} (hjk : j ≠ k) :
    |Real.sin ((t - angles.angle k) / 2) /
        Real.sin ((angles.angle j - angles.angle k) / 2)| =
      nodeIndexSign j k * (Real.sin ((t - angles.angle k) / 2) /
        Real.sin ((angles.angle j - angles.angle k) / 2)) := by
  rw [abs_div, abs_of_pos (sin_numerator_pos_on_wrapGap angles ht k),
    abs_sin_denominator_ordered angles hjk]
  by_cases h : k < j <;> simp [nodeIndexSign, h, div_neg]

/--
@isnad1 id=eq.2h4v.s6.83b9b1453a5b from=translated src=- shape=92948d16 vocab=29c5de31
-/
theorem abs_sineCardinal_on_wrapGap (angles : CyclicAngles n hn) {t : ℝ}
    (ht : t ∈ wrapGap angles) (j : Fin n) :
    |sineCardinal angles.angle j t| = wrapCoefficient j * sineCardinal angles.angle j t := by
  unfold sineCardinal wrapCoefficient
  rw [Finset.abs_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  exact abs_sine_ratio_on_wrapGap angles ht (Finset.mem_erase.mp hk).1.symm

/--
@isnad1 id=lt.2h4v.s5.cbe401a1eb12 from=translated src=- shape=f4ec9900 vocab=9c4ba141
-/
lemma wrapCoefficient_mul_sineCardinal_pos (angles : CyclicAngles n hn) {t : ℝ}
    (ht : t ∈ wrapGap angles) (j : Fin n) :
    0 < wrapCoefficient j * sineCardinal angles.angle j t := by
  rw [← abs_sineCardinal_on_wrapGap angles ht j]
  exact abs_pos.mpr (sineCardinal_ne_zero_on_wrapGap angles ht j)

/--
@isnad1 id=eq.2h3v.s6.d8bd7fe51761 from=translated src=- shape=a111c90a vocab=06301246
-/
theorem sineLebesgueFunction_on_wrapGap (angles : CyclicAngles n hn) {t : ℝ}
    (ht : t ∈ wrapGap angles) :
    (∑ j, |sineCardinal angles.angle j t|) = sineInterpolant angles.angle wrapCoefficient t := by
  unfold sineInterpolant
  apply Finset.sum_congr rfl
  intro j hj
  exact abs_sineCardinal_on_wrapGap angles ht j

/--
@isnad1 id=eq.2h3v.s7.cd3a5ffab32d from=translated src=- shape=825b3f13 vocab=26455dda
-/
theorem lebesgueFunction_on_wrapGap (angles : CyclicAngles n hn) {t : ℝ}
    (ht : t ∈ wrapGap angles) :
    lebesgueFunction (phaseNodes angles.angle) (Circle.exp t : ℂ) =
      sineInterpolant angles.angle wrapCoefficient t := by
  rw [lebesgueFunction_phase]
  exact sineLebesgueFunction_on_wrapGap angles ht

/--
@isnad1 id=eq.1h3v.s5.dfbe2d2da5a4 from=translated src=- shape=e126c43e vocab=fb47f2fc
-/
lemma wrapInterpolant_at_node (angles : CyclicAngles n hn) (j : Fin n) :
    sineInterpolant angles.angle wrapCoefficient (angles.angle j) = wrapCoefficient j :=
  sineInterpolant_at_node angles.angle angles.phaseNodes_injective wrapCoefficient j

/--
@isnad1 id=eq.1h2v.s5.308feeb0ab28 from=translated src=- shape=44670157 vocab=aa732bcf
-/
lemma wrapInterpolant_at_last (angles : CyclicAngles n hn) :
    sineInterpolant angles.angle wrapCoefficient (angles.angle (lastNodeIndex hn)) = 1 := by
  rw [wrapInterpolant_at_node, wrapCoefficient_at_last]

/--
@isnad1 id=eq.1h2v.s6.79bb1769b5e3 from=translated src=- shape=603b8a70 vocab=06787f8d
-/
lemma wrapInterpolant_at_zero (angles : CyclicAngles n hn) :
    sineInterpolant angles.angle wrapCoefficient 0 = (-1 : ℝ) ^ (n - 1) := by
  rw [← angles.first_eq_zero, wrapInterpolant_at_node, wrapCoefficient_at_first]

/--
@isnad1 id=eq.1h3v.s6.fc2b46abbfdc from=translated src=- shape=7c7c472c vocab=e399f031
-/
lemma wrapInterpolant_add_two_pi (angles : CyclicAngles n hn) (t : ℝ) :
    sineInterpolant angles.angle wrapCoefficient (t + 2 * Real.pi) =
      (-1 : ℝ) ^ (n - 1) * sineInterpolant angles.angle wrapCoefficient t := by
  unfold sineInterpolant
  simp_rw [sineCardinal_add_two_pi]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/--
@isnad1 id=eq.1h2v.s5.7e70b39ebd3f from=translated src=- shape=0d481463 vocab=9361e0a6
-/
lemma wrapInterpolant_at_two_pi (angles : CyclicAngles n hn) :
    sineInterpolant angles.angle wrapCoefficient (2 * Real.pi) = 1 := by
  have h := wrapInterpolant_add_two_pi angles 0
  rw [zero_add, wrapInterpolant_at_zero, ← mul_pow] at h
  norm_num at h
  exact h

end

end UnitCircleInterpolation
