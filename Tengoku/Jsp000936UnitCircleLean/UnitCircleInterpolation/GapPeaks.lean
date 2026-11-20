/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.OrdinaryPeaks
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.WrapPeaks
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual peak and height of each cyclic node gap

A cut at zero denotes the final gap from the last node to the copy of the
first node at `2π`. A positive cut denotes the ordinary gap ending at that
node. Each height is the value of the actual signed sine interpolant at its
unique strict peak, and hence the literal complex Lebesgue function there.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

/-- The left endpoint of the cyclic gap ending at a cut. The zero cut wraps.-/
def gapLeft (angles : CyclicAngles n hn) (cut : Fin n) : ℝ :=
  if cut.val = 0 then angles.angle (lastNodeIndex hn)
  else angles.angle (gapPredecessor cut)

/-- The right endpoint, using `2π` for the copy of the first node at the zero cut.-/
def gapRight (angles : CyclicAngles n hn) (cut : Fin n) : ℝ :=
  if cut.val = 0 then 2 * Real.pi else angles.angle cut

/-- The actual real signs of the cardinals on this gap, including the wrap sign.-/
def cyclicGapCoefficient (cut : Fin n) : Fin n → ℝ :=
  if cut.val = 0 then wrapCoefficient else gapCoefficient cut

/-- The signed sine interpolant that equals the literal Lebesgue function on the gap.-/
def gapInterpolant (angles : CyclicAngles n hn) (cut : Fin n) : ℝ → ℝ :=
  sineInterpolant angles.angle (cyclicGapCoefficient cut)

/-- Every cut names an actual open cyclic node gap.-/
def gapInterval (angles : CyclicAngles n hn) (cut : Fin n) : Set ℝ :=
  Set.Ioo (gapLeft angles cut) (gapRight angles cut)

/--
@isnad1 id=eq.2h3v.s5.2b9a9ccebf26 from=translated src=- shape=7f1d2889 vocab=bfeba1fe
-/
lemma gapLeft_of_zero (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : cut.val = 0) : gapLeft angles cut = angles.angle (lastNodeIndex hn) := by
  simp only [gapLeft, hcut, ↓reduceIte]

/--
@isnad1 id=eq.2h3v.s5.4355550facb1 from=translated src=- shape=f13411b3 vocab=b3d3801c
-/
lemma gapRight_of_zero (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : cut.val = 0) : gapRight angles cut = 2 * Real.pi := by
  simp only [gapRight, hcut, ↓reduceIte]

/--
@isnad1 id=eq.2h3v.s5.e57a22a10324 from=translated src=- shape=617ebedc vocab=d1b0c211
-/
lemma gapInterpolant_of_zero (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : cut.val = 0) :
    gapInterpolant angles cut = sineInterpolant angles.angle wrapCoefficient := by
  simp only [gapInterpolant, cyclicGapCoefficient, hcut, ↓reduceIte]

/--
@isnad1 id=eq.2h3v.s5.6984192f6222 from=translated src=- shape=dd8e8668 vocab=d0fbef10
-/
lemma gapInterval_of_zero (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : cut.val = 0) : gapInterval angles cut = wrapGap angles := by
  rw [gapInterval, gapLeft_of_zero angles cut hcut, gapRight_of_zero angles cut hcut]
  rfl

/--
@isnad1 id=eq.2h3v.s5.0f391f4b89c5 from=translated src=- shape=dc4df89c vocab=7a4c4648
-/
lemma gapLeft_of_pos (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) : gapLeft angles cut = angles.angle (gapPredecessor cut) := by
  simp only [gapLeft, Nat.ne_of_gt hcut, ↓reduceIte]

/--
@isnad1 id=eq.2h3v.s5.7ef1eea237b9 from=translated src=- shape=05ecfe4a vocab=eab2b417
-/
lemma gapRight_of_pos (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) : gapRight angles cut = angles.angle cut := by
  simp only [gapRight, Nat.ne_of_gt hcut, ↓reduceIte]

/--
@isnad1 id=eq.2h3v.s5.97dff08f62ff from=translated src=- shape=b5e9a23d vocab=2702f5c1
-/
lemma gapInterpolant_of_pos (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) :
    gapInterpolant angles cut = sineInterpolant angles.angle (gapCoefficient cut) := by
  simp only [gapInterpolant, cyclicGapCoefficient, Nat.ne_of_gt hcut, ↓reduceIte]

/--
@isnad1 id=eq.2h3v.s5.acde9369b896 from=translated src=- shape=7705119d vocab=b0096ab4
-/
lemma gapInterval_of_pos (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) : gapInterval angles cut = ordinaryGap angles cut hcut := by
  rw [gapInterval, gapLeft_of_pos angles cut hcut, gapRight_of_pos angles cut hcut]
  rfl

/--
@isnad1 id=eq.1h2v.s5.22fb43bf48fe from=translated src=- shape=7c4a0dff vocab=db757442
-/
@[simp] lemma gapLeft_zero (angles : CyclicAngles n hn) :
    gapLeft angles ⟨0, hn⟩ = angles.angle (lastNodeIndex hn) :=
  gapLeft_of_zero angles _ rfl

/--
@isnad1 id=eq.1h2v.s5.2172fd820a25 from=translated src=- shape=051bfa96 vocab=0562c4d0
-/
@[simp] lemma gapRight_zero (angles : CyclicAngles n hn) :
    gapRight angles ⟨0, hn⟩ = 2 * Real.pi :=
  gapRight_of_zero angles _ rfl

/--
@isnad1 id=eq.1h2v.s5.b0170b86f1db from=translated src=- shape=5a33f388 vocab=631c635e
-/
@[simp] lemma gapInterpolant_zero (angles : CyclicAngles n hn) :
    gapInterpolant angles ⟨0, hn⟩ = sineInterpolant angles.angle wrapCoefficient :=
  gapInterpolant_of_zero angles _ rfl

/--
@isnad1 id=eq.1h2v.s5.c63aa383b122 from=translated src=- shape=492c6460 vocab=801110a7
-/
@[simp] lemma gapInterval_zero (angles : CyclicAngles n hn) :
    gapInterval angles ⟨0, hn⟩ = wrapGap angles :=
  gapInterval_of_zero angles _ rfl

/--
@isnad1 id=lt.1h3v.s5.de1c62eebd6c from=translated src=- shape=59f8a666 vocab=7bd4c3b3
-/
lemma gapLeft_lt_gapRight (angles : CyclicAngles n hn) (cut : Fin n) :
    gapLeft angles cut < gapRight angles cut := by
  by_cases hzero : cut.val = 0
  · rw [gapLeft_of_zero angles cut hzero, gapRight_of_zero angles cut hzero]
    exact angles.lt_two_pi _
  · have hpos : 0 < cut.val := Nat.pos_of_ne_zero hzero
    rw [gapLeft_of_pos angles cut hpos, gapRight_of_pos angles cut hpos]
    apply angles.strictMono
    change cut.val - 1 < cut.val
    omega

/--
@isnad1 id=le.1h3v.s5.a7b26d34d5b9 from=translated src=- shape=80fcade7 vocab=5de01fa3
-/
lemma gapLeft_nonneg (angles : CyclicAngles n hn) (cut : Fin n) :
    0 ≤ gapLeft angles cut := by
  unfold gapLeft
  split_ifs <;> exact angles.nonneg _

/--
@isnad1 id=le.1h3v.s5.4c961cbd1d97 from=translated src=- shape=42735ef0 vocab=7889406e
-/
lemma gapRight_le_two_pi (angles : CyclicAngles n hn) (cut : Fin n) :
    gapRight angles cut ≤ 2 * Real.pi := by
  unfold gapRight
  split_ifs
  · exact le_rfl
  · exact (angles.lt_two_pi _).le

/--
@isnad1 id=mem.2h4v.s6.9c07839c1868 from=translated src=- shape=4c85bbcc vocab=865230f7
-/
lemma gapInterval_mem_Ioo (angles : CyclicAngles n hn) (cut : Fin n)
    {t : ℝ} (ht : t ∈ gapInterval angles cut) : t ∈ Set.Ioo 0 (2 * Real.pi) :=
  ⟨(gapLeft_nonneg angles cut).trans_lt ht.1,
    ht.2.trans_le (gapRight_le_two_pi angles cut)⟩

/-- On every open cyclic gap the actual signed interpolant is the complex objective.
@isnad1 id=eq.2h4v.s7.c749946cbfe7 from=translated src=- shape=4eeafc7e vocab=5b11c939
-/
theorem lebesgueFunction_on_gapInterval (angles : CyclicAngles n hn) (cut : Fin n)
    {t : ℝ} (ht : t ∈ gapInterval angles cut) :
    lebesgueFunction (phaseNodes angles.angle) (Circle.exp t : ℂ) =
      gapInterpolant angles cut t := by
  by_cases hzero : cut.val = 0
  · rw [gapInterval_of_zero angles cut hzero] at ht
    rw [gapInterpolant_of_zero angles cut hzero]
    exact lebesgueFunction_on_wrapGap angles ht
  · have hpos : 0 < cut.val := Nat.pos_of_ne_zero hzero
    rw [gapInterval_of_pos angles cut hpos] at ht
    rw [gapInterpolant_of_pos angles cut hpos]
    exact lebesgueFunction_on_gap angles cut hpos ht

/-- A strict, nondegenerate peak above one exists on every cyclic gap for `n ≥ 2`.
@isnad1 id=ex.2h3v.s7.fa976672127e from=translated src=- shape=355d7a4c vocab=76813123
-/
theorem exists_gapInterpolant_strict_peak (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) :
    ∃ peak : ℝ,
      StrictIntervalPeak (gapInterpolant angles cut)
        (gapLeft angles cut) (gapRight angles cut) peak ∧
      1 < gapInterpolant angles cut peak ∧
      deriv (deriv (gapInterpolant angles cut)) peak < 0 := by
  by_cases hzero : cut.val = 0
  · rw [gapInterpolant_of_zero angles cut hzero,
      gapLeft_of_zero angles cut hzero, gapRight_of_zero angles cut hzero]
    exact exists_wrapInterpolant_strict_peak angles hsize
  · have hpos : 0 < cut.val := Nat.pos_of_ne_zero hzero
    rw [gapInterpolant_of_pos angles cut hpos,
      gapLeft_of_pos angles cut hpos, gapRight_of_pos angles cut hpos]
    exact exists_ordinaryGap_strict_peak angles hsize cut hpos

private lemma strictIntervalPeak_unique {f : ℝ → ℝ} {a b p q : ℝ}
    (hp : StrictIntervalPeak f a b p) (hq : StrictIntervalPeak f a b q) : q = p := by
  apply (hp.eq_iff q (Set.Ioo_subset_Icc_self hq.mem_Ioo)).mp
  exact le_antisymm (hp.isMaxOn (Set.Ioo_subset_Icc_self hq.mem_Ioo))
    (hq.isMaxOn (Set.Ioo_subset_Icc_self hp.mem_Ioo))

/-- The peak exists uniquely with all three proved properties.
@isnad1 id=existsun.2h3v.s7.768663352e3c from=translated src=- shape=355d7a4c vocab=16de30b8
-/
theorem existsUnique_gapInterpolant_strict_peak (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) :
    ∃! peak : ℝ,
      StrictIntervalPeak (gapInterpolant angles cut)
        (gapLeft angles cut) (gapRight angles cut) peak ∧
      1 < gapInterpolant angles cut peak ∧
      deriv (deriv (gapInterpolant angles cut)) peak < 0 := by
  obtain ⟨peak, hp⟩ := exists_gapInterpolant_strict_peak angles hsize cut
  exact ⟨peak, hp, fun _ hq => strictIntervalPeak_unique hp.1 hq.1⟩

/-- Choose the proved unique peak, rather than assuming a maximizer property.-/
def gapPeak (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (cut : Fin n) : ℝ :=
  Classical.choose (exists_gapInterpolant_strict_peak angles hsize cut)

/-- The actual signed interpolant value at the peak.-/
def gapHeight (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (cut : Fin n) : ℝ :=
  gapInterpolant angles cut (gapPeak angles hsize cut)

/--
@isnad1 id=strictin.2h3v.s5.67beb03f4d84 from=translated src=- shape=ebff3433 vocab=1d465508
-/
theorem gapPeak_strictIntervalPeak (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) :
    StrictIntervalPeak (gapInterpolant angles cut)
      (gapLeft angles cut) (gapRight angles cut) (gapPeak angles hsize cut) :=
  (Classical.choose_spec (exists_gapInterpolant_strict_peak angles hsize cut)).1

/--
@isnad1 id=mem.2h3v.s5.f0f321c326da from=translated src=- shape=8147dcb7 vocab=a72a56e9
-/
theorem gapPeak_mem_Ioo (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (cut : Fin n) :
    gapPeak angles hsize cut ∈ Set.Ioo (gapLeft angles cut) (gapRight angles cut) :=
  (gapPeak_strictIntervalPeak angles hsize cut).mem_Ioo

/--
@isnad1 id=mem.2h3v.s5.43313518cb71 from=translated src=- shape=baab9146 vocab=eb131796
-/
theorem gapPeak_mem_gapInterval (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) : gapPeak angles hsize cut ∈ gapInterval angles cut :=
  gapPeak_mem_Ioo angles hsize cut

/--
@isnad1 id=mem.2h3v.s6.238e433f06a8 from=translated src=- shape=aaf8030a vocab=0bbb8c7b
-/
theorem gapPeak_mem_turn (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (cut : Fin n) :
    gapPeak angles hsize cut ∈ Set.Ioo 0 (2 * Real.pi) :=
  gapInterval_mem_Ioo angles cut (gapPeak_mem_gapInterval angles hsize cut)

/-- Every strict interval peak of this actual interpolant is the chosen peak.
@isnad1 id=eq.3h4v.s5.bb5bef00e0c4 from=translated src=- shape=9c3fada6 vocab=359b7b90
-/
theorem gapPeak_unique (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (cut : Fin n) {peak : ℝ}
    (hpeak : StrictIntervalPeak (gapInterpolant angles cut)
      (gapLeft angles cut) (gapRight angles cut) peak) : peak = gapPeak angles hsize cut :=
  strictIntervalPeak_unique (gapPeak_strictIntervalPeak angles hsize cut) hpeak

/--
@isnad1 id=lt.2h3v.s5.ee8e864be297 from=translated src=- shape=90be3932 vocab=aca5e2d7
-/
theorem one_lt_gapHeight (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (cut : Fin n) :
    1 < gapHeight angles hsize cut :=
  (Classical.choose_spec (exists_gapInterpolant_strict_peak angles hsize cut)).2.1

/--
@isnad1 id=le.3h4v.s6.655f34044a44 from=translated src=- shape=a21f0a33 vocab=4706cb1f
-/
theorem gapInterpolant_le_gapHeight (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) {t : ℝ}
    (ht : t ∈ Set.Icc (gapLeft angles cut) (gapRight angles cut)) :
    gapInterpolant angles cut t ≤ gapHeight angles hsize cut :=
  (gapPeak_strictIntervalPeak angles hsize cut).isMaxOn ht

/--
@isnad1 id=lt.2h3v.s6.3212ac70af6a from=translated src=- shape=defc2937 vocab=08893dca
-/
theorem gapPeak_second_deriv_neg (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) :
    deriv (deriv (gapInterpolant angles cut)) (gapPeak angles hsize cut) < 0 :=
  (Classical.choose_spec (exists_gapInterpolant_strict_peak angles hsize cut)).2.2

/-- The peak height is a value of the literal complex Lebesgue function.
@isnad1 id=eq.2h3v.s7.0dc99f6fd235 from=translated src=- shape=3e165bf6 vocab=3fbaa542
-/
theorem gapHeight_eq_lebesgueFunction (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) :
    gapHeight angles hsize cut = lebesgueFunction (phaseNodes angles.angle)
      (Circle.exp (gapPeak angles hsize cut) : ℂ) :=
  (lebesgueFunction_on_gapInterval angles cut
    (gapPeak_mem_gapInterval angles hsize cut)).symm

/-- The genuine distinct unit-circle node family corresponding to the angular data.-/
def CyclicAngles.toNodeFamily (angles : CyclicAngles n hn) : NodeFamily n where
  point i := Circle.exp (angles.angle i)
  injective := by
    intro i j hij
    exact angles.phaseNodes_injective (congrArg ((↑) : Circle → ℂ) hij)

/--
@isnad1 id=eq.1h2v.s5.481c37ec3b38 from=translated src=- shape=0f656df8 vocab=1eba027f
-/
@[simp] theorem CyclicAngles.toNodeFamily_coordinates (angles : CyclicAngles n hn) :
    angles.toNodeFamily.coordinates = phaseNodes angles.angle := rfl

/-- The original full-circle objective for the genuine angular node family.-/
def angularAmplification (angles : CyclicAngles n hn) : ℝ :=
  amplification angles.toNodeFamily

/-- Each actual gap peak is bounded by the full-circle amplification.
@isnad1 id=le.2h3v.s5.4dac964c46c0 from=translated src=- shape=43ac1801 vocab=a21b1c57
-/
theorem gapHeight_le_amplification (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) :
    gapHeight angles hsize cut ≤ amplification angles.toNodeFamily := by
  rw [gapHeight_eq_lebesgueFunction]
  simpa only [CyclicAngles.toNodeFamily_coordinates] using
    le_amplification angles.toNodeFamily (Circle.exp (gapPeak angles hsize cut))

/--
@isnad1 id=le.2h3v.s5.f283425a7a4e from=translated src=- shape=f66e8d61 vocab=0bf3923c
-/
theorem gapHeight_le_angularAmplification (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) :
    gapHeight angles hsize cut ≤ angularAmplification angles :=
  gapHeight_le_amplification angles hsize cut

end

end UnitCircleInterpolation
