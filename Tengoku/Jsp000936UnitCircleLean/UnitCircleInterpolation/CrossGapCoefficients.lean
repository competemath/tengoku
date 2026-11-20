/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.GapSigns

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coefficients of differences and sums across two gap cuts

These results use `gapCoefficient` literally, including its translated-wrap
interpretation at cut zero. They do not use `cyclicGapCoefficient`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

private lemma gapIndexSign_consecutive_cuts {i j k : Fin n}
    (hij : i.val + 1 = j.val) (hki : k ≠ i) :
    gapIndexSign j k = gapIndexSign i k := by
  have hkval : k.val ≠ i.val := fun h => hki (Fin.ext h)
  have hside : k < j ↔ k < i := by
    change k.val < j.val ↔ k.val < i.val
    omega
  simp only [gapIndexSign, hside]

/-- Moving the cut one step flips every coefficient except at the crossed node.
@isnad1 id=eq.1h4v.s5.90a49ebdb829 from=translated src=- shape=a70494a4 vocab=cc68cc3c
-/
theorem gapCoefficient_consecutive_cuts (i j k : Fin n)
    (hij : i.val + 1 = j.val) :
    gapCoefficient j k = if k = i then gapCoefficient i k else -gapCoefficient i k := by
  by_cases hki : k = i
  · rw [ite_eq_left hki]
    unfold gapCoefficient
    apply Finset.prod_congr rfl
    intro l hl
    rw [gapIndexSign_consecutive_cuts hij]
    simpa [hki] using (Finset.mem_erase.mp hl).1
  · rw [ite_eq_right hki]
    let P : ℝ := ∏ l ∈ (Finset.univ.erase k).erase i,
      gapIndexSign i l * nodeIndexSign k l
    have hprod : (∏ l ∈ (Finset.univ.erase k).erase i,
        gapIndexSign j l * nodeIndexSign k l) = P := by
      apply Finset.prod_congr rfl
      intro l hl
      rw [gapIndexSign_consecutive_cuts hij (Finset.mem_erase.mp hl).1]
    have hmem : i ∈ (Finset.univ.erase k : Finset (Fin n)) :=
      Finset.mem_erase.mpr ⟨Ne.symm hki, Finset.mem_univ i⟩
    have hi : gapCoefficient i k = -nodeIndexSign k i * P := by
      unfold gapCoefficient
      rw [← Finset.mul_prod_erase (Finset.univ.erase k)
        (fun l => gapIndexSign i l * nodeIndexSign k l) hmem]
      simp only [gapIndexSign, lt_self_iff_false, ite_false]
      change (-1 * nodeIndexSign k i) * P = -nodeIndexSign k i * P
      ring
    have hj : gapCoefficient j k = nodeIndexSign k i * P := by
      unfold gapCoefficient
      rw [← Finset.mul_prod_erase (Finset.univ.erase k)
        (fun l => gapIndexSign j l * nodeIndexSign k l) hmem, hprod]
      have hlt : i < j := by change i.val < j.val; omega
      simp [gapIndexSign, hlt]
    rw [hi, hj]
    ring

/-- Including the sign of the omitted factor makes cut transport uniformly alternating.
@isnad1 id=eq.1h4v.s6.3fdc8098f130 from=translated src=- shape=eab2287e vocab=e3d7201a
-/
theorem gapCoefficient_signed_consecutive_cuts (i j k : Fin n)
    (hij : i.val + 1 = j.val) :
    gapIndexSign j k * gapCoefficient j k =
      -(gapIndexSign i k * gapCoefficient i k) := by
  rw [gapCoefficient_consecutive_cuts i j k hij]
  by_cases hki : k = i
  · rw [ite_eq_left hki]
    have hlt : i < j := by change i.val < j.val; omega
    simp [hki, gapIndexSign, hlt]
  · rw [ite_eq_right hki, gapIndexSign_consecutive_cuts hij hki]
    ring

/-- The phase associated with the number of cut steps from `i` to `j`.-/
def crossGapPhase (i j : Fin n) : ℝ := (-1 : ℝ) ^ (j.val - i.val)

/--
@isnad1 id=eq.0h3v.s4.6ba7f9c1a5dd from=translated src=- shape=279d3914 vocab=d033b498
-/
lemma crossGapPhase_mul_self (i j : Fin n) :
    crossGapPhase i j * crossGapPhase i j = 1 := by
  unfold crossGapPhase
  rw [← mul_pow]
  norm_num

/--
@isnad1 id=ne.0h3v.s4.a48ddfa323ea from=translated src=- shape=4a298764 vocab=9ca060cb
-/
lemma crossGapPhase_ne_zero (i j : Fin n) : crossGapPhase i j ≠ 0 := by
  unfold crossGapPhase
  exact pow_ne_zero _ (by norm_num)

/-- Exact transport of the signed coefficient between arbitrary ordered cuts.
@isnad1 id=eq.1h4v.s5.215198a59cba from=translated src=- shape=ac799594 vocab=2db5c227
-/
theorem gapCoefficient_signed_between_cuts (i j k : Fin n) (hij : i ≤ j) :
    gapIndexSign j k * gapCoefficient j k =
      crossGapPhase i j * (gapIndexSign i k * gapCoefficient i k) := by
  have haux : ∀ d : ℕ, ∀ j : Fin n, j.val = i.val + d →
      gapIndexSign j k * gapCoefficient j k =
        (-1 : ℝ) ^ d * (gapIndexSign i k * gapCoefficient i k) := by
    intro d
    induction d with
    | zero =>
      intro j hj
      have hji : j = i := Fin.ext (by omega)
      simp [hji]
    | succ d ih =>
      intro j hj
      let l : Fin n := ⟨j.val - 1, (Nat.sub_le _ _).trans_lt j.isLt⟩
      have hl : l.val = i.val + d := by dsimp [l]; omega
      have hlj : l.val + 1 = j.val := by dsimp [l]; omega
      rw [gapCoefficient_signed_consecutive_cuts l j k hlj, ih l hl, pow_succ]
      ring
  simpa only [crossGapPhase] using haux (j.val - i.val) j (by
    have hval : i.val ≤ j.val := hij
    omega)

/-- Outside the half-open interval of cuts, both coefficients differ by the phase alone.
@isnad1 id=eq.2h4v.s5.1604b19e7b22 from=translated src=- shape=bd357b74 vocab=5f4aa4ca
-/
theorem gapCoefficient_between_cuts_outside (i j k : Fin n) (hij : i ≤ j)
    (hk : k < i ∨ j ≤ k) :
    gapCoefficient j k = crossGapPhase i j * gapCoefficient i k := by
  have h := gapCoefficient_signed_between_cuts i j k hij
  rcases hk with hki | hjk
  · have hkj : k < j := hki.trans_le hij
    simpa [gapIndexSign, hki, hkj] using h
  · have hki : ¬k < i := not_lt.mpr (hij.trans hjk)
    have hkj : ¬k < j := not_lt.mpr hjk
    simp only [gapIndexSign, ite_eq_right hki, ite_eq_right hkj, neg_one_mul, mul_neg] at h
    exact neg_injective h

/-- Between the two cuts, omitting a crossed factor supplies one additional minus sign.
@isnad1 id=eq.3h4v.s5.62b8f0fb77cb from=translated src=- shape=2a44f854 vocab=868904bb
-/
theorem gapCoefficient_between_cuts_inside (i j k : Fin n) (hij : i ≤ j)
    (hik : i ≤ k) (hkj : k < j) :
    gapCoefficient j k = -crossGapPhase i j * gapCoefficient i k := by
  have h := gapCoefficient_signed_between_cuts i j k hij
  have hki : ¬k < i := not_lt.mpr hik
  simpa [gapIndexSign, hki, hkj, neg_mul, mul_neg] using h

/-- A single piecewise form of the literal two-cut coefficient identity.
@isnad1 id=eq.1h4v.s6.459121373062 from=translated src=- shape=0d172238 vocab=28f4777e
-/
theorem gapCoefficient_between_cuts (i j k : Fin n) (hij : i ≤ j) :
    gapCoefficient j k =
      if i ≤ k ∧ k < j then -crossGapPhase i j * gapCoefficient i k
      else crossGapPhase i j * gapCoefficient i k := by
  by_cases hk : i ≤ k ∧ k < j
  · rw [ite_eq_left hk]
    exact gapCoefficient_between_cuts_inside i j k hij hk.1 hk.2
  · rw [ite_eq_right hk]
    apply gapCoefficient_between_cuts_outside i j k hij
    by_cases hki : k < i
    · exact Or.inl hki
    · exact Or.inr (le_of_not_gt (fun hkj => hk ⟨le_of_not_gt hki, hkj⟩))

/-- Literal coefficients of the difference of the two phase-aligned interpolants.-/
def crossDifferenceCoefficient (i j k : Fin n) : ℝ :=
  gapCoefficient i k - crossGapPhase i j * gapCoefficient j k

/-- Literal coefficients of the sum of the two phase-aligned interpolants.-/
def crossSumCoefficient (i j k : Fin n) : ℝ :=
  gapCoefficient i k + crossGapPhase i j * gapCoefficient j k

/--
@isnad1 id=eq.3h4v.s5.c6c48a77923c from=translated src=- shape=cdb21ee9 vocab=4aafb7f9
-/
theorem crossDifferenceCoefficient_inside (i j k : Fin n) (hij : i ≤ j)
    (hik : i ≤ k) (hkj : k < j) :
    crossDifferenceCoefficient i j k = 2 * gapCoefficient i k := by
  unfold crossDifferenceCoefficient
  rw [gapCoefficient_between_cuts_inside i j k hij hik hkj]
  calc
    gapCoefficient i k - crossGapPhase i j *
        (-crossGapPhase i j * gapCoefficient i k) =
      gapCoefficient i k +
        (crossGapPhase i j * crossGapPhase i j) * gapCoefficient i k := by ring
    _ = 2 * gapCoefficient i k := by rw [crossGapPhase_mul_self]; ring

/--
@isnad1 id=eq.2h4v.s5.f3dc72633f87 from=translated src=- shape=c94deab0 vocab=06ba190a
-/
theorem crossDifferenceCoefficient_outside (i j k : Fin n) (hij : i ≤ j)
    (hk : k < i ∨ j ≤ k) : crossDifferenceCoefficient i j k = 0 := by
  unfold crossDifferenceCoefficient
  rw [gapCoefficient_between_cuts_outside i j k hij hk, ← mul_assoc,
    crossGapPhase_mul_self, one_mul, sub_self]

/--
@isnad1 id=eq.3h4v.s5.938caa612043 from=translated src=- shape=f454f3bc vocab=69609a8d
-/
theorem crossSumCoefficient_inside (i j k : Fin n) (hij : i ≤ j)
    (hik : i ≤ k) (hkj : k < j) : crossSumCoefficient i j k = 0 := by
  unfold crossSumCoefficient
  rw [gapCoefficient_between_cuts_inside i j k hij hik hkj]
  calc
    gapCoefficient i k + crossGapPhase i j *
        (-crossGapPhase i j * gapCoefficient i k) =
      gapCoefficient i k -
        (crossGapPhase i j * crossGapPhase i j) * gapCoefficient i k := by ring
    _ = 0 := by rw [crossGapPhase_mul_self, one_mul, sub_self]

/--
@isnad1 id=eq.2h4v.s5.e83722646a4a from=translated src=- shape=416db1f2 vocab=f726f400
-/
theorem crossSumCoefficient_outside (i j k : Fin n) (hij : i ≤ j)
    (hk : k < i ∨ j ≤ k) :
    crossSumCoefficient i j k = 2 * gapCoefficient i k := by
  unfold crossSumCoefficient
  rw [gapCoefficient_between_cuts_outside i j k hij hk, ← mul_assoc,
    crossGapPhase_mul_self, one_mul]
  ring

/-- Every original gap coefficient is nonzero, with no condition on its cut.
@isnad1 id=ne.0h3v.s4.f6635acd98c7 from=translated src=- shape=4a298764 vocab=55fc1fe7
-/
lemma gapCoefficient_ne_zero (cut k : Fin n) : gapCoefficient cut k ≠ 0 := by
  intro hzero
  have h := abs_gapCoefficient cut k
  rw [hzero, abs_zero] at h
  norm_num at h

/--
@isnad1 id=eq.1h4v.s6.81ca721c320b from=translated src=- shape=cd455e55 vocab=e8265228
-/
theorem crossDifferenceCoefficient_eq (i j k : Fin n) (hij : i ≤ j) :
    crossDifferenceCoefficient i j k =
      if i ≤ k ∧ k < j then 2 * gapCoefficient i k else 0 := by
  by_cases hk : i ≤ k ∧ k < j
  · rw [ite_eq_left hk]
    exact crossDifferenceCoefficient_inside i j k hij hk.1 hk.2
  · rw [ite_eq_right hk]
    apply crossDifferenceCoefficient_outside i j k hij
    by_cases hki : k < i
    · exact Or.inl hki
    · exact Or.inr (le_of_not_gt (fun hkj => hk ⟨le_of_not_gt hki, hkj⟩))

/--
@isnad1 id=eq.1h4v.s6.af8861909037 from=translated src=- shape=14c0f105 vocab=b1e55262
-/
theorem crossSumCoefficient_eq (i j k : Fin n) (hij : i ≤ j) :
    crossSumCoefficient i j k =
      if i ≤ k ∧ k < j then 0 else 2 * gapCoefficient i k := by
  by_cases hk : i ≤ k ∧ k < j
  · rw [ite_eq_left hk]
    exact crossSumCoefficient_inside i j k hij hk.1 hk.2
  · rw [ite_eq_right hk]
    apply crossSumCoefficient_outside i j k hij
    by_cases hki : k < i
    · exact Or.inl hki
    · exact Or.inr (le_of_not_gt (fun hkj => hk ⟨le_of_not_gt hki, hkj⟩))

/-- The difference is supported exactly on the half-open block between the cuts.
@isnad1 id=iff.1h4v.s5.aa63bd7d0505 from=translated src=- shape=529274f2 vocab=06ba190a
-/
theorem crossDifferenceCoefficient_ne_zero_iff (i j k : Fin n) (hij : i ≤ j) :
    crossDifferenceCoefficient i j k ≠ 0 ↔ i ≤ k ∧ k < j := by
  rw [crossDifferenceCoefficient_eq i j k hij]
  by_cases hk : i ≤ k ∧ k < j
  · simp [hk, gapCoefficient_ne_zero]
  · simp [hk]

/-- The sum is supported exactly on the complementary two nodal blocks.
@isnad1 id=iff.1h4v.s5.9ffa650eb7ce from=translated src=- shape=82fd4a65 vocab=69609a8d
-/
theorem crossSumCoefficient_ne_zero_iff (i j k : Fin n) (hij : i ≤ j) :
    crossSumCoefficient i j k ≠ 0 ↔ k < i ∨ j ≤ k := by
  rw [crossSumCoefficient_eq i j k hij]
  by_cases hk : i ≤ k ∧ k < j
  · have houtside : ¬(k < i ∨ j ≤ k) := by
      change ¬(k.val < i.val ∨ j.val ≤ k.val)
      have hik : i.val ≤ k.val := hk.1
      have hkj : k.val < j.val := hk.2
      omega
    simp [hk, houtside]
  · have houtside : k < i ∨ j ≤ k := by
      by_cases hki : k < i
      · exact Or.inl hki
      · exact Or.inr (le_of_not_gt (fun hkj => hk ⟨le_of_not_gt hki, hkj⟩))
    simp [hk, houtside, gapCoefficient_ne_zero]

/--
@isnad1 id=eq.3h4v.s5.7c5e6ceeea50 from=translated src=- shape=39014ec1 vocab=3e034dab
-/
theorem abs_crossDifferenceCoefficient_inside (i j k : Fin n) (hij : i ≤ j)
    (hik : i ≤ k) (hkj : k < j) : |crossDifferenceCoefficient i j k| = 2 := by
  rw [crossDifferenceCoefficient_inside i j k hij hik hkj, abs_mul,
    abs_gapCoefficient, mul_one]
  norm_num

/--
@isnad1 id=eq.2h4v.s5.e2e92fc19a92 from=translated src=- shape=d5c525a8 vocab=febe7ec8
-/
theorem abs_crossSumCoefficient_outside (i j k : Fin n) (hij : i ≤ j)
    (hk : k < i ∨ j ≤ k) : |crossSumCoefficient i j k| = 2 := by
  rw [crossSumCoefficient_outside i j k hij hk, abs_mul,
    abs_gapCoefficient, mul_one]
  norm_num

/-- The interpolant here is the literal difference, without replacing its cardinal sum.
@isnad1 id=eq.0h5v.s5.c5a0ffea5323 from=translated src=- shape=c4bffdbc vocab=7b3509f7
-/
theorem crossDifferenceInterpolant_identity (θ : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    sineInterpolant θ (crossDifferenceCoefficient i j) t =
      sineInterpolant θ (gapCoefficient i) t -
        crossGapPhase i j * sineInterpolant θ (gapCoefficient j) t := by
  unfold sineInterpolant crossDifferenceCoefficient
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The interpolant here is the literal sum of the phase-aligned gap interpolants.
@isnad1 id=eq.0h5v.s5.0df4fb302400 from=translated src=- shape=c4bffdbc vocab=3bac853b
-/
theorem crossSumInterpolant_identity (θ : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    sineInterpolant θ (crossSumCoefficient i j) t =
      sineInterpolant θ (gapCoefficient i) t +
        crossGapPhase i j * sineInterpolant θ (gapCoefficient j) t := by
  unfold sineInterpolant crossSumCoefficient
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/--
@isnad1 id=eq.1h5v.s5.f2212ed3e983 from=translated src=- shape=1d0c7423 vocab=985bb2fa
-/
lemma crossDifferenceInterpolant_at_node (angles : CyclicAngles n hn) (i j k : Fin n) :
    sineInterpolant angles.angle (crossDifferenceCoefficient i j) (angles.angle k) =
      crossDifferenceCoefficient i j k :=
  sineInterpolant_at_node angles.angle angles.phaseNodes_injective
    (crossDifferenceCoefficient i j) k

/--
@isnad1 id=eq.1h5v.s5.c116a60e514b from=translated src=- shape=1d0c7423 vocab=6917d6f5
-/
lemma crossSumInterpolant_at_node (angles : CyclicAngles n hn) (i j k : Fin n) :
    sineInterpolant angles.angle (crossSumCoefficient i j) (angles.angle k) =
      crossSumCoefficient i j k :=
  sineInterpolant_at_node angles.angle angles.phaseNodes_injective
    (crossSumCoefficient i j) k

/--
@isnad1 id=eq.4h5v.s6.c4c8f83817b6 from=translated src=- shape=8e7f344d vocab=f58eb317
-/
theorem crossDifferenceInterpolant_at_node_inside (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i ≤ j) (hik : i ≤ k) (hkj : k < j) :
    sineInterpolant angles.angle (crossDifferenceCoefficient i j) (angles.angle k) =
      2 * gapCoefficient i k := by
  rw [crossDifferenceInterpolant_at_node,
    crossDifferenceCoefficient_inside i j k hij hik hkj]

/--
@isnad1 id=eq.3h5v.s6.1c0c554b4143 from=translated src=- shape=bff6957b vocab=4b7b94a4
-/
theorem crossDifferenceInterpolant_at_node_outside (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i ≤ j) (hk : k < i ∨ j ≤ k) :
    sineInterpolant angles.angle (crossDifferenceCoefficient i j) (angles.angle k) = 0 := by
  rw [crossDifferenceInterpolant_at_node,
    crossDifferenceCoefficient_outside i j k hij hk]

/--
@isnad1 id=eq.4h5v.s6.afea3a78bdf2 from=translated src=- shape=fe799592 vocab=913940ee
-/
theorem crossSumInterpolant_at_node_inside (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i ≤ j) (hik : i ≤ k) (hkj : k < j) :
    sineInterpolant angles.angle (crossSumCoefficient i j) (angles.angle k) = 0 := by
  rw [crossSumInterpolant_at_node, crossSumCoefficient_inside i j k hij hik hkj]

/--
@isnad1 id=eq.3h5v.s6.30395a0e13be from=translated src=- shape=5c697695 vocab=2ba0fde9
-/
theorem crossSumInterpolant_at_node_outside (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i ≤ j) (hk : k < i ∨ j ≤ k) :
    sineInterpolant angles.angle (crossSumCoefficient i j) (angles.angle k) =
      2 * gapCoefficient i k := by
  rw [crossSumInterpolant_at_node, crossSumCoefficient_outside i j k hij hk]

/--
@isnad1 id=iff.2h5v.s6.2936a71f4432 from=translated src=- shape=57e4525e vocab=4b7b94a4
-/
theorem crossDifferenceInterpolant_at_node_ne_zero_iff (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i ≤ j) :
    sineInterpolant angles.angle (crossDifferenceCoefficient i j) (angles.angle k) ≠ 0 ↔
      i ≤ k ∧ k < j := by
  rw [crossDifferenceInterpolant_at_node]
  exact crossDifferenceCoefficient_ne_zero_iff i j k hij

/--
@isnad1 id=iff.2h5v.s6.ed2bb3d82eba from=translated src=- shape=ef136d8e vocab=913940ee
-/
theorem crossSumInterpolant_at_node_ne_zero_iff (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i ≤ j) :
    sineInterpolant angles.angle (crossSumCoefficient i j) (angles.angle k) ≠ 0 ↔
      k < i ∨ j ≤ k := by
  rw [crossSumInterpolant_at_node]
  exact crossSumCoefficient_ne_zero_iff i j k hij

/-- Consecutive indices in the nonzero difference block have opposite coefficients.
@isnad1 id=eq.4h5v.s6.1fa0130ffd46 from=translated src=- shape=984c49e3 vocab=6742d060
-/
theorem crossDifferenceCoefficient_consecutive_flip (i j k l : Fin n)
    (hij : i ≤ j) (hkl : k.val + 1 = l.val) (hik : i ≤ k) (hlj : l < j) :
    crossDifferenceCoefficient i j l = -crossDifferenceCoefficient i j k := by
  have hkl_lt : k < l := by change k.val < l.val; omega
  have hil : i ≤ l := hik.trans hkl_lt.le
  have hkj : k < j := hkl_lt.trans hlj
  have hli : l ≠ i := ne_of_gt (hik.trans_lt hkl_lt)
  rw [crossDifferenceCoefficient_inside i j l hij hil hlj,
    crossDifferenceCoefficient_inside i j k hij hik hkj,
    gapCoefficient_consecutive_flip i k l hkl hli]
  ring

/-- On either complementary block, consecutive nonzero sum coefficients alternate.
@isnad1 id=eq.4h5v.s6.5afa9f06aa20 from=translated src=- shape=1da328c1 vocab=c5569414
-/
theorem crossSumCoefficient_consecutive_flip (i j k l : Fin n)
    (hij : i < j) (hkl : k.val + 1 = l.val)
    (hk : k < i ∨ j ≤ k) (hl : l < i ∨ j ≤ l) :
    crossSumCoefficient i j l = -crossSumCoefficient i j k := by
  have hli : l ≠ i := by
    intro hli
    rcases hl with hl | hl
    · exact (lt_irrefl i) (hli ▸ hl)
    · exact (not_le_of_gt hij) (hli ▸ hl)
  rw [crossSumCoefficient_outside i j l hij.le hl,
    crossSumCoefficient_outside i j k hij.le hk,
    gapCoefficient_consecutive_flip i k l hkl hli]
  ring

/--
@isnad1 id=eq.5h6v.s6.83757ee714a6 from=translated src=- shape=bc39d2fb vocab=6bde05cc
-/
theorem crossDifferenceInterpolant_consecutive_flip (angles : CyclicAngles n hn)
    (i j k l : Fin n) (hij : i ≤ j) (hkl : k.val + 1 = l.val)
    (hik : i ≤ k) (hlj : l < j) :
    sineInterpolant angles.angle (crossDifferenceCoefficient i j) (angles.angle l) =
      -sineInterpolant angles.angle (crossDifferenceCoefficient i j) (angles.angle k) := by
  rw [crossDifferenceInterpolant_at_node, crossDifferenceInterpolant_at_node]
  exact crossDifferenceCoefficient_consecutive_flip i j k l hij hkl hik hlj

/--
@isnad1 id=eq.5h6v.s6.8cd8d66f75d6 from=translated src=- shape=7def3a55 vocab=94a6e7a2
-/
theorem crossSumInterpolant_consecutive_flip (angles : CyclicAngles n hn)
    (i j k l : Fin n) (hij : i < j) (hkl : k.val + 1 = l.val)
    (hk : k < i ∨ j ≤ k) (hl : l < i ∨ j ≤ l) :
    sineInterpolant angles.angle (crossSumCoefficient i j) (angles.angle l) =
      -sineInterpolant angles.angle (crossSumCoefficient i j) (angles.angle k) := by
  rw [crossSumInterpolant_at_node, crossSumInterpolant_at_node]
  exact crossSumCoefficient_consecutive_flip i j k l hij hkl hk hl

end

end UnitCircleInterpolation
