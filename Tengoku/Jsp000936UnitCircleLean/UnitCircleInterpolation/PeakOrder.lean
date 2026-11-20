/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.GapWronskian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Peaks in their physical order around the circle

The gap cuts are ordered as `1, ..., n - 1, 0`. The final entry is the actual
positive wrap-gap interpolant. Every peak lies strictly after its left node
and before the next node, or before `2π` in the final gap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

/-- The gap after a physical nodal index, with the final index sent to cut zero.-/
def physicalGapCut (hn : 0 < n) (k : Fin n) : Fin n :=
  if h : k.val + 1 < n then ⟨k.val + 1, h⟩ else ⟨0, hn⟩

/--
@isnad1 id=eq.2h2v.s5.cdd02ab56c72 from=translated src=- shape=6975c69a vocab=f865914f
-/
lemma physicalGapCut_of_next_lt (hn : 0 < n) (k : Fin n) (h : k.val + 1 < n) :
    physicalGapCut hn k = ⟨k.val + 1, h⟩ := by
  simp only [physicalGapCut, dite_eq_left h]

/--
@isnad1 id=eq.2h2v.s5.15fecc146806 from=translated src=- shape=0ffa06e6 vocab=f865914f
-/
lemma physicalGapCut_of_last (hn : 0 < n) (k : Fin n) (h : k.val + 1 = n) :
    physicalGapCut hn k = ⟨0, hn⟩ := by
  simp [physicalGapCut, h]

/--
@isnad1 id=injectiv.1h1v.s4.1a902adf8ac2 from=translated src=- shape=63f8cf57 vocab=ecdb810a
-/
lemma physicalGapCut_injective (hn : 0 < n) : Function.Injective (physicalGapCut hn) := by
  intro k l heq
  apply Fin.ext
  have hkn := k.isLt
  have hln := l.isLt
  by_cases hk : k.val + 1 < n
  · by_cases hl : l.val + 1 < n
    · rw [physicalGapCut_of_next_lt hn k hk, physicalGapCut_of_next_lt hn l hl] at heq
      have hv : k.val + 1 = l.val + 1 := congrArg Fin.val heq
      omega
    · have hl' : l.val + 1 = n := by omega
      rw [physicalGapCut_of_next_lt hn k hk, physicalGapCut_of_last hn l hl'] at heq
      have hv : k.val + 1 = 0 := congrArg Fin.val heq
      omega
  · by_cases hl : l.val + 1 < n
    · have hk' : k.val + 1 = n := by omega
      rw [physicalGapCut_of_last hn k hk', physicalGapCut_of_next_lt hn l hl] at heq
      have hv : 0 = l.val + 1 := congrArg Fin.val heq
      omega
    · omega

/--
@isnad1 id=surjecti.1h1v.s4.d3f723dab799 from=translated src=- shape=63f8cf57 vocab=c74c5835
-/
lemma physicalGapCut_surjective (hn : 0 < n) : Function.Surjective (physicalGapCut hn) :=
  Finite.surjective_of_injective (physicalGapCut_injective hn)

def physicalGapEquiv (hn : 0 < n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (physicalGapCut hn)
    ⟨physicalGapCut_injective hn, physicalGapCut_surjective hn⟩

/--
@isnad1 id=eq.1h3v.s5.9d31a23ed4dc from=translated src=- shape=c4be26b5 vocab=27888399
-/
lemma gapLeft_physicalGapCut (angles : CyclicAngles n hn) (k : Fin n) :
    gapLeft angles (physicalGapCut hn k) = angles.angle k := by
  by_cases hk : k.val + 1 < n
  · have hpred : gapPredecessor (⟨k.val + 1, hk⟩ : Fin n) = k := by
      apply Fin.ext
      simp [gapPredecessor]
    rw [physicalGapCut_of_next_lt hn k hk, gapLeft_of_pos angles _ (by simp), hpred]
  · have hlast : k = lastNodeIndex hn := by
      apply Fin.ext
      change k.val = n - 1
      have hkn := k.isLt
      omega
    have hkn : k.val + 1 = n := by have h := k.isLt; omega
    rw [physicalGapCut_of_last hn k hkn, gapLeft_zero, hlast]

/--
@isnad1 id=eq.1h3v.s5.f26a2e7945d9 from=translated src=- shape=c4be26b5 vocab=71e45a1e
-/
lemma gapRight_physicalGapCut (angles : CyclicAngles n hn) (k : Fin n) :
    gapRight angles (physicalGapCut hn k) = cyclicGapRight angles k := by
  by_cases hk : k.val + 1 < n
  · rw [physicalGapCut_of_next_lt hn k hk, gapRight_of_pos angles _ (by simp)]
    simp only [cyclicGapRight, dite_eq_left hk]
  · have hkn : k.val + 1 = n := by have h := k.isLt; omega
    rw [physicalGapCut_of_last hn k hkn, gapRight_zero]
    simp only [cyclicGapRight, dite_eq_right hk]

def orderedGapInterpolant (angles : CyclicAngles n hn) (k : Fin n) : ℝ → ℝ :=
  gapInterpolant angles (physicalGapCut hn k)

def orderedPeak (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (k : Fin n) : ℝ :=
  gapPeak angles hsize (physicalGapCut hn k)

def orderedHeight (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (k : Fin n) : ℝ :=
  gapHeight angles hsize (physicalGapCut hn k)

/--
@isnad1 id=mem.2h3v.s5.d41d3cad43cd from=translated src=- shape=8147dcb7 vocab=19ae504e
-/
lemma orderedPeak_mem_node_gap (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (k : Fin n) :
    orderedPeak angles hsize k ∈ Set.Ioo (angles.angle k) (cyclicGapRight angles k) := by
  have h := gapPeak_mem_Ioo angles hsize (physicalGapCut hn k)
  rw [gapLeft_physicalGapCut, gapRight_physicalGapCut] at h
  exact h

/--
@isnad1 id=le.2h4v.s5.ac4bb56e1a02 from=translated src=- shape=4e5c5be3 vocab=f31be8df
-/
lemma cyclicGapRight_le_angle_of_lt (angles : CyclicAngles n hn) {k l : Fin n}
    (hkl : k < l) : cyclicGapRight angles k ≤ angles.angle l := by
  have hk : k.val + 1 < n := by
    have hklval : k.val < l.val := hkl
    have hln := l.isLt
    omega
  rw [cyclicGapRight, dite_eq_left hk]
  exact angles.strictMono.monotone (show (⟨k.val + 1, hk⟩ : Fin n) ≤ l from hkl)

/--
@isnad1 id=strictmo.2h2v.s5.a58a6a01a652 from=translated src=- shape=077cc051 vocab=a4235744
-/
lemma orderedPeak_strictMono (angles : CyclicAngles n hn) (hsize : 2 ≤ n) :
    StrictMono (orderedPeak angles hsize) := by
  intro k l hkl
  exact ((orderedPeak_mem_node_gap angles hsize k).2.trans_le
    (cyclicGapRight_le_angle_of_lt angles hkl)).trans
      (orderedPeak_mem_node_gap angles hsize l).1

/--
@isnad1 id=mem.2h3v.s6.36e57b06a89d from=translated src=- shape=aaf8030a vocab=5e2018c3
-/
lemma orderedPeak_mem_Ioo (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (k : Fin n) :
    orderedPeak angles hsize k ∈ Set.Ioo 0 (2 * Real.pi) := by
  have h := gapPeak_mem_turn angles hsize (physicalGapCut hn k)
  exact h

/--
@isnad1 id=hasderiv.2h3v.s6.e25406d279f3 from=translated src=- shape=b65f7e45 vocab=77556f1f
-/
lemma orderedPeak_hasDerivAt_zero (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (k : Fin n) : HasDerivAt (orderedGapInterpolant angles k) 0 (orderedPeak angles hsize k) :=
  (gapPeak_strictIntervalPeak angles hsize (physicalGapCut hn k)).hasDerivAt_zero

/--
@isnad1 id=eq.2h3v.s5.c80c7bed7ecc from=translated src=- shape=c2c749f7 vocab=07bb881c
-/
lemma orderedHeight_eq_value (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (k : Fin n) :
    orderedHeight angles hsize k = orderedGapInterpolant angles k (orderedPeak angles hsize k) :=
  rfl

/--
@isnad1 id=lt.2h3v.s5.d7ee9be0a4ff from=translated src=- shape=90be3932 vocab=d1911f8a
-/
lemma one_lt_orderedHeight (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (k : Fin n) :
    1 < orderedHeight angles hsize k :=
  one_lt_gapHeight angles hsize (physicalGapCut hn k)

/--
@isnad1 id=lt.2h3v.s6.1d0839e8033b from=translated src=- shape=defc2937 vocab=3dc937e6
-/
lemma orderedPeak_second_deriv_neg (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (k : Fin n) : deriv (deriv (orderedGapInterpolant angles k)) (orderedPeak angles hsize k) < 0 :=
  gapPeak_second_deriv_neg angles hsize (physicalGapCut hn k)

end

end UnitCircleInterpolation
