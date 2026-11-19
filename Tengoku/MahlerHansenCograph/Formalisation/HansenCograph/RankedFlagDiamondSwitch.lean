/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.FlagRankedSequence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Switching a middle face in a saturated flag

This file isolates the order-theoretic operation used by the portal-vector
monotonicity argument.  Replacing one entry of a saturated flag by another
element covering the same predecessor and covered by the same successor
again gives a saturated flag.
-/

namespace HansenCograph

universe u

/-- Every two consecutive cover steps have a unique alternative middle
element.  The inequality in the payload distinguishes the alternative from
the supplied middle element.-/
def RankTwoDiamond (P : Type u) [PartialOrder P] : Prop :=
  ∀ {a b c : P}, a ⋖ b → b ⋖ c →
    ∃! b' : P, a ⋖ b' ∧ b' ⋖ c ∧ b' ≠ b

namespace RankTwoDiamond

/-- The canonical alternative middle element in a thin rank-two interval.-/
noncomputable def otherMiddle {P : Type u} [PartialOrder P]
    (hP : RankTwoDiamond P) {a b c : P} (hab : a ⋖ b) (hbc : b ⋖ c) : P :=
  Classical.choose (hP hab hbc)

theorem otherMiddle_spec {P : Type u} [PartialOrder P]
    (hP : RankTwoDiamond P) {a b c : P} (hab : a ⋖ b) (hbc : b ⋖ c) :
    a ⋖ hP.otherMiddle hab hbc ∧
      hP.otherMiddle hab hbc ⋖ c ∧
      hP.otherMiddle hab hbc ≠ b :=
  (Classical.choose_spec (hP hab hbc)).1

/-- Switching the chosen alternative middle again returns the original
middle element.-/
theorem otherMiddle_reverse {P : Type u} [PartialOrder P]
    (hP : RankTwoDiamond P) {a b c : P} (hab : a ⋖ b) (hbc : b ⋖ c) :
    hP.otherMiddle (hP.otherMiddle_spec hab hbc).1
        (hP.otherMiddle_spec hab hbc).2.1 = b := by
  unfold otherMiddle
  exact ((Classical.choose_spec
    (hP (hP.otherMiddle_spec hab hbc).1
      (hP.otherMiddle_spec hab hbc).2.1)).2 b
        ⟨hab, hbc, (hP.otherMiddle_spec hab hbc).2.2.symm⟩).symm

/-- Thin rank-two intervals are preserved by order isomorphisms.-/
theorem orderIso {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) (hP : RankTwoDiamond P) : RankTwoDiamond Q := by
  intro a b c hab hbc
  obtain ⟨b', hb', hub'⟩ := hP
    ((apply_covBy_apply_iff e.symm).mpr hab)
    ((apply_covBy_apply_iff e.symm).mpr hbc)
  refine ⟨e b', ?_, ?_⟩
  · constructor
    · simpa only [OrderIso.apply_symm_apply] using
        (apply_covBy_apply_iff e).mpr hb'.1
    constructor
    · simpa only [OrderIso.apply_symm_apply] using
        (apply_covBy_apply_iff e).mpr hb'.2.1
    · intro h
      apply hb'.2.2
      apply e.injective
      simpa only [OrderIso.apply_symm_apply] using h
  · intro x hx
    have hxpre : (e.symm a) ⋖ (e.symm x) ∧
        (e.symm x) ⋖ (e.symm c) ∧ e.symm x ≠ e.symm b :=
      ⟨(apply_covBy_apply_iff e.symm).mpr hx.1,
        (apply_covBy_apply_iff e.symm).mpr hx.2.1,
        fun h ↦ hx.2.2 (e.symm.injective h)⟩
    have heq : e.symm x = b' := hub' (e.symm x) hxpre
    apply e.symm.injective
    simpa only [OrderIso.symm_apply_apply] using heq

/-- Reversing the order preserves thin rank-two intervals.-/
theorem orderDual {P : Type u} [PartialOrder P]
    (hP : RankTwoDiamond P) : RankTwoDiamond (OrderDual P) := by
  intro a b c hab hbc
  have hab' : @CovBy P _ b a := by
    refine ⟨hab.1, ?_⟩
    intro x hbx hxa
    exact hab.2 hxa hbx
  have hbc' : @CovBy P _ c b := by
    refine ⟨hbc.1, ?_⟩
    intro x hcx hxb
    exact hbc.2 hxb hcx
  obtain ⟨b', hb', hub'⟩ := @hP c b a hbc' hab'
  refine ⟨b', ?_, ?_⟩
  · constructor
    · refine ⟨hb'.2.1.1, ?_⟩
      intro x hb'x hxa
      exact hb'.2.1.2 hxa hb'x
    constructor
    · refine ⟨hb'.1.1, ?_⟩
      intro x hcx hxb'
      exact hb'.1.2 hxb' hcx
    · exact hb'.2.2
  intro x hx
  apply hub' x
  constructor
  · refine ⟨hx.2.1.1, ?_⟩
    intro y hcy hyx
    exact hx.2.1.2 hyx hcy
  constructor
  · refine ⟨hx.1.1, ?_⟩
    intro y hxy hya
    exact hx.1.2 hya hxy
  · exact hx.2.2

end RankTwoDiamond

namespace RankedFlag

variable {P : Type u} [PartialOrder P] [BoundedOrder P]

/-- The predecessor index of the switched middle entry.-/
def switchPredIndex {N : ℕ} (i : Fin N) : Fin (N + 2) :=
  ⟨i.1, by omega⟩

/-- The index of the switched middle entry.-/
def switchMiddleIndex {N : ℕ} (i : Fin N) : Fin (N + 2) :=
  ⟨i.1 + 1, by omega⟩

/-- The successor index of the switched middle entry.-/
def switchSuccIndex {N : ℕ} (i : Fin N) : Fin (N + 2) :=
  ⟨i.1 + 2, by omega⟩

theorem covBy_switchPred_middle {N : ℕ}
    (f : RankedFlag P (N + 1)) (i : Fin N) :
    f (switchPredIndex i) ⋖ f (switchMiddleIndex i) := by
  let j : Fin (N + 1) := ⟨i.1, by omega⟩
  have h := f.covBy_succ j
  have hpred : j.castSucc = switchPredIndex i := by
    apply Fin.ext
    rfl
  have hmid : j.succ = switchMiddleIndex i := by
    apply Fin.ext
    rfl
  rw [hpred, hmid] at h
  exact h

theorem covBy_switchMiddle_succ {N : ℕ}
    (f : RankedFlag P (N + 1)) (i : Fin N) :
    f (switchMiddleIndex i) ⋖ f (switchSuccIndex i) := by
  let j : Fin (N + 1) := ⟨i.1 + 1, by omega⟩
  have h := f.covBy_succ j
  have hmid : j.castSucc = switchMiddleIndex i := by
    apply Fin.ext
    rfl
  have hsucc : j.succ = switchSuccIndex i := by
    apply Fin.ext
    rfl
  rw [hmid, hsucc] at h
  exact h

/-- Replace one non-endpoint entry of a saturated flag, provided the new
entry has the same two incident cover relations.-/
def switchMiddle {N : ℕ} (f : RankedFlag P (N + 1)) (i : Fin N)
    (b' : P)
    (hlo : f (switchPredIndex i) ⋖ b')
    (hhi : b' ⋖ f (switchSuccIndex i)) :
    RankedFlag P (N + 1) where
  toFun j := if j = switchMiddleIndex i then b' else f j
  map_zero := by
    have hne : (0 : Fin (N + 2)) ≠ switchMiddleIndex i := by
      intro h
      have := congrArg Fin.val h
      simp [switchMiddleIndex] at this
    simp [hne, f.map_zero]
  map_last := by
    have hne : Fin.last (N + 1) ≠ switchMiddleIndex i := by
      intro h
      have := congrArg Fin.val h
      simp [switchMiddleIndex] at this
      omega
    simp [hne, f.map_last]
  covBy_succ := by
    intro j
    by_cases hjlo : j.1 = i.1
    · have hpred : j.castSucc = switchPredIndex i := by
        apply Fin.ext
        exact hjlo
      have hmid : j.succ = switchMiddleIndex i := by
        apply Fin.ext
        simp [switchMiddleIndex, hjlo]
      have hne : switchPredIndex i ≠ switchMiddleIndex i := by
        intro h
        have := congrArg Fin.val h
        simp [switchPredIndex, switchMiddleIndex] at this
      rw [hpred, hmid]
      simp only [hne, ite_false, ite_true]
      simpa only [switchPredIndex] using hlo
    · by_cases hjhi : j.1 = i.1 + 1
      · have hmid : j.castSucc = switchMiddleIndex i := by
          apply Fin.ext
          exact hjhi
        have hsucc : j.succ = switchSuccIndex i := by
          apply Fin.ext
          simp [switchSuccIndex, hjhi]
        have hne : switchSuccIndex i ≠ switchMiddleIndex i := by
          intro h
          have := congrArg Fin.val h
          simp [switchSuccIndex, switchMiddleIndex] at this
        rw [hmid, hsucc]
        simp only [ite_true, hne, ite_false]
        simpa only [switchSuccIndex] using hhi
      · have hleft : j.castSucc ≠ switchMiddleIndex i := by
          intro h
          apply hjhi
          have := congrArg Fin.val h
          simpa [switchMiddleIndex] using this
        have hright : j.succ ≠ switchMiddleIndex i := by
          intro h
          apply hjlo
          have := congrArg Fin.val h
          simp [switchMiddleIndex] at this
          omega
        simp [hleft, hright, f.covBy_succ j]

@[simp] theorem switchMiddle_apply_middle {N : ℕ}
    (f : RankedFlag P (N + 1)) (i : Fin N) (b' : P)
    (hlo : f (switchPredIndex i) ⋖ b')
    (hhi : b' ⋖ f (switchSuccIndex i)) :
    switchMiddle f i b' hlo hhi (switchMiddleIndex i) = b' := by
  simp [switchMiddle]

theorem switchMiddle_apply_of_ne {N : ℕ}
    (f : RankedFlag P (N + 1)) (i : Fin N) (b' : P)
    (hlo : f (switchPredIndex i) ⋖ b')
    (hhi : b' ⋖ f (switchSuccIndex i))
    (j : Fin (N + 2)) (hj : j ≠ switchMiddleIndex i) :
    switchMiddle f i b' hlo hhi j = f j := by
  simp [switchMiddle, hj]

/-- Replacing the same position twice, first by an alternative middle and
then by the original entry, recovers the initial saturated flag.-/
theorem switchMiddle_restore {N : ℕ}
    (f : RankedFlag P (N + 1)) (i : Fin N) (b' : P)
    (hlo : f (switchPredIndex i) ⋖ b')
    (hhi : b' ⋖ f (switchSuccIndex i)) :
    switchMiddle (switchMiddle f i b' hlo hhi) i
        (f (switchMiddleIndex i))
        (by
          have hne : switchPredIndex i ≠ switchMiddleIndex i := by
            intro h
            have := congrArg Fin.val h
            simp [switchPredIndex, switchMiddleIndex] at this
          rw [switchMiddle_apply_of_ne _ _ _ _ _ _ hne]
          exact covBy_switchPred_middle f i
          )
        (by
          have hne : switchSuccIndex i ≠ switchMiddleIndex i := by
            intro h
            have := congrArg Fin.val h
            simp [switchSuccIndex, switchMiddleIndex] at this
          rw [switchMiddle_apply_of_ne _ _ _ _ _ _ hne]
          exact covBy_switchMiddle_succ f i
          ) = f := by
  apply RankedFlag.ext
  intro j
  by_cases hj : j = switchMiddleIndex i
  · subst j
    simp
  · rw [switchMiddle_apply_of_ne _ _ _ _ _ _ hj,
      switchMiddle_apply_of_ne _ _ _ _ _ _ hj]

end RankedFlag
end HansenCograph
