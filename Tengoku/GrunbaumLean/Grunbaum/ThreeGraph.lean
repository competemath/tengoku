/-
Copyright (c) 2026 Giuliano Basso. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuliano Basso, Claude
-/
import Tengoku.GrunbaumLean.FranklFuredi.Remarks

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complements on 3-graphs: blow-ups and twins

We add a few general facts to the formalization of Frankl and Füredi
(`FranklFuredi.ThreeGraph`):

* `FranklFuredi.ThreeGraph.pullback_pullback`, `FranklFuredi.ThreeGraph.pullback_id` :
  blow-ups compose;
* `FranklFuredi.ThreeGraph.ext_of_lt` : on a linearly ordered vertex set, a 3-graph is
  determined by its edges `a < b < c`;
* `FranklFuredi.ThreeGraph.exists_twinFree_quotient` : if any four points span an even number of
  edges, then being *twins* (equal or contained in no common edge) is an equivalence relation,
  and the 3-graph is a blow-up of a twin-free 3-graph. This is how blow-ups enter the
  classification (FF) of the errata.
-/

namespace FranklFuredi.ThreeGraph

universe u

variable {V W X : Type*} [DecidableEq V]

/-! ### Blow-ups -/

section Pullback

variable [DecidableEq W] [DecidableEq X] [Fintype V] [Fintype W]

omit [DecidableEq V] in
/-- Blow-ups compose.
@isnad1 id=eq.0h6v.s5.40f4f75d1981 from=translated src=- shape=7c4da67a vocab=f52b992c
-/
theorem pullback_pullback (K : ThreeGraph X) (f : W → X) (g : V → W) :
    (K.pullback f).pullback g = K.pullback (f ∘ g) := by
  classical
  apply ext_of_isEdge
  intro a b c hab hac hbc
  simp only [isEdge_pullback, Function.comp_apply]
  constructor
  · rintro ⟨-, -, -, -, -, -, h⟩
    exact ⟨hab, hac, hbc, h⟩
  · rintro ⟨-, -, -, h⟩
    exact ⟨hab, hac, hbc, fun e => h.ne_12 (by rw [e]), fun e => h.ne_13 (by rw [e]),
      fun e => h.ne_23 (by rw [e]), h⟩

/-- The blow-up along the identity is the 3-graph itself.
@isnad1 id=eq.0h2v.s4.890b6c892ce8 from=translated src=- shape=7bfed018 vocab=6db7ffa7
-/
theorem pullback_id (H : ThreeGraph V) : H.pullback id = H := by
  apply ext_of_isEdge
  intro a b c hab hac hbc
  simp [isEdge_pullback, hab, hac, hbc]

end Pullback

/-- On a linearly ordered vertex set, a 3-graph is determined by its edges `a < b < c`.
@isnad1 id=eq.1h3v.s6.7fe9bf478fef from=translated src=- shape=f12abf1d vocab=13719899
-/
theorem ext_of_lt [LinearOrder V] {H H' : ThreeGraph V}
    (h : ∀ a b c, a < b → b < c → (H.IsEdge a b c ↔ H'.IsEdge a b c)) : H = H' := by
  apply ext_of_isEdge
  intro a b c hab hac hbc
  rcases lt_or_gt_of_ne hab with hab' | hab' <;> rcases lt_or_gt_of_ne hac with hac' | hac' <;>
    rcases lt_or_gt_of_ne hbc with hbc' | hbc'
  · exact h a b c hab' hbc'
  · rw [isEdge_comm_23, isEdge_comm_23 (H := H')]; exact h a c b hac' hbc'
  · exact absurd (hab'.trans hbc') (not_lt.mpr hac'.le)
  · rw [isEdge_rotate, isEdge_rotate (H := H'), isEdge_rotate, isEdge_rotate (H := H')]
    exact h c a b hac' hab'
  · rw [isEdge_comm_12, isEdge_comm_12 (H := H')]; exact h b a c hab' hac'
  · exact absurd (hbc'.trans hab') (not_lt.mpr hac'.le)
  · rw [isEdge_rotate, isEdge_rotate (H := H')]; exact h b c a hbc' hac'
  · rw [isEdge_comm_13, isEdge_comm_13 (H := H')]; exact h c b a hbc' hab'

/-! ### Twins -/

section Twins

variable {H : ThreeGraph V}

/-- The twin relation: `a = b`, or no edge contains both `a` and `b`.-/
def TwinRel (H : ThreeGraph V) (a b : V) : Prop := a = b ∨ ∀ z, ¬H.IsEdge a b z

/-- A 3-graph is *twin-free* if any two distinct points lie in a common edge.-/
def TwinFree (H : ThreeGraph V) : Prop := ∀ a b, a ≠ b → ∃ z, H.IsEdge a b z

/-- Twins have the same link. This is Proposition 6 of Frankl and Füredi.
@isnad1 id=iff.2h6v.s5.04b8c62af0e7 from=translated src=- shape=405f4f9b vocab=2505613c
-/
theorem isEdge_congr_of_twinRel (hP : Good H.IsEdge) {a a' : V} (h : TwinRel H a a')
    (b c : V) : H.IsEdge a b c ↔ H.IsEdge a' b c := by
  rcases h with rfl | h
  · rfl
  by_cases haa : a = a'
  · rw [haa]
  exact (prop6 hP haa).mpr h b c

/--
@isnad1 id=iff.2h6v.s5.81085bce4aa6 from=translated src=- shape=e508f860 vocab=2505613c
-/
theorem isEdge_congr₂_of_twinRel (hP : Good H.IsEdge) {b b' : V} (h : TwinRel H b b')
    (a c : V) : H.IsEdge a b c ↔ H.IsEdge a b' c := by
  rw [isEdge_comm_12, isEdge_comm_12 (b := b'), isEdge_congr_of_twinRel hP h]

/--
@isnad1 id=iff.2h6v.s5.77895f4dbc50 from=translated src=- shape=0f3e9104 vocab=2505613c
-/
theorem isEdge_congr₃_of_twinRel (hP : Good H.IsEdge) {c c' : V} (h : TwinRel H c c')
    (a b : V) : H.IsEdge a b c ↔ H.IsEdge a b c' := by
  rw [isEdge_comm_13, isEdge_comm_13 (c := c'), isEdge_congr_of_twinRel hP h]

/--
@isnad1 id=twinrel.1h4v.s4.4d6c3c3d8fd0 from=translated src=- shape=f840286b vocab=2eb0a90b
-/
lemma TwinRel.symm {a b : V} (h : TwinRel H a b) : TwinRel H b a := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr fun z hz => h z (isEdge_comm_12.mp hz)

/-- If any four points span an even number of edges, the twin relation is an equivalence
relation.
@isnad1 id=equivale.1h2v.s4.408e90b1049f from=translated src=- shape=a87d1ca6 vocab=ba74b4a9
-/
theorem twinRel_equivalence (hP : Good H.IsEdge) : Equivalence (TwinRel H) where
  refl _ := Or.inl rfl
  symm := TwinRel.symm
  trans := by
    rintro a b c hab hbc
    rcases hab with rfl | hab
    · exact hbc
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    right
    intro z hz
    -- `b` and `c` are twins, so `b` lies in the edge `a c z` in place of `c`
    have hcb : TwinRel H c b := TwinRel.symm (Or.inr hbc)
    exact hab z ((isEdge_congr₂_of_twinRel hP hcb a z).mp hz)

/-- The setoid of twins.-/
def twinSetoid (hP : Good H.IsEdge) : Setoid V := ⟨TwinRel H, twinRel_equivalence hP⟩

/-- **Twin reduction.** If any four points span an even number of edges, then `H` is a blow-up
of a twin-free 3-graph `H'` with the same property: collapse every class of twins to a point.
@isnad1 id=ex.1h2v.s6.94f235f7f65a from=translated src=- shape=7e3c76ea vocab=9dc7c03e
-/
theorem exists_twinFree_quotient {V : Type u} [DecidableEq V] [Fintype V] {H : ThreeGraph V}
    (hP : Good H.IsEdge) :
    ∃ (Q : Type u) (_ : Fintype Q) (_ : DecidableEq Q) (π : V → Q) (H' : ThreeGraph Q),
      Function.Surjective π ∧ Good H'.IsEdge ∧ TwinFree H' ∧ H = H'.pullback π := by
  classical
  let s := twinSetoid hP
  let Q := Quotient s
  let π : V → Q := Quotient.mk s
  let H' : ThreeGraph Q := H.pullback Quotient.out
  have hout : ∀ a : V, TwinRel H a (π a).out := fun a =>
    (twinRel_equivalence hP).symm (Quotient.mk_out (s := s) a)
  have hrep : ∀ a b c : V, H.IsEdge a b c ↔ H.IsEdge (π a).out (π b).out (π c).out := by
    intro a b c
    rw [isEdge_congr_of_twinRel hP (hout a), isEdge_congr₂_of_twinRel hP (hout b),
      isEdge_congr₃_of_twinRel hP (hout c)]
  have hne : ∀ a b z : V, H.IsEdge a b z → π a ≠ π b := by
    intro a b z hz hπ
    have hab : TwinRel H a b := Quotient.exact hπ
    rcases hab with rfl | hab
    · exact hz.ne_12 rfl
    · exact hab z hz
  refine ⟨Q, inferInstance, inferInstance, π, H', Quotient.mk_surjective, good_pullback hP _,
    ?_, ?_⟩
  · -- `H'` is twin-free
    intro q q' hqq'
    have hnot : ¬TwinRel H q.out q'.out := by
      intro h
      apply hqq'
      rw [← Quotient.out_eq q, ← Quotient.out_eq q']
      exact Quotient.sound h
    simp only [TwinRel, not_or, not_forall, not_not] at hnot
    obtain ⟨-, z, hz⟩ := hnot
    refine ⟨π z, ?_⟩
    simp only [H', isEdge_pullback]
    refine ⟨hqq', ?_, ?_, ?_⟩
    · intro h
      have := hne q.out z q'.out ((isEdge_comm_23).mp hz)
      simp only [π, Quotient.out_eq] at this h
      exact this h
    · intro h
      have := hne q'.out z q.out (isEdge_rotate.mp hz)
      simp only [π, Quotient.out_eq] at this h
      exact this h
    · rw [← isEdge_congr₃_of_twinRel hP (hout z)]
      exact hz
  · -- `H` is the blow-up of `H'`
    apply ext_of_isEdge
    intro a b c hab hac hbc
    simp only [H', isEdge_pullback, hab, hac, hbc, ne_eq, not_false_eq_true, true_and]
    constructor
    · intro h
      exact ⟨hne a b c h, hne a c b (isEdge_comm_23.mp h), hne b c a (isEdge_rotate.mp h),
        (hrep a b c).mp h⟩
    · rintro ⟨-, -, -, h⟩
      exact (hrep a b c).mpr h

end Twins

end FranklFuredi.ThreeGraph
