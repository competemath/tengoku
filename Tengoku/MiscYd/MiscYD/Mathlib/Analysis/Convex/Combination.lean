module

public import Tengoku

public section

open AffineMap Finset

section oldVars
variable {ι R E : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup E]
  [Module R E] {s : Finset ι} {f : ι → E} {x : E}

end oldVars

variable {ι 𝕜 V : Type*} [Field 𝕜] [AddCommGroup V]
  [Module 𝕜 V] {s t : Finset ι} {v w : ι → 𝕜} {x y : ι → V} {i : ι}

/--
@isnad1 id=eq.3h9v.s6.382a00a8c60e from=translated src=- shape=b661db13 vocab=ac46abe5
-/
@[congr]
lemma centerMass_congr (hst : s = t) (hvw : ∀ i ∈ t, v i = w i) (hxy : ∀ i ∈ t, x i = y i) :
    s.centerMass v x = t.centerMass w y := by
  unfold centerMass; rw [sum_congr hst hvw, sum_congr hst fun i hi ↦ by rw [hvw i hi, hxy i hi]]

variable [DecidableEq ι]

/--
@isnad1 id=eq.4h7v.s8.8c78f499af17 from=translated src=- shape=37c437d2 vocab=43800ba1
-/
lemma centerMass_union (hst : Disjoint s t) (hs : (∀ i ∈ s, w i = 0) ∨ ∑ i ∈ s, w i ≠ 0)
    (ht : (∀ i ∈ t, w i = 0) ∨ ∑ i ∈ t, w i ≠ 0) (hw₁ : ∑ i ∈ s ∪ t, w i = 1) :
    (s ∪ t).centerMass w x =
      (∑ i ∈ s, w i) • s.centerMass w x + (∑ i ∈ t, w i) • t.centerMass w x := by
  obtain hs | hs := hs
  · simp only [sum_union hst, sum_eq_zero hs, zero_add] at hw₁
    simp only [centerMass, sum_union hst, sum_eq_zero hs, hw₁, zero_add, inv_one, smul_add,
      one_smul, inv_zero, zero_smul, smul_zero, add_eq_right]
    exact sum_eq_zero fun i hi ↦ by simp [hs _ hi]
  obtain ht | ht := ht
  · simp only [sum_union hst, sum_eq_zero ht, add_zero] at hw₁
    simp only [centerMass, sum_union hst, hw₁, sum_eq_zero ht, add_zero, inv_one, smul_add,
      one_smul, inv_zero, zero_smul, smul_zero, add_eq_left]
    exact sum_eq_zero fun i hi ↦ by simp [ht _ hi]
  · simp [centerMass, hs, ht, hst, sum_union, hw₁]

/--
@isnad1 id=eq.4h7v.s8.d9875e05535a from=translated src=- shape=5a3357f6 vocab=de05bfa7
-/
lemma centerMass_union_of_ne_zero (hst : Disjoint s t) (hs : ∑ i ∈ s, w i ≠ 0)
    (ht : ∑ i ∈ t, w i ≠ 0) (hw₁ : ∑ i ∈ s ∪ t, w i = 1) :
    (s ∪ t).centerMass w x =
      (∑ i ∈ s, w i) • s.centerMass w x + (∑ i ∈ t, w i) • t.centerMass w x :=
  centerMass_union hst (.inr hs) (.inr ht) hw₁

/--
@isnad1 id=eq.4h7v.s8.bccb9df66345 from=translated src=- shape=24591343 vocab=aa98fe61
-/
lemma lineMap_centerMass_centerMass (hst : Disjoint s t)
    (hs : (∀ i ∈ s, w i = 0) ∨ ∑ i ∈ s, w i ≠ 0) (ht : (∀ i ∈ t, w i = 0) ∨ ∑ i ∈ t, w i ≠ 0)
    (hw₁ : ∑ i ∈ s ∪ t, w i = 1) :
    lineMap (s.centerMass w x) (t.centerMass w x) (∑ i ∈ t, w i) = (s ∪ t).centerMass w x := by
  rw [lineMap_apply_module, ← hw₁, sum_union hst, add_sub_cancel_right,
    centerMass_union hst hs ht hw₁]

/--
@isnad1 id=eq.4h7v.s8.ecbe7177dd67 from=translated src=- shape=4196b24d vocab=9d442f3b
-/
lemma lineMap_centerMass_centerMass_of_ne_zero (hst : Disjoint s t) (hs : ∑ i ∈ s, w i ≠ 0)
    (ht : ∑ i ∈ t, w i ≠ 0) (hw₁ : ∑ i ∈ s ∪ t, w i = 1) :
    lineMap (s.centerMass w x) (t.centerMass w x) (∑ i ∈ t, w i) = (s ∪ t).centerMass w x :=
  lineMap_centerMass_centerMass hst (.inr hs) (.inr ht) hw₁

/--
@isnad1 id=eq.4h7v.s8.ef5cccb29309 from=translated src=- shape=68a37dcb vocab=721cb9d2
-/
lemma lineMap_centerMass_sdiff (hi : i ∈ s) (hi₀ : w i ≠ 0) (hi₁ : w i ≠ 1)
    (hw₁ : ∑ i ∈ s, w i = 1) :
    lineMap ((s \ {i}).centerMass w x) (x i) (w i) = s.centerMass w x := by
  rw [← centerMass_singleton i x hi₀, ← sum_singleton w i,
    lineMap_centerMass_centerMass] <;>
    simp [*, sub_eq_zero, eq_comm (b := w _)]

/--
@isnad1 id=eq.2h7v.s6.2cd2bf3593e2 from=translated src=- shape=4a9dfb74 vocab=c728493f
-/
lemma centerMass_sdiff_of_weight_eq_zero (hi : i ∈ s) (hi₀ : w i = 0) :
    (s \ {i}).centerMass w x = s.centerMass w x := by
  simp [hi₀, sum_sdiff_eq_sub (singleton_subset_iff.2 hi), centerMass]

/--
@isnad1 id=eq.3h7v.s8.18e58d5eb0a3 from=translated src=- shape=fa37b89a vocab=721cb9d2
-/
lemma lineMap_centerMass_sdiff_singleton_of_ne_one (hi : i ∈ s) (hi₁ : w i ≠ 1)
    (hw₁ : ∑ j ∈ s, w j = 1) :
    lineMap ((s \ {i}).centerMass w x) (x i) (w i) = s.centerMass w x := by
  obtain hi₀ | hi₀ := eq_or_ne (w i) 0
  · simp [centerMass_sdiff_of_weight_eq_zero hi, hi₀]
  · rw [← centerMass_singleton i x hi₀, ← sum_singleton w i, lineMap_centerMass_centerMass] <;>
      simp [*, sub_eq_zero, eq_comm (b := w _)]

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/--
@isnad1 id=eq.3h7v.s8.9760e32031f8 from=translated src=- shape=371b731c vocab=6c7cfe05
-/
lemma centerMass_union_of_nonneg (hst : Disjoint s t) (hw₀ : ∀ i ∈ s ∪ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ s ∪ t, w i = 1) :
    (s ∪ t).centerMass w x =
      (∑ i ∈ s, w i) • s.centerMass w x + (∑ i ∈ t, w i) • t.centerMass w x := by
  refine centerMass_union hst ?_ ?_ hw₁
  · rw [← sum_eq_zero_iff_of_nonneg fun j hj ↦ hw₀ _ <| subset_union_left hj]
    exact em _
  · rw [← sum_eq_zero_iff_of_nonneg fun j hj ↦ hw₀ _ <| subset_union_right hj]
    exact em _

/--
@isnad1 id=eq.3h7v.s8.caee1312e028 from=translated src=- shape=17974915 vocab=0f6ec047
-/
lemma lineMap_centerMass_centerMass_of_nonneg (hst : Disjoint s t) (hw₀ : ∀ i ∈ s ∪ t, 0 ≤ w i)
    (hw₁ : ∑ i ∈ s ∪ t, w i = 1) :
    lineMap (s.centerMass w x) (t.centerMass w x) (∑ i ∈ t, w i) = (s ∪ t).centerMass w x := by
  rw [lineMap_apply_module, ← hw₁, sum_union hst, add_sub_cancel_right,
    centerMass_union_of_nonneg hst hw₀ hw₁]

/--
@isnad1 id=eq.3h7v.s8.e010b513166c from=translated src=- shape=43b4ad72 vocab=dc972f5d
-/
lemma lineMap_centerMass_sdiff_singleton_of_nonneg (hi : i ∈ s) (hw₀ : ∀ j ∈ s \ {i}, 0 ≤ w j)
    (hw₁ : ∑ j ∈ s, w j = 1) :
    lineMap ((s \ {i}).centerMass w x) (x i) (w i) = s.centerMass w x := by
  obtain hi₁ | hi₁ := eq_or_ne (w i) 1
  · rw [← centerMass_singleton i x (w := w) (by simp [hi₁]), ← sum_singleton w i,
      lineMap_centerMass_centerMass]
    rotate_left 2
    · rw [← sum_eq_zero_iff_of_nonneg hw₀]
      exact em _
    all_goals simp [*]
  · exact lineMap_centerMass_sdiff_singleton_of_ne_one hi hi₁ hw₁
