/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Defs

/-!
# Finite Boolean Hamming geometry -- proof internals
-/

public section

namespace Complexity

namespace BooleanHamming

/--
@isnad1 id=iff.0h4v.s5.48c435de699f from=translated src=- shape=dd1cb4a4 vocab=417a6f0b
-/
theorem mem_disagreement_internal {length : ℕ} (left right : Word length)
    (coordinate : Fin length) :
    coordinate ∈ disagreement left right ↔
      left coordinate ≠ right coordinate := by
  simp [disagreement]

/--
@isnad1 id=eq.0h2v.s4.d4cc0e44997f from=translated src=- shape=fc61c6a6 vocab=45847dc7
-/
theorem distance_refl_internal {length : ℕ} (word : Word length) :
    distance word word = 0 := by
  simp [distance, disagreement]

/--
@isnad1 id=eq.0h3v.s4.92cf2b1eda1f from=translated src=- shape=9ee3e7a7 vocab=45847dc7
-/
theorem distance_comm_internal {length : ℕ} (left right : Word length) :
    distance left right = distance right left := by
  apply congrArg Finset.card
  ext coordinate
  simp [disagreement, ne_comm]

/--
@isnad1 id=iff.0h3v.s4.40c47e7991a7 from=translated src=- shape=b2a84df1 vocab=45847dc7
-/
theorem distance_eq_zero_iff_internal {length : ℕ} (left right : Word length) :
    distance left right = 0 ↔ left = right := by
  constructor
  · intro hzero
    funext coordinate
    by_contra hne
    have hmem : coordinate ∈ disagreement left right :=
      (mem_disagreement_internal left right coordinate).mpr hne
    have hempty : disagreement left right = ∅ :=
      Finset.card_eq_zero.mp hzero
    rw [hempty] at hmem
    simp at hmem
  · rintro rfl
    exact distance_refl_internal left

/--
@isnad1 id=le.0h4v.s5.be0badc69ae4 from=translated src=- shape=cdbbb858 vocab=4732b166
-/
theorem distance_triangle_internal {length : ℕ}
    (first second third : Word length) :
    distance first third ≤ distance first second + distance second third := by
  unfold distance
  calc
    (disagreement first third).card ≤
        (disagreement first second ∪ disagreement second third).card := by
      apply Finset.card_le_card
      intro coordinate hcoordinate
      have hne :=
        (mem_disagreement_internal first third coordinate).mp hcoordinate
      apply Finset.mem_union.mpr
      by_cases hfirst : first coordinate = second coordinate
      · right
        apply (mem_disagreement_internal second third coordinate).mpr
        intro hsecond
        exact hne (hfirst.trans hsecond)
      · exact Or.inl <|
          (mem_disagreement_internal first second coordinate).mpr hfirst
    _ ≤ (disagreement first second).card +
        (disagreement second third).card :=
      Finset.card_union_le (disagreement first second)
        (disagreement second third)

/--
@isnad1 id=le.0h3v.s4.e886fa1f1447 from=translated src=- shape=a427f74f vocab=7dd93b8f
-/
theorem distance_le_length_internal {length : ℕ} (left right : Word length) :
    distance left right ≤ length := by
  unfold distance
  calc
    (disagreement left right).card ≤
        (Finset.univ : Finset (Fin length)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = length := by simp

/--
@isnad1 id=eq.0h3v.s4.c21d827f0982 from=translated src=- shape=a920acc6 vocab=fc67524c
-/
theorem distance_eq_popCount_translate_internal {length : ℕ}
    (left right : Word length) :
    distance left right = popCount (translate right left) := by
  apply congrArg Finset.card
  ext coordinate
  simp [disagreement, translate]

/--
@isnad1 id=eq.0h3v.s4.d250316f8705 from=translated src=- shape=a1f2d8cb vocab=c9fbc299
-/
theorem translate_translate_internal {length : ℕ}
    (center word : Word length) :
    translate center (translate center word) = word := by
  funext coordinate
  simp [translate]

/--
@isnad1 id=eq.0h3v.s5.066face2b971 from=translated src=- shape=d7f3ec61 vocab=393703c2
-/
theorem relativeDistance_eq_distance_div_internal {length : ℕ}
    (left right : Word length) :
    BooleanListCode.relativeDistance left right =
      (distance left right : ℚ) / length := by
  simp [BooleanListCode.relativeDistance, uniformProbability,
    distance, disagreement]

/--
@isnad1 id=iff.0h4v.s5.6d9ef282c6d9 from=translated src=- shape=850b96dd vocab=23177144
-/
theorem mem_sphere_internal {length : ℕ} (center word : Word length)
    (radius : ℕ) :
    word ∈ sphere center radius ↔ distance word center = radius := by
  simp [sphere]

/--
@isnad1 id=iff.0h4v.s5.8295274732a5 from=translated src=- shape=850b96dd vocab=27130f5d
-/
theorem mem_ball_internal {length : ℕ} (center word : Word length)
    (radius : ℕ) :
    word ∈ ball center radius ↔ distance word center ≤ radius := by
  simp [ball]

/--
@isnad1 id=le.1h4v.s5.e17338a50970 from=translated src=- shape=fd20c8e6 vocab=dbdbb14b
-/
theorem ball_mono_internal {length : ℕ} (center : Word length)
    {first second : ℕ} (hradius : first ≤ second) :
    ball center first ⊆ ball center second := by
  intro word hword
  exact (mem_ball_internal center word second).mpr <|
    (mem_ball_internal center word first).mp hword |>.trans hradius

/--
@isnad1 id=eq.0h3v.s6.e419e81916ae from=translated src=- shape=4b0c5811 vocab=dd0b69d7
-/
theorem card_distance_filter_eq_popCount_filter_internal {length : ℕ}
    (center : Word length) (predicate : ℕ → Prop) [DecidablePred predicate] :
    (Finset.univ.filter fun word : Word length =>
      predicate (distance word center)).card =
    (Finset.univ.filter fun word : Word length =>
      predicate (popCount word)).card := by
  apply Finset.card_bij'
      (fun word _ => translate center word)
      (fun word _ => translate center word)
  · intro word hword
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hword ⊢
    rw [← distance_eq_popCount_translate_internal]
    exact hword
  · intro word hword
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hword ⊢
    rw [distance_eq_popCount_translate_internal,
      translate_translate_internal]
    exact hword
  · intro word _
    exact translate_translate_internal center word
  · intro word _
    exact translate_translate_internal center word

/--
@isnad1 id=eq.0h3v.s4.a04c2cecdb88 from=translated src=- shape=b8340341 vocab=fdd8cd10
-/
theorem card_sphere_internal {length : ℕ} (center : Word length)
    (radius : ℕ) :
    (sphere center radius).card = length.choose radius := by
  calc
    (sphere center radius).card =
        (Finset.univ.filter fun word : Word length =>
          distance word center = radius).card := rfl
    _ = (Finset.univ.filter fun word : Word length =>
          popCount word = radius).card :=
      card_distance_filter_eq_popCount_filter_internal center
        (fun weight => weight = radius)
    _ = length.choose radius := card_filter_popCount_eq length radius

/--
@isnad1 id=eq.0h3v.s4.b9330e5aaa3e from=translated src=- shape=b8340341 vocab=0f54d2d5
-/
theorem card_ball_internal {length : ℕ} (center : Word length)
    (radius : ℕ) :
    (ball center radius).card = volume length radius := by
  calc
    (ball center radius).card =
        (Finset.univ.filter fun word : Word length =>
          distance word center ≤ radius).card := rfl
    _ = (Finset.univ.filter fun word : Word length =>
          popCount word ≤ radius).card :=
      card_distance_filter_eq_popCount_filter_internal center
        (fun weight => weight ≤ radius)
    _ = (Finset.univ.filter fun word : Word length =>
          popCount word ∈ Finset.range (radius + 1)).card := by
      congr 1
      ext word
      simp
    _ = ∑ weight ∈ Finset.range (radius + 1), length.choose weight :=
      card_filter_popCount_mem length (Finset.range (radius + 1))
    _ = volume length radius := rfl

/--
@isnad1 id=le.0h2v.s4.5d097d724ff5 from=translated src=- shape=a458b0eb vocab=723ca04b
-/
theorem volume_le_two_pow_internal (length radius : ℕ) :
    volume length radius ≤ 2 ^ length := by
  let center : Word length := fun _ => false
  rw [← card_ball_internal center radius]
  calc
    (ball center radius).card ≤
        (Finset.univ : Finset (Word length)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ length := by
      rw [Finset.card_univ, card_finArrowBool]

/--
@isnad1 id=eq.1h2v.s5.200244868a16 from=translated src=- shape=e9a1d57f vocab=723ca04b
-/
theorem volume_eq_two_pow_of_length_le_radius_internal
    {length radius : ℕ} (hradius : length ≤ radius) :
    volume length radius = 2 ^ length := by
  let center : Word length := fun _ => false
  rw [← card_ball_internal center radius]
  have hball : ball center radius = Finset.univ := by
    ext word
    simp [ball, (distance_le_length_internal word center).trans hradius]
  rw [hball, Finset.card_univ, card_finArrowBool]

/--
@isnad1 id=disjoint.1h4v.s5.8f2d64cec4c2 from=translated src=- shape=eb5c5055 vocab=06c8c1d2
-/
theorem disjoint_balls_of_two_mul_radius_lt_distance_internal
    {length radius : ℕ} {left right : Word length}
    (hfar : 2 * radius < distance left right) :
    Disjoint (ball left radius) (ball right radius) := by
  apply Finset.disjoint_left.mpr
  intro word hleft hright
  have hwordLeft : distance word left ≤ radius :=
    (mem_ball_internal left word radius).mp hleft
  have hleftWord : distance left word ≤ radius := by
    rw [distance_comm_internal]
    exact hwordLeft
  have hwordRight : distance word right ≤ radius :=
    (mem_ball_internal right word radius).mp hright
  have htriangle := distance_triangle_internal left word right
  omega

/--
@isnad1 id=pairwise.2h4v.s5.77c7a3499c7c from=translated src=- shape=1b8af56b vocab=189e5143
-/
theorem pairwiseDisjoint_balls_of_isSeparated_internal
    {length minimumDistance radius : ℕ} {code : Finset (Word length)}
    (hcode : IsSeparated code minimumDistance)
    (hradius : 2 * radius < minimumDistance) :
    (code : Set (Word length)).PairwiseDisjoint fun center =>
      ball center radius := by
  intro left hleft right hright hne
  apply disjoint_balls_of_two_mul_radius_lt_distance_internal
  exact hradius.trans_le (hcode hleft hright hne)

/--
@isnad1 id=le.2h4v.s6.0c92c6c1762f from=translated src=- shape=3ee295a7 vocab=ebd6620f
-/
theorem packing_bound_internal
    {length minimumDistance radius : ℕ} {code : Finset (Word length)}
    (hcode : IsSeparated code minimumDistance)
    (hradius : 2 * radius < minimumDistance) :
    code.card * volume length radius ≤ 2 ^ length := by
  have hdisjoint :
      (code : Set (Word length)).PairwiseDisjoint fun center =>
        ball center radius :=
    pairwiseDisjoint_balls_of_isSeparated_internal hcode hradius
  calc
    code.card * volume length radius =
        ∑ center ∈ code, (ball center radius).card := by
      simp [card_ball_internal]
    _ = (code.biUnion fun center => ball center radius).card :=
      (Finset.card_biUnion hdisjoint).symm
    _ ≤ (Finset.univ : Finset (Word length)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ length := by
      rw [Finset.card_univ, card_finArrowBool]

end BooleanHamming

end Complexity
