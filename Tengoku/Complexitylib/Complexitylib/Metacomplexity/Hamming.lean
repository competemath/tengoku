/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Internal
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Existence
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Hamming.Code

/-!
# Finite Boolean Hamming geometry

This module supplies the exact finite geometry used by coding-based
metacomplexity and hardness magnification: a metric on Boolean words, exact
binomial sphere and ball counts, and the Hamming packing bound. Absolute and
rational relative distance are connected explicitly. `BooleanCode` then packages
injective finite encodings, exact rate, minimum distance, and exhaustive unique
decoding without asserting an efficient implementation. A finite
Gilbert--Varshamov theorem supplies separated covering codes nonconstructively.
-/

public section

namespace Complexity

namespace BooleanHamming

/-- Membership in the disagreement support is pointwise inequality.
@isnad1 id=iff.0h4v.s5.48c435de699f from=translated src=- shape=dd1cb4a4 vocab=417a6f0b
-/
@[simp] theorem mem_disagreement {length : ℕ} (left right : Word length)
    (coordinate : Fin length) :
    coordinate ∈ disagreement left right ↔
      left coordinate ≠ right coordinate :=
  mem_disagreement_internal left right coordinate

/-- Every word has distance zero from itself.
@isnad1 id=eq.0h2v.s4.d4cc0e44997f from=translated src=- shape=fc61c6a6 vocab=45847dc7
-/
@[simp] theorem distance_refl {length : ℕ} (word : Word length) :
    distance word word = 0 :=
  distance_refl_internal word

/-- Boolean Hamming distance is symmetric.
@isnad1 id=eq.0h3v.s4.92cf2b1eda1f from=translated src=- shape=9ee3e7a7 vocab=45847dc7
-/
theorem distance_comm {length : ℕ} (left right : Word length) :
    distance left right = distance right left :=
  distance_comm_internal left right

/-- Distance zero characterizes equality of words.
@isnad1 id=iff.0h3v.s4.40c47e7991a7 from=translated src=- shape=b2a84df1 vocab=45847dc7
-/
@[simp] theorem distance_eq_zero_iff {length : ℕ} (left right : Word length) :
    distance left right = 0 ↔ left = right :=
  distance_eq_zero_iff_internal left right

/-- Boolean Hamming distance satisfies the triangle inequality.
@isnad1 id=le.0h4v.s5.be0badc69ae4 from=translated src=- shape=cdbbb858 vocab=4732b166
-/
theorem distance_triangle {length : ℕ}
    (first second third : Word length) :
    distance first third ≤ distance first second + distance second third :=
  distance_triangle_internal first second third

/-- Hamming distance never exceeds the word length.
@isnad1 id=le.0h3v.s4.e886fa1f1447 from=translated src=- shape=a427f74f vocab=7dd93b8f
-/
theorem distance_le_length {length : ℕ} (left right : Word length) :
    distance left right ≤ length :=
  distance_le_length_internal left right

/-- Distance from `right` is the Hamming weight after XOR translation.
@isnad1 id=eq.0h3v.s4.c21d827f0982 from=translated src=- shape=a920acc6 vocab=fc67524c
-/
theorem distance_eq_popCount_translate {length : ℕ}
    (left right : Word length) :
    distance left right = popCount (translate right left) :=
  distance_eq_popCount_translate_internal left right

/-- XOR translation by a fixed center is an involution.
@isnad1 id=eq.0h3v.s4.d250316f8705 from=translated src=- shape=a1f2d8cb vocab=c9fbc299
-/
@[simp] theorem translate_translate {length : ℕ}
    (center word : Word length) :
    translate center (translate center word) = word :=
  translate_translate_internal center word

/-- The list-decoding relative distance is absolute Hamming distance divided by
the coordinate count. This remains valid at length zero under rational
division's total convention.
@isnad1 id=eq.0h3v.s5.066face2b971 from=translated src=- shape=d7f3ec61 vocab=393703c2
-/
theorem relativeDistance_eq_distance_div {length : ℕ}
    (left right : Word length) :
    BooleanListCode.relativeDistance left right =
      (distance left right : ℚ) / length :=
  relativeDistance_eq_distance_div_internal left right

/-- Membership in a Hamming sphere.
@isnad1 id=iff.0h4v.s5.6d9ef282c6d9 from=translated src=- shape=850b96dd vocab=23177144
-/
@[simp] theorem mem_sphere {length : ℕ} (center word : Word length)
    (radius : ℕ) :
    word ∈ sphere center radius ↔ distance word center = radius :=
  mem_sphere_internal center word radius

/-- Membership in a closed Hamming ball.
@isnad1 id=iff.0h4v.s5.8295274732a5 from=translated src=- shape=850b96dd vocab=27130f5d
-/
@[simp] theorem mem_ball {length : ℕ} (center word : Word length)
    (radius : ℕ) :
    word ∈ ball center radius ↔ distance word center ≤ radius :=
  mem_ball_internal center word radius

/-- Increasing the radius enlarges a Hamming ball.
@isnad1 id=le.1h4v.s5.e17338a50970 from=translated src=- shape=fd20c8e6 vocab=dbdbb14b
-/
theorem ball_mono {length : ℕ} (center : Word length)
    {first second : ℕ} (hradius : first ≤ second) :
    ball center first ⊆ ball center second :=
  ball_mono_internal center hradius

/-- XOR translation makes every distance-profile count center-independent.
@isnad1 id=eq.0h3v.s6.e419e81916ae from=translated src=- shape=4b0c5811 vocab=dd0b69d7
-/
theorem card_distance_filter_eq_popCount_filter {length : ℕ}
    (center : Word length) (predicate : ℕ → Prop) [DecidablePred predicate] :
    (Finset.univ.filter fun word : Word length =>
      predicate (distance word center)).card =
    (Finset.univ.filter fun word : Word length =>
      predicate (popCount word)).card :=
  card_distance_filter_eq_popCount_filter_internal center predicate

/-- A radius-`r` sphere in the Boolean cube has exactly `length.choose r`
words, independently of its center.
@isnad1 id=eq.0h3v.s4.a04c2cecdb88 from=translated src=- shape=b8340341 vocab=fdd8cd10
-/
theorem card_sphere {length : ℕ} (center : Word length) (radius : ℕ) :
    (sphere center radius).card = length.choose radius :=
  card_sphere_internal center radius

/-- A radius-`r` Boolean Hamming ball has its exact binomial volume.
@isnad1 id=eq.0h3v.s4.b9330e5aaa3e from=translated src=- shape=b8340341 vocab=0f54d2d5
-/
theorem card_ball {length : ℕ} (center : Word length) (radius : ℕ) :
    (ball center radius).card = volume length radius :=
  card_ball_internal center radius

/-- A Hamming ball contains at most all `2^length` Boolean words.
@isnad1 id=le.0h2v.s4.5d097d724ff5 from=translated src=- shape=a458b0eb vocab=723ca04b
-/
theorem volume_le_two_pow (length radius : ℕ) :
    volume length radius ≤ 2 ^ length :=
  volume_le_two_pow_internal length radius

/-- Once the radius reaches the word length, the ball is the entire cube.
@isnad1 id=eq.1h2v.s5.200244868a16 from=translated src=- shape=e9a1d57f vocab=723ca04b
-/
theorem volume_eq_two_pow_of_length_le_radius
    {length radius : ℕ} (hradius : length ≤ radius) :
    volume length radius = 2 ^ length :=
  volume_eq_two_pow_of_length_le_radius_internal hradius

/-- Balls of radius `r` around centers farther than `2r` are disjoint.
@isnad1 id=disjoint.1h4v.s5.8f2d64cec4c2 from=translated src=- shape=eb5c5055 vocab=06c8c1d2
-/
theorem disjoint_balls_of_two_mul_radius_lt_distance
    {length radius : ℕ} {left right : Word length}
    (hfar : 2 * radius < distance left right) :
    Disjoint (ball left radius) (ball right radius) :=
  disjoint_balls_of_two_mul_radius_lt_distance_internal hfar

/-- A separated finite code induces pairwise-disjoint decoding balls below
half its minimum distance.
@isnad1 id=pairwise.2h4v.s5.77c7a3499c7c from=translated src=- shape=1b8af56b vocab=189e5143
-/
theorem pairwiseDisjoint_balls_of_isSeparated
    {length minimumDistance radius : ℕ} {code : Finset (Word length)}
    (hcode : IsSeparated code minimumDistance)
    (hradius : 2 * radius < minimumDistance) :
    (code : Set (Word length)).PairwiseDisjoint fun center =>
      ball center radius :=
  pairwiseDisjoint_balls_of_isSeparated_internal hcode hradius

/-- Finite Boolean Hamming packing bound.
@isnad1 id=le.2h4v.s6.0c92c6c1762f from=translated src=- shape=3ee295a7 vocab=ebd6620f
-/
theorem packing_bound
    {length minimumDistance radius : ℕ} {code : Finset (Word length)}
    (hcode : IsSeparated code minimumDistance)
    (hradius : 2 * radius < minimumDistance) :
    code.card * volume length radius ≤ 2 ^ length :=
  packing_bound_internal hcode hradius

end BooleanHamming

end Complexity
