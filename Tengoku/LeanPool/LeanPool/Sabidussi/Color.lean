/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/
module

public import Tengoku

/-!
# The four colours used in the Sabidussi proof

This file contains the elementary algebra over `F₂²` used by the proof. We use an explicit
product so that the three admissible local frames can be given by concrete formulas.
-/

@[expose] public section

namespace Sabidussi

open scoped BigOperators

/-- The field with two elements. -/
abbrev F₂ := ZMod 2

/-- The four-element colour space. -/
abbrev Color := F₂ × F₂

/--
@isnad1 id=eq.0h1v.s5.f1d887ac7c67 from=translated src=- shape=1347b6cc vocab=e45bf785
-/
@[simp]
theorem F₂_add_self (x : F₂) : x + x = 0 := ZModModule.add_self x

/--
@isnad1 id=eq.0h1v.s6.c3e8af92532d from=translated src=- shape=1347b6cc vocab=6fd6f044
-/
@[simp]
theorem color_add_self (x : Color) : x + x = 0 := by
  ext <;> simp

/--
@isnad1 id=eq.0h2v.s6.8786c45f69fe from=translated src=- shape=0a5e0eb3 vocab=e45bf785
-/
theorem F₂_add_shuffle (a b : F₂) : a + (b + (a + b)) = 0 := by
  calc
    a + (b + (a + b)) = (a + a) + (b + b) := by abel
    _ = 0 := by simp

/-- The alternating form polarizing `quadratic`. -/
def bracket (x y : Color) : F₂ := x.1 * y.2 + x.2 * y.1

/-- The quadratic form detecting the colour `(1, 1)`. -/
def quadratic (x : Color) : F₂ := x.1 * x.2

/--
@isnad1 id=eq.0h2v.s6.053a432d42f4 from=translated src=- shape=15af9b1f vocab=4892618e
-/
@[simp]
theorem bracket_apply (x y : Color) : bracket x y = x.1 * y.2 + x.2 * y.1 := rfl

/--
@isnad1 id=eq.0h1v.s5.2d064886a39b from=translated src=- shape=a847ef84 vocab=26b8455f
-/
@[simp]
theorem quadratic_apply (x : Color) : quadratic x = x.1 * x.2 := rfl

/--
@isnad1 id=eq.0h1v.s6.65c9cc2ce5ab from=translated src=- shape=d7485c18 vocab=587b5347
-/
theorem bracket_zero_left (x : Color) : bracket 0 x = 0 := by
  simp [bracket]

/--
@isnad1 id=eq.0h1v.s6.43203b056101 from=translated src=- shape=8fc7241c vocab=587b5347
-/
theorem bracket_zero_right (x : Color) : bracket x 0 = 0 := by
  simp [bracket]

/--
@isnad1 id=eq.0h3v.s6.382d3b434391 from=translated src=- shape=086cad00 vocab=4ab0e444
-/
theorem bracket_add_left (x y z : Color) :
    bracket (x + y) z = bracket x z + bracket y z := by
  simp only [bracket, Prod.fst_add, Prod.snd_add]
  ring

/--
@isnad1 id=eq.0h3v.s6.51ea70153a87 from=translated src=- shape=50a03441 vocab=4ab0e444
-/
theorem bracket_add_right (x y z : Color) :
    bracket x (y + z) = bracket x y + bracket x z := by
  simp only [bracket, Prod.fst_add, Prod.snd_add]
  ring

/-- Bracketing with a fixed left argument, as an additive homomorphism. -/
def bracketRightHom (x : Color) : Color →+ F₂ where
  toFun := bracket x
  map_zero' := bracket_zero_right x
  map_add' := bracket_add_right x

/--
@isnad1 id=eq.0h2v.s7.fd2b3aa9f850 from=translated src=- shape=cadf4f78 vocab=51761572
-/
@[simp]
theorem bracketRightHom_apply (x y : Color) : bracketRightHom x y = bracket x y := rfl

/--
@isnad1 id=eq.0h3v.s6.d4991b2995a7 from=translated src=- shape=37ed2936 vocab=831207d0
-/
theorem sum_bracket_right {I : Type*} [Fintype I] (x : Color) (f : I → Color) :
    ∑ i, bracket x (f i) = bracket x (∑ i, f i) := by
  change ∑ i, bracketRightHom x (f i) = bracketRightHom x (∑ i, f i)
  exact (map_sum (bracketRightHom x) f Finset.univ).symm

/--
@isnad1 id=eq.0h2v.s3.d0742d692364 from=translated src=- shape=ab795eaa vocab=614bad1b
-/
theorem bracket_comm (x y : Color) : bracket x y = bracket y x := by
  simp [bracket, add_comm, mul_comm]

/--
@isnad1 id=eq.0h1v.s4.01acb3bce35d from=translated src=- shape=34c957ae vocab=587b5347
-/
theorem bracket_self (x : Color) : bracket x x = 0 := by
  simp [bracket, mul_comm]

/--
@isnad1 id=eq.0h2v.s6.8f3ec38ea782 from=translated src=- shape=0b0cbe16 vocab=e9fa6e12
-/
theorem quadratic_add (x y : Color) :
    quadratic (x + y) = quadratic x + quadratic y + bracket x y := by
  simp only [quadratic, bracket, Prod.fst_add, Prod.snd_add]
  ring

/-- The three locally admissible difference vectors at a 6-valent vertex. -/
def tripleDifference (t : Color) : Fin 3 → Color
  | ⟨0, _⟩ => t
  | ⟨1, _⟩ => (t.2, t.1 + t.2)
  | ⟨2, _⟩ => (t.1 + t.2, t.1)

/--
@isnad1 id=eq.0h1v.s4.b0965cad8cf9 from=translated src=- shape=e4549ac5 vocab=9fe56d68
-/
@[simp]
theorem tripleDifference_zero (t : Color) : tripleDifference t 0 = t := rfl

/--
@isnad1 id=eq.0h1v.s5.b89b53a718c2 from=translated src=- shape=31467c6d vocab=a102409d
-/
@[simp]
theorem tripleDifference_one (t : Color) :
    tripleDifference t 1 = (t.2, t.1 + t.2) := rfl

/--
@isnad1 id=eq.0h1v.s5.31cb7bb88365 from=translated src=- shape=04ea9261 vocab=a102409d
-/
@[simp]
theorem tripleDifference_two (t : Color) :
    tripleDifference t 2 = (t.1 + t.2, t.1) := rfl

/--
@isnad1 id=eq.0h1v.s6.cc44eb2f7066 from=translated src=- shape=ca0e76f9 vocab=76e2144a
-/
theorem sum_tripleDifference (t : Color) : ∑ i, tripleDifference t i = 0 := by
  rw [Fin.sum_univ_three]
  change t + (t.2, t.1 + t.2) + (t.1 + t.2, t.1) = 0
  ext
  · change t.1 + t.2 + (t.1 + t.2) = 0
    exact F₂_add_self (t.1 + t.2)
  · change t.2 + (t.1 + t.2) + t.1 = 0
    calc
      t.2 + (t.1 + t.2) + t.1 = (t.1 + t.1) + (t.2 + t.2) := by abel
      _ = 0 := by simp

/--
@isnad1 id=ne.1h2v.s6.dbd95e5c4319 from=translated src=- shape=5b993987 vocab=53583cb6
-/
theorem tripleDifference_ne_zero (t : Color) (ht : t ≠ 0) (i : Fin 3) :
    tripleDifference t i ≠ 0 := by
  fin_cases i
  · simpa using ht
  · intro h
    apply ht
    rcases Prod.mk_eq_zero.mp h with ⟨h₂, hsum⟩
    ext
    · simpa [h₂] using hsum
    · exact h₂
  · intro h
    apply ht
    rcases Prod.mk_eq_zero.mp h with ⟨hsum, h₁⟩
    ext
    · exact h₁
    · simpa [h₁] using hsum

/-- At a 4-valent vertex the two local differences coincide. -/
def doubleDifference (t : Color) : Fin 2 → Color
  | ⟨0, _⟩ => t
  | ⟨1, _⟩ => t

/--
@isnad1 id=eq.0h1v.s6.187aa6d944b7 from=translated src=- shape=ca0e76f9 vocab=c95dda19
-/
theorem sum_doubleDifference (t : Color) : ∑ i, doubleDifference t i = 0 := by
  rw [Fin.sum_univ_two]
  exact color_add_self t

/--
@isnad1 id=ne.1h2v.s6.fe74449899ca from=translated src=- shape=5b993987 vocab=a11bae0a
-/
theorem doubleDifference_ne_zero (t : Color) (ht : t ≠ 0) (i : Fin 2) :
    doubleDifference t i ≠ 0 := by
  fin_cases i <;> exact ht

/-- The local quadratic contribution from two equal nonzero differences vanishes.
@isnad1 id=eq.0h1v.s7.f4de585f05d2 from=translated src=- shape=9519f1f7 vocab=ce40c51c
-/
theorem double_local_quadratic (t : Color) :
    (∑ i, quadratic (doubleDifference t i)) +
      (∑ i, ∑ j,
        if j < i then bracket (doubleDifference t i) (doubleDifference t j) else 0) = 0 := by
  simp only [Fin.sum_univ_two, doubleDifference, quadratic, bracket]
  norm_num
  ring_nf
  rw [show (2 : F₂) = 0 from ZMod.natCast_self 2]
  simp

/-- The local quadratic contribution from the three `tripleDifference`s vanishes.
@isnad1 id=eq.0h1v.s7.e99fe6a35d5c from=translated src=- shape=9519f1f7 vocab=deff511e
-/
theorem triple_local_quadratic (t : Color) :
    (∑ i, quadratic (tripleDifference t i)) +
      (∑ i, ∑ j,
        if j < i then bracket (tripleDifference t i) (tripleDifference t j) else 0) = 0 := by
  simp only [Fin.sum_univ_three, tripleDifference, quadratic, bracket]
  split_ifs <;> try omega
  ring_nf
  rw [show (8 : F₂) = 0 from (show Even 8 by exact ⟨4, rfl⟩).natCast_zmod_two,
    show (4 : F₂) = 0 from (show Even 4 by exact ⟨2, rfl⟩).natCast_zmod_two]
  simp

end Sabidussi
