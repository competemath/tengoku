/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Tengoku

/-!
# LeanPool.EcTateLean.Algebra.CharP.Basic

Imported Lean Pool material for `LeanPool.EcTateLean.Algebra.CharP.Basic`.
-/

@[expose] public section

/--
@isnad1 id=or.0h1v.s5.435a6a99961d from=translated src=- shape=fbc3e758 vocab=45ece501
-/
lemma ringChar_is_zero_or_prime (R : Type _) [NonAssocSemiring R] [NoZeroDivisors R]
    [Nontrivial R] : ringChar R = 0 ∨ Nat.Prime (ringChar R) :=
  (CharP.char_is_prime_or_zero R (ringChar R)).symm

/--
@isnad1 id=eq.1h3v.s7.99b0561191ce from=translated src=- shape=7b231323 vocab=8b61bde9
-/
lemma add_pow_ringChar {R : Type _} [CommRing R] [IsDomain R] (a b : R) (h : ringChar R ≠ 0) :
    (a + b) ^ ringChar R =
    a ^ ringChar R +
    b ^ ringChar R := by
  have : NeZero (ringChar R) := ⟨h⟩
  have : CharP R (ringChar R) := ringChar.charP R
  have : Fact (Nat.Prime (ringChar R)) := CharP.char_is_prime_of_pos R (ringChar R)
  exact add_pow_char a b (ringChar R)

/--
@isnad1 id=eq.1h3v.s7.8f6d500cdd35 from=translated src=- shape=7b231323 vocab=2d0581ae
-/
lemma sub_pow_ringChar {R : Type _} [CommRing R] [IsDomain R] (a b : R) (h : ringChar R ≠ 0) :
    (a - b) ^ ringChar R =
    a ^ ringChar R -
    b ^ ringChar R := by
  have : NeZero (ringChar R) := ⟨h⟩
  have : CharP R (ringChar R) := ringChar.charP R
  have : Fact (Nat.Prime (ringChar R)) := CharP.char_is_prime_of_pos R (ringChar R)
  exact sub_pow_char a b

/--
@isnad1 id=injectiv.1h1v.s5.9ce3ff1c0960 from=translated src=- shape=1d9e1791 vocab=aff0d674
-/
lemma pow_ringChar_injective {R : Type _} [CommRing R] [IsDomain R]
    (hn : ringChar R ≠ 0) : Function.Injective (· ^ ringChar R : R → R) := by
  intros x y h
  rw [← sub_eq_zero] at h ⊢
  rw [← sub_pow_ringChar _ _ hn] at h
  exact (pow_eq_zero_iff hn).mp h
