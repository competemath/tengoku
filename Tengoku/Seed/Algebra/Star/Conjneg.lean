/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.BigOperators.Pi
public import Tengoku.Seed.Algebra.Star.Pi
public import Tengoku.Seed.Algebra.Group.Pointwise.Set.Basic

/-!
# Conjugation-negation operator

This file defines the conjugation-negation operator, useful in Fourier analysis.

The way this operator enters the picture is that the adjoint of convolution with a function `f` is
convolution with `conjneg f`.
-/

@[expose] public section

open Function
open scoped ComplexConjugate

variable {ι G R : Type*} [AddGroup G]

section CommSemiring
variable [CommSemiring R] [StarRing R] {f g : G → R}

/-- Conjugation-negation. Sends `f` to `fun x ↦ conj (f (-x))`. -/
def conjneg (f : G → R) : G → R := conj fun x ↦ f (-x)

/--
@isnad1 id=eq.0h4v.s6.6dabe1fbf142 from=seed src=0 shape=94126746 vocab=94c1c86a
-/
@[simp] lemma conjneg_apply (f : G → R) (x : G) : conjneg f x = conj (f (-x)) := rfl
/--
@isnad1 id=eq.0h3v.s5.cb32058e149a from=seed src=0 shape=652fd2eb vocab=8cf38a14
-/
@[simp] lemma conjneg_conjneg (f : G → R) : conjneg (conjneg f) = f := by ext; simp

/--
@isnad1 id=involuti.0h2v.s4.ef08a44a326e from=seed src=0 shape=14740304 vocab=b7fd9555
-/
lemma conjneg_involutive : Involutive (conjneg : (G → R) → G → R) := conjneg_conjneg
/--
@isnad1 id=bijectiv.0h2v.s5.8d2c562471a0 from=seed src=0 shape=e272e2dd vocab=76c250ea
-/
lemma conjneg_bijective : Bijective (conjneg : (G → R) → G → R) := conjneg_involutive.bijective
/--
@isnad1 id=injectiv.0h2v.s5.5be895ab7f13 from=seed src=0 shape=e272e2dd vocab=4f957979
-/
lemma conjneg_injective : Injective (conjneg : (G → R) → G → R) := conjneg_involutive.injective
/--
@isnad1 id=surjecti.0h2v.s5.742a1a7b680a from=seed src=0 shape=e272e2dd vocab=f3e48105
-/
lemma conjneg_surjective : Surjective (conjneg : (G → R) → G → R) := conjneg_involutive.surjective

/--
@isnad1 id=iff.0h4v.s5.a7120def6738 from=seed src=0 shape=5adbbae0 vocab=8cf38a14
-/
@[simp] lemma conjneg_inj : conjneg f = conjneg g ↔ f = g := conjneg_injective.eq_iff
/--
@isnad1 id=iff.0h4v.s5.796978ae1e47 from=seed src=0 shape=5adbbae0 vocab=8cf38a14
-/
lemma conjneg_ne_conjneg : conjneg f ≠ conjneg g ↔ f ≠ g := conjneg_injective.ne_iff

/--
@isnad1 id=eq.0h3v.s8.842b4e9fc664 from=seed src=0 shape=54a77001 vocab=c9174f0d
-/
@[simp] lemma conjneg_conj (f : G → R) : conjneg (conj f) = conj (conjneg f) := rfl

/--
@isnad1 id=eq.0h2v.s6.7c4bb41cfbeb from=seed src=0 shape=d1b26266 vocab=8cf38a14
-/
@[simp] lemma conjneg_zero : conjneg (0 : G → R) = 0 := by ext; simp
/--
@isnad1 id=eq.0h2v.s6.b7ea09be7069 from=seed src=0 shape=d1b26266 vocab=8cf38a14
-/
@[simp] lemma conjneg_one : conjneg (1 : G → R) = 1 := by ext; simp
/--
@isnad1 id=eq.0h4v.s6.61583432e5df from=seed src=0 shape=81dd6cc7 vocab=32b74228
-/
@[simp] lemma conjneg_add (f g : G → R) : conjneg (f + g) = conjneg f + conjneg g := by ext; simp
/--
@isnad1 id=eq.0h4v.s6.80e4a54cadf8 from=seed src=0 shape=81dd6cc7 vocab=49037bcb
-/
@[simp] lemma conjneg_mul (f g : G → R) : conjneg (f * g) = conjneg f * conjneg g := by ext; simp

/--
@isnad1 id=eq.0h5v.s6.6c991c3e64f0 from=seed src=0 shape=0dd5015f vocab=43ea3165
-/
@[simp] lemma conjneg_sum (s : Finset ι) (f : ι → G → R) :
    conjneg (∑ i ∈ s, f i) = ∑ i ∈ s, conjneg (f i) := by ext; simp

/--
@isnad1 id=eq.0h5v.s6.67db010bdf77 from=seed src=0 shape=0dd5015f vocab=9fb84bae
-/
@[simp] lemma conjneg_prod (s : Finset ι) (f : ι → G → R) :
    conjneg (∏ i ∈ s, f i) = ∏ i ∈ s, conjneg (f i) := by ext; simp

/--
@isnad1 id=iff.0h3v.s6.a11edfcb5378 from=seed src=0 shape=0d58c814 vocab=8cf38a14
-/
@[simp] lemma conjneg_eq_zero : conjneg f = 0 ↔ f = 0 := by
  rw [← conjneg_inj, conjneg_conjneg, conjneg_zero]

/--
@isnad1 id=iff.0h3v.s6.cf7f2ec442b1 from=seed src=0 shape=0d58c814 vocab=8cf38a14
-/
@[simp] lemma conjneg_eq_one : conjneg f = 1 ↔ f = 1 := by
  rw [← conjneg_inj, conjneg_conjneg, conjneg_one]

/--
@isnad1 id=iff.0h3v.s6.f5b52ae968bb from=seed src=0 shape=0d58c814 vocab=8cf38a14
-/
lemma conjneg_ne_zero : conjneg f ≠ 0 ↔ f ≠ 0 := conjneg_eq_zero.not
/--
@isnad1 id=iff.0h3v.s6.453c99064a5c from=seed src=0 shape=0d58c814 vocab=8cf38a14
-/
lemma conjneg_ne_one : conjneg f ≠ 1 ↔ f ≠ 1 := conjneg_eq_one.not

/--
@isnad1 id=eq.0h3v.s6.ea4a3cda05ac from=seed src=0 shape=d12a4f06 vocab=58f5f45d
-/
lemma sum_conjneg [Fintype G] (f : G → R) : ∑ a, conjneg f a = ∑ a, conj (f a) :=
  Fintype.sum_equiv (Equiv.neg _) _ _ fun _ ↦ rfl

/--
@isnad1 id=eq.0h3v.s6.70d4ec3852c5 from=seed src=0 shape=52ef2ac5 vocab=780fba67
-/
@[simp] lemma support_conjneg (f : G → R) : support (conjneg f) = -support f := by
  ext; simp [starRingEnd_apply]

/-- `conjneg` bundled as a ring homomorphism. -/
@[simps] def conjnegRingHom : (G → R) →+* (G → R) where
  toFun := conjneg
  map_zero' := conjneg_zero
  map_one' := conjneg_one
  map_add' := conjneg_add
  map_mul' := conjneg_mul

end CommSemiring

section CommRing
variable [CommRing R] [StarRing R]

/--
@isnad1 id=eq.0h4v.s6.5a6496d67368 from=seed src=0 shape=81dd6cc7 vocab=20f0cd33
-/
@[simp] lemma conjneg_sub (f g : G → R) : conjneg (f - g) = conjneg f - conjneg g := by ext; simp
/--
@isnad1 id=eq.0h3v.s6.d8d35bcc99e3 from=seed src=0 shape=3499288d vocab=fa4b348b
-/
@[simp] lemma conjneg_neg (f : G → R) : conjneg (-f) = -conjneg f := by ext; simp

end CommRing
