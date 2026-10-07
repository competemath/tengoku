/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.DirectSum.Algebra
public import Tengoku.Seed.Algebra.MonoidAlgebra.Basic
public import Tengoku.Seed.Data.Finsupp.ToDFinsupp

/-!
# Conversion between `AddMonoidAlgebra` and homogeneous `DirectSum`

This module provides conversions between `AddMonoidAlgebra` and `DirectSum`.
The latter is essentially a dependent version of the former.

Note that since `DirectSum.instMul` combines indices additively, there is no equivalent to
`MonoidAlgebra`.

## Main definitions

* `AddMonoidAlgebra.toDirectSum : AddMonoidAlgebra M ι → (⨁ i : ι, M)`
* `DirectSum.toAddMonoidAlgebra : (⨁ i : ι, M) → AddMonoidAlgebra M ι`
* Bundled equiv versions of the above:
  * `addMonoidAlgebraEquivDirectSum : AddMonoidAlgebra M ι ≃ (⨁ i : ι, M)`
  * `addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ (⨁ i : ι, M)`
  * `addMonoidAlgebraRingEquivDirectSum R : AddMonoidAlgebra M ι ≃+* (⨁ i : ι, M)`
  * `addMonoidAlgebraAlgEquivDirectSum R : AddMonoidAlgebra A ι ≃ₐ[R] (⨁ i : ι, A)`

## Theorems

The defining feature of these operations is that they map `AddMonoidAlgebra.single` to
`DirectSum.of` and vice versa:

* `AddMonoidAlgebra.toDirectSum_single`
* `DirectSum.toAddMonoidAlgebra_of`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to
`AddMonoidAlgebra.toDirectSum`:

* `addMonoidAlgebraAddEquivDirectSum_apply`
* `add_monoid_algebra_lequiv_direct_sum_apply`
* `addMonoidAlgebraAddEquivDirectSum_symm_apply`
* `add_monoid_algebra_lequiv_direct_sum_symm_apply`

## Implementation notes

This file largely just copies the API of `Mathlib/Data/Finsupp/ToDFinsupp.lean`, and reuses the
proofs. Recall that `AddMonoidAlgebra M ι` is defeq to `ι →₀ M` and `⨁ i : ι, M` is defeq to
`Π₀ i : ι, M`.
-/

@[expose] public section


variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

open DirectSum

/-! ### Basic definitions and lemmas -/


section Defs

/-- Interpret an `AddMonoidAlgebra` as a homogeneous `DirectSum`. -/
def AddMonoidAlgebra.toDirectSum [Semiring M] (f : AddMonoidAlgebra M ι) : ⨁ _ : ι, M :=
  f.coeff.toDFinsupp

section

variable [DecidableEq ι] [Semiring M]

/--
@isnad1 id=eq.0h4v.s7.a902af95363c from=seed src=0 shape=d8c731b1 vocab=99a07841
-/
@[simp]
lemma AddMonoidAlgebra.toDirectSum_single (i : ι) (m : M) : toDirectSum (single i m) = .of _ i m :=
  Finsupp.toDFinsupp_single i m

variable [∀ m : M, Decidable (m ≠ 0)]

/-- Interpret a homogeneous `DirectSum` as an `AddMonoidAlgebra`. -/
def DirectSum.toAddMonoidAlgebra (f : ⨁ _ : ι, M) : AddMonoidAlgebra M ι := .ofCoeff f.toFinsupp

/--
@isnad1 id=eq.0h4v.s7.b8af5b2d319a from=seed src=0 shape=8ed06e3e vocab=7b44546d
-/
@[simp]
theorem DirectSum.toAddMonoidAlgebra_of (i : ι) (m : M) :
    (DirectSum.of _ i m : ⨁ _ : ι, M).toAddMonoidAlgebra = .single i m := by
  ext : 1; exact DFinsupp.toFinsupp_single i m

/--
@isnad1 id=eq.0h3v.s5.6e1401aa90df from=seed src=0 shape=4944d3fc vocab=9e17412c
-/
@[simp]
theorem AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra (f : AddMonoidAlgebra M ι) :
    f.toDirectSum.toAddMonoidAlgebra = f := by ext : 1; exact Finsupp.toDFinsupp_toFinsupp _

/--
@isnad1 id=eq.0h3v.s5.7fb904879a05 from=seed src=0 shape=2dd03241 vocab=cc7de62f
-/
@[simp]
theorem DirectSum.toAddMonoidAlgebra_toDirectSum (f : ⨁ _ : ι, M) :
    f.toAddMonoidAlgebra.toDirectSum = f :=
  (DFinsupp.toFinsupp_toDFinsupp (show Π₀ _ : ι, M from f) :)

end

end Defs

/-! ### Lemmas about arithmetic operations -/


section Lemmas

namespace AddMonoidAlgebra

/--
@isnad1 id=eq.0h2v.s7.e8990b60244d from=seed src=0 shape=8c53eae3 vocab=4b7d3e2f
-/
@[simp]
theorem toDirectSum_zero [Semiring M] : (0 : AddMonoidAlgebra M ι).toDirectSum = 0 :=
  Finsupp.toDFinsupp_zero

/--
@isnad1 id=eq.0h4v.s7.f373051a54ca from=seed src=0 shape=dee93ef2 vocab=10cd2967
-/
@[simp]
theorem toDirectSum_add [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f + g).toDirectSum = f.toDirectSum + g.toDirectSum :=
  Finsupp.toDFinsupp_add _ _

/--
@isnad1 id=eq.0h3v.s6.e83e440f5420 from=seed src=0 shape=9c225c19 vocab=c8bfb570
-/
@[simp]
theorem toDirectSum_natCast [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : ℕ) :
    (n : AddMonoidAlgebra M ι).toDirectSum = n :=
  Finsupp.toDFinsupp_single _ _

/--
@isnad1 id=eq.0h3v.s6.8215a2e4dab1 from=seed src=0 shape=ecd8b29b vocab=ca239bee
-/
@[simp]
theorem toDirectSum_ofNat [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : AddMonoidAlgebra M ι).toDirectSum = ofNat(n) :=
  Finsupp.toDFinsupp_single _ _

/--
@isnad1 id=eq.0h4v.s7.82ed370dc96e from=seed src=0 shape=dee93ef2 vocab=f975714e
-/
@[simp]
theorem toDirectSum_sub [Ring M] (f g : AddMonoidAlgebra M ι) :
    (f - g).toDirectSum = f.toDirectSum - g.toDirectSum :=
  Finsupp.toDFinsupp_sub _ _

/--
@isnad1 id=eq.0h3v.s7.fe0b19914f46 from=seed src=0 shape=886b9643 vocab=49e84a86
-/
@[simp]
theorem toDirectSum_neg [Ring M] (f : AddMonoidAlgebra M ι) :
    (-f).toDirectSum = - f.toDirectSum :=
  Finsupp.toDFinsupp_neg _

/--
@isnad1 id=eq.0h3v.s6.1209a36689f0 from=seed src=0 shape=9c225c19 vocab=f8d570ed
-/
@[simp]
theorem toDirectSum_intCast [DecidableEq ι] [AddMonoid ι] [Ring M] (z : ℤ) :
    (Int.cast z : AddMonoidAlgebra M ι).toDirectSum = z :=
  Finsupp.toDFinsupp_single _ _

/--
@isnad1 id=eq.0h2v.s6.5aa2ac8afe19 from=seed src=0 shape=abfccd51 vocab=95b581cb
-/
@[simp]
theorem toDirectSum_one [DecidableEq ι] [Zero ι] [Semiring M] :
    (1 : AddMonoidAlgebra M ι).toDirectSum = 1 :=
  Finsupp.toDFinsupp_single _ _

/--
@isnad1 id=eq.0h4v.s7.6905e9b979d8 from=seed src=0 shape=2fdb687e vocab=2bee4f6c
-/
@[simp]
theorem toDirectSum_mul [DecidableEq ι] [AddMonoid ι] [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f * g).toDirectSum = f.toDirectSum * g.toDirectSum := by
  let to_hom : AddMonoidAlgebra M ι →+ ⨁ _ : ι, M :=
  { toFun := toDirectSum
    map_zero' := toDirectSum_zero
    map_add' := toDirectSum_add }
  change to_hom (f * g) = to_hom f * to_hom g
  revert f g
  rw [AddMonoidHom.map_mul_iff]
  ext xi xv yi yv : 4
  simp [to_hom, AddMonoidAlgebra.single_mul_single, DirectSum.of_mul_of]

end AddMonoidAlgebra

namespace DirectSum

variable [DecidableEq ι]

/--
@isnad1 id=eq.0h2v.s7.f3644db0f448 from=seed src=0 shape=97c54980 vocab=966c7476
-/
@[simp]
theorem toAddMonoidAlgebra_zero [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    toAddMonoidAlgebra 0 = (0 : AddMonoidAlgebra M ι) := by simp [toAddMonoidAlgebra]

/--
@isnad1 id=eq.0h4v.s7.66e633e3da22 from=seed src=0 shape=da87924b vocab=3adf7a42
-/
@[simp]
theorem toAddMonoidAlgebra_add [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f + g).toAddMonoidAlgebra = toAddMonoidAlgebra f + toAddMonoidAlgebra g := by
  ext; simp [toAddMonoidAlgebra]

/--
@isnad1 id=eq.0h3v.s6.779fa2e04706 from=seed src=0 shape=58b49792 vocab=aac76ba1
-/
@[simp]
theorem toAddMonoidAlgebra_natCast [AddMonoid ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (n : ℕ) :
    (n : ⨁ _ : ι, M).toAddMonoidAlgebra = n := by
  ext : 1; exact DFinsupp.toFinsupp_single ..

/--
@isnad1 id=eq.0h3v.s6.1d1c0c37d8e1 from=seed src=0 shape=b300e4fc vocab=e123c07e
-/
@[simp]
theorem toAddMonoidAlgebra_ofNat [AddMonoid ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] (n : ℕ)
    [n.AtLeastTwo] :
    (ofNat(n) : ⨁ _ : ι, M).toAddMonoidAlgebra = ofNat(n) :=
  toAddMonoidAlgebra_natCast _

/--
@isnad1 id=eq.0h4v.s7.cf7f045ece2c from=seed src=0 shape=da87924b vocab=656f31e7
-/
@[simp]
theorem toAddMonoidAlgebra_sub [Ring M] [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f - g).toAddMonoidAlgebra = toAddMonoidAlgebra f - toAddMonoidAlgebra g := by
  ext : 1; exact DFinsupp.toFinsupp_sub ..

/--
@isnad1 id=eq.0h3v.s7.5e55cfc9ce7d from=seed src=0 shape=08946c05 vocab=ae49ca0c
-/
@[simp]
theorem toAddMonoidAlgebra_neg [Ring M] [∀ m : M, Decidable (m ≠ 0)] (f : ⨁ _ : ι, M) :
    (-f).toAddMonoidAlgebra = -toAddMonoidAlgebra f := by
  ext : 1; exact DFinsupp.toFinsupp_neg ..

/--
@isnad1 id=eq.0h3v.s7.be2164bd0510 from=seed src=0 shape=58b49792 vocab=df8b695a
-/
@[simp]
theorem toAddMonoidAlgebra_intCast [AddMonoid ι] [Ring M] [∀ m : M, Decidable (m ≠ 0)] (z : ℤ) :
    (z : ⨁ _ : ι, M).toAddMonoidAlgebra = z := by
  ext : 1; exact DFinsupp.toFinsupp_single ..

/--
@isnad1 id=eq.0h2v.s6.763f824c280b from=seed src=0 shape=0c6dae3f vocab=d801dc6a
-/
@[simp]
theorem toAddMonoidAlgebra_one [Zero ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    (1 : ⨁ _ : ι, M).toAddMonoidAlgebra = 1 := by
  ext : 1; exact DFinsupp.toFinsupp_single ..

/--
@isnad1 id=eq.0h4v.s7.fad2a266037c from=seed src=0 shape=21e603cc vocab=024616b6
-/
@[simp]
theorem toAddMonoidAlgebra_mul [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] (f g : ⨁ _ : ι, M) :
    (f * g).toAddMonoidAlgebra = toAddMonoidAlgebra f * toAddMonoidAlgebra g := by
  apply_fun AddMonoidAlgebra.toDirectSum
  · simp
  · apply Function.LeftInverse.injective
    apply AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra

end DirectSum

end Lemmas

/-! ### Bundled `Equiv`s -/


section Equivs

/-- `AddMonoidAlgebra.toDirectSum` and `DirectSum.toAddMonoidAlgebra` together form an
equiv. -/
@[simps -fullyApplied]
def addMonoidAlgebraEquivDirectSum [DecidableEq ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    AddMonoidAlgebra M ι ≃ ⨁ _ : ι, M where
  toFun := AddMonoidAlgebra.toDirectSum
  invFun := DirectSum.toAddMonoidAlgebra

/-- The additive version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps! -fullyApplied]
def addMonoidAlgebraAddEquivDirectSum [DecidableEq ι] [Semiring M] [∀ m : M, Decidable (m ≠ 0)] :
    AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M where
  toEquiv := addMonoidAlgebraEquivDirectSum
  map_add' := AddMonoidAlgebra.toDirectSum_add

/-- The ring version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps -fullyApplied]
def addMonoidAlgebraRingEquivDirectSum [DecidableEq ι] [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] : AddMonoidAlgebra M ι ≃+* ⨁ _ : ι, M :=
  { (addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_mul' := AddMonoidAlgebra.toDirectSum_mul }

/-- The algebra version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps -fullyApplied]
def addMonoidAlgebraAlgEquivDirectSum [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A]
    [Algebra R A] [∀ m : A, Decidable (m ≠ 0)] : AddMonoidAlgebra A ι ≃ₐ[R] ⨁ _ : ι, A :=
  { (addMonoidAlgebraRingEquivDirectSum : AddMonoidAlgebra A ι ≃+* ⨁ _ : ι, A) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    commutes' := fun _r => AddMonoidAlgebra.toDirectSum_single _ _ }

/--
@isnad1 id=eq.0h4v.s7.f54c4f3db5d5 from=seed src=0 shape=8cb8beea vocab=6f59d35b
-/
@[simp]
theorem AddMonoidAlgebra.toDirectSum_pow [DecidableEq ι] [AddMonoid ι] [Semiring M]
    (f : AddMonoidAlgebra M ι) (n : ℕ) :
    (f ^ n).toDirectSum = f.toDirectSum ^ n := by
  classical exact map_pow addMonoidAlgebraRingEquivDirectSum f n

/--
@isnad1 id=eq.0h4v.s7.d72eb60c8f06 from=seed src=0 shape=fb881519 vocab=113362e0
-/
@[simp]
theorem DirectSum.toAddMonoidAlgebra_pow [DecidableEq ι] [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] (f : ⨁ _ : ι, M) (n : ℕ) :
    (f ^ n).toAddMonoidAlgebra = toAddMonoidAlgebra f ^ n := by
  exact map_pow addMonoidAlgebraRingEquivDirectSum.symm f n

end Equivs
