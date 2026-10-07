/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.FreeAlgebra
public import Tengoku.Seed.SetTheory.Cardinal.Free

import Tengoku.Seed.Algebra.MonoidAlgebra.Cardinal

/-!
# Cardinality of free algebras

This file contains some results about the cardinality of `FreeAlgebra`,
parallel to that of `MvPolynomial`.
-/

public section

universe u v

variable (R : Type u) [CommSemiring R]

open Cardinal

namespace FreeAlgebra

variable (X : Type v)

/--
@isnad1 id=eq.0h2v.s5.600afa7f79e2 from=seed src=0 shape=033598fd vocab=10e7cb03
-/
@[simp]
theorem cardinalMk_eq_max_lift [Nonempty X] [Nontrivial R] :
    #(FreeAlgebra R X) = Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #X ⊔ ℵ₀ := by
  have hX := mk_freeMonoid X
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq,
    MonoidAlgebra.cardinalMk_eq_max_lift_of_infinite, hX, lift_max, lift_aleph0, sup_assoc]

/--
@isnad1 id=eq.0h2v.s4.cde74f480972 from=seed src=0 shape=aed74b54 vocab=e2d0090c
-/
@[simp]
theorem cardinalMk_eq_lift [IsEmpty X] : #(FreeAlgebra R X) = Cardinal.lift.{v} #R := by
  simp [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq,
    MonoidAlgebra.cardinalMk_eq_lift_of_fintype]

/--
@isnad1 id=eq.0h2v.s4.ed8468de9a6c from=seed src=0 shape=9f25e614 vocab=489967d9
-/
@[nontriviality]
theorem cardinalMk_eq_one [Subsingleton R] : #(FreeAlgebra R X) = 1 := by
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq, mk_eq_one]

/--
@isnad1 id=le.0h2v.s5.54ccd43e6bc9 from=seed src=0 shape=2df494c0 vocab=55a2a226
-/
theorem cardinalMk_le_max_lift :
    #(FreeAlgebra R X) ≤ Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #X ⊔ ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (cardinalMk_eq_one R X).trans_le (le_max_of_le_right one_le_aleph0)
  cases isEmpty_or_nonempty X
  · exact (cardinalMk_eq_lift R X).trans_le (le_max_of_le_left <| le_max_left _ _)
  · exact (cardinalMk_eq_max_lift R X).le

variable (X : Type u)

/--
@isnad1 id=eq.0h2v.s5.54f543977c95 from=seed src=0 shape=5deacb92 vocab=4333fa51
-/
theorem cardinalMk_eq_max [Nonempty X] [Nontrivial R] : #(FreeAlgebra R X) = #R ⊔ #X ⊔ ℵ₀ := by
  simp

/--
@isnad1 id=eq.0h2v.s4.53ea86fc2bfd from=seed src=0 shape=7f14c476 vocab=70056668
-/
theorem cardinalMk_eq [IsEmpty X] : #(FreeAlgebra R X) = #R := by
  simp

/--
@isnad1 id=le.0h2v.s5.c6275a55cac5 from=seed src=0 shape=f7190c0f vocab=c3cd7675
-/
theorem cardinalMk_le_max : #(FreeAlgebra R X) ≤ #R ⊔ #X ⊔ ℵ₀ := by
  simpa using cardinalMk_le_max_lift R X

end FreeAlgebra

namespace Algebra

/--
@isnad1 id=le.0h3v.s6.5ac4866246d3 from=seed src=0 shape=11e0c4d9 vocab=1c652ebf
-/
theorem lift_cardinalMk_adjoin_le {A : Type v} [Semiring A] [Algebra R A] (s : Set A) :
    lift.{u} #(adjoin R s) ≤ lift.{v} #R ⊔ lift.{u} #s ⊔ ℵ₀ := by
  have H := mk_range_le_lift (f := FreeAlgebra.lift R ((↑) : s → A))
  rw [lift_umax, lift_id'.{v, u}] at H
  rw [Algebra.adjoin_eq_range_freeAlgebra_lift]
  exact H.trans (FreeAlgebra.cardinalMk_le_max_lift R s)

/--
@isnad1 id=le.0h3v.s6.8599fe96eaed from=seed src=0 shape=e66407ce vocab=b6605e3c
-/
theorem cardinalMk_adjoin_le {A : Type u} [Semiring A] [Algebra R A] (s : Set A) :
    #(adjoin R s) ≤ #R ⊔ #s ⊔ ℵ₀ := by
  simpa using lift_cardinalMk_adjoin_le R s

end Algebra
