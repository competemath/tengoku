/-
Copyright (c) 2026 Jon Bannon, Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Monica Omar
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.CStarAlgebra.Basic

/-! # Unitary maps in C⋆-algebras

This file defines some basic maps by unitaries in C⋆-algebras. -/

@[expose] public section

namespace Unitary
variable {R A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [Ring R] [Module R A]

section mulLeft
variable [SMulCommClass R A A]

set_option backward.isDefEq.respectTransparency false in
variable (R A) in
/-- Left multiplication by a unitary as a linear isometric equivalence. -/
noncomputable def mulLeft : unitary A →* A ≃ₗᵢ[R] A where
  toFun u :=
    { __ := (toUnits u).mulLeftLinearEquiv R A
      norm_map' _ := CStarRing.norm_coe_unitary_mul _ _ }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

variable (R) in
/--
@isnad1 id=eq.0h4v.s10.7062656c9551 from=seed src=0 shape=0309b3b5 vocab=f6b04f50
-/
@[simp] lemma mulLeft_apply (u : unitary A) (x : A) :
    mulLeft R A u x = u * x := rfl

variable (R) in
/--
@isnad1 id=eq.0h4v.s10.915c1cb34e19 from=seed src=0 shape=f3def527 vocab=979b097b
-/
lemma symm_mulLeft_apply (u : unitary A) (x : A) :
    (mulLeft R A u).symm x = (star u : A) * x := rfl

/--
@isnad1 id=eq.0h3v.s11.84b6472a33d9 from=seed src=0 shape=d4248263 vocab=aa78b64a
-/
@[simp] lemma symm_mulLeft (u : unitary A) :
    (mulLeft R A u).symm = mulLeft R A (star u) := by ext; rfl

/--
@isnad1 id=eq.0h4v.s11.a494fdf8ab35 from=seed src=0 shape=706faf9b vocab=320ddcc6
-/
lemma mulLeft_trans_mulLeft (u v : unitary A) :
    (mulLeft R A u).trans (mulLeft R A v) = mulLeft R A (v * u) := map_mul _ _ _ |>.symm

/--
@isnad1 id=eq.0h5v.s11.a25a08bc5268 from=seed src=0 shape=7f11f070 vocab=db8a789f
-/
lemma mulLeft_mul_apply (u v : unitary A) (x : A) :
    mulLeft R A (u * v) x = mulLeft R A u (mulLeft R A v x) := by simp

/--
@isnad1 id=eq.0h3v.s11.18e75b440273 from=seed src=0 shape=566058c8 vocab=19910171
-/
@[simp] lemma toLinearEquiv_mulLeft (u : unitary A) :
    (mulLeft R A u).toLinearEquiv = (toUnits u).mulLeftLinearEquiv R A := rfl

end mulLeft

section mulRight
variable [IsScalarTower R A A]

variable (R) in
/-- Right multiplication by a unitary as a linear isometric equivalence. -/
noncomputable def mulRight (u : unitary A) : A ≃ₗᵢ[R] A where
  toLinearEquiv := (toUnits u).mulRightLinearEquiv R
  norm_map' _ := CStarRing.norm_mul_coe_unitary _ _

variable (R) in
/--
@isnad1 id=eq.0h4v.s8.19be811c0391 from=seed src=0 shape=94b83512 vocab=7359b5f4
-/
@[simp] lemma mulRight_apply (u : unitary A) (x : A) :
    mulRight R u x = x * u := rfl

variable (R) in
/--
@isnad1 id=eq.0h4v.s9.07daad4a0859 from=seed src=0 shape=91037eb3 vocab=67be85e8
-/
lemma symm_mulRight_apply (u : unitary A) (x : A) :
    (mulRight R u).symm x = x * (star u : A) := rfl

/--
@isnad1 id=eq.0h3v.s8.831fc290bf77 from=seed src=0 shape=b687e915 vocab=61905d8c
-/
@[simp] lemma symm_mulRight (u : unitary A) :
    (mulRight R u).symm = mulRight R (star u) := by
  ext; rfl

/--
@isnad1 id=eq.0h4v.s9.636064083079 from=seed src=0 shape=14a394b5 vocab=aa271918
-/
lemma mulRight_trans_mulRight (u v : unitary A) :
    (mulRight R u).trans (mulRight R v) = mulRight R (u * v) := by ext; simp [mul_assoc]

/--
@isnad1 id=eq.0h5v.s10.10aa1244fdfe from=seed src=0 shape=478737cd vocab=c28c4662
-/
lemma mulRight_mul_apply (u v : unitary A) (x : A) :
    mulRight R (u * v) x = mulRight R v (mulRight R u x) := by simp [mul_assoc]

/--
@isnad1 id=eq.0h3v.s8.47740881d4a4 from=seed src=0 shape=c16aef93 vocab=a09bcaf0
-/
lemma toLinearMap_mulRight (u : unitary A) :
    (mulRight R u).toLinearMap = LinearMap.mulRight R (u : A) := rfl

/--
@isnad1 id=eq.0h2v.s8.247abca2be1f from=seed src=0 shape=e32e9ea3 vocab=91ed89e7
-/
@[simp] lemma mulRight_one : mulRight R 1 = .refl R A := by
  ext; simp

/--
@isnad1 id=eq.0h3v.s9.fa962ce0eb1c from=seed src=0 shape=86428ecd vocab=255b4712
-/
@[simp] lemma toLinearEquiv_mulRight (u : unitary A) :
    (mulRight R u).toLinearEquiv = (toUnits u).mulRightLinearEquiv R := rfl

end mulRight

end Unitary
