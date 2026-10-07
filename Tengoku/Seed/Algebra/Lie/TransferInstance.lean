/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/

module

public import Tengoku.Seed.Algebra.Lie.Basic
public import Tengoku.Seed.Algebra.Group.TransferInstance

/-!
# Transfer Lie brackets along AddEquiv, LinearEquiv and Equiv

Main definitions:
* `AddEquiv.lieRing` transferring a LieRing structure along an additive equivalence.
* `LinearEquiv.lieAlgebra` transferring a Lie algebra structure along a linear equivalence.

-/

@[expose] public section

section

variable {R M L : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LieRing L] [LieAlgebra R L]

/-- Transfer `LieRing` across an `AddEquiv` -/
protected abbrev AddEquiv.lieRing (e : M ≃+ L) : LieRing M where
  bracket x y := e.symm ⁅e x, e y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp

/--
@isnad1 id=eq.0h5v.s8.f41ae2784a4d from=seed src=0 shape=d0651abe vocab=ead6f5f2
-/
lemma AddEquiv.bracket_def (e : M ≃+ L) (x y : M) :
    letI := e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

/-- Transfer `LieAlgebra` across a `LinearEquiv` -/
protected abbrev LinearEquiv.lieAlgebra (e : M ≃ₗ[R] L) :
    letI := e.toAddEquiv.lieRing
    LieAlgebra R M :=
  letI := e.toAddEquiv.lieRing
  { lie_smul _ _ _ := by simp [AddEquiv.bracket_def] }

variable (R) in
/-- An equivalence `e : M ≃ₗ[R] L` gives a Lie algebra equivalence `M ≃ₗ⁅R⁆ L` where the Lie bracket
on `M` is the one obtained by transporting a Lie Bracket on `L` back along `e`. -/
def LinearEquiv.lieEquiv (e : M ≃ₗ[R] L) :
    letI := e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    M ≃ₗ⁅R⁆ L :=
  letI := e.toAddEquiv.lieRing
  letI := e.lieAlgebra
  { e with map_lie' := by simp [AddEquiv.bracket_def] }

/--
@isnad1 id=eq.0h5v.s8.3cbcf500b7ee from=seed src=0 shape=55dc005f vocab=cafb091d
-/
@[simp]
lemma LinearEquiv.lieEquiv_apply (e : M ≃ₗ[R] L) (a : M) :
    e.lieEquiv R a = e a := rfl

/--
@isnad1 id=eq.0h5v.s9.996907d33738 from=seed src=0 shape=7484fbb5 vocab=27bb949b
-/
@[simp]
lemma LinearEquiv.lieEquiv_symm_apply (e : M ≃ₗ[R] L) (b : L) :
    letI := e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    (e.lieEquiv R).symm b = e.symm b := rfl

end

namespace Equiv

variable {R L' L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (e : L' ≃ L)

/-- Transfer `LieRing` across an `Equiv` -/
@[deprecated AddEquiv.lieRing (since := "2026-07-30")]
protected abbrev lieRing : LieRing L' :=
  letI := e.addCommGroup
  e.addEquiv.lieRing

/--
@isnad1 id=eq.0h5v.s6.172570b709eb from=seed src=0 shape=e426b7a6 vocab=505f5a06
-/
@[deprecated AddEquiv.bracket_def (since := "2026-07-30")]
lemma bracket_def (x y : L') :
    letI := e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

@[deprecated (since := "2026-07-30")] alias lieAlgebra := LinearEquiv.lieAlgebra
@[deprecated (since := "2026-07-30")] alias lieEquiv := LinearEquiv.lieEquiv
/--
@isnad1 id=eq.0h5v.s8.3cbcf500b7ee from=seed src=0 shape=55dc005f vocab=cafb091d
-/
@[deprecated (since := "2026-07-30")] alias lieEquiv_apply := LinearEquiv.lieEquiv_apply
/--
@isnad1 id=eq.0h5v.s9.996907d33738 from=seed src=0 shape=7484fbb5 vocab=27bb949b
-/
@[deprecated (since := "2026-07-30")] alias lieEquiv_symm_apply := LinearEquiv.lieEquiv_symm_apply

end Equiv
