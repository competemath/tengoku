/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Module.Projective
public import Tengoku.Seed.LinearAlgebra.Basis.Prod
public import Tengoku.Seed.RingTheory.Finiteness.Small

/-!
# Stably free modules

## Main definition
* `IsStablyFree`: A module `M` over a ring `R` is called stably free if there exists a finite free
  `R`-module `N` such that `M ⊕ N` is free.
-/

public section

universe u v w

namespace Module

/-- A module `M` over a ring `R` is called stably free if there exists a finite free `R`-module `N`
such that `M ⊕ N` is free.

The underlying constructor is marked as private. The intended constructor of `IsStablyFree` is
`IsStablyFree.of_free_prod`, and use `IsStablyFree.exist_free_prod` to extract the property from
`IsStablyFree`. -/
@[stacks 0BC3 "(2)"]
class IsStablyFree (R : Type u) [Ring R] (M : Type*) [AddCommGroup M] [Module R M] : Prop where
  private exist_free_prod' : ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module R N)
    (_ : Module.Finite R N) (_ : Free R N), Free R (M × N)

variable (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]

/--
@isnad1 id=ex.0h2v.s7.ab15529cc40d from=seed src=0 shape=ef67ff4d vocab=3febf690
-/
theorem IsStablyFree.exist_free_prod [IsStablyFree R M] :
    ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module R N) (_ : Module.Finite R N) (_ : Free R N),
      Free R (M × N) :=
  IsStablyFree.exist_free_prod'

variable {R M N} in
/--
@isnad1 id=isstably.0h4v.s6.bbef5b0167b1 from=seed src=0 shape=d780dd9d vocab=6fd8bf32
-/
theorem IsStablyFree.equiv (e : M ≃ₗ[R] N) [IsStablyFree R M] : IsStablyFree R N := by
  obtain ⟨P, hPc, hPm, hPfin, hPfree, _⟩ := IsStablyFree.exist_free_prod R M
  exact ⟨P, hPc, hPm, hPfin, hPfree, Free.of_equiv (e.prodCongr (LinearEquiv.refl R P))⟩

variable {R M N} in
/--
@isnad1 id=iff.0h4v.s6.bc564c797ead from=seed src=0 shape=145a6737 vocab=6fd8bf32
-/
theorem IsStablyFree.equiv_iff (e : M ≃ₗ[R] N) : IsStablyFree R M ↔ IsStablyFree R N :=
  ⟨fun h ↦ h.equiv e, fun h ↦ h.equiv e.symm⟩

/--
@isnad1 id=isstably.0h2v.s5.986fee299e4a from=seed src=0 shape=dcff9ff3 vocab=e5ba5480
-/
instance IsStablyFree.ulift [IsStablyFree R M] : IsStablyFree R (ULift.{w} M) :=
  IsStablyFree.equiv ULift.moduleEquiv.symm

/--
@isnad1 id=isstably.0h2v.s5.3a93e7003087 from=seed src=0 shape=92b50873 vocab=e5ba5480
-/
theorem IsStablyFree.of_ulift [IsStablyFree R (ULift.{w} M)] : IsStablyFree R M :=
  IsStablyFree.equiv ULift.moduleEquiv

/--
@isnad1 id=isstably.0h2v.s5.fe033598269d from=seed src=0 shape=9f8b07a1 vocab=a7e1b96f
-/
instance IsStablyFree.shrink [Small.{w, v} M] [IsStablyFree R M] : IsStablyFree R (Shrink.{w} M) :=
  IsStablyFree.equiv (Shrink.linearEquiv R M).symm

/--
@isnad1 id=isstably.0h2v.s5.5ce595a5ec8a from=seed src=0 shape=bb6fcc08 vocab=a7e1b96f
-/
theorem IsStablyFree.of_shrink [Small.{w, v} M] [IsStablyFree R (Shrink.{w} M)] :
    IsStablyFree R M :=
  IsStablyFree.equiv (Shrink.linearEquiv R M)

instance [Free R M] : IsStablyFree R M :=
  ⟨PUnit, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/--
@isnad1 id=isstably.0h3v.s6.5828df3fc41d from=seed src=0 shape=58c82b2e vocab=3febf690
-/
theorem IsStablyFree.of_free_prod [Module.Finite R N] [Free R N] [Free R (M × N)] :
    IsStablyFree R M :=
  have : Small.{u} N := Module.Finite.small.{u} R N
  let +nondep eN : N ≃ₗ[R] Shrink.{u} N := (Shrink.linearEquiv R N).symm
  ⟨Shrink.{u} N, inferInstance, inferInstance, Module.Finite.equiv eN,
    Free.of_equiv eN, Free.of_equiv ((LinearEquiv.refl R M).prodCongr eN)⟩

/--
@isnad1 id=isstably.0h3v.s6.55b05ed7b004 from=seed src=0 shape=b98e597b vocab=3febf690
-/
theorem IsStablyFree.of_free_prod' [Module.Finite R N] [Free R N] [Free R (N × M)] :
    IsStablyFree R M :=
  have : Free R (M × N) := Free.of_equiv (LinearEquiv.prodComm R N M)
  .of_free_prod R M N

instance (priority := low) [IsStablyFree R M] : Projective R M := by
  obtain ⟨N, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R M
  exact Projective.of_split (LinearMap.inl R M N) (LinearMap.fst R M N) (LinearMap.ext fun _ ↦ rfl)

end Module
