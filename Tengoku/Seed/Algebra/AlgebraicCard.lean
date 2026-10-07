/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Polynomial.Cardinal
public import Tengoku.Seed.RingTheory.Algebraic.Basic

/-!
### Cardinality of algebraic numbers

In this file, we prove variants of the following result: the cardinality of algebraic numbers under
an R-algebra is at most `#R[X] * ℵ₀`.

Although this can be used to prove that real or complex transcendental numbers exist, a more direct
proof is given by `Liouville.transcendental`.
-/

public section


universe u v

open Cardinal Polynomial Set

open Cardinal Polynomial

namespace Algebraic

/--
@isnad1 id=infinite.0h2v.s5.13f28f6b5c9c from=seed src=0 shape=46c0a699 vocab=04dfffc8
-/
theorem infinite_of_charZero (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    [CharZero A] : { x : A | IsAlgebraic R x }.Infinite := by
  let := MulActionWithZero.nontrivial R A
  exact infinite_of_injective_forall_mem Nat.cast_injective isAlgebraic_natCast

/--
@isnad1 id=le.0h2v.s5.29c399288aeb from=seed src=0 shape=2e2f7ddb vocab=d31ae486
-/
theorem aleph0_le_cardinalMk_of_charZero (R A : Type*) [CommRing R] [Ring A]
    [Algebra R A] [CharZero A] : ℵ₀ ≤ #{ x : A // IsAlgebraic R x } :=
  infinite_iff.1 (Set.infinite_coe_iff.2 <| infinite_of_charZero R A)

section lift

variable (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

/--
@isnad1 id=le.0h2v.s6.a01339bdc434 from=seed src=0 shape=8412a0e6 vocab=6e945388
-/
theorem cardinalMk_lift_le_mul :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } ≤ Cardinal.lift.{v} #R[X] * ℵ₀ := by
  rw [← mk_uLift, ← mk_uLift]
  choose g hg₁ hg₂ using fun x : { x : A | IsAlgebraic R x } => x.coe_prop
  refine lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le g fun f => ?_
  rw [lift_le_aleph0, le_aleph0_iff_set_countable]
  suffices MapsTo (↑) (g ⁻¹' {f}) (f.rootSet A) from
    this.countable_of_injOn Subtype.coe_injective.injOn (f.rootSet_finite A).countable
  rintro x (rfl : g x = f)
  exact mem_rootSet.2 ⟨hg₁ x, hg₂ x⟩

/--
@isnad1 id=le.0h2v.s6.8ebee1d93835 from=seed src=0 shape=637d97e7 vocab=396fc7d5
-/
theorem cardinalMk_lift_le_max :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } ≤ max (Cardinal.lift.{v} #R) ℵ₀ :=
  (cardinalMk_lift_le_mul R A).trans <| by grw [lift_le.2 cardinalMk_le_max]; simp

/--
@isnad1 id=eq.0h2v.s6.79863c72fdec from=seed src=0 shape=7a0802bd vocab=42fb797a
-/
@[simp]
theorem cardinalMk_lift_of_infinite [Infinite R] :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } = Cardinal.lift.{v} #R :=
  ((cardinalMk_lift_le_max R A).trans_eq (max_eq_left <| aleph0_le_mk _)).antisymm <|
    lift_mk_le'.2 ⟨⟨fun x => ⟨algebraMap R A x, isAlgebraic_algebraMap _⟩, fun _ _ h =>
      FaithfulSMul.algebraMap_injective R A (Subtype.ext_iff.1 h)⟩⟩

variable [Countable R]

/--
@isnad1 id=countabl.0h2v.s6.ef07bede4145 from=seed src=0 shape=89c55f0b vocab=3fd4f761
-/
@[simp]
protected theorem countable : Set.Countable { x : A | IsAlgebraic R x } := by
  rw [← le_aleph0_iff_set_countable, ← lift_le_aleph0]
  apply (cardinalMk_lift_le_max R A).trans
  simp

/--
@isnad1 id=eq.0h2v.s6.f68acc2ca20b from=seed src=0 shape=bc835ed8 vocab=9a6d7e63
-/
@[simp]
theorem cardinalMk_of_countable_of_charZero [CharZero A] :
    #{ x : A // IsAlgebraic R x } = ℵ₀ :=
  (Algebraic.countable R A).le_aleph0.antisymm (aleph0_le_cardinalMk_of_charZero R A)

end lift

section NonLift

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

/--
@isnad1 id=le.0h2v.s6.dea3d94db29b from=seed src=0 shape=308d9c23 vocab=59ad8bea
-/
theorem cardinalMk_le_mul : #{ x : A // IsAlgebraic R x } ≤ #R[X] * ℵ₀ := by
  rw [← lift_id #_, ← lift_id #R[X]]
  exact cardinalMk_lift_le_mul R A

/--
@isnad1 id=le.0h2v.s6.dfd4bd188d5a from=seed src=0 shape=209d7bea vocab=bbd5a08d
-/
@[stacks 09GK]
theorem cardinalMk_le_max : #{ x : A // IsAlgebraic R x } ≤ max #R ℵ₀ := by
  rw [← lift_id #_, ← lift_id #R]
  exact cardinalMk_lift_le_max R A

/--
@isnad1 id=eq.0h2v.s6.be8eb682347b from=seed src=0 shape=f23e72bd vocab=46f2fabd
-/
@[simp]
theorem cardinalMk_of_infinite [Infinite R] : #{ x : A // IsAlgebraic R x } = #R :=
  lift_inj.1 <| cardinalMk_lift_of_infinite R A

end NonLift

end Algebraic
