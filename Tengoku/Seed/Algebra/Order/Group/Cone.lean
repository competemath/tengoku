/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison, Artie Khovanov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Subgroup.Defs
public import Tengoku.Seed.Algebra.Order.Group.Unbundled.Basic
public import Tengoku.Seed.Algebra.Order.Monoid.Submonoid

/-!
# Construct ordered groups from groups with a specified positive cone.

In this file we provide the structure `GroupCone` and the predicate `IsMaxCone` that encode
the axioms of ordered groups in terms of the subset of non-negative elements.

We also provide constructors that convert between
cones in groups and the corresponding ordered groups.
-/

@[expose] public section

/-- `AddGroupConeClass S G` says that `S` is a type of cones in `G`. -/
class AddGroupConeClass (S : Type*) (G : outParam Type*) [AddCommGroup G] [SetLike S G] : Prop
    extends AddSubmonoidClass S G where
  eq_zero_of_mem_of_neg_mem {C : S} {a : G} : a ∈ C → -a ∈ C → a = 0

/-- `GroupConeClass S G` says that `S` is a type of cones in `G`. -/
@[to_additive]
class GroupConeClass (S : Type*) (G : outParam Type*) [CommGroup G] [SetLike S G] : Prop
    extends SubmonoidClass S G where
  eq_one_of_mem_of_inv_mem {C : S} {a : G} : a ∈ C → a⁻¹ ∈ C → a = 1

export GroupConeClass (eq_one_of_mem_of_inv_mem)
export AddGroupConeClass (eq_zero_of_mem_of_neg_mem)

/-- A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `-a` for any nonzero `a`.
This is equivalent to being the set of non-negative elements of
some order making the group into a partially ordered group. -/
structure AddGroupCone (G : Type*) [AddCommGroup G] extends AddSubmonoid G where
  eq_zero_of_mem_of_neg_mem' {a} : a ∈ carrier → -a ∈ carrier → a = 0

/-- A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `a⁻¹` for any non-identity `a`.
This is equivalent to being the set of elements that are at least 1 in
some order making the group into a partially ordered group. -/
@[to_additive]
structure GroupCone (G : Type*) [CommGroup G] extends Submonoid G where
  eq_one_of_mem_of_inv_mem' {a} : a ∈ carrier → a⁻¹ ∈ carrier → a = 1

@[to_additive]
instance GroupCone.instSetLike (G : Type*) [CommGroup G] : SetLike (GroupCone G) G where
  coe C := C.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

@[to_additive]
instance (G : Type*) [CommGroup G] : PartialOrder (GroupCone G) := .ofSetLike (GroupCone G) G

/--
@isnad1 id=groupcon.0h1v.s3.9536b23b611f from=seed src=0 shape=3d1b05f8 vocab=f73a5110
-/
@[to_additive]
instance GroupCone.instGroupConeClass (G : Type*) [CommGroup G] :
    GroupConeClass (GroupCone G) G where
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_one_of_mem_of_inv_mem {C} := C.eq_one_of_mem_of_inv_mem'

initialize_simps_projections GroupCone (carrier → coe, as_prefix coe)
initialize_simps_projections AddGroupCone (carrier → coe, as_prefix coe)

namespace GroupCone
variable {H : Type*} [CommGroup H] [PartialOrder H] [IsOrderedMonoid H] {a : H}

variable (H) in
/-- The cone of elements that are at least 1. -/
@[to_additive /-- The cone of non-negative elements. -/]
def oneLE : GroupCone H where
  __ := Submonoid.oneLE H
  eq_one_of_mem_of_inv_mem' {a} := by simpa using ge_antisymm

/--
@isnad1 id=eq.0h1v.s5.6640dfbb0cde from=seed src=0 shape=fbb2e310 vocab=bb204aa9
-/
@[to_additive (attr := simp)]
lemma oneLE_toSubmonoid : (oneLE H).toSubmonoid = .oneLE H := rfl
/--
@isnad1 id=iff.0h2v.s5.c840a24d49b1 from=seed src=0 shape=ea0a7987 vocab=948eb42f
-/
@[to_additive (attr := simp)]
lemma mem_oneLE : a ∈ oneLE H ↔ 1 ≤ a := Iff.rfl
/--
@isnad1 id=eq.0h1v.s5.c9586b6e5b0a from=seed src=0 shape=3bd58850 vocab=2b779cfb
-/
@[to_additive (attr := simp, norm_cast)]
lemma coe_oneLE : oneLE H = {x : H | 1 ≤ x} := rfl

/--
@isnad1 id=hasmemor.0h1v.s5.488f42ec6276 from=seed src=0 shape=7cdc28cf vocab=12201da5
-/
@[to_additive]
instance oneLE.hasMemOrInvMem {H : Type*} [CommGroup H] [LinearOrder H] [IsOrderedMonoid H] :
    HasMemOrInvMem (oneLE H) where
  mem_or_inv_mem := by simpa using le_total 1

end GroupCone

variable {S G : Type*} [CommGroup G] [SetLike S G] (C : S)

/-- Construct a partial order by designating a cone in an abelian group. -/
@[to_additive /-- Construct a partial order by designating a cone in an abelian group. -/]
abbrev PartialOrder.mkOfGroupCone [GroupConeClass S G] : PartialOrder G where
  le a b := b / a ∈ C
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using eq_one_of_mem_of_inv_mem nab (by simpa using nba)

/--
@isnad1 id=iff.0h5v.s5.19bab00af172 from=seed src=0 shape=bfe76f79 vocab=0a0e1b31
-/
@[to_additive (attr := simp)]
lemma PartialOrder.mkOfGroupCone_le_iff {S G : Type*} [CommGroup G] [SetLike S G]
    [GroupConeClass S G] {C : S} {a b : G} :
    (mkOfGroupCone C).le a b ↔ b / a ∈ C := Iff.rfl

/-- Construct a linear order by designating a maximal cone in an abelian group. -/
@[to_additive /-- Construct a linear order by designating a maximal cone in an abelian group. -/]
abbrev LinearOrder.mkOfGroupCone
    [GroupConeClass S G] [HasMemOrInvMem C] [DecidablePred (· ∈ C)] : LinearOrder G where
  __ := PartialOrder.mkOfGroupCone C
  le_total a b := by simpa using mem_or_inv_mem C (b / a)
  toDecidableLE _ := _

/-- Construct a partially ordered abelian group by designating a cone in an abelian group.
@isnad1 id=other.0h3v.s5.c53e4d7d709d from=seed src=0 shape=5d4b776a vocab=3c891eed
-/
@[to_additive
  /-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/]
lemma IsOrderedMonoid.mkOfCone [GroupConeClass S G] :
    let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
    IsOrderedMonoid G :=
  let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
  { mul_le_mul_left := fun a b nab c ↦ by simpa [· ≤ ·] using nab }
