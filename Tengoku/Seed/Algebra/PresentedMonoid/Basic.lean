/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.FreeMonoid.Basic
public import Tengoku.Seed.Algebra.Group.Submonoid.Operations
public import Tengoku.Seed.GroupTheory.Congruence.Hom

/-!
# Defining a monoid given by generators and relations

Given relations `rels` on the free monoid on a type `α`, this file constructs the monoid
given by generators `x : α` and relations `rels`.

## Main definitions

* `PresentedMonoid rels`: the quotient of the free monoid on a type `α` by the closure of one-step
  reductions (arising from a binary relation on free monoid elements `rels`).
* `PresentedMonoid.of`: The canonical map from `α` to a presented monoid with generators `α`.
* `PresentedMonoid.lift f`: the canonical monoid homomorphism `PresentedMonoid rels → M`, given
  a function `f : α → G` from a type `α` to a monoid `M` which satisfies the relations `rels`.

## Tags

generators, relations, monoid presentations
-/

@[expose] public section

variable {α : Type*}

/-- Given a set of relations, `rels`, over a type `α`, `PresentedMonoid` constructs the monoid with
generators `x : α` and relations `rels` as a quotient of a congruence structure over rels. -/
@[to_additive /-- Given a set of relations, `rels`, over a type `α`, `PresentedAddMonoid` constructs
the monoid with generators `x : α` and relations `rels` as a quotient of an AddCon structure over
rels -/]
def PresentedMonoid (rels : FreeMonoid α → FreeMonoid α → Prop) := (conGen rels).Quotient

namespace PresentedMonoid

open Set Submonoid

@[to_additive]
instance {rels : FreeMonoid α → FreeMonoid α → Prop} : Monoid (PresentedMonoid rels) :=
  inferInstanceAs <| Monoid (conGen rels).Quotient

/-- The quotient map from the free monoid on `α` to the presented monoid with the same generators
and the given relations `rels`. -/
@[to_additive /-- The quotient map from the free additive monoid on `α` to the presented additive
monoid with the same generators and the given relations `rels` -/]
def mk (rels : FreeMonoid α → FreeMonoid α → Prop) : FreeMonoid α →* PresentedMonoid rels where
  toFun := Quotient.mk (conGen rels).toSetoid
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- `of` is the canonical map from `α` to a presented monoid with generators `x : α`. The term `x`
is mapped to the equivalence class of the image of `x` in `FreeMonoid α`. -/
@[to_additive
/-- `of` is the canonical map from `α` to a presented additive monoid with generators `x : α`. The
term `x` is mapped to the equivalence class of the image of `x` in `FreeAddMonoid α`. -/]
def of (rels : FreeMonoid α → FreeMonoid α → Prop) (x : α) : PresentedMonoid rels :=
  mk rels (.of x)

section inductionOn

variable {α₁ α₂ α₃ : Type*} {rels₁ : FreeMonoid α₁ → FreeMonoid α₁ → Prop}
  {rels₂ : FreeMonoid α₂ → FreeMonoid α₂ → Prop} {rels₃ : FreeMonoid α₃ → FreeMonoid α₃ → Prop}

local notation "P₁" => PresentedMonoid rels₁
local notation "P₂" => PresentedMonoid rels₂
local notation "P₃" => PresentedMonoid rels₃

/--
@isnad1 id=var.0h5v.s6.69d9f6d9b66f from=seed src=0 shape=a909cf65 vocab=414e5d53
-/
@[to_additive (attr := elab_as_elim), induction_eliminator]
protected theorem inductionOn {δ : P₁ → Prop} (q : P₁) (h : ∀ a, δ (mk rels₁ a)) : δ q :=
  Quotient.ind h q

/--
@isnad1 id=var.0h8v.s7.a6c8af3844f6 from=seed src=0 shape=83796cd3 vocab=414e5d53
-/
@[to_additive (attr := elab_as_elim)]
protected theorem inductionOn₂ {δ : P₁ → P₂ → Prop} (q₁ : P₁) (q₂ : P₂)
    (h : ∀ a b, δ (mk rels₁ a) (mk rels₂ b)) : δ q₁ q₂ :=
  Quotient.inductionOn₂ q₁ q₂ h

/--
@isnad1 id=var.0h11v.s8.e227cfa9a968 from=seed src=0 shape=3e4f3a40 vocab=414e5d53
-/
@[to_additive (attr := elab_as_elim)]
protected theorem inductionOn₃ {δ : P₁ → P₂ → P₃ → Prop} (q₁ : P₁)
    (q₂ : P₂) (q₃ : P₃) (h : ∀ a b c, δ (mk rels₁ a) (mk rels₂ b) (mk rels₃ c)) :
    δ q₁ q₂ q₃ :=
  Quotient.inductionOn₃ q₁ q₂ q₃ h

end inductionOn

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop} {x y : FreeMonoid α}

/--
@isnad1 id=iff.0h4v.s7.b194dd6a3774 from=seed src=0 shape=dfc9dcd7 vocab=85de8c90
-/
lemma mk_eq_mk_iff : mk rels x = mk rels y ↔ conGen rels x y := Quotient.eq

/--
@isnad1 id=eq.0h5v.s7.cde34f377677 from=seed src=0 shape=c6887396 vocab=414e5d53
-/
lemma mk_eq_mk_of_rel (h : rels x y) : mk rels x = mk rels y := mk_eq_mk_iff.2 (.of _ _ h)

/-- The generators of a presented monoid generate the presented monoid. That is, the submonoid
closure of the set of generators equals `⊤`.
@isnad1 id=eq.0h2v.s6.3f1ce5e7a6d3 from=seed src=0 shape=e8792b16 vocab=3daa7057
-/
@[to_additive (attr := simp) /-- The generators of a presented additive monoid generate the
presented additive monoid. That is, the additive submonoid closure of the set of generators equals
`⊤`. -/]
theorem closure_range_of (rels : FreeMonoid α → FreeMonoid α → Prop) :
    Submonoid.closure (Set.range (of rels)) = ⊤ := by
  rw [Submonoid.eq_top_iff']
  intro x
  induction x with | _ a
  induction a with
  | one => exact Submonoid.one_mem _
  | of x => exact subset_closure <| by simp [range, of]
  | mul x y hx hy => exact Submonoid.mul_mem _ hx hy

/--
@isnad1 id=surjecti.0h2v.s6.128790cd522d from=seed src=0 shape=6f40a3be vocab=ced808a6
-/
@[to_additive]
theorem surjective_mk {rels : FreeMonoid α → FreeMonoid α → Prop} :
    Function.Surjective (mk rels) := fun x ↦ PresentedMonoid.inductionOn x fun a ↦ .intro a rfl

section ToMonoid
variable {α M : Type*} [Monoid M] (f : α → M)
variable {rels : FreeMonoid α → FreeMonoid α → Prop}
variable (h : ∀ a b : FreeMonoid α, rels a b → FreeMonoid.lift f a = FreeMonoid.lift f b)

/-- The extension of a map `f : α → M` that satisfies the given relations to a monoid homomorphism
from `PresentedMonoid rels → M`. -/
@[to_additive /-- The extension of a map `f : α → M` that satisfies the given relations to an
additive-monoid homomorphism from `PresentedAddMonoid rels → M` -/]
def lift : PresentedMonoid rels →* M :=
  Con.lift _ (FreeMonoid.lift f) (Con.conGen_le.2 h)

/--
@isnad1 id=eq.2h5v.s10.e1c4f7597ff9 from=seed src=0 shape=dcf04174 vocab=0d9bcab1
-/
@[to_additive]
theorem toMonoid.unique (g : MonoidHom (conGen rels).Quotient M)
    (hg : ∀ a : α, g (of rels a) = f a) : g = lift f h :=
  Con.lift_unique (Con.conGen_le.2 h) g (FreeMonoid.hom_eq hg)

/--
@isnad1 id=eq.1h5v.s8.14a10f5ac6b5 from=seed src=0 shape=9f7094e3 vocab=f8225761
-/
@[to_additive (attr := simp)]
theorem lift_of {x : α} : lift f h (of rels x) = f x := rfl

end ToMonoid

/--
@isnad1 id=eq.1h5v.s7.34c8b8491568 from=seed src=0 shape=5fe06336 vocab=64b04012
-/
@[to_additive (attr := ext)]
theorem ext {M : Type*} [Monoid M] (rels : FreeMonoid α → FreeMonoid α → Prop)
    {φ ψ : PresentedMonoid rels →* M} (hx : ∀ (x : α), φ (.of rels x) = ψ (.of rels x)) :
    φ = ψ := by
  apply MonoidHom.eq_of_eqOn_denseM (closure_range_of _)
  grind [Set.eqOn_range]

end PresentedMonoid
