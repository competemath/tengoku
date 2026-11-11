/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Aintlib.BernoulliRegular.Reflection.SingularKummer.CharacterProjectionEigen
public import Tengoku.Aintlib.BernoulliRegular.Reflection.SingularKummer.FiniteGroupComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singular Kummer: elementary quotient components

This file defines the elementary quotient

```text
  V = A / pA
```

for an additive abelian group `A`, equips it with its natural `ZMod p`-module
structure, and transports a `Delta = (ZMod p)ˣ` action on `A` to a linear
action on `V`.

The `i`-th component of `V` is the range of the same character projection used
elsewhere in the singular-Kummer argument.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace ElementaryQuotientComponent

variable {p : ℕ}
variable {A : Type*} [AddCommGroup A]

/-- The elementary quotient `V = A / pA`.-/
abbrev ElementaryQuotient (A : Type*) [AddCommGroup A] (p : ℕ) : Type _ :=
  elementaryQuotient A p

/-- The quotient map `A -> A / pA`.-/
def quotientMap (A : Type*) [AddCommGroup A] (p : ℕ) :
    A →+ ElementaryQuotient A p :=
  QuotientAddGroup.mk' (multiplesSubgroup A p)

/--
@isnad1 id=eq.0h3v.s7.dc680bbdbef2 from=translated src=- shape=47c9b4b6 vocab=4b1dcb60
-/
@[simp]
theorem quotientMap_apply (p : ℕ) (x : A) :
    quotientMap A p x = (QuotientAddGroup.mk x : ElementaryQuotient A p) :=
  rfl

/-- The quotient map `A -> A / pA` is surjective.
@isnad1 id=surjecti.0h2v.s6.6592f8c648b0 from=translated src=- shape=ec3d2faf vocab=b43beb84
-/
theorem quotientMap_surjective (p : ℕ) :
    Function.Surjective (quotientMap A p) := by
  simpa [quotientMap, ElementaryQuotient] using
    QuotientAddGroup.mk'_surjective (multiplesSubgroup A p)

/-- The quotient `A / pA` is naturally a `ZMod p`-module.-/
instance instModuleZModElementaryQuotient :
    Module (ZMod p) (ElementaryQuotient A p) :=
  QuotientAddGroup.zmodModule (n := p) (H := multiplesSubgroup A p) (by
    intro x
    exact ⟨x, rfl⟩)

/-- An additive equivalence of `A` preserves the subgroup `pA`.
@isnad1 id=le.0h3v.s6.18431c3fad8e from=translated src=- shape=a47ed808 vocab=afb75e7c
-/
theorem multiplesSubgroup_le_comap_addEquiv
    (p : ℕ) (e : A ≃+ A) :
    multiplesSubgroup A p ≤
      (multiplesSubgroup A p).comap e.toAddMonoidHom := by
  rintro x ⟨y, rfl⟩
  change e (p • y) ∈ multiplesSubgroup A p
  rw [map_nsmul]
  exact ⟨e y, rfl⟩

/-- An additive equivalence of `A` induces an additive equivalence of
`A / pA`.-/
def quotientAddEquiv (p : ℕ) (e : A ≃+ A) :
    ElementaryQuotient A p ≃+
      ElementaryQuotient A p where
  toFun :=
    QuotientAddGroup.map (multiplesSubgroup A p) (multiplesSubgroup A p)
      e.toAddMonoidHom (multiplesSubgroup_le_comap_addEquiv p e)
  invFun :=
    QuotientAddGroup.map (multiplesSubgroup A p) (multiplesSubgroup A p)
      e.symm.toAddMonoidHom (multiplesSubgroup_le_comap_addEquiv p e.symm)
  left_inv := by
    intro x
    induction x using QuotientAddGroup.induction_on
    simp [QuotientAddGroup.map_mk]
  right_inv := by
    intro x
    induction x using QuotientAddGroup.induction_on
    simp [QuotientAddGroup.map_mk]
  map_add' := fun x y =>
    map_add _ x y

/--
@isnad1 id=eq.0h4v.s8.fc491f90a79e from=translated src=- shape=6901ae34 vocab=4334486e
-/
@[simp]
theorem quotientAddEquiv_mk (p : ℕ) (e : A ≃+ A) (x : A) :
    quotientAddEquiv p e
        (QuotientAddGroup.mk x : ElementaryQuotient A p) =
      QuotientAddGroup.mk (e x) :=
  rfl

/-- An additive equivalence of `A` induces a `ZMod p`-linear equivalence of
`A / pA`.-/
def quotientLinearEquiv (p : ℕ) (e : A ≃+ A) :
    ElementaryQuotient A p ≃ₗ[ZMod p]
      ElementaryQuotient A p :=
  { (quotientAddEquiv p e).toAddMonoidHom.toZModLinearMap p with
    invFun := quotientAddEquiv p e.symm
    left_inv := (quotientAddEquiv p e).left_inv
    right_inv := (quotientAddEquiv p e).right_inv }

/--
@isnad1 id=eq.0h4v.s8.c462754e4f23 from=translated src=- shape=6991fdba vocab=d1f3c7a2
-/
@[simp]
theorem quotientLinearEquiv_mk (p : ℕ) (e : A ≃+ A) (x : A) :
    quotientLinearEquiv p e
        (QuotientAddGroup.mk x : ElementaryQuotient A p) =
      QuotientAddGroup.mk (e x) :=
  rfl

/--
@isnad1 id=eq.0h4v.s9.9945c7399f42 from=translated src=- shape=4b30844e vocab=3426e52c
-/
@[simp]
theorem quotientLinearEquiv_quotientMap (p : ℕ) (e : A ≃+ A) (x : A) :
    quotientLinearEquiv p e (quotientMap A p x) =
      quotientMap A p (e x) :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.5984426f49bb from=translated src=- shape=88b844bd vocab=29b19372
-/
@[simp]
theorem zmod_smul_eq_val_nsmul [NeZero p]
    (a : ZMod p) (x : ElementaryQuotient A p) :
    a • x = a.val • x := by
  calc
    a • x = (a.val : ZMod p) • x := by
      rw [ZMod.natCast_zmod_val a]
    _ = a.val • x := Nat.cast_smul_eq_nsmul (ZMod p) a.val x

/-- A `Delta` action on `A` induces a linear `Delta` action on `V = A / pA`.-/
def elementaryQuotientAction [NeZero p]
    (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    CharacterProjection.Delta p →*
      ElementaryQuotient A p ≃ₗ[ZMod p] ElementaryQuotient A p where
  toFun d := quotientLinearEquiv p (Multiplicative.toAdd (ρ d))
  map_one' := by
    ext x
    induction x using QuotientAddGroup.induction_on
    simp [quotientLinearEquiv]
  map_mul' a b := by
    ext x
    induction x using QuotientAddGroup.induction_on
    simp [quotientLinearEquiv, map_mul]

/-- The induced `Delta` action on `A / pA` is the quotient of the action on
`A`.
@isnad1 id=eq.0h5v.s11.56f2a16ced35 from=translated src=- shape=ac2ff3b5 vocab=51ceee1f
-/
@[simp]
theorem elementaryQuotientAction_quotientMap [NeZero p]
    (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (d : CharacterProjection.Delta p) (x : A) :
    elementaryQuotientAction (p := p) ρ d (quotientMap A p x) =
      quotientMap A p ((Multiplicative.toAdd (ρ d)) x) :=
  rfl

/--
@isnad1 id=eq.0h5v.s11.c6d2a665cb99 from=translated src=- shape=b5b9006e vocab=8d9aad2e
-/
@[simp]
theorem elementaryQuotientAction_mk [NeZero p]
    (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (d : CharacterProjection.Delta p) (x : A) :
    elementaryQuotientAction (p := p) ρ d
        (QuotientAddGroup.mk x : ElementaryQuotient A p) =
      QuotientAddGroup.mk ((Multiplicative.toAdd (ρ d)) x) :=
  rfl

/-- The character projection acting on the elementary quotient `V = A / pA`.-/
abbrev elementaryProjection [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    ElementaryQuotient A p →ₗ[ZMod p] ElementaryQuotient A p :=
  CharacterProjection.characterProjection (p := p) i
    (elementaryQuotientAction (p := p) ρ)

/-- The `i`-th component of `V = A / pA`.-/
abbrev elementaryComponent [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    Submodule (ZMod p) (ElementaryQuotient A p) :=
  LinearMap.range (elementaryProjection (p := p) i ρ)

/--
@isnad1 id=eq.0h4v.s8.c42b5d85b544 from=translated src=- shape=4afea1df vocab=593c957d
-/
theorem elementaryComponent_eq_range_projection [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    elementaryComponent (p := p) i ρ =
      LinearMap.range (elementaryProjection (p := p) i ρ) :=
  rfl

/--
@isnad1 id=iff.0h5v.s8.d88a9e3bac7c from=translated src=- shape=8e6361ac vocab=72b7b6c9
-/
theorem mem_elementaryComponent_iff_exists [NeZero p]
    {i : ℕ} {ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)}
    {x : ElementaryQuotient A p} :
    x ∈ elementaryComponent (p := p) i ρ ↔
      ∃ y : ElementaryQuotient A p,
        elementaryProjection (p := p) i ρ y = x :=
  Iff.rfl

/-- Nontriviality of the `i`-th component of `V = A / pA`.-/
def ElementaryComponentNontrivial [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) : Prop :=
  elementaryComponent (p := p) i ρ ≠ ⊥

/--
@isnad1 id=ex.1h4v.s8.024a07a9619e from=translated src=- shape=0121b538 vocab=a81bdfcb
-/
theorem exists_ne_zero_mem_elementaryComponent [NeZero p]
    {i : ℕ} {ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)}
    (h : ElementaryComponentNontrivial (p := p) i ρ) :
    ∃ x : ElementaryQuotient A p,
      x ≠ 0 ∧ x ∈ elementaryComponent (p := p) i ρ := by
  obtain ⟨x, hxmem, hxne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨x, hxne, hxmem⟩

/--
@isnad1 id=elementa.1h4v.s8.f53e5b4bb30f from=translated src=- shape=c52af5d7 vocab=a81bdfcb
-/
theorem elementaryComponentNontrivial_of_exists_ne_zero_mem [NeZero p]
    {i : ℕ} {ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)}
    (h : ∃ x : ElementaryQuotient A p,
      x ≠ 0 ∧ x ∈ elementaryComponent (p := p) i ρ) :
    ElementaryComponentNontrivial (p := p) i ρ := by
  obtain ⟨x, hxne, hxmem⟩ := h
  rw [ElementaryComponentNontrivial]
  exact (Submodule.ne_bot_iff _).2 ⟨x, hxmem, hxne⟩

/--
@isnad1 id=iff.0h4v.s8.3a69a7c3448d from=translated src=- shape=3c4513f8 vocab=a81bdfcb
-/
theorem elementaryComponentNontrivial_iff_exists_ne_zero_mem [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    ElementaryComponentNontrivial (p := p) i ρ ↔
      ∃ x : ElementaryQuotient A p,
        x ≠ 0 ∧ x ∈ elementaryComponent (p := p) i ρ :=
  ⟨exists_ne_zero_mem_elementaryComponent,
    elementaryComponentNontrivial_of_exists_ne_zero_mem⟩

end ElementaryQuotientComponent

end SingularKummer
end Reflection
end BernoulliRegular

end

end
