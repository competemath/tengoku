/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Aintlib.BernoulliRegular.Reflection.SingularKummer.ProjectedFiniteComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singular Kummer: torsion components

For an additive abelian group `A`, this file sets up the `p`-torsion subgroup

```text
  A[p] = {x : A | p • x = 0}
```

as a `ZMod p`-module.  A `Delta = (ZMod p)ˣ` action on `A` restricts to a
linear action on `A[p]`, so the same character projections used for
`V = A / pA` define the projected components of `A[p]`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace TorsionComponent

variable {p : ℕ}
variable {A : Type*} [AddCommGroup A]

/-- The additive subgroup `A[p]`.-/
abbrev PTorsion (A : Type*) [AddCommGroup A] (p : ℕ) : Type _ :=
  torsionBySubgroup A p

/-- The group `A[p]` is naturally a `ZMod p`-module.-/
instance instModuleZModPTorsion [NeZero p] :
    Module (ZMod p) (PTorsion A p) :=
  AddCommGroup.zmodModule (n := p) fun x => by
    exact Subtype.ext <| x.2

/-- An additive equivalence of `A` restricts to an additive equivalence of
`A[p]`.-/
def torsionAddEquiv (p : ℕ) (e : A ≃+ A) :
    PTorsion A p ≃+ PTorsion A p where
  toFun x :=
    ⟨e x.1, by
      simpa using congrArg e x.2⟩
  invFun x :=
    ⟨e.symm x.1, by
      simpa using congrArg e.symm x.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    simp
  right_inv := by
    intro x
    apply Subtype.ext
    simp
  map_add' := by
    intro x y
    apply Subtype.ext
    simp

/--
@isnad1 id=eq.0h4v.s8.08e6cedb1b72 from=translated src=- shape=9561af0f vocab=8aab309c
-/
@[simp]
theorem torsionAddEquiv_apply_coe (p : ℕ) (e : A ≃+ A) (x : PTorsion A p) :
    ((torsionAddEquiv p e x : PTorsion A p) : A) = e x.1 :=
  rfl

/-- An additive equivalence of `A` restricts to a `ZMod p`-linear equivalence
of `A[p]`.-/
def torsionLinearEquiv [NeZero p] (e : A ≃+ A) :
    PTorsion A p ≃ₗ[ZMod p] PTorsion A p :=
  { (torsionAddEquiv p e).toAddMonoidHom.toZModLinearMap p with
    invFun := torsionAddEquiv p e.symm
    left_inv := (torsionAddEquiv p e).left_inv
    right_inv := (torsionAddEquiv p e).right_inv }

/--
@isnad1 id=eq.0h4v.s8.0ca3ff54dab6 from=translated src=- shape=a37abaf7 vocab=141aebb6
-/
@[simp]
theorem torsionLinearEquiv_apply_coe [NeZero p]
    (e : A ≃+ A) (x : PTorsion A p) :
    ((torsionLinearEquiv (p := p) e x : PTorsion A p) : A) = e x.1 := by
  change ((torsionAddEquiv p e x : PTorsion A p) : A) = e x.1
  rfl

/-- A `Delta` action on `A` restricts to a linear `Delta` action on `A[p]`.-/
def torsionAction [NeZero p]
    (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    CharacterProjection.Delta p →*
      PTorsion A p ≃ₗ[ZMod p] PTorsion A p where
  toFun d := torsionLinearEquiv (p := p) (Multiplicative.toAdd (ρ d))
  map_one' := by
    ext x
    simp [torsionLinearEquiv, torsionAddEquiv]
  map_mul' a b := by
    ext x
    simp [torsionLinearEquiv, torsionAddEquiv, map_mul]

/--
@isnad1 id=eq.0h5v.s11.3ed5f4d5de28 from=translated src=- shape=b675e736 vocab=c878bb26
-/
@[simp]
theorem torsionAction_apply_coe [NeZero p]
    (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (d : CharacterProjection.Delta p) (x : PTorsion A p) :
    ((torsionAction (p := p) ρ d x : PTorsion A p) : A) =
      (Multiplicative.toAdd (ρ d)) x.1 := by
  change ((torsionLinearEquiv (p := p) (Multiplicative.toAdd (ρ d)) x :
      PTorsion A p) : A) = (Multiplicative.toAdd (ρ d)) x.1
  simp

/--
@isnad1 id=eq.0h4v.s8.871533946040 from=translated src=- shape=c681b646 vocab=e774e99d
-/
@[simp]
theorem coe_zmod_smul [NeZero p] (a : ZMod p) (x : PTorsion A p) :
    ((a • x : PTorsion A p) : A) = a.val • (x : A) := by
  have hsmul : (a : ZMod p) • x = a.val • x := by
    calc
      (a : ZMod p) • x = (a.val : ZMod p) • x := by
        rw [ZMod.natCast_zmod_val a]
      _ = a.val • x := Nat.cast_smul_eq_nsmul (ZMod p) a.val x
  calc
    ((a • x : PTorsion A p) : A) =
        ((a.val • x : PTorsion A p) : A) := congrArg (fun y : PTorsion A p => (y : A)) hsmul
    _ = a.val • (x : A) := rfl

/-- The character projection acting on `A[p]`.-/
abbrev torsionProjection [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    PTorsion A p →ₗ[ZMod p] PTorsion A p :=
  CharacterProjection.characterProjection (p := p) i
    (torsionAction (p := p) ρ)

/-- The `i`-th projected component of `A[p]`.-/
abbrev torsionComponent [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    Submodule (ZMod p) (PTorsion A p) :=
  LinearMap.range (torsionProjection (p := p) i ρ)

/--
@isnad1 id=eq.0h4v.s8.fcaedba46329 from=translated src=- shape=4afea1df vocab=9865c8a8
-/
theorem torsionComponent_eq_range_projection [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    torsionComponent (p := p) i ρ =
      LinearMap.range (torsionProjection (p := p) i ρ) :=
  rfl

/--
@isnad1 id=iff.0h5v.s8.aba7727983eb from=translated src=- shape=8e6361ac vocab=e5287a66
-/
theorem mem_torsionComponent_iff_exists [NeZero p]
    {i : ℕ} {ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)}
    {x : PTorsion A p} :
    x ∈ torsionComponent (p := p) i ρ ↔
      ∃ y : PTorsion A p,
        torsionProjection (p := p) i ρ y = x :=
  Iff.rfl

/-- Nontriviality of the `i`-th projected component of `A[p]`.-/
def TorsionComponentNontrivial [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) : Prop :=
  torsionComponent (p := p) i ρ ≠ ⊥

/--
@isnad1 id=ex.1h4v.s8.58eb6cb8a097 from=translated src=- shape=0121b538 vocab=1e846bc1
-/
theorem exists_ne_zero_mem_torsionComponent [NeZero p]
    {i : ℕ} {ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)}
    (h : TorsionComponentNontrivial (p := p) i ρ) :
    ∃ x : PTorsion A p,
      x ≠ 0 ∧ x ∈ torsionComponent (p := p) i ρ := by
  obtain ⟨x, hxmem, hxne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨x, hxne, hxmem⟩

/--
@isnad1 id=torsionc.1h4v.s8.527489d9fc41 from=translated src=- shape=c52af5d7 vocab=1e846bc1
-/
theorem torsionComponentNontrivial_of_exists_ne_zero_mem [NeZero p]
    {i : ℕ} {ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)}
    (h : ∃ x : PTorsion A p,
      x ≠ 0 ∧ x ∈ torsionComponent (p := p) i ρ) :
    TorsionComponentNontrivial (p := p) i ρ := by
  obtain ⟨x, hxne, hxmem⟩ := h
  rw [TorsionComponentNontrivial]
  exact (Submodule.ne_bot_iff _).2 ⟨x, hxmem, hxne⟩

/--
@isnad1 id=iff.0h4v.s8.f667f40eee2c from=translated src=- shape=3c4513f8 vocab=1e846bc1
-/
theorem torsionComponentNontrivial_iff_exists_ne_zero_mem [NeZero p]
    (i : ℕ) (ρ : CharacterProjection.Delta p →* Multiplicative (A ≃+ A)) :
    TorsionComponentNontrivial (p := p) i ρ ↔
      ∃ x : PTorsion A p,
        x ≠ 0 ∧ x ∈ torsionComponent (p := p) i ρ :=
  ⟨exists_ne_zero_mem_torsionComponent,
    torsionComponentNontrivial_of_exists_ne_zero_mem⟩

end TorsionComponent

end SingularKummer
end Reflection
end BernoulliRegular

end

end
