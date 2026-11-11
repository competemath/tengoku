/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Aintlib.BernoulliRegular.Reflection.SingularKummer.FiniteLevelIdempotent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singular Kummer: exact finite-level projections for additive actions

This file applies the exact finite-level character idempotent to an additive
action.  If a finite group `D` acts on an additive group `A` by additive
automorphisms and `A` is viewed as a `ZMod m`-module, then a character

```text
  chi : D -> (ZMod m)^*
```

defines an exact finite-level projection.  Its range is the subgroup on which
the action has character `chi`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelAdditiveProjection

open FiniteLevelIdempotent

variable {m : ℕ}
variable {D A : Type*} [Group D] [Fintype D]
variable [AddCommGroup A] [Module (ZMod m) A]

/-- An additive equivalence is `ZMod m`-linear for the canonical `ZMod m`
module structure on an additive group.-/
def addEquivToZModLinearEquiv (e : A ≃+ A) :
    A ≃ₗ[ZMod m] A :=
  { e.toAddMonoidHom.toZModLinearMap m with
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

/--
@isnad1 id=eq.0h4v.s8.694d2c6590f3 from=translated src=- shape=885cf723 vocab=8863f51b
-/
@[simp]
theorem addEquivToZModLinearEquiv_apply (e : A ≃+ A) (x : A) :
    addEquivToZModLinearEquiv (m := m) e x = e x :=
  rfl

/-- A group action by additive automorphisms, made linear over `ZMod m`.-/
def linearAction (rho : D →* Multiplicative (A ≃+ A)) :
    D →* A ≃ₗ[ZMod m] A where
  toFun d := addEquivToZModLinearEquiv (m := m) (Multiplicative.toAdd (rho d))
  map_one' := by
    ext x
    simp [addEquivToZModLinearEquiv]
  map_mul' a b := by
    ext x
    simp [addEquivToZModLinearEquiv, map_mul]

omit [Fintype D] in
/--
@isnad1 id=eq.0h6v.s10.73e68945fc7c from=translated src=- shape=53db65eb vocab=f04ba647
-/
@[simp]
theorem linearAction_apply (rho : D →* Multiplicative (A ≃+ A)) (d : D) (x : A) :
    linearAction (m := m) rho d x = Multiplicative.toAdd (rho d) x :=
  rfl

/-- The exact finite-level projection attached to an additive action and a
multiplicative character.-/
abbrev projection (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ) :
    A →ₗ[ZMod m] A :=
  FiniteLevelIdempotent.projection (m := m) (linearAction (m := m) rho) chi

/-- The additive subgroup cut out by the exact finite-level projection.-/
abbrev componentSubgroup (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ) :
    AddSubgroup A :=
  (LinearMap.range (projection (m := m) rho chi)).toAddSubgroup

/-- The same subgroup as a `ZMod m`-submodule.-/
abbrev componentSubmodule (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ) :
    Submodule (ZMod m) A :=
  LinearMap.range (projection (m := m) rho chi)

/--
@isnad1 id=iff.0h6v.s8.aecb83f81c1f from=translated src=- shape=e720a8ce vocab=6da436f4
-/
theorem mem_componentSubgroup_iff
    (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ) {x : A} :
    x ∈ componentSubgroup (m := m) rho chi ↔
      x ∈ LinearMap.range (projection (m := m) rho chi) :=
  Iff.rfl

/-- Elements in the exact projection subgroup satisfy the finite-level
character relation.
@isnad1 id=eq.1h7v.s10.1ee62a16282c from=translated src=- shape=cf6fbd31 vocab=e831babe
-/
theorem apply_eq_character_smul_of_mem_component
    (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ)
    (d : D) {x : A}
    (hx : x ∈ componentSubgroup (m := m) rho chi) :
    Multiplicative.toAdd (rho d) x = (chi d : ZMod m) • x :=
  FiniteLevelIdempotent.mem_range_apply
    (m := m) (linearAction (m := m) rho) chi d hx

/-- The exact finite-level projection acts as the identity on its own range.
@isnad1 id=eq.2h6v.s8.c8f6435b9624 from=translated src=- shape=190260e1 vocab=611bc6fd
-/
theorem projection_apply_eq_self_of_mem_component
    (hcard : IsUnit (Fintype.card D : ZMod m))
    (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ)
    {x : A}
    (hx : x ∈ componentSubgroup (m := m) rho chi) :
    projection (m := m) rho chi x = x :=
  FiniteLevelIdempotent.projection_apply_eq_self_of_mem_range
    (m := m) hcard (linearAction (m := m) rho) chi hx

/-- Idempotence of the exact finite-level additive projection.
@isnad1 id=eq.1h6v.s9.71e616788d1d from=translated src=- shape=4c0fbd20 vocab=093627db
-/
theorem projection_apply_projection
    (hcard : IsUnit (Fintype.card D : ZMod m))
    (rho : D →* Multiplicative (A ≃+ A)) (chi : D →* (ZMod m)ˣ) (x : A) :
    projection (m := m) rho chi (projection (m := m) rho chi x) =
      projection (m := m) rho chi x :=
  FiniteLevelIdempotent.projection_apply_projection
    (m := m) hcard (linearAction (m := m) rho) chi x

end FiniteLevelAdditiveProjection

end SingularKummer
end Reflection
end BernoulliRegular

end

end
