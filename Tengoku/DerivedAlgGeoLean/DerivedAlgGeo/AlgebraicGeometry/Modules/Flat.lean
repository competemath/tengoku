/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Algebra.Category.ModuleCat.Products
import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Flatness of a module sheaf over a morphism

`Scheme.Modules.IsFlatOver p M` says that `M` is flat over the base along
`p : X ⟶ S`, stalkwise: at every point of `X`, the stalk of `M` is flat as a
module over the corresponding stalk of `S`, restricted along the local-ring
map `p` induces.

This is a property of one module sheaf and one morphism. It needs no derived
category, no moduli problem and no perfectness notion, and it is used before
any of them: Tor-amplitude models, geometric fibers and base-change arguments
all ask for flat terms. It lives with `X.Modules` for that reason — the
carrier in its public type is a module sheaf, and `moduleStalkFunctor`, the
only other repository construction it mentions, is the neighbouring
`Modules/Pullback/Stalk.lean`.

Flatness over the identity is equivalent to flatness at each module stalk,
and is preserved by indexed coproducts of module sheaves.

It previously sat in `Moduli/PerfectComplex/Relative.lean`, where its first
consumer was; see `docs/architecture/cutover-ledger.md`, finding 11.

## Not a morphism-flatness predicate

`Mathlib.AlgebraicGeometry.Morphisms.Flat` is a different subject: it asks
that the *morphism* be flat, which is this condition for the structure sheaf
alone. Nothing here specializes to or is implied by that class, and no
instance relates them.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

namespace Scheme

/-- A module sheaf on `X` is flat over `S` when every stalk, restricted along
the local-ring map induced by `p`, is a flat module over the corresponding
stalk of `S`.-/
def Modules.IsFlatOver {X S : Scheme.{u}} (p : X ⟶ S)
    (M : X.Modules) : Prop :=
  ∀ x : X, Module.Flat (S.presheaf.stalk (p x))
    ((ModuleCat.restrictScalars (p.stalkMap x).hom).obj
      ((Scheme.Modules.moduleStalkFunctor X x).obj M))

/-- The identity morphism induces identity maps on stalk rings, and
`ModuleCat.restrictScalarsId'App` removes the scalar-restriction bookkeeping.
@isnad1 id=iff.0h2v.s10.aa9f4b12bfae from=translated src=- shape=2b28bae4 vocab=6865f3c4
-/
theorem Modules.isFlatOverId_iff_stalkwiseFlat
    (X : Scheme.{u}) (M : X.Modules) :
    Modules.IsFlatOver (𝟙 X) M ↔
      ∀ x : X, Module.Flat (X.presheaf.stalk x)
        ((Modules.moduleStalkFunctor X x).obj M) := by
  constructor
  · intro h x
    have h := h x
    dsimp [Modules.IsFlatOver] at h
    rw [Scheme.Hom.stalkMap_id] at h
    change Module.Flat (X.presheaf.stalk x)
      ((ModuleCat.restrictScalars (RingHom.id (X.presheaf.stalk x))).obj
        ((Modules.moduleStalkFunctor X x).obj M)) at h
    letI : Module.Flat (X.presheaf.stalk x)
        ((ModuleCat.restrictScalars (RingHom.id (X.presheaf.stalk x))).obj
          ((Modules.moduleStalkFunctor X x).obj M)) := h
    exact Module.Flat.of_linearEquiv
      (ModuleCat.restrictScalarsId'App (RingHom.id _) rfl
        ((Modules.moduleStalkFunctor X x).obj M)).toLinearEquiv.symm
  · intro h x
    have h := h x
    dsimp [Modules.IsFlatOver]
    rw [Scheme.Hom.stalkMap_id]
    change Module.Flat (X.presheaf.stalk x)
      ((ModuleCat.restrictScalars (RingHom.id (X.presheaf.stalk x))).obj
        ((Modules.moduleStalkFunctor X x).obj M))
    letI : Module.Flat (X.presheaf.stalk x)
        ((Modules.moduleStalkFunctor X x).obj M) := h
    exact Module.Flat.of_linearEquiv
      (ModuleCat.restrictScalarsId'App (RingHom.id _) rfl
        ((Modules.moduleStalkFunctor X x).obj M)).toLinearEquiv

end Scheme

end AlgebraicGeometry
