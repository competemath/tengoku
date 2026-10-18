/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Flat
import Tengoku.Seed.AlgebraicGeometry.Geometrically.Integral
import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Algebra
import Tengoku.LanaBelyi.Belyi.Definable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descent of geometric integrality along a field extension

This file provides the geometric-integrality half of the descent step **B3c** (taxis #167,
child #204): if the base change `X₀ ×_{Spec k} Spec K` of a scheme `X₀ / k` along a field
extension `k ⊆ K` is geometrically integral over `K`, then `X₀` is geometrically integral
over `k`.

The mathematical content is packaged as two reusable statements:

* `AlgebraicGeometry.IsIntegral.of_flat_surjective`: integrality of the source of a flat
  surjective morphism of schemes descends to the target. (Reducedness descends because the
  stalk maps are faithfully flat, hence injective; irreducibility descends because a
  surjective continuous image of an irreducible space is irreducible.)
* `Belyi.geometricallyIntegral_of_baseChange`: geometric integrality of the base change of
  `X₀ / k` along `k ⊆ K` descends to `X₀ / k`. Given a field `L / k` to test against, one
  builds a common field extension `M` of `L` and `K` over `k` (a residue field of the
  tensor product `L ⊗[k] K`); the fibre `X₀ ×_k L` becomes integral after base change to
  `M`, and integrality then descends from `X₀ ×_k M` to `X₀ ×_k L` by
  `IsIntegral.of_flat_surjective`.
-/

universe u

open CategoryTheory Limits MorphismProperty TensorProduct

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **Integrality descends along a flat surjective morphism of schemes.** If `p : X ⟶ Y` is
flat and surjective and `X` is integral, then `Y` is integral.

Reducedness descends because each stalk map `𝒪_{Y, p x} ⟶ 𝒪_{X, x}` is a flat local
homomorphism of local rings, hence faithfully flat and injective, so a reduced stalk of `X`
forces the corresponding stalk of `Y` to be reduced. Irreducibility descends because `Y` is
the continuous surjective image of the irreducible space `X`. -/
theorem IsIntegral.of_flat_surjective (p : X ⟶ Y) [Flat p] [Surjective p] [IsIntegral X] :
    IsIntegral Y := by
  have hsurj : Function.Surjective p.base := ‹Surjective p›.surj
  haveI : Nonempty X := IrreducibleSpace.toNonempty
  -- `Y` is irreducible: it is the surjective continuous image of the irreducible space `X`.
  haveI : IrreducibleSpace Y := by
    have himg : p.base '' Set.univ = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ.mpr hsurj]
    have hpre : IsPreirreducible (Set.univ : Set Y) := by
      have := (PreirreducibleSpace.isPreirreducible_univ (X := X)).image p.base
        p.continuous.continuousOn
      rwa [himg] at this
    exact { toPreirreducibleSpace := ⟨hpre⟩, toNonempty := ⟨p.base (Classical.arbitrary X)⟩ }
  -- `Y` is reduced: each stalk map is faithfully flat, hence injective.
  haveI : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    algebraize [(p.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (p.base x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap p x) (p.toLRSHom.prop x)
    exact isReduced_of_injective (p.stalkMap x).hom ‹RingHom.FaithfullyFlat _›.injective
  haveI : IsReduced Y := isReduced_of_isReduced_stalk (X := Y)
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

end AlgebraicGeometry

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

end Belyi
