/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Etale
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FlatMono
import Tengoku.LanaOka.Oka.AlgebraicGeometry.AlgClosed.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite étale morphisms bijective on closed points are isomorphisms

Let `K` be an algebraically closed field, `Y` a scheme locally of finite type over `K` and
`f : X ⟶ Y` a finite étale morphism which is injective and surjective on closed points. Then `f`
is an isomorphism.

Proof: the two projections `X ×_Y X ⟶ X` agree on closed points (closed points map to closed
points between Jacobson schemes locally of finite type, and `f` is injective on them), hence are
equal because `f` is unramified (`AlgebraicGeometry.ext_of_apply_eq_of_formallyUnramified`).
Thus `f` is a monomorphism. Its image is closed (`f` is finite) and contains all closed points,
hence is everything (`Y` is Jacobson). A flat, quasi-compact, surjective monomorphism is an
isomorphism (`AlgebraicGeometry.Flat.isIso_of_surjective_of_mono`).

## Main results

- `AlgebraicGeometry.mono_of_injOn_closedPoints`: a formally unramified morphism locally of finite
  type between schemes locally of finite type over `K` which is injective on closed points is a
  monomorphism.
- `AlgebraicGeometry.isIso_of_isFinite_of_etale_of_bijOn_closedPoints`: a finite étale morphism
  which is injective and surjective on closed points is an isomorphism.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]

/-- A closed morphism `f : X ⟶ Y` into a Jacobson scheme whose image contains all closed points
of `Y` is surjective. -/
theorem surjective_of_isClosedMap_of_closedPoints_subset [JacobsonSpace Y] (f : X ⟶ Y)
    (hf : IsClosedMap f) (hsurj : ∀ y : Y, IsClosed {y} → ∃ x, f x = y) : Surjective f := by
  refine ⟨fun y ↦ ?_⟩
  have hcl : IsClosed (Set.range f) := hf.isClosed_range
  have hsub : closedPoints Y ⊆ Set.range f := fun y hy ↦ hsurj y hy
  have : Set.range f = Set.univ := by
    rw [← hcl.closure_eq, ← Set.univ_subset_iff]
    exact (closure_closedPoints (X := Y)).symm.subset.trans (closure_mono hsub)
  exact this.symm.subset (Set.mem_univ y)

end AlgebraicGeometry
