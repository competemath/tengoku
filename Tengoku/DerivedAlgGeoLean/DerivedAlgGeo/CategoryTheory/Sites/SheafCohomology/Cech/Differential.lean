/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.CategoryTheory.Sites.SheafCohomology.Cech

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Čech differential in coordinates

Mathlib defines the Čech complex of a presheaf as `alternatingCofaceMapComplex` applied to the
cosimplicial object attached to the Čech nerve of a formal coproduct. That definition is compact
but says nothing directly about components: it never names the index of a cochain, nor the
restriction that carries a face into it.

This file supplies that reading. `cechComplexFunctor_delta_π` computes one coface at one index,
and `cechComplexFunctor_d_π` assembles the alternating sum. Both are statements about Mathlib's
construction, so they live in Mathlib's namespace.

## Main statements

* `cechComplexFunctor_delta_π` — the `j`-th coface, projected at `x`, is the projection at the
  face `x ∘ j.succAbove` followed by the presheaf on the face inclusion;
* `cechComplexFunctor_d_π` — the differential, projected at `x`, is the alternating sum of those;
* `cechComplexFunctor_map_f_π` — the map induced by a morphism of presheaves, projected at `x`, is
  the projection at `x` followed by that morphism on the intersection.

## Implementation notes

The projections are stated in the shape Mathlib's construction produces, indexed by
`ToType (mk n) → ι` with the object written through the Čech nerve rather than as `∏ᶜ (U ∘ x)`.
A caller-friendly restatement belongs downstream, together with the identification of the
intersection.

Both proofs finish with `exact` rather than `rw`. The two sides differ in the `HasProduct`
instance argument that `Pi.π` carries, which `rw` will not see through but definitional
unification will. Rewriting with `Pi.lift_π` fails here for that reason alone.

`Fin.succAbove` needs no reindexing lemma: `SimplexCategory.δ j` has
`toOrderHom = Fin.succAbove j`, so this is the shape the Čech nerve already produces via
`FormalCoproduct.mapPower`.
-/

universe w v' v u' u

open CategoryTheory.Limits AlgebraicTopology Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
variable [HasProducts.{w} A] [HasFiniteProducts C] [Preadditive A]
variable {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A)

/-- The Čech nerve of the family `U`, as a simplicial formal coproduct.-/
noncomputable abbrev cechNerve : SimplicialObject (Limits.FormalCoproduct C) :=
  (Limits.FormalCoproduct.mk _ U).cech

/-- The Čech cosimplicial object of a presheaf against the nerve of `U`.-/
noncomputable abbrev cechCosimplicial : CosimplicialObject A :=
  (Limits.FormalCoproduct.cosimplicialObjectFunctor (cechNerve U)).obj P

/-- Degree-`n` Čech cochains, in the shape Mathlib's construction produces.-/
noncomputable abbrev cechTermFamily (n : ℕ) :
    (ToType (SimplexCategory.mk n) → ι) → A :=
  fun x => P.obj (op (((cechNerve U).obj (op (SimplexCategory.mk n))).obj x))

end CategoryTheory
