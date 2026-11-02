/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.PrincipalStalkQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local length through closed factors

Restriction of scalars along a surjective ring homomorphism preserves module length. Applied to
the surjective stalk maps of closed immersions, this shows that the local length of a composite
through a closed subscheme can be computed over the intermediate stalk. For a finite closed
intersection, the ambient local multiplicity can therefore be computed over either factor, and
the natural-number multiplicity coincides with either projected length. If the corresponding
pullback projection has a principal stalk kernel, that multiplicity is the principal-divisor
coefficient on the factor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace AlgebraicGeometry.Chow

/-- Composing with a closed immersion does not change local length: the outer stalk acts through
the surjective map to the intermediate stalk.-/
theorem morphismLocalLength_comp_closedImmersion
    {Z Y X : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    [IsClosedImmersion g] (z : Z) :
    morphismLocalLength (f ≫ g) z = morphismLocalLength f z := by
  unfold morphismLocalLength
  letI : Algebra ↑(X.presheaf.stalk ((f ≫ g) z))
      ↑(Y.presheaf.stalk (f z)) :=
    (g.stalkMap (f z)).hom.toAlgebra
  letI : Algebra ↑(Y.presheaf.stalk (f z)) ↑(Z.presheaf.stalk z) :=
    (f.stalkMap z).hom.toAlgebra
  letI : Algebra ↑(X.presheaf.stalk ((f ≫ g) z)) ↑(Z.presheaf.stalk z) :=
    ((f ≫ g).stalkMap z).hom.toAlgebra
  letI : IsScalarTower ↑(X.presheaf.stalk ((f ≫ g) z))
      ↑(Y.presheaf.stalk (f z)) ↑(Z.presheaf.stalk z) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      change ((f ≫ g).stalkMap z).hom r =
        (f.stalkMap z).hom ((g.stalkMap (f z)).hom r)
      rw [Scheme.Hom.stalkMap_comp]
      rfl)
  exact Module.length_eq_of_surjective (g.stalkMap_surjective (f z))

namespace FiniteClosedIntersectionData

/-- The ambient local length of a finite closed intersection equals its length over the first
closed factor.-/
theorem morphismLocalLength_eq_fst
    {X : Scheme.{u}} {p : ℕ} (d : FiniteClosedIntersectionData X p)
    (z : d.intersection) :
    morphismLocalLength d.toX z =
      morphismLocalLength (Limits.pullback.fst d.i d.j) z := by
  exact morphismLocalLength_comp_closedImmersion
    (Limits.pullback.fst d.i d.j) d.i z

/-- The ambient local length of a finite closed intersection equals its length over the second
closed factor.-/
theorem morphismLocalLength_eq_snd
    {X : Scheme.{u}} {p : ℕ} (d : FiniteClosedIntersectionData X p)
    (z : d.intersection) :
    morphismLocalLength d.toX z =
      morphismLocalLength (Limits.pullback.snd d.i d.j) z := by
  rw [show d.toX = Limits.pullback.snd d.i d.j ≫ d.j by
    exact Limits.pullback.condition]
  exact morphismLocalLength_comp_closedImmersion
    (Limits.pullback.snd d.i d.j) d.j z

/-- Ambient intersection multiplicity equals local length over the first closed factor.-/
theorem localMultiplicity_eq_fst
    {X : Scheme.{u}} {p : ℕ} (d : FiniteClosedIntersectionData X p)
    (z : d.intersection) :
    d.localMultiplicity z =
      (morphismLocalLength (Limits.pullback.fst d.i d.j) z).toNat := by
  change (morphismLocalLength d.toX z).toNat =
    (morphismLocalLength (Limits.pullback.fst d.i d.j) z).toNat
  rw [d.morphismLocalLength_eq_fst]

/-- Ambient intersection multiplicity equals local length over the second closed factor.-/
theorem localMultiplicity_eq_snd
    {X : Scheme.{u}} {p : ℕ} (d : FiniteClosedIntersectionData X p)
    (z : d.intersection) :
    d.localMultiplicity z =
      (morphismLocalLength (Limits.pullback.snd d.i d.j) z).toNat := by
  change (morphismLocalLength d.toX z).toNat =
    (morphismLocalLength (Limits.pullback.snd d.i d.j) z).toNat
  rw [d.morphismLocalLength_eq_snd]

end FiniteClosedIntersectionData

end AlgebraicGeometry.Chow
