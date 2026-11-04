/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.ProjectiveSpace
import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FiniteType
import Tengoku.Seed.AlgebraicGeometry.Properties

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Projective integral scheme classes over a commutative ring

The base scheme, scheme-class predicate and base-compatible projective integral
class are independent of Chow operations. The original public namespaces and
interfaces are retained so existing consumers can use this geometric provider.
-/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory SchemeProjectiveSpace

universe u

namespace AlgebraicGeometry.Chow.M7

section SpkDef

variable (k : Type u) [CommRing k]

/-- The base `Spec k`.-/
abbrev Spk : Scheme.{u} := Spec (CommRingCat.of k)

end SpkDef

namespace K3

section SchemeClassDef

variable (k : Type u) [CommRing k]

/-- A class of noetherian locally-finite-type `k`-schemes (a predicate on the scheme together
with its structure data).-/
abbrev SchemeClass : Type (u + 1) :=
  ∀ (X : Scheme.{u}) [X.Over (Spk k)] [LocallyOfFiniteType (X ↘ Spk k)] [IsNoetherian X], Prop

end SchemeClassDef

end K3

namespace CIICLASS

open K3

/-- **Integral, with a `k`-closed immersion into some `ℙᴺ_k`.**  Unlike `D28.ProjectiveIntegral`
the immersion is required to commute with the structure morphisms to `Spec k`.-/
def ProjectiveIntegralK (k : Type u) [CommRing k] : SchemeClass k := fun X _ _ _ ↦
  IsIntegral X ∧ ∃ (N : ℕ) (j : X ⟶ space k N), IsClosedImmersion j ∧
    j ≫ toSpec k N = X ↘ Spk k

/-- Integrality is invariant under isomorphism.
@isnad1 id=isintegr.0h3v.s3.40f52396ff52 from=translated src=- shape=a72e8271 vocab=760dc768
-/
theorem isIntegral_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) [IsIntegral Y] : IsIntegral X := by
  haveI : Nonempty X := ⟨e.inv (Classical.choice inferInstance)⟩
  exact isIntegral_of_isOpenImmersion e.hom

variable {k : Type u} [CommRing k]

/-- Closed `k`-subschemes of members are members once integral.
@isnad1 id=projecti.2h5v.s7.fc9ee7800455 from=translated src=- shape=13886bea vocab=0fed6ce4
-/
theorem projectiveIntegralK_of_closedImmersion {X Y : Scheme.{u}} [X.Over (Spk k)]
    [LocallyOfFiniteType (X ↘ Spk k)] [IsNoetherian X] (hX : ProjectiveIntegralK k X)
    [Y.Over (Spk k)] [LocallyOfFiniteType (Y ↘ Spk k)] [IsNoetherian Y]
    (f : Y ⟶ X) [IsClosedImmersion f] (hf : f ≫ X ↘ Spk k = Y ↘ Spk k) (hY : IsIntegral Y) :
    ProjectiveIntegralK k Y := by
  obtain ⟨-, N, j, hj, hjk⟩ := hX
  haveI := hj
  exact ⟨hY, N, f ≫ j, inferInstance, by rw [Category.assoc, hjk, hf]⟩

end CIICLASS

end AlgebraicGeometry.Chow.M7
