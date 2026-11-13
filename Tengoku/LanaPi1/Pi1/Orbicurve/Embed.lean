module

public import Tengoku.LanaPi1.Pi1.Orbicurve.SubfieldGalois

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Embedding covers of subfield orbicurves into `Ω`

Let `Ω` be algebraically closed and `B` a finite extension of `K₀ = k(t)` inside `Ω`. Every
domain `Z` finite type over `k`, integrally closed, and integral over the coordinate ring of `B`
(e.g. the coordinate ring of a finite étale cover of `ofSubfield B m`) is the coordinate ring of a
finite extension `L ⊇ B` inside `Ω` (`exists_algEquiv_coordRing`).
-/

@[expose] public section
namespace Tengoku.LanaPi1 end Tengoku.LanaPi1 open Tengoku.LanaPi1 
universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace Tengoku.LanaPi1.AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (t : Ω)

section Embed

variable [IsAlgClosed Ω] {B : IntermediateField (K₀ k t) Ω} [FiniteDimensional (K₀ k t) B]
  (Z : Type u) [CommRing Z] [IsDomain Z] [Algebra k Z] [IsIntegrallyClosed Z]
  [Algebra.FiniteType k Z]

/-- The inclusion of the coordinate ring of `B` into `Ω`.-/
noncomputable def coordRingVal : coordRing k t B →+* Ω :=
  B.val.toRingHom.comp (coordRing k t B).val.toRingHom

omit [IsAlgClosed Ω] [FiniteDimensional (K₀ k t) B] in
/--
@isnad1 id=injectiv.0h4v.s15.58f62e789738 from=translated src=- shape=14efd117 vocab=6c751c6c
-/
lemma coordRingVal_injective : Function.Injective (coordRingVal t (B := B)) :=
  fun _ _ h => Subtype.val_injective (Subtype.val_injective h)

omit [IsAlgClosed Ω] [FiniteDimensional (K₀ k t) B] in
/--
@isnad1 id=isintegr.1h5v.s13.9dc0fb062a4d from=translated src=- shape=e23865da vocab=936a8d91
-/
lemma isIntegral_A₀_of_coordRing {x : Ω} (h : IsIntegral (coordRing k t B) x) :
    IsIntegral (A₀ k t) x := by
  haveI : IsScalarTower (A₀ k t) (coordRing k t B) Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact isIntegral_trans (R := A₀ k t) (A := coordRing k t B) _ h

end Embed

end Tengoku.LanaPi1.AffOrbicurve
-- Tengoku: root names of this library moved to Tengoku.LanaPi1 so they do not collide with other libraries (generated)
