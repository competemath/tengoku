/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
Adapted from the Apache-licensed `SchemeIsomorphismOpenShrink.lean`
in Vilin97/Clawristotle.
-/
import Tengoku.Seed.AlgebraicGeometry.Restrict

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Shrinking an isomorphism open

If a morphism is an isomorphism over a target open, an upstairs open can
be transported through the inverse to a smaller target open. Its inverse
image is the intersection with the original isomorphism locus.
-/

open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An isomorphism over an open remains an isomorphism after shrinking
the target open.
@isnad1 id=isiso.1h5v.s8.14b4446fd936 from=translated src=- shape=4763f09e vocab=6a11ab48
-/
theorem isIso_morphismRestrict_of_le
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U V : Y.Opens) (hVU : V ≤ U)
    [IsIso (f ∣_ U)] :
    IsIso (f ∣_ V) := by
  let h :=
    IsOpenImmersion.isPullback
      (f ∣_ V)
      (X.homOfLE (f.preimage_mono hVU))
      (Y.homOfLE hVU)
      (f ∣_ U)
      (morphismRestrict_homOfLE f V U hVU).symm
      (by
        simp only [Scheme.opensRange_homOfLE,
          ← Scheme.Hom.comp_preimage, morphismRestrict_ι])
  exact h.isIso_fst_of_isIso

/-- Transport an upstairs open through the inverse over a target
isomorphism open.-/
noncomputable def isomorphismTargetShrink
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) : Y.Opens :=
  U.ι ''ᵁ
    (((inv (f ∣_ U)) ≫ (f ⁻¹ᵁ U).ι) ⁻¹ᵁ W)

/-- The transported open is contained in the original isomorphism
open.
@isnad1 id=le.0h5v.s7.35720e7af024 from=translated src=- shape=1cb56a41 vocab=188d84dc
-/
theorem isomorphismTargetShrink_le
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) :
    f.isomorphismTargetShrink U W ≤ U :=
  U.ι_image_le _

/-- The inverse image of the transported open is its intersection with
the original isomorphism locus.
@isnad1 id=eq.0h5v.s9.3b90ca33db61 from=translated src=- shape=4368270d vocab=9e159b98
-/
theorem preimage_isomorphismTargetShrink
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) :
    f ⁻¹ᵁ f.isomorphismTargetShrink U W =
      (f ⁻¹ᵁ U) ⊓ W := by
  rw [isomorphismTargetShrink,
    ← image_morphismRestrict_preimage]
  simp only [← Scheme.Hom.comp_preimage,
    IsIso.hom_inv_id_assoc,
    Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]

/-- The morphism remains an isomorphism over the transported open.
@isnad1 id=isiso.0h5v.s8.70c7dc0a2b2f from=translated src=- shape=feae367e vocab=033334f6
-/
theorem isIso_isomorphismTargetShrink
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) :
    IsIso (f ∣_ f.isomorphismTargetShrink U W) :=
  f.isIso_morphismRestrict_of_le U _
    (f.isomorphismTargetShrink_le U W)

/-- A point lies in the transported target open when its inverse image
over the original open lies in the upstairs open.
@isnad1 id=mem.1h6v.s11.d1b170391990 from=translated src=- shape=c3ab8792 vocab=fbb06372
-/
theorem mem_isomorphismTargetShrink
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (W : X.Opens) (x : U.toScheme)
    (hx :
      (f ⁻¹ᵁ U).ι ((inv (f ∣_ U)) x) ∈ W) :
    U.ι x ∈ f.isomorphismTargetShrink U W := by
  change x ∈ U.ι ⁻¹ᵁ f.isomorphismTargetShrink U W
  rw [isomorphismTargetShrink,
    U.ι.preimage_image_eq]
  exact hx

end AlgebraicGeometry.Scheme.Hom
