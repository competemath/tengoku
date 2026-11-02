/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion
import Tengoku.Seed.AlgebraicGeometry.IdealSheaf.Basic
import Tengoku.Seed.AlgebraicGeometry.AffineScheme

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Route E27: the stalk kernel of a closed immersion is the localised ideal

For a closed immersion `j : V ⟶ W`, an affine open `U ∋ j q`, the kernel of the stalk map
`𝒪_{W, j q} → 𝒪_{V,q}` is the extension of `ker (j^♯_U) = j.ker.ideal U` through the germ map.
(Both stalks are localisations of the affine rings and `j^♯_U` is surjective.)
-/
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace AlgebraicGeometry.Chow.M7
namespace E27

theorem ker_stalkMap_eq_map_germ {V W : Scheme.{u}} (j : V ⟶ W) [IsClosedImmersion j]
    (U : W.affineOpens) (q : V) (hq : j q ∈ U.1) :
    RingHom.ker (j.stalkMap q).hom =
      (RingHom.ker (j.app U.1).hom).map (W.presheaf.germ U.1 (j q) hq).hom := by
  have hq' : q ∈ j ⁻¹ᵁ U.1 := hq
  have hV : IsAffineOpen (j ⁻¹ᵁ U.1) := IsAffineHom.isAffine_preimage _ U.2
  letI : Algebra Γ(W, U.1) (W.presheaf.stalk (j q)) :=
    W.presheaf.algebra_section_stalk ⟨j q, hq⟩
  haveI hlocW := U.2.isLocalization_stalk ⟨j q, hq⟩
  letI : Algebra Γ(V, j ⁻¹ᵁ U.1) (V.presheaf.stalk q) :=
    V.presheaf.algebra_section_stalk ⟨q, hq'⟩
  haveI hlocV := hV.isLocalization_stalk ⟨q, hq'⟩
  have hsurj : Function.Surjective (j.app U.1).hom := j.app_surjective U.1 U.2
  have hgerm : ∀ r : Γ(W, U.1), (j.stalkMap q).hom (W.presheaf.germ U.1 (j q) hq r) =
      V.presheaf.germ (j ⁻¹ᵁ U.1) q hq' ((j.app U.1).hom r) := fun r =>
    Scheme.Hom.germ_stalkMap_apply j U.1 q hq r
  apply le_antisymm
  · intro s hs
    obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj
      (U.2.primeIdealOf ⟨j q, hq⟩).asIdeal.primeCompl s
    have hs0 : (j.stalkMap q).hom s = 0 := hs
    have h1 := congrArg (j.stalkMap q).hom hrt
    rw [map_mul, hs0, zero_mul] at h1
    have h2 : V.presheaf.germ (j ⁻¹ᵁ U.1) q hq' ((j.app U.1).hom r) = 0 := by
      have := hgerm r
      rw [← this]
      exact h1.symm
    have h3 : algebraMap Γ(V, j ⁻¹ᵁ U.1) (V.presheaf.stalk q) ((j.app U.1).hom r) = 0 := h2
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
      (hV.primeIdealOf ⟨q, hq'⟩).asIdeal.primeCompl _ _).mp h3
    obtain ⟨m₀, hm₀⟩ := hsurj (m : Γ(V, j ⁻¹ᵁ U.1))
    have hmu : IsUnit (algebraMap Γ(V, j ⁻¹ᵁ U.1) (V.presheaf.stalk q) (m : Γ(V, j ⁻¹ᵁ U.1))) :=
      IsLocalization.map_units (V.presheaf.stalk q) m
    have hm₀u : IsUnit (W.presheaf.germ U.1 (j q) hq m₀) := by
      refine isUnit_of_map_unit (j.stalkMap q).hom _ ?_
      rw [hgerm, hm₀]
      exact hmu
    have htu : IsUnit (algebraMap Γ(W, U.1) (W.presheaf.stalk (j q)) (t : Γ(W, U.1))) :=
      IsLocalization.map_units (W.presheaf.stalk (j q)) t
    have hker : m₀ * r ∈ RingHom.ker (j.app U.1).hom := by
      rw [RingHom.mem_ker, map_mul, hm₀]
      exact hm
    have hmem : s * (algebraMap Γ(W, U.1) (W.presheaf.stalk (j q)) (t : Γ(W, U.1)) *
        W.presheaf.germ U.1 (j q) hq m₀) ∈
        (RingHom.ker (j.app U.1).hom).map (W.presheaf.germ U.1 (j q) hq).hom := by
      have : s * (algebraMap Γ(W, U.1) (W.presheaf.stalk (j q)) (t : Γ(W, U.1)) *
          W.presheaf.germ U.1 (j q) hq m₀) =
          W.presheaf.germ U.1 (j q) hq (m₀ * r) := by
        rw [map_mul, ← mul_assoc, hrt, mul_comm]
        rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ hker
    exact (Ideal.mul_unit_mem_iff_mem _ (htu.mul hm₀u)).mp hmem
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, hgerm]
    rw [RingHom.mem_ker] at ha
    rw [ha, map_zero]

theorem ker_stalkMap_eq_map_germ_ker {V W : Scheme.{u}} (j : V ⟶ W) [IsClosedImmersion j]
    (U : W.affineOpens) (q : V) (hq : j q ∈ U.1) :
    RingHom.ker (j.stalkMap q).hom = (j.ker.ideal U).map (W.presheaf.germ U.1 (j q) hq).hom := by
  rw [Scheme.Hom.ker_apply]
  exact ker_stalkMap_eq_map_germ j U q hq

end E27
end AlgebraicGeometry.Chow.M7
