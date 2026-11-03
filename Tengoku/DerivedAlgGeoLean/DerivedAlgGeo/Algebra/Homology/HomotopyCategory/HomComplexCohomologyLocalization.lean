/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexLocalization
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Module.Localization.Cohomology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Degree-zero cohomology of a localized Hom complex

The map on the concrete kernel/range quotient of the degree-zero Hom-complex
cohomology is a module localization when its three contributing cochain maps
are localizations. A bounded-above source, bounded-below target, and finite
presentation in the contributing source degrees supply those hypotheses.

This is not a derived-Hom or geometric base-change theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped ModuleCat.Algebra

namespace CochainComplex.HomComplex

universe u v w

noncomputable section

variable {R : Type u} [CommRing R]
  (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (S : Submonoid R)

private abbrev localized (E : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj E

private theorem delta_comp_delta
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    (E F : CochainComplex C ℤ) :
    (δ_hom R E F 0 1).comp (δ_hom R E F (-1) 0) = 0 := by
  apply LinearMap.ext
  intro γ
  change δ 0 1 (δ (-1) 0 γ) = 0
  exact δ_δ (-1) 0 1 γ

private theorem localized_delta_eq_map (i j : ℤ)
    [IsLocalizedModule S (cochainLocalizedMap P Q i S)]
    [IsLocalizedModule S (cochainLocalizedMap P Q j S)] :
    (IsLocalizedModule.map S (cochainLocalizedMap P Q i S)
      (cochainLocalizedMap P Q j S)) (δ_hom R P Q i j) =
      δ_hom R (localized S P) (localized S Q) i j := by
  apply IsLocalizedModule.linearMap_ext S (cochainLocalizedMap P Q i S)
    (cochainLocalizedMap P Q j S)
  apply LinearMap.ext
  intro γ
  simp only [LinearMap.comp_apply, IsLocalizedModule.map_apply]
  change (cochainLocalizedMap P Q j S) (δ i j γ) =
    δ i j ((cochainLocalizedMap P Q i S) γ)
  exact cochainLocalizedMap_delta P Q i S j γ

/-- Degree-zero cohomology of the Hom complex as cycles modulo boundaries.-/
abbrev concreteCohomology
    {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
    (E F : CochainComplex C ℤ) : Type w :=
  (δ_hom R E F 0 1).ker ⧸
    (IsLocalizedModule.boundaryToCycles
      (δ_hom R E F (-1) 0) (δ_hom R E F 0 1)
      (delta_comp_delta E F)).range

private def cohomologyEquivOfEq
    {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (d₀ d₀' : M₀ →ₗ[R] M₁) (d₁ d₁' : M₁ →ₗ[R] M₂)
    (hd : d₁.comp d₀ = 0) (hd' : d₁'.comp d₀' = 0)
    (h₀ : d₀ = d₀') (h₁ : d₁ = d₁') :
    (d₁.ker ⧸ (IsLocalizedModule.boundaryToCycles d₀ d₁ hd).range) ≃ₗ[R]
      (d₁'.ker ⧸ (IsLocalizedModule.boundaryToCycles d₀' d₁' hd').range) := by
  subst d₀'
  subst d₁'
  exact LinearEquiv.refl R _

private def localizedCohomologyEquiv
    (hprev : IsLocalizedModule S (cochainLocalizedMap P Q (-1) S))
    (hcur : IsLocalizedModule S (cochainLocalizedMap P Q 0 S))
    (hnext : IsLocalizedModule S (cochainLocalizedMap P Q 1 S)) :
    ((IsLocalizedModule.localizedDifferential S
        (cochainLocalizedMap P Q 0 S) (cochainLocalizedMap P Q 1 S)
        (δ_hom R P Q 0 1)).ker ⧸
      (IsLocalizedModule.localizedBoundaryToCycles S
        (cochainLocalizedMap P Q (-1) S)
        (cochainLocalizedMap P Q 0 S)
        (cochainLocalizedMap P Q 1 S)
        (δ_hom R P Q (-1) 0) (δ_hom R P Q 0 1)
        (delta_comp_delta P Q)).range) ≃ₗ[R]
      concreteCohomology (R := R) (localized S P) (localized S Q) := by
  letI := hprev
  letI := hcur
  letI := hnext
  have h₀ := localized_delta_eq_map P Q S (-1) 0
  have h₁ := localized_delta_eq_map P Q S 0 1
  have hd : ((IsLocalizedModule.map S (cochainLocalizedMap P Q 0 S)
      (cochainLocalizedMap P Q 1 S)) (δ_hom R P Q 0 1)).comp
      ((IsLocalizedModule.map S (cochainLocalizedMap P Q (-1) S)
        (cochainLocalizedMap P Q 0 S)) (δ_hom R P Q (-1) 0)) = 0 := by
    rw [h₀, h₁]
    exact delta_comp_delta (localized S P) (localized S Q)
  exact cohomologyEquivOfEq
    ((IsLocalizedModule.map S (cochainLocalizedMap P Q (-1) S)
      (cochainLocalizedMap P Q 0 S)) (δ_hom R P Q (-1) 0))
    (δ_hom R (localized S P) (localized S Q) (-1) 0)
    ((IsLocalizedModule.map S (cochainLocalizedMap P Q 0 S)
      (cochainLocalizedMap P Q 1 S)) (δ_hom R P Q 0 1))
    (δ_hom R (localized S P) (localized S Q) 0 1)
    hd (delta_comp_delta (localized S P) (localized S Q)) h₀ h₁

end

end CochainComplex.HomComplex
