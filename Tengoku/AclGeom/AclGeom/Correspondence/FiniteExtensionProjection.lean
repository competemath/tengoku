/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.FiniteExtensionChart
import Tengoku.AclGeom.AclGeom.Correspondence.PrincipalLocalization
import Tengoku.AclGeom.AclGeom.Correspondence.FunctionFieldEquivalence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dominant rational projections between finite-extension charts

A ground-field embedding of the target function field into the source
function field is the contravariant datum of a dominant rational map.  This
file spreads such an embedding to one explicit principal-open partial map
between `FiniteExtensionChart`s by clearing denominators of a finite family
of target coordinate-ring generators.

Unlike a birational transition, the field map need not be surjective.  This
is the form needed for the three projections from a normalized
multiplication graph to its two input charts and its output chart.
-/

namespace AclGeom

noncomputable section

open IntermediateField
open AlgebraicGeometry
open CategoryTheory
open scoped nonZeroDivisors

universe u v w

namespace FiniteExtensionProjection

variable {k K₁ K₂ L₁ L₂ : Type u} {ι₁ : Type v} {ι₂ : Type w}
  [Field k] [Field K₁] [Field K₂] [Field L₁] [Field L₂]
  [Algebra k K₁] [Algebra K₁ L₁] [Algebra k L₁]
  [IsScalarTower k K₁ L₁] [FiniteDimensional K₁ L₁]
  [Algebra k K₂] [Algebra K₂ L₂] [Algebra k L₂]
  [IsScalarTower k K₂ L₂] [FiniteDimensional K₂ L₂]

/-- The target coordinate ring embedded in the source extension field.-/
def projectionAlgHom (a₂ : ι₂ → K₂) (e : L₂ →ₐ[k] L₁) :
    FiniteExtensionChart.coordinateRing
        (k := k) (K := K₂) (L := L₂) a₂ →ₐ[k] L₁ :=
  e.comp (Subalgebra.val _)

omit [Algebra k K₂] [IsScalarTower k K₂ L₂] in
/-- A field embedding is injective on the target coordinate ring.-/
theorem projectionAlgHom_injective (a₂ : ι₂ → K₂) (e : L₂ →ₐ[k] L₁) :
    Function.Injective (projectionAlgHom (k := k) a₂ e) :=
  e.injective.comp Subtype.val_injective

/-- The contravariant embedding between the scheme-theoretic function
fields induced by an embedding of the selected ambient extension fields.-/
def functionFieldAlgHom
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₂ →ₐ[k] L₁) :
    (FiniteExtensionChart.scheme
      (k := k) (K := K₂) (L := L₂) a₂).functionField →ₐ[k]
      (FiniteExtensionChart.scheme
        (k := k) (K := K₁) (L := L₁) a₁).functionField :=
  (FiniteExtensionChart.functionFieldAlgEquiv a₁ ha₁).symm.toAlgHom.comp
    (e.comp (FiniteExtensionChart.functionFieldAlgEquiv a₂ ha₂).toAlgHom)

/-- Conjugating the scheme-theoretic function-field embedding back to the
selected ambient extension fields recovers the original embedding.-/
@[simp] theorem functionFieldAlgHom_commutes
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤)
    (ha₂ : adjoin k (Set.range a₂) = ⊤)
    (e : L₂ →ₐ[k] L₁)
    (z : (FiniteExtensionChart.scheme
      (k := k) (K := K₂) (L := L₂) a₂).functionField) :
    FiniteExtensionChart.functionFieldAlgEquiv
        (k := k) (K := K₁) (L := L₁) a₁ ha₁
        (functionFieldAlgHom a₁ a₂ ha₁ ha₂ e z) =
      e (FiniteExtensionChart.functionFieldAlgEquiv
        (k := k) (K := K₂) (L := L₂) a₂ ha₂ z) := by
  simp [functionFieldAlgHom]

/-- A ground-field embedding of the target function field into the source
function field spreads to a dominant map on one dense principal open.-/
def partialMap [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤) (e : L₂ →ₐ[k] L₁) :
    (FiniteExtensionChart.scheme
      (k := k) (K := K₁) (L := L₁) a₁).PartialMap
      (FiniteExtensionChart.scheme
        (k := k) (K := K₂) (L := L₂) a₂) := by
  letI : IsFractionRing
      (FiniteExtensionChart.coordinateRing
        (k := k) (K := K₁) (L := L₁) a₁) L₁ :=
    FiniteExtensionChart.isFractionRing_extension a₁ ha₁
  exact PrincipalLocalization.partialMapOfGenerators
    (FiniteExtensionChart.coordinateGenerators
      (k := k) (K := K₂) (L := L₂) a₂)
    (FiniteExtensionChart.adjoin_coordinateGenerators_eq_top
      (k := k) (K := K₂) (L := L₂) a₂)
    (projectionAlgHom (k := k) a₂ e)
    (projectionAlgHom_injective (k := k) a₂ e)

instance partialMap_isDominant [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤) (e : L₂ →ₐ[k] L₁) :
    IsDominant (partialMap (k := k) a₁ a₂ ha₁ e).hom := by
  letI : IsFractionRing
      (FiniteExtensionChart.coordinateRing
        (k := k) (K := K₁) (L := L₁) a₁) L₁ :=
    FiniteExtensionChart.isFractionRing_extension a₁ ha₁
  change IsDominant (PrincipalLocalization.partialMapOfGenerators
    (FiniteExtensionChart.coordinateGenerators
      (k := k) (K := K₂) (L := L₂) a₂)
    (FiniteExtensionChart.adjoin_coordinateGenerators_eq_top
      (k := k) (K := K₂) (L := L₂) a₂)
    (projectionAlgHom (k := k) a₂ e)
    (projectionAlgHom_injective (k := k) a₂ e)).hom
  infer_instance

/-- The dominant rational map represented by the explicit principal-open
projection.-/
def rationalMap [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤) (e : L₂ →ₐ[k] L₁) :
    Scheme.RationalMap
      (FiniteExtensionChart.scheme
        (k := k) (K := K₁) (L := L₁) a₁)
      (FiniteExtensionChart.scheme
        (k := k) (K := K₂) (L := L₂) a₂) :=
  (partialMap (k := k) a₁ a₂ ha₁ e).toRationalMap

instance rationalMap_isDominant [Fintype ι₂]
    (a₁ : ι₁ → K₁) (a₂ : ι₂ → K₂)
    (ha₁ : adjoin k (Set.range a₁) = ⊤) (e : L₂ →ₐ[k] L₁) :
    (rationalMap (k := k) a₁ a₂ ha₁ e).IsDominant := by
  unfold rationalMap
  infer_instance

end FiniteExtensionProjection

end

end AclGeom
