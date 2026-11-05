/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Affine
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FiniteType
import Tengoku.Seed.AlgebraicGeometry.Morphisms.QuasiCompact
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Separated
import Tengoku.Seed.AlgebraicGeometry.Properties
import Tengoku.Seed.AlgebraicGeometry.FunctionField
import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Algebra
import Tengoku.Seed.LinearAlgebra.Dimension.Free

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Affine models of finite extensions

This module turns a finitely generated field together with a finite field
extension into an honest affine scheme over the original ground field.  If
`K = k(a_i)` and `L / K` is finite, adjoining the images of the `a_i` and a
finite `K`-basis of `L` gives a finitely generated integral `k`-algebra whose
fraction field is `L`.

The resulting affine scheme is integral, separated, quasi-compact, and
locally of finite type over `Spec k`.  It is the basic chart used to replace
the finite normal fields in the normalized correspondence chunk by concrete
scheme models before Weil gluing.

This module is part of the formalization of the
Evans--Hrushovski--Gismatullin reconstruction theorem; the source of truth
is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry

universe u v

namespace FiniteExtensionChart

variable {k K L : Type u} {ι : Type v} [Field k] [Field K] [Field L]
  [Algebra K L] [Algebra k L] [FiniteDimensional K L]

/-- A finite family of generators for `L` as a field over `k`: the displayed
parameters, followed by a chosen `K`-basis of the finite extension.-/
def generators (a : ι → K) :
    ι ⊕ Fin (Module.finrank K L) → L
  | Sum.inl i => algebraMap K L (a i)
  | Sum.inr j => Module.finBasis K L j

variable [Algebra k K] [IsScalarTower k K L]

omit [FiniteDimensional K L] in
/-- The original parameter coordinates, viewed in the field that they
generate.-/
def liftedCoordinates (a : ι → K) :
    ι → adjoin k (Set.range a) :=
  fun i ↦ ⟨a i, subset_adjoin k _ (Set.mem_range_self i)⟩

omit [FiniteDimensional K L] in
@[simp]
theorem liftedCoordinates_coe (a : ι → K) (i : ι) :
    (liftedCoordinates (k := k) a i : K) = a i :=
  rfl

omit [FiniteDimensional K L] in
/-- The lifted parameter coordinates generate their intermediate field.-/
theorem adjoin_liftedCoordinates_eq_top (a : ι → K) :
    adjoin k (Set.range (liftedCoordinates (k := k) a)) = ⊤ := by
  let A := adjoin k (Set.range a)
  apply A.lift_injective
  rw [A.lift_adjoin, A.lift_top]
  change adjoin k (Subtype.val ''
    Set.range (liftedCoordinates (k := k) a)) = A
  congr 1
  ext x
  simp [liftedCoordinates]

/-- Adding a `K`-basis to coordinates that generate `K / k` generates all
of the finite extension `L / k`.-/
theorem adjoin_generators_eq_top (a : ι → K)
    (ha : adjoin k (Set.range a) = ⊤) :
    adjoin k (Set.range (generators (K := K) (L := L) a)) = ⊤ := by
  let b := Module.finBasis K L
  let e : K →ₐ[k] L := IsScalarTower.toAlgHom k K L
  let F := adjoin k (Set.range (generators (K := K) (L := L) a))
  have hmap : (⊤ : IntermediateField k K).map e ≤ F := by
    rw [← ha, adjoin_map]
    apply adjoin.mono
    rintro y ⟨x, ⟨i, rfl⟩, rfl⟩
    exact Set.mem_range_self
      (Sum.inl i : ι ⊕ Fin (Module.finrank K L))
  apply top_unique
  intro z hz
  change z ∈ F
  rw [← b.sum_repr z]
  apply sum_mem
  intro i hi
  rw [Algebra.smul_def]
  apply mul_mem
  · apply hmap
    change e (b.repr z i) ∈ (⊤ : IntermediateField k K).map e
    exact ⟨b.repr z i, Set.mem_univ _, rfl⟩
  · exact subset_adjoin k
      (Set.range (generators (K := K) (L := L) a))
      (Set.mem_range_self
        (Sum.inr i : ι ⊕ Fin (Module.finrank K L)))

/-- The finitely generated integral coordinate ring of the affine extension
chart.-/
def coordinateRing (a : ι → K) : Subalgebra k L :=
  Algebra.adjoin k (Set.range (generators (K := K) (L := L) a))

/-- The chosen field generators, regarded as elements of the chart
coordinate ring.-/
def coordinateGenerators (a : ι → K) :
    ι ⊕ Fin (Module.finrank K L) →
      coordinateRing (k := k) (K := K) (L := L) a :=
  fun i ↦ ⟨generators (K := K) (L := L) a i,
    Algebra.subset_adjoin (Set.mem_range_self i)⟩

omit [Algebra k K] [IsScalarTower k K L] in
/-- The chosen coordinate-ring generators generate the whole chart algebra
over the ground field.-/
theorem adjoin_coordinateGenerators_eq_top (a : ι → K) :
    Algebra.adjoin k (Set.range
      (coordinateGenerators (k := k) (K := K) (L := L) a)) = ⊤ := by
  let C := coordinateRing (k := k) (K := K) (L := L) a
  apply Subalgebra.map_injective (f := C.val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  change Algebra.adjoin k
      (C.val '' Set.range
        (coordinateGenerators (k := k) (K := K) (L := L) a)) = C
  have hrange : C.val '' Set.range
      (coordinateGenerators (k := k) (K := K) (L := L) a) =
      Set.range (generators (K := K) (L := L) a) := by
    ext z
    constructor
    · rintro ⟨c, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨coordinateGenerators (k := k) (K := K) (L := L) a i,
        ⟨i, rfl⟩, rfl⟩
  rw [hrange]
  rfl

/-- The affine scheme attached to a finite extension chart.-/
abbrev scheme (a : ι → K) : Scheme :=
  Spec (.of (coordinateRing (k := k) (K := K) (L := L) a))

/-- The structure morphism from a finite extension chart to `Spec k`.-/
def structureMap (a : ι → K) :
    scheme (k := k) (K := K) (L := L) a ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap k (coordinateRing (k := k) (K := K) (L := L) a)))

instance finiteType [Finite ι] (a : ι → K) :
    Algebra.FiniteType k
      (coordinateRing (k := k) (K := K) (L := L) a) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)

instance locallyOfFiniteType [Finite ι] (a : ι → K) :
    LocallyOfFiniteType
      (structureMap (k := k) (K := K) (L := L) a) := by
  unfold structureMap scheme
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

instance quasiCompact (a : ι → K) :
    QuasiCompact
      (structureMap (k := k) (K := K) (L := L) a) := by
  unfold structureMap scheme
  infer_instance

/-- Every affine extension chart is separated as an absolute scheme.-/
instance schemeSeparated (a : ι → K) :
    (scheme (k := k) (K := K) (L := L) a).IsSeparated := by
  unfold scheme
  infer_instance

instance integral (a : ι → K) :
    IsIntegral (scheme (k := k) (K := K) (L := L) a) := by
  unfold scheme
  infer_instance

/-- The ground-field algebra structure on the function field of a chart.-/
noncomputable instance functionFieldAlgebra (a : ι → K) :
    Algebra k (scheme (k := k) (K := K) (L := L) a).functionField :=
  RingHom.toAlgebra <|
    (StructureSheaf.toStalk
      (coordinateRing (k := k) (K := K) (L := L) a)
      (genericPoint (Spec (.of
        (coordinateRing (k := k) (K := K) (L := L) a))))).hom.comp
      (algebraMap k (coordinateRing (k := k) (K := K) (L := L) a))

/-- The intermediate field generated by the coordinate ring generators.
It is a concrete fraction field of `coordinateRing`.-/
def generatedField (a : ι → K) : IntermediateField k L :=
  adjoin k (Set.range (generators (K := K) (L := L) a))

instance coordinateRingAlgebraGeneratedField (a : ι → K) :
    Algebra (coordinateRing (k := k) (K := K) (L := L) a)
      (generatedField (k := k) (K := K) (L := L) a) := by
  change Algebra
    (Algebra.adjoin k (Set.range (generators (K := K) (L := L) a)))
    (adjoin k (Set.range (generators (K := K) (L := L) a)))
  infer_instance

instance isFractionRing (a : ι → K) :
    IsFractionRing (coordinateRing (k := k) (K := K) (L := L) a)
      (generatedField (k := k) (K := K) (L := L) a) := by
  change IsFractionRing
    (Algebra.adjoin k (Set.range (generators (K := K) (L := L) a)))
    (adjoin k (Set.range (generators (K := K) (L := L) a)))
  infer_instance

/-- When the displayed coordinates generate `K`, the fraction field of
the affine chart is canonically equivalent to `L`.-/
def generatedFieldEquiv (a : ι → K)
    (ha : adjoin k (Set.range a) = ⊤) :
    generatedField (k := k) (K := K) (L := L) a ≃ₐ[k] L :=
  (IntermediateField.equivOfEq
    (adjoin_generators_eq_top (K := K) (L := L) a ha)).trans
      IntermediateField.topEquiv

/-- When the displayed coordinates generate `K`, the ambient extension field
`L` itself is a fraction field of the chart coordinate ring.  This formulation
is convenient for clearing denominators directly inside `L`.-/
theorem isFractionRing_extension (a : ι → K)
    (ha : adjoin k (Set.range a) = ⊤) :
    IsFractionRing
      (coordinateRing (k := k) (K := K) (L := L) a) L := by
  apply IsFractionRing.of_field
  intro z
  let z' : generatedField (k := k) (K := K) (L := L) a :=
    ⟨z, by
      change z ∈ adjoin k
        (Set.range (generators (K := K) (L := L) a))
      rw [adjoin_generators_eq_top (K := K) (L := L) a ha]
      trivial⟩
  obtain ⟨x, y, hy, hxy⟩ :=
    IsFractionRing.div_surjective
      (coordinateRing (k := k) (K := K) (L := L) a) z'
  refine ⟨x, y, ?_⟩
  exact (congr_arg Subtype.val hxy).symm

/-- The scheme-theoretic function field of a chart, identified over `k`
with the selected ambient finite extension.-/
noncomputable def functionFieldAlgEquiv (a : ι → K)
    (ha : adjoin k (Set.range a) = ⊤) :
    (scheme (k := k) (K := K) (L := L) a).functionField ≃ₐ[k] L := by
  unfold scheme
  let A := coordinateRing (k := k) (K := K) (L := L) a
  letI : Algebra k (Spec (.of A)).functionField :=
    RingHom.toAlgebra <| (StructureSheaf.toStalk A
      (genericPoint (Spec (.of A)))).hom.comp (algebraMap k A)
  letI : Algebra A (Spec (.of A)).functionField :=
    RingHom.toAlgebra <| (StructureSheaf.toStalk A
      (genericPoint (Spec (.of A)))).hom
  letI : IsFractionRing A (Spec (.of A)).functionField := by
    change IsFractionRing (↑(CommRingCat.of A)) _
    exact functionField_isFractionRing_of_affine _
  letI : IsFractionRing A L := isFractionRing_extension a ha
  letI : IsScalarTower k A (Spec (.of A)).functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact (IsLocalization.algEquiv (nonZeroDivisors A)
    (Spec (.of A)).functionField L).restrictScalars k

/-- The chart function-field equivalence sends the generic germ of a
coordinate-ring element to that element in the selected ambient field.-/
theorem functionFieldAlgEquiv_toStalk (a : ι → K)
    (ha : adjoin k (Set.range a) = ⊤)
    (z : coordinateRing (k := k) (K := K) (L := L) a) :
    functionFieldAlgEquiv (k := k) (K := K) (L := L) a ha
        ((StructureSheaf.toStalk
          (coordinateRing (k := k) (K := K) (L := L) a)
          (genericPoint (scheme (k := k) (K := K) (L := L) a))) z) =
      (z : L) := by
  unfold scheme
  let A := coordinateRing (k := k) (K := K) (L := L) a
  letI : Algebra A (Spec (.of A)).functionField :=
    RingHom.toAlgebra <| (StructureSheaf.toStalk A
      (genericPoint (Spec (.of A)))).hom
  letI : IsFractionRing A (Spec (.of A)).functionField := by
    change IsFractionRing (↑(CommRingCat.of A)) _
    exact functionField_isFractionRing_of_affine _
  letI : IsFractionRing A L := isFractionRing_extension a ha
  unfold functionFieldAlgEquiv
  dsimp only
  exact (IsLocalization.algEquiv (nonZeroDivisors A)
    (Spec (.of A)).functionField L).commutes z

/-- A displayed parameter as an element of the affine coordinate ring.-/
def parameter (a : ι → K) (i : ι) :
    coordinateRing (k := k) (K := K) (L := L) a :=
  ⟨algebraMap K L (a i), Algebra.subset_adjoin
    (Set.mem_range_self
      (Sum.inl i : ι ⊕ Fin (Module.finrank K L)))⟩

omit [Algebra k K] [IsScalarTower k K L] in
@[simp]
theorem parameter_coe (a : ι → K) (i : ι) :
    (parameter (k := k) (K := K) (L := L) a i : L) =
      algebraMap K L (a i) :=
  rfl

end FiniteExtensionChart

end

end AclGeom
