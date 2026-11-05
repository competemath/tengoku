/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.GroupConfig.Constructible.Basic
import Tengoku.Seed.RingTheory.MvPolynomial.Tower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closure operations on field-defined constructible sets

This module proves the finite Boolean, polynomial-substitution and ordinary
quantifier portions of `cor:constructible-closure` in the supplemental blueprint
`sources/group_configuration/09-constructibility.tex`. Enlarging the coefficient
field preserves constructibility. Finite-tuple quantification uses K-points
Chevalley and requires an algebraically closed ambient field; the other operations
do not require finite coordinate types or algebraic closedness.

The generic-quantifier lemma consumes Boolean operations and polynomial
substitution after adjoining its sampling tuple to the coefficient field. The
constructible graph and word relations consume ordinary quantifier closure.

**Status:** these closure operations are proved. The generic quantifier is
developed in `GroupConfig.Constructible.Generic`, and quasi-rational graphs in
`GroupConfig.Constructible.QuasiRational`. The constructible partial-function
interface remains a separate obligation. Actual group constructibility is proved in
`GroupConfig.Constructible.CanonicalPresentation`.
-/

namespace GroupConfig

variable {k K ι : Type*} [Field k] [Field K] [Algebra k K]
variable {s t : Set (ι → K)}

/-- The empty set is constructible over any base field.-/
theorem IsConstructibleOver.empty : IsConstructibleOver k (∅ : Set (ι → K)) :=
  ⟨∅, .empty, rfl⟩

/-- The whole coordinate space is constructible over any base field.-/
theorem IsConstructibleOver.univ : IsConstructibleOver k (Set.univ : Set (ι → K)) :=
  ⟨Set.univ, .univ, rfl⟩

/-- A union of two constructible sets is constructible over the same field.-/
theorem IsConstructibleOver.union (hs : IsConstructibleOver k s)
    (ht : IsConstructibleOver k t) :
    IsConstructibleOver k (s ∪ t) := by
  obtain ⟨C, hC, rfl⟩ := hs
  obtain ⟨D, hD, rfl⟩ := ht
  exact ⟨C ∪ D, hC.union hD, Set.preimage_union.symm⟩

/-- An intersection of two constructible sets is constructible over the same field.-/
theorem IsConstructibleOver.inter (hs : IsConstructibleOver k s)
    (ht : IsConstructibleOver k t) :
    IsConstructibleOver k (s ∩ t) := by
  obtain ⟨C, hC, rfl⟩ := hs
  obtain ⟨D, hD, rfl⟩ := ht
  exact ⟨C ∩ D, hC.inter hD, Set.preimage_inter.symm⟩

/-- The complement of a constructible set is constructible over the same field.-/
theorem IsConstructibleOver.compl (hs : IsConstructibleOver k s) :
    IsConstructibleOver k sᶜ := by
  obtain ⟨C, hC, rfl⟩ := hs
  exact ⟨Cᶜ, hC.compl, Set.preimage_compl.symm⟩

/-- A finite indexed union of constructible sets is constructible.-/
theorem IsConstructibleOver.iUnion {α : Type*} [Finite α] {s : α → Set (ι → K)}
    (hs : ∀ i, IsConstructibleOver k (s i)) : IsConstructibleOver k (⋃ i, s i) := by
  classical
  choose C hC heq using hs
  refine ⟨⋃ i, C i, .iUnion hC, ?_⟩
  rw [Set.preimage_iUnion]
  exact congrArg (fun f ↦ ⋃ i, f i) (funext heq)

/-- A finite indexed intersection of constructible sets is constructible.-/
theorem IsConstructibleOver.iInter {α : Type*} [Finite α] {s : α → Set (ι → K)}
    (hs : ∀ i, IsConstructibleOver k (s i)) : IsConstructibleOver k (⋂ i, s i) := by
  classical
  choose C hC heq using hs
  refine ⟨⋂ i, C i, .iInter hC, ?_⟩
  rw [Set.preimage_iInter]
  exact congrArg (fun f ↦ ⋂ i, f i) (funext heq)

/-- The zero set of a polynomial over the base is constructible.-/
theorem IsConstructibleOver.polynomial_zero (p : MvPolynomial ι k) :
    IsConstructibleOver k {x : ι → K | MvPolynomial.aeval x p = 0} := by
  classical
  apply isConstructibleOver_iff_exists_polynomial_data.mpr
  refine ⟨{⟨1, 1, fun _ ↦ p⟩}, ?_⟩
  intro x
  simp

/-- The nonzero locus of a polynomial over the base is constructible.-/
theorem IsConstructibleOver.polynomial_ne_zero (p : MvPolynomial ι k) :
    IsConstructibleOver k {x : ι → K | MvPolynomial.aeval x p ≠ 0} :=
  (IsConstructibleOver.polynomial_zero p).compl

/-- Substituting polynomial expressions over the base preserves constructibility.-/
theorem IsConstructibleOver.preimage_polynomial {κ : Type*}
    (q : κ → MvPolynomial ι k) {s : Set (κ → K)}
    (hs : IsConstructibleOver k s) :
    IsConstructibleOver k ((fun x i ↦ MvPolynomial.aeval x (q i)) ⁻¹' s) := by
  obtain ⟨C, hC, rfl⟩ := hs
  obtain ⟨cells, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hC
  let f : MvPolynomial κ k →+* MvPolynomial ι k :=
    (MvPolynomial.aeval (R := k) q).toRingHom
  refine ⟨(cells.map f).toSet, (cells.map f).isConstructible_toSet, ?_⟩
  rw [PrimeSpectrum.ConstructibleSetData.toSet_map]
  ext x
  suffices MvPolynomial.pointToPoint (fun i ↦ MvPolynomial.aeval x (q i)) =
      PrimeSpectrum.comap f (MvPolynomial.pointToPoint x) by
    exact (congrArg (fun p ↦ p ∈ cells.toSet) this).to_iff
  apply PrimeSpectrum.ext
  ext p
  simp only [MvPolynomial.pointToPoint, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    MvPolynomial.mem_vanishingIdeal_singleton_iff]
  rw [show MvPolynomial.aeval x (f p) =
      MvPolynomial.aeval (fun i ↦ MvPolynomial.aeval x (q i)) p from
    MvPolynomial.comp_aeval_apply (f := q) (MvPolynomial.aeval x) p]

/-- Enlarging the field of coefficients preserves constructibility.-/
theorem IsConstructibleOver.extend_base {L : Type*} [Field L] [Algebra k L]
    [Algebra L K] [IsScalarTower k L K] (hs : IsConstructibleOver k s) :
    IsConstructibleOver L s := by
  obtain ⟨C, hC, rfl⟩ := hs
  obtain ⟨cells, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hC
  let f : MvPolynomial ι k →+* MvPolynomial ι L :=
    MvPolynomial.map (algebraMap k L)
  refine ⟨(cells.map f).toSet, (cells.map f).isConstructible_toSet, ?_⟩
  rw [PrimeSpectrum.ConstructibleSetData.toSet_map]
  ext x
  suffices PrimeSpectrum.comap f (MvPolynomial.pointToPoint (k := L) x) =
      MvPolynomial.pointToPoint (k := k) x by
    exact (congrArg (fun p ↦ p ∈ cells.toSet) this).symm.to_iff
  apply PrimeSpectrum.ext
  ext p
  simp [MvPolynomial.pointToPoint, f, MvPolynomial.aeval_map_algebraMap]

/-- Enlarging an intermediate coefficient field along its inclusion preserves
constructibility. Admissible word relations and their common sampling field
use this form without choosing a separate algebra structure.-/
theorem IsConstructibleOver.of_le_intermediateField
    {E E' : IntermediateField k K} (h : E ≤ E') {X : Type*} {s : Set (X → K)}
    (hs : IsConstructibleOver (↥E) s) : IsConstructibleOver (↥E') s := by
  let _ : Algebra ↥E ↥E' := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower ↥E ↥E' K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact hs.extend_base

/-- Changing an intermediate coefficient field to an equal scalar restriction
preserves constructibility. The generic quantifier and the staged stabilizer
sampling field use this form to transport their actual coefficient inclusions.-/
theorem IsConstructibleOver.of_restrictScalars_eq {M : IntermediateField k K}
    {E : IntermediateField (↥M) K} {E' : IntermediateField k K}
    (hE : E.restrictScalars k = E') {X : Type*} {s : Set (X → K)} (h : IsConstructibleOver (↥E) s) :
    IsConstructibleOver (↥E') s := by
  have hmem (x : ↥E) : (x : K) ∈ E' := hE ▸ (IntermediateField.mem_restrictScalars k).2 x.2
  let _ : Algebra ↥E ↥E' := RingHom.toAlgebra
    { toFun := fun x ↦ ⟨x, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have : IsScalarTower ↥E ↥E' K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact h.extend_base

/-- Existential quantification over all ambient-field tuples `y : κ → K` preserves
constructibility when `κ` is finite and the ambient field is algebraically closed.
This is K-points Chevalley in formula form.-/
theorem IsConstructibleOver.exists [Finite ι] {κ : Type*} [Finite κ] [IsAlgClosed K]
    {φ : (ι → K) → (κ → K) → Prop}
    (hφ : IsConstructibleOver k {z : (ι ⊕ κ) → K | φ (z ∘ Sum.inl) (z ∘ Sum.inr)}) :
    IsConstructibleOver k {x : ι → K | ∃ y, φ x y} := by
  convert hφ.image_projection using 1
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨Sum.elim x y, hy, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z ∘ Sum.inr, hz⟩

/-- Universal quantification over a finite tuple preserves constructibility in an
algebraically closed ambient field, by complementing an existential quantifier.-/
theorem IsConstructibleOver.forall [Finite ι] {κ : Type*} [Finite κ] [IsAlgClosed K]
    {φ : (ι → K) → (κ → K) → Prop}
    (hφ : IsConstructibleOver k {z : (ι ⊕ κ) → K | φ (z ∘ Sum.inl) (z ∘ Sum.inr)}) :
    IsConstructibleOver k {x : ι → K | ∀ y, φ x y} := by
  have hn : IsConstructibleOver k {x : ι → K | ∃ y, ¬φ x y} := hφ.compl.exists
  convert hn.compl using 1
  ext x
  simp

end GroupConfig
