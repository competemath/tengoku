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

/-- The empty set is constructible over any base field.
@isnad1 id=isconstr.0h3v.s5.2ff559f8fde5 from=translated src=- shape=c6f95907 vocab=ed6ac4e6
-/
theorem IsConstructibleOver.empty : IsConstructibleOver k (∅ : Set (ι → K)) :=
  ⟨∅, .empty, rfl⟩

/-- The whole coordinate space is constructible over any base field.
@isnad1 id=isconstr.0h3v.s5.a186955348e2 from=translated src=- shape=f30770bb vocab=4731c9c2
-/
theorem IsConstructibleOver.univ : IsConstructibleOver k (Set.univ : Set (ι → K)) :=
  ⟨Set.univ, .univ, rfl⟩

/-- A union of two constructible sets is constructible over the same field.
@isnad1 id=isconstr.2h5v.s6.0bd7e7c3a87d from=translated src=- shape=8466832f vocab=e4420914
-/
theorem IsConstructibleOver.union (hs : IsConstructibleOver k s)
    (ht : IsConstructibleOver k t) :
    IsConstructibleOver k (s ∪ t) := by
  obtain ⟨C, hC, rfl⟩ := hs
  obtain ⟨D, hD, rfl⟩ := ht
  exact ⟨C ∪ D, hC.union hD, Set.preimage_union.symm⟩

/-- An intersection of two constructible sets is constructible over the same field.
@isnad1 id=isconstr.2h5v.s6.abc64a369746 from=translated src=- shape=8466832f vocab=5b0c4f60
-/
theorem IsConstructibleOver.inter (hs : IsConstructibleOver k s)
    (ht : IsConstructibleOver k t) :
    IsConstructibleOver k (s ∩ t) := by
  obtain ⟨C, hC, rfl⟩ := hs
  obtain ⟨D, hD, rfl⟩ := ht
  exact ⟨C ∩ D, hC.inter hD, Set.preimage_inter.symm⟩

/-- The complement of a constructible set is constructible over the same field.
@isnad1 id=isconstr.1h4v.s5.9a83134a25e3 from=translated src=- shape=3bc88025 vocab=d7220e1d
-/
theorem IsConstructibleOver.compl (hs : IsConstructibleOver k s) :
    IsConstructibleOver k sᶜ := by
  obtain ⟨C, hC, rfl⟩ := hs
  exact ⟨Cᶜ, hC.compl, Set.preimage_compl.symm⟩

/-- A finite indexed union of constructible sets is constructible.
@isnad1 id=isconstr.1h5v.s6.887bc6c4c91e from=translated src=- shape=b7de68a6 vocab=d7489e5b
-/
theorem IsConstructibleOver.iUnion {α : Type*} [Finite α] {s : α → Set (ι → K)}
    (hs : ∀ i, IsConstructibleOver k (s i)) : IsConstructibleOver k (⋃ i, s i) := by
  classical
  choose C hC heq using hs
  refine ⟨⋃ i, C i, .iUnion hC, ?_⟩
  rw [Set.preimage_iUnion]
  exact congrArg (fun f ↦ ⋃ i, f i) (funext heq)

/-- A finite indexed intersection of constructible sets is constructible.
@isnad1 id=isconstr.1h5v.s6.43506d29b2d4 from=translated src=- shape=b7de68a6 vocab=91695838
-/
theorem IsConstructibleOver.iInter {α : Type*} [Finite α] {s : α → Set (ι → K)}
    (hs : ∀ i, IsConstructibleOver k (s i)) : IsConstructibleOver k (⋂ i, s i) := by
  classical
  choose C hC heq using hs
  refine ⟨⋂ i, C i, .iInter hC, ?_⟩
  rw [Set.preimage_iInter]
  exact congrArg (fun f ↦ ⋂ i, f i) (funext heq)

/-- The zero set of a polynomial over the base is constructible.
@isnad1 id=isconstr.0h4v.s8.c198d3101776 from=translated src=- shape=2edee47d vocab=dd55cc00
-/
theorem IsConstructibleOver.polynomial_zero (p : MvPolynomial ι k) :
    IsConstructibleOver k {x : ι → K | MvPolynomial.aeval x p = 0} := by
  classical
  apply isConstructibleOver_iff_exists_polynomial_data.mpr
  refine ⟨{⟨1, 1, fun _ ↦ p⟩}, ?_⟩
  intro x
  simp

/-- The nonzero locus of a polynomial over the base is constructible.
@isnad1 id=isconstr.0h4v.s8.a6254beefcf8 from=translated src=- shape=2edee47d vocab=dd55cc00
-/
theorem IsConstructibleOver.polynomial_ne_zero (p : MvPolynomial ι k) :
    IsConstructibleOver k {x : ι → K | MvPolynomial.aeval x p ≠ 0} :=
  (IsConstructibleOver.polynomial_zero p).compl

/-- Substituting polynomial expressions over the base preserves constructibility.
@isnad1 id=isconstr.1h6v.s8.7019fe76f4b2 from=translated src=- shape=92eb7bc4 vocab=9670b335
-/
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

/-- Enlarging the field of coefficients preserves constructibility.
@isnad1 id=isconstr.1h5v.s7.adbac23c1234 from=translated src=- shape=84f7c619 vocab=964fde6d
-/
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
use this form without choosing a separate algebra structure.
@isnad1 id=isconstr.2h6v.s7.fadda653cd6e from=translated src=- shape=2e7faa7e vocab=bf961e33
-/
theorem IsConstructibleOver.of_le_intermediateField
    {E E' : IntermediateField k K} (h : E ≤ E') {X : Type*} {s : Set (X → K)}
    (hs : IsConstructibleOver (↥E) s) : IsConstructibleOver (↥E') s := by
  let _ : Algebra ↥E ↥E' := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower ↥E ↥E' K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact hs.extend_base

/-- Changing an intermediate coefficient field to an equal scalar restriction
preserves constructibility. The generic quantifier and the staged stabilizer
sampling field use this form to transport their actual coefficient inclusions.
@isnad1 id=isconstr.2h7v.s9.5f20a43edd0f from=translated src=- shape=4ce4bbdf vocab=30674139
-/
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
This is K-points Chevalley in formula form.
@isnad1 id=isconstr.1h5v.s6.0925ccce658a from=translated src=- shape=a1aaa4f8 vocab=05647b34
-/
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
algebraically closed ambient field, by complementing an existential quantifier.
@isnad1 id=isconstr.1h5v.s6.e768211a708f from=translated src=- shape=b5ee4e0a vocab=05647b34
-/
theorem IsConstructibleOver.forall [Finite ι] {κ : Type*} [Finite κ] [IsAlgClosed K]
    {φ : (ι → K) → (κ → K) → Prop}
    (hφ : IsConstructibleOver k {z : (ι ⊕ κ) → K | φ (z ∘ Sum.inl) (z ∘ Sum.inr)}) :
    IsConstructibleOver k {x : ι → K | ∀ y, φ x y} := by
  have hn : IsConstructibleOver k {x : ι → K | ∃ y, ¬φ x y} := hφ.compl.exists
  convert hn.compl using 1
  ext x
  simp

end GroupConfig
