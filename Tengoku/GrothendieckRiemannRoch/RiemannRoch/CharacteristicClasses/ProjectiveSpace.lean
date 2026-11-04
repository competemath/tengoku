/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Tengoku.Seed.AlgebraicGeometry.Noetherian
import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous
import Tengoku.Seed.RingTheory.MvPolynomial.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scheme projective space from the standard graded polynomial ring

This file realizes projective `n`-space over a commutative ring as Mathlib's scheme-level `Proj`.
It proves that the standard coordinate basic opens are affine and cover the scheme, identifies the
degree-zero component with the coefficient ring, and equips the resulting structure morphism to
`Spec R` with its properness instance.

The twisting sheaf `O(1)` and its section-to-Cartier-divisor interface are separate geometric
constructions and are not postulated here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace SchemeProjectiveSpace

/-- The standard polynomial ring in `n+1` variables.-/
abbrev Polynomial (R : Type u) [CommRing R] (n : ℕ) :=
  MvPolynomial (Fin (n + 1)) R

/-- Its grading by total degree.-/
abbrev grading (R : Type u) [CommRing R] (n : ℕ) :
    ℕ → Submodule R (Polynomial R n) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

local instance gradedAlgebra (R : Type u) [CommRing R] (n : ℕ) :
    GradedAlgebra (grading R n) := MvPolynomial.gradedAlgebra

/-- Projective `n`-space over a commutative ring as the scheme `Proj` of the standard graded
polynomial ring in `n+1` variables.-/
noncomputable def space (R : Type u) [CommRing R] (n : ℕ) : Scheme :=
  Proj (grading R n)

/-- The `i`th homogeneous coordinate.-/
def coordinate (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    Polynomial R n := MvPolynomial.X (R := R) i

/--
@isnad1 id=mem.0h3v.s8.b3dce9b0678e from=translated src=- shape=8125ac70 vocab=2a5c86ee
-/
theorem coordinate_mem_degree_one (R : Type u) [CommRing R] (n : ℕ)
    (i : Fin (n + 1)) : coordinate R n i ∈ grading R n 1 := by
  exact MvPolynomial.isHomogeneous_X R i

/-- The standard coordinate basic open in projective space.-/
def coordinateOpen (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    (space R n).Opens :=
  Proj.basicOpen (grading R n) (coordinate R n i)

/--
@isnad1 id=eq.0h2v.s7.6c67b10a0ecc from=translated src=- shape=c628d28f vocab=47c1e76f
-/
theorem coordinateOpen_iSup_eq_top (R : Type u) [CommRing R] (n : ℕ) :
    ⨆ i : Fin (n + 1), coordinateOpen R n i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top (grading R n) (coordinate R n)
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro d hd p hp
  change p ∈ Ideal.span (Set.range (MvPolynomial.X (R := R)))
  rw [show Set.range (MvPolynomial.X (R := R)) =
      MvPolynomial.X '' (Set.univ : Set (Fin (n + 1))) by simp]
  rw [MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hdeg : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (Finsupp.mem_support_iff.mp hm)
  have hm0 : m ≠ 0 := by
    intro hm0
    subst m
    simp at hdeg
    omega
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
  exact ⟨i, Set.mem_univ _, hi⟩

/-- The structure morphism to the spectrum of the degree-zero component.-/
noncomputable def toSpecZero (R : Type u) [CommRing R] (n : ℕ) :
    space R n ⟶ Spec (.of (grading R n 0)) :=
  Proj.toSpecZero (grading R n)

/-- The standard graded polynomial ring is of finite type over its degree-zero component.-/
instance (R : Type u) [CommRing R] (n : ℕ) :
    Algebra.FiniteType (grading R n 0) (Polynomial R n) := by
  classical
  refine ⟨⟨Finset.univ.image (coordinate R n), ?_⟩⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a =>
      let a0 : grading R n 0 :=
        ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C (σ := Fin (n + 1)) a⟩
      change (a0 : Polynomial R n) ∈ Algebra.adjoin (grading R n 0)
        (Set.range (coordinate R n))
      exact (Algebra.adjoin (grading R n 0)
        (Set.range (coordinate R n))).algebraMap_mem a0
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp =>
      exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

instance (R : Type u) [CommRing R] (n : ℕ) :
    IsProper (toSpecZero R n) := by
  dsimp [toSpecZero, space]
  infer_instance

/-- The degree-zero component of the standard graded polynomial ring is the coefficient ring.-/
noncomputable def degreeZeroEquiv (R : Type u) [CommRing R] (n : ℕ) :
    grading R n 0 ≃+* R where
  toFun p := MvPolynomial.constantCoeff p.1
  invFun a := ⟨MvPolynomial.C a,
    MvPolynomial.isHomogeneous_C (σ := Fin (n + 1)) a⟩
  left_inv p := by
    apply Subtype.ext
    change MvPolynomial.C (MvPolynomial.constantCoeff p.1) = p.1
    rw [MvPolynomial.constantCoeff_eq]
    rw [← MvPolynomial.homogeneousComponent_zero]
    simpa using MvPolynomial.homogeneousComponent_of_mem (m := 0) p.2
  right_inv a := MvPolynomial.constantCoeff_C _ a
  map_mul' p q := map_mul MvPolynomial.constantCoeff p.1 q.1
  map_add' p q := map_add MvPolynomial.constantCoeff p.1 q.1

/-- The structure morphism of projective space over its coefficient ring.-/
noncomputable def toSpec (R : Type u) [CommRing R] (n : ℕ) :
    space R n ⟶ Spec (.of R) :=
  toSpecZero R n ≫ Spec.map (degreeZeroEquiv R n).symm.toCommRingCatIso.hom

instance (R : Type u) [CommRing R] (n : ℕ) : IsProper (toSpec R n) := by
  dsimp [toSpec]
  infer_instance

/-- Projective space is quasi-compact, hence compact as a topological space, over every
coefficient ring.
@isnad1 id=compacts.0h2v.s4.e6b089f8a51d from=translated src=- shape=e3028cdf vocab=7e4ae427
-/
theorem compactSpace (R : Type u) [CommRing R] (n : ℕ) :
    CompactSpace (space R n) :=
  (quasiCompact_iff_compactSpace (toSpec R n)).mp inferInstance

end SchemeProjectiveSpace
