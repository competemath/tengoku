/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Algebra.Algebra.Operations
import Tengoku.Seed.Algebra.DirectSum.Module
import Tengoku.Seed.LinearAlgebra.Basis.Basic
import Tengoku.Seed.LinearAlgebra.Basis.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Graded pieces determined by a weighted basis

Given a basis-like family `b : ι → A` and a weight `w : ι → ℕ`, this file
defines the weight-`k` submodule as the span of the corresponding basis
vectors. It proves that a linearly independent spanning family gives an
internal direct-sum decomposition and that multiplicativity may be checked on
basis vectors.

The construction is independent of numerical intersection rings and algebraic
geometry. Geometric numerical-ring constructors consume it from
`AlgebraicGeometry/Numerical/Core/GradedBasis.lean`.
-/

universe u v

open Submodule Set

namespace DerivedAlgGeo.LinearAlgebra

variable {ι : Type v} {A : Type u} [CommRing A] [Algebra ℚ A]

/-- The span of the vectors of weight `k`.-/
def gradedPiece (b : ι → A) (w : ι → ℕ) (k : ℕ) : Submodule ℚ A :=
  span ℚ (b '' (w ⁻¹' {k}))

variable {b : ι → A} {w : ι → ℕ} {n : ℕ}

/-- Every vector of the indexed family lies in its own graded piece.
@isnad1 id=mem.0h5v.s6.0b82b13acb0d from=translated src=- shape=c5e52a27 vocab=0392ea46
-/
theorem mem_gradedPiece (i : ι) : b i ∈ gradedPiece b w (w i) :=
  subset_span ⟨i, rfl, rfl⟩

/-- If all weights are at most `n`, every graded piece above `n` vanishes.
@isnad1 id=eq.2h6v.s6.36a5b056c77a from=translated src=- shape=08b33ccd vocab=cad331e9
-/
theorem gradedPiece_eq_bot (hw : ∀ i, w i ≤ n) {k : ℕ} (hk : n < k) :
    gradedPiece b w k = ⊥ := by
  have hempty : w ⁻¹' {k} = (∅ : Set ι) := by
    ext i
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    intro h
    have := hw i
    omega
  rw [gradedPiece, hempty, image_empty, span_empty]

/-- Graded pieces cut out by distinct weights are independent.
@isnad1 id=isupinde.1h4v.s6.3cada1cac68a from=translated src=- shape=120ea992 vocab=f41f64d3
-/
theorem gradedPiece_iSupIndep (hb : LinearIndependent ℚ b) :
    iSupIndep (gradedPiece b w) := by
  intro k
  have key : Disjoint (span ℚ (b '' (w ⁻¹' {k}))) (span ℚ (b '' (w ⁻¹' {k})ᶜ)) :=
    hb.disjoint_span_image disjoint_compl_right
  refine Disjoint.mono_right ?_ key
  refine iSup_le fun j => iSup_le fun hj => span_mono (image_mono ?_)
  intro i hi
  simp only [mem_preimage, mem_singleton_iff] at hi
  simp only [mem_compl_iff, mem_preimage, mem_singleton_iff]
  rw [hi]
  exact hj

/-- The graded pieces span whenever the indexed family spans.
@isnad1 id=eq.1h4v.s8.ebcc4db3af71 from=translated src=- shape=dd4d75f2 vocab=f907c662
-/
theorem gradedPiece_iSup_eq_top (hsp : span ℚ (range b) = ⊤) :
    ⨆ k, gradedPiece b w k = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hsp, span_le]
  rintro _ ⟨i, rfl⟩
  exact Submodule.mem_iSup_of_mem (w i) (mem_gradedPiece i)

/-- A linearly independent spanning family decomposes the module as the
direct sum of its weight pieces.
@isnad1 id=isintern.2h4v.s7.51f6439b7c34 from=translated src=- shape=88c043b4 vocab=685d4757
-/
theorem gradedPiece_isInternal (hb : LinearIndependent ℚ b)
    (hsp : span ℚ (range b) = ⊤) :
    DirectSum.IsInternal (gradedPiece b w) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradedPiece_iSupIndep hb) (gradedPiece_iSup_eq_top hsp)

/-- Multiplicativity of the grading, promoted from indexed vectors to all
elements of their weight pieces.
@isnad1 id=mem.3h8v.s8.249d7a33fa58 from=translated src=- shape=89ab71d2 vocab=f1439cd9
-/
theorem gradedPiece_mul_mem
    (hmul : ∀ p q : ι, b p * b q ∈ gradedPiece b w (w p + w q))
    {i j : ℕ} {x y : A} (hx : x ∈ gradedPiece b w i)
    (hy : y ∈ gradedPiece b w j) :
    x * y ∈ gradedPiece b w (i + j) := by
  have hle : gradedPiece b w i * gradedPiece b w j ≤ gradedPiece b w (i + j) := by
    rw [gradedPiece, gradedPiece, Submodule.span_mul_span, span_le]
    rintro _ ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩
    simp only [mem_preimage, mem_singleton_iff] at hp hq
    rw [← hp, ← hq]
    exact hmul p q
  exact hle (Submodule.mul_mem_mul hx hy)

end DerivedAlgGeo.LinearAlgebra
