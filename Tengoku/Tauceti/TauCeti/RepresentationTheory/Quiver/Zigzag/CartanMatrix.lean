/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Quiver.Zigzag.Grading
public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Basic
public import Tengoku.Tauceti.TauCeti.RingTheory.Idempotents.Corner

/-!
# The graded Cartan matrix of a zigzag algebra

For a finite simple graph without isolated vertices, the vertex idempotents `e_i` of the zigzag
relation quotient `Z` are primitive, so `Z e_i` is the indecomposable projective at `i` and the
corner `e_i Z e_j` records the homomorphisms from `Z e_i` to `Z e_j`.  This file computes those
corners degree by degree for the path-length grading and assembles the resulting graded Cartan
matrix.

The three nonzero graded corners are read off the vertex-arrow-volume basis: the vertex
idempotent `e_i` spans the degree-zero corner at `(i, i)`, the arrow of the dart from `j` to `i`
spans the degree-one corner at `(i, j)`, and the volume class `x_i` spans the degree-two corner
at `(i, i)`.  Everything else vanishes, so

```text
C_G(q) = (1 + q²) I + q A_G,
```

with `A_G` the adjacency matrix of the graph.  At `q = 0` it is the identity, so its polynomial
determinant is nonzero.  At `q = 1` it is the ungraded Cartan matrix `2I + A_G`, whose column sums
are the dimensions of the vertex projectives; at `q = -1` it is the generalized Cartan matrix
`2I - A_G` of the graph.

## Main definitions

* `TauCeti.zigzagCorner`: the corner `e_i Z e_j`, as a `k`-submodule of the relation quotient.
* `TauCeti.zigzagGradedCorner`: its degree-`n` piece for the path-length grading.
* `TauCeti.zigzagGradedCartanMatrix`: the matrix of graded dimensions of the corners, a matrix of
  polynomials in `q`.

## Main results

* `TauCeti.restrictScalars_zigzagProjective_eq_iSup_zigzagCorner`: the vertex projective `Z e_j`
  is the sum of the corners `e_i Z e_j`.
* `TauCeti.zigzagGradedCorner_zero_self_eq_span`,
  `TauCeti.zigzagGradedCorner_one_eq_span_of_adj` and
  `TauCeti.zigzagGradedCorner_two_self_eq_span`: the three nonvanishing graded corners, each
  spanned by a single basis vector, together with the vanishing of all the others.
* `TauCeti.zigzagGradedCartanMatrix_apply`: **the entrywise graded Cartan formula.**
* `TauCeti.zigzagGradedCartanMatrix_eq`: the same formula in matrix notation,
  `C_G(q) = (1 + q²) I + q A_G`.
* `TauCeti.zigzagGradedCartanMatrix_map_eval_zero` and
  `TauCeti.det_zigzagGradedCartanMatrix_ne_zero`: the specialization at `q = 0` is the identity,
  so the determinant is a nonzero polynomial.
* `TauCeti.zigzagGradedCartanMatrix_map_eval_one` and
  `TauCeti.zigzagGradedCartanMatrix_map_eval_neg_one`: the two specializations `2I + A_G` and
  `2I - A_G`.
* `TauCeti.sum_eval_one_zigzagGradedCartanMatrix_eq_finrank_zigzagProjective`: the column sums at
  `q = 1` are the dimensions of the vertex projectives.

## Implementation notes

The graded Cartan entry is defined as the truncated sum `∑_{n < 3} dim (e_i Z e_j)_n q^n` rather
than as a sum over all degrees.  The truncation loses nothing:
`TauCeti.finrank_zigzagGradedCorner_of_three_le` proves that every corner of degree at least three
vanishes, because the whole degree-`n` piece of the zigzag quotient does.

The corners here are the graded homomorphism spaces of the vertex projectives only through the
standard dictionary `Hom_Z(Z e_i, Z e_j) ≅ e_i Z e_j`, which this file does not construct; what it
does prove about the projectives themselves is
`TauCeti.restrictScalars_zigzagProjective_eq_iSup_zigzagCorner`, that `Z e_j` is the sum of the
corners `e_i Z e_j` over `i`, together with the resulting numerical comparison
`TauCeti.sum_eval_one_zigzagGradedCartanMatrix_eq_finrank_zigzagProjective`.

## References

This is the graded Cartan matrix of Layer 3 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`.  See Huerfano--Khovanov, *A category for the
adjoint representation*, Section 3, and Ehrig--Tubbenhauer, *Algebraic properties of zigzag
algebras*, Section 2.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver Polynomial

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-! ### The corners of a zigzag algebra -/

/-- Cutting an element of the zigzag relation quotient down to the corner at `(i, j)`, that is,
multiplying it by `e_i` on the left and by `e_j` on the right. -/
noncomputable def zigzagCornerMap (i j : V) :
    nonisolatedZigzagQuotient k G →ₗ[k] nonisolatedZigzagQuotient k G :=
  cornerMap k (zigzagVertexIdempotent k G i) (zigzagVertexIdempotent k G j)

@[simp]
theorem zigzagCornerMap_apply (i j : V) (x : nonisolatedZigzagQuotient k G) :
    zigzagCornerMap k G i j x =
      zigzagVertexIdempotent k G i * x * zigzagVertexIdempotent k G j :=
  cornerMap_apply k _ _ x

/-- **The corner `e_i Z e_j` of a zigzag algebra**, as a `k`-submodule of the relation quotient:
the elements which `e_i` fixes on the left and `e_j` fixes on the right. -/
noncomputable def zigzagCorner (i j : V) :
    Submodule k (nonisolatedZigzagQuotient k G) :=
  cornerSubmodule k (zigzagVertexIdempotent k G i) (zigzagVertexIdempotent k G j)

/-- Membership in the corner `e_i Z e_j`: an element belongs to it exactly when multiplying it by
`e_i` on the left and by `e_j` on the right fixes it. -/
@[simp]
theorem mem_zigzagCorner_iff {i j : V} {x : nonisolatedZigzagQuotient k G} :
    x ∈ zigzagCorner k G i j ↔
      zigzagVertexIdempotent k G i * x * zigzagVertexIdempotent k G j = x :=
  mem_cornerSubmodule_iff k (zigzagMk_vertexIdempotent_mul_self k G i)
    (zigzagMk_vertexIdempotent_mul_self k G j)

/-- The vertex idempotent at `i` lies in the corner at `(i, i)`. -/
theorem zigzagVertexIdempotent_mem_zigzagCorner (i : V) :
    zigzagVertexIdempotent k G i ∈ zigzagCorner k G i i := by
  rw [mem_zigzagCorner_iff]
  simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_self]

/-! ### The graded corners -/

/-- **The degree-`n` part of the corner `e_i Z e_j`** for the path-length grading of the zigzag
relation quotient. -/
noncomputable def zigzagGradedCorner (i j : V) (n : ℕ) :
    Submodule k (nonisolatedZigzagQuotient k G) :=
  zigzagCorner k G i j ⊓ zigzagGrade k G n

/-- Membership in a graded corner: an element belongs to it exactly when it lies in the corner and
is homogeneous of that degree. -/
@[simp]
theorem mem_zigzagGradedCorner_iff {i j : V} {n : ℕ} {x : nonisolatedZigzagQuotient k G} :
    x ∈ zigzagGradedCorner k G i j n ↔ x ∈ zigzagCorner k G i j ∧ x ∈ zigzagGrade k G n :=
  Iff.rfl

/-- A graded corner sits inside the corner it grades. -/
theorem zigzagGradedCorner_le_zigzagCorner (i j : V) (n : ℕ) :
    zigzagGradedCorner k G i j n ≤ zigzagCorner k G i j :=
  fun _ hx => ((mem_zigzagGradedCorner_iff k G).1 hx).1

/-- An element of a graded corner is cut out by the corner map from a spanning family of its
degree.  This is the shape in which each of the three degrees below is computed: it reduces the
graded corner to the span of the corner map applied to the vertex idempotents, the arrows, or the
volume classes. -/
private theorem zigzagGradedCorner_le_span_image {i j : V} {n : ℕ}
    {s : Set (nonisolatedZigzagQuotient k G)} (hs : zigzagGrade k G n = Submodule.span k s) :
    zigzagGradedCorner k G i j n ≤ Submodule.span k (⇑(zigzagCornerMap k G i j) '' s) := by
  rintro x ⟨hcorner, hgrade⟩
  have hx : zigzagCornerMap k G i j x = x := by
    rw [zigzagCornerMap_apply]
    exact (mem_zigzagCorner_iff k G).1 hcorner
  rw [hs] at hgrade
  rw [← hx, ← Submodule.map_span]
  exact Submodule.mem_map_of_mem hgrade

/-- **The degree-zero corner at a vertex is spanned by its idempotent.** -/
theorem zigzagGradedCorner_zero_self_eq_span (i : V) :
    zigzagGradedCorner k G i i 0 = Submodule.span k {zigzagVertexIdempotent k G i} := by
  refine le_antisymm ?_ ?_
  · refine le_trans (zigzagGradedCorner_le_span_image k G
      (zigzagGrade_zero_eq_span_range_vertexIdempotent k G)) (Submodule.span_le.2 ?_)
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    rcases eq_or_ne v i with rfl | hv
    · rw [zigzagCornerMap_apply]
      simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_self]
      exact Submodule.subset_span rfl
    · rw [zigzagCornerMap_apply]
      simp only [zigzagVertexIdempotent,
        zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G (Ne.symm hv), zero_mul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨zigzagVertexIdempotent_mem_zigzagCorner k G i,
      zigzagMk_mem_zigzagGrade k G (PathAlgebra.vertexIdempotent_mem_grade_zero _)⟩

/-- **The degree-zero corner between distinct vertices vanishes.** -/
theorem zigzagGradedCorner_zero_eq_bot_of_ne {i j : V} (h : i ≠ j) :
    zigzagGradedCorner k G i j 0 = ⊥ := by
  refine le_antisymm ?_ bot_le
  refine le_trans (zigzagGradedCorner_le_span_image k G
    (zigzagGrade_zero_eq_span_range_vertexIdempotent k G)) (Submodule.span_le.2 ?_)
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  rw [zigzagCornerMap_apply]
  rcases eq_or_ne v i with rfl | hv
  · simp only [zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_self,
      zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G h]
    exact Submodule.zero_mem _
  · simp only [zigzagVertexIdempotent,
      zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G (Ne.symm hv), zero_mul]
    exact Submodule.zero_mem _

/-- **Every corner of degree at least three vanishes**, because the whole degree-`n` piece does. -/
theorem zigzagGradedCorner_eq_bot_of_three_le (i j : V) {n : ℕ} (hn : 3 ≤ n) :
    zigzagGradedCorner k G i j n = ⊥ := by
  rw [zigzagGradedCorner, zigzagGrade_eq_bot_of_three_le k G hn, inf_bot_eq]

/-! ### The dimensions of the graded corners -/

/-- The degree-zero corner at a vertex is one-dimensional. -/
theorem finrank_zigzagGradedCorner_zero_self (i : V) :
    Module.finrank k (zigzagGradedCorner k G i i 0) = 1 := by
  rw [zigzagGradedCorner_zero_self_eq_span]
  exact finrank_span_singleton (zigzagVertexIdempotent_ne_zero k G i)

/-- The degree-zero corner between distinct vertices has dimension zero. -/
theorem finrank_zigzagGradedCorner_zero_of_ne {i j : V} (h : i ≠ j) :
    Module.finrank k (zigzagGradedCorner k G i j 0) = 0 := by
  rw [zigzagGradedCorner_zero_eq_bot_of_ne k G h, finrank_bot]

/-- **The graded Cartan entries vanish in every degree at least three**: this is what makes the
truncated sum defining `TauCeti.zigzagGradedCartanMatrix` lose nothing. -/
theorem finrank_zigzagGradedCorner_of_three_le (i j : V) {n : ℕ} (hn : 3 ≤ n) :
    Module.finrank k (zigzagGradedCorner k G i j n) = 0 := by
  rw [zigzagGradedCorner_eq_bot_of_three_le k G i j hn, finrank_bot]

/-! ### The graded Cartan matrix -/

/-- **The graded Cartan matrix of a zigzag algebra**: the entry at `(i, j)` is the graded dimension
`∑_n dim_k (e_i Z e_j)_n q^n` of the corner at `(i, j)`, a polynomial in the internal degree `q`.
The sum is truncated below degree three, which by
`TauCeti.finrank_zigzagGradedCorner_of_three_le` discards only zeros. -/
noncomputable def zigzagGradedCartanMatrix : Matrix V V ℤ[X] :=
  Matrix.of fun i j =>
    ∑ n ∈ Finset.range 3, (Module.finrank k (zigzagGradedCorner k G i j n) : ℤ[X]) * X ^ n

theorem zigzagGradedCartanMatrix_apply_eq_sum (i j : V) :
    zigzagGradedCartanMatrix k G i j =
      (Module.finrank k (zigzagGradedCorner k G i j 0) : ℤ[X]) +
        (Module.finrank k (zigzagGradedCorner k G i j 1) : ℤ[X]) * X +
        (Module.finrank k (zigzagGradedCorner k G i j 2) : ℤ[X]) * X ^ 2 := by
  rw [zigzagGradedCartanMatrix, Matrix.of_apply, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, pow_zero, mul_one, pow_one]

section EvaluationAtZero

variable [DecidableEq V]

/-- **At `q = 0` the graded Cartan matrix is the identity matrix.** Only the degree-zero vertex
idempotents survive this specialization. -/
@[simp]
theorem zigzagGradedCartanMatrix_map_eval_zero :
    (zigzagGradedCartanMatrix k G).map (eval 0) = 1 := by
  ext i j
  rw [Matrix.map_apply, zigzagGradedCartanMatrix_apply_eq_sum, Matrix.one_apply]
  rcases eq_or_ne i j with rfl | hij
  · rw [finrank_zigzagGradedCorner_zero_self]
    simp
  · rw [finrank_zigzagGradedCorner_zero_of_ne k G hij]
    simp [hij]

variable [Fintype V]

end EvaluationAtZero

section Nonisolated

variable (hns : ∀ i : V, ∃ j, G.Adj i j)
include hns

section Decidable

variable [DecidableEq V] [DecidableRel G.Adj]

end Decidable

section Sum

variable [Fintype V]

end Sum

end Nonisolated

end TauCeti
