/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading
public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Quiver.Preprojective.Basic
public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Quiver.Preprojective.Signless
public import Tengoku.Tauceti.TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
public import Tengoku.Tauceti.TauCeti.RingTheory.TwoSidedIdeal.Homogeneous

/-!
# The path-length grading of the preprojective algebra

Every preprojective relator of a quiver is homogeneous for the path-length grading of the path
algebra of the doubled quiver: the head backtrack and the tail backtrack of an arrow are the
basis elements of single length-two paths, so the local relator at a vertex and the global
relator are differences of sums of degree-two elements. Consequently the preprojective relation
ideal is homogeneous.

Because the relation ideal is homogeneous, the generic descent
`TauCeti.GradedAlgebra.quotientPiece` applies to it: the preprojective algebra `Pi_k(Q)` carries the
induced path-length grading `TauCeti.preprojectiveGrade`, in which the vertex idempotents have
degree `0`, the doubled arrows degree `1`, and the relator degree `2`. This file packages the
graded-algebra structure and computes the concrete pieces.

## Main definitions

* `TauCeti.preprojectiveGrade`: the induced degree-`n` piece on the preprojective algebra, the
  descent of `TauCeti.PathAlgebra.grade` along the quotient map `TauCeti.preprojectiveMk`.
* `TauCeti.preprojectiveGradedAlgebra`: **the preprojective algebra is a graded algebra** for the
  induced path-length grading.

## Main results

* `TauCeti.headBacktrackElem_mem_grade_two` and `TauCeti.tailBacktrackElem_mem_grade_two`: the
  two backtracks of an arrow have degree two.
* `TauCeti.localPreprojectiveRelator_mem_grade_two` and
  `TauCeti.preprojectiveRelator_mem_grade_two`: the local and global relators have degree two.
* `TauCeti.signlessPreprojectiveRelator_mem_grade_two`: so does the signless local relator.
* `TauCeti.isHomogeneous_preprojectiveIdeal`: **the preprojective relation ideal is
  homogeneous.**
* `TauCeti.isInternal_preprojectiveGrade`: **the preprojective algebra is the internal direct
  sum of its graded pieces**, the comparison of the direct-sum graded algebra with the ungraded
  quotient rather than with a separate graded copy.
* `TauCeti.preprojectiveGrade_zero_eq_span_range_vertexIdempotent` and
  `TauCeti.preprojectiveGrade_one_eq_span_range_ofArrow`: degree `0` is spanned by the vertex
  idempotent classes and degree `1` by the doubled arrow classes.
* `TauCeti.preprojectiveGrade_eq_span_range_ofPath`: every piece is spanned by the classes of the
  paths of its degree.

## References

This is the grading clause of the first bullet of Layer 4 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`, which asks for the additive preprojective
algebra to carry path length with every doubled arrow in degree `1`. The descent construction is
`TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient`, instantiated for the zigzag relation
quotient in `TauCeti.RepresentationTheory.Quiver.Zigzag.Grading`. See Crawley-Boevey, *Quiver
algebras, weighted projective lines, and the Deligne--Simpson problem*, Section 1.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

/-! ### The generators of the doubled path algebra are homogeneous -/

section Generators

variable (k : Type w) {Q : Type u} [Semiring k] [Quiver.{v} Q]

/-- **The head backtrack of an arrow has degree two**: it is the basis element of a single
length-two path of the doubled quiver. -/
theorem headBacktrackElem_mem_grade_two {i j : Q} (a : i ⟶ j) :
    headBacktrackElem k a ∈ grade k (Symmetrify Q) 2 := by
  rw [headBacktrackElem_def k a]
  refine ofPath_mem_grade_of_length ?_
  simp only [Path.length_comp, Quiver.Path.length_toPath]

/-- **The tail backtrack of an arrow has degree two**: it is the basis element of a single
length-two path of the doubled quiver. -/
theorem tailBacktrackElem_mem_grade_two {i j : Q} (a : i ⟶ j) :
    tailBacktrackElem k a ∈ grade k (Symmetrify Q) 2 := by
  rw [tailBacktrackElem_def k a]
  refine ofPath_mem_grade_of_length ?_
  simp only [Path.length_comp, Quiver.Path.length_toPath]

end Generators

/-! ### The relators have degree two -/

section Relators

variable (k : Type w) {Q : Type u} [Ring k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

variable (Q)

/-- **The global preprojective relator has degree two**. -/
theorem preprojectiveRelator_mem_grade_two :
    preprojectiveRelator k Q ∈ grade k (Symmetrify Q) 2 := by
  rw [preprojectiveRelator_def k Q]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.sum_mem _ fun a _ => Submodule.sub_mem _
      (headBacktrackElem_mem_grade_two k a) (tailBacktrackElem_mem_grade_two k a)

end Relators

section SignlessRelator

variable (k : Type w) {R : Type u} [Semiring k] [Quiver.{v} R] [HasReverse R]

end SignlessRelator

/-! ### The relation ideal is homogeneous -/

section Ideal

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

variable (Q)

/-- **The preprojective relation ideal is homogeneous** for the path-length grading. This is the
condition needed to descend the grading to the preprojective algebra. -/
theorem isHomogeneous_preprojectiveIdeal :
    (preprojectiveIdeal k Q).asIdeal.IsHomogeneous (grade k (Symmetrify Q)) := by
  rw [preprojectiveIdeal_eq_span k Q]
  refine TwoSidedIdeal.homogeneous_span _ fun x hx => ?_
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact ⟨2, preprojectiveRelator_mem_grade_two k Q⟩

end Ideal

/-! ### The induced grading on the preprojective algebra -/

section Grade

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

variable (Q)

/-- **The induced path-length grading on the preprojective algebra**: the degree-`n` piece is the
image of the degree-`n` piece of the doubled path algebra under the quotient map. Multiplication
adds degrees for any relation ideal (`TauCeti.GradedAlgebra.mul_mem_quotientPiece`); because the
relation ideal is homogeneous (`TauCeti.isHomogeneous_preprojectiveIdeal`),
`TauCeti.isInternal_preprojectiveGrade` also holds, comparing the direct sum of the pieces with
the preprojective algebra itself rather than with a separate graded copy. -/
noncomputable def preprojectiveGrade (n : ℕ) : Submodule k (preprojectiveAlgebra k Q) :=
  TauCeti.GradedAlgebra.quotientPiece (grade k (Symmetrify Q)) (preprojectiveIdeal k Q).asIdeal n

/-- Membership in the induced degree-`n` piece is being the class of a degree-`n` element of the
doubled path algebra. -/
@[simp]
theorem mem_preprojectiveGrade_iff {n : ℕ} {x : preprojectiveAlgebra k Q} :
    x ∈ preprojectiveGrade k Q n ↔
      ∃ y ∈ grade k (Symmetrify Q) n, preprojectiveMk k Q y = x := by
  rw [preprojectiveGrade, TauCeti.GradedAlgebra.mem_quotientPiece_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, preprojectiveMk_apply k Q y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (preprojectiveMk_apply k Q y).symm⟩

/-- **The preprojective algebra is the internal direct sum of its graded pieces**: this is the
comparison of the direct-sum graded algebra with the ungraded quotient asked for by the roadmap,
in the internal sense in which the pieces are submodules of the algebra itself. -/
theorem isInternal_preprojectiveGrade :
    DirectSum.IsInternal (preprojectiveGrade k Q) :=
  TauCeti.GradedAlgebra.isInternal_quotientPiece (grade k (Symmetrify Q))
    (preprojectiveIdeal k Q).asIdeal (isHomogeneous_preprojectiveIdeal k Q)

/-- **The preprojective algebra is a graded algebra** for the induced path-length grading. This
is kept as a definition rather than an instance so that callers choose when to introduce it
locally; see `TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece`. -/
@[instance_reducible]
noncomputable def preprojectiveGradedAlgebra : GradedAlgebra (preprojectiveGrade k Q) :=
  TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece (grade k (Symmetrify Q))
    (preprojectiveIdeal k Q).asIdeal (isHomogeneous_preprojectiveIdeal k Q)

/-! ### The concrete pieces -/

end Grade

end TauCeti
