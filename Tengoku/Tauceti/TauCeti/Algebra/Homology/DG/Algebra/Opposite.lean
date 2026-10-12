/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Algebra.Homology.DG.Algebra.Defs
public import Tengoku.Tauceti.TauCeti.RingTheory.GradedAlgebra.Opposite

/-!
# Opposites of differential graded algebras

The opposite of a differential graded algebra uses the Koszul-signed multiplication

`op a * op b = (-1) ^ (|a| * |b|) • op (b * a)`.

With this multiplication, the unchanged differential `d (op a) = op (d a)` again obeys the
graded Leibniz rule.  The ordinary multiplicative opposite does not: reversing the two factors
without the Koszul sign puts the Leibniz sign on the wrong term.

## Main definitions

* `GradedOpposite.differential`: the differential induced on the graded opposite.

## Main results

* `GradedOpposite.differential_op` and `GradedOpposite.differential_unop`: normalization of the
  differential through the two directions of the underlying linear equivalence.
* `IsDGAlgebra.gradedOpposite`: the Koszul-signed opposite of a differential graded algebra is a
  differential graded algebra.

The convention follows B. Keller, *Deriving DG categories*, Section 1, and B. Keller,
*Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open scoped DirectSum

namespace TauCeti

universe uR uA

namespace GradedOpposite

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  (G : InternalGrading R A)

/-- The differential on the graded opposite, unchanged on underlying elements. -/
noncomputable def differential (d : A →ₗ[R] A) :
    GradedOpposite G →ₗ[R] GradedOpposite G :=
  (opLinearEquiv G).conj d

/-- The opposite differential acts by the original differential on underlying elements. -/
@[simp]
theorem differential_op (d : A →ₗ[R] A) (a : A) :
    differential G d (op G a) = op G (d a) := by
  rw [differential, LinearEquiv.conj_apply_apply]
  simp

/-- Returning the opposite differential to the original algebra gives the original
differential. -/
@[simp]
theorem differential_unop (d : A →ₗ[R] A) (a : GradedOpposite G) :
    unop G (differential G d a) = d (unop G a) := by
  have h := differential_op G d (unop G a)
  rw [op_unop G a] at h
  exact (congrArg (unop G) h).trans (unop_op G _)

variable [GradedAlgebra G.piece] {d : A →ₗ[R] A}

end GradedOpposite

namespace IsDGAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {G : InternalGrading R A} [GradedAlgebra G.piece] {d : A →ₗ[R] A}

end IsDGAlgebra

end TauCeti
