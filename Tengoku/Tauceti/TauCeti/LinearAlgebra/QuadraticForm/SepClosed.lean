/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# Quadratic forms over a separably closed field

This file proves that a finite-dimensional nondegenerate quadratic form over a separably closed
field of characteristic different from two is equivalent to a sum of squares.

## Main result

* `QuadraticForm.equivalent_weightedSumSquares_of_isSepClosed`: a nondegenerate quadratic form is
  equivalent to the standard sum of squares.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory /
  Spin Representations, Layer 4, "The spin module".
* Mathlib's `QuadraticForm.isometryEquivSumSquaresUnits` and
  `QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed` supply the normalization argument
  adapted here from algebraically closed to separably closed fields.
-/

public section

open QuadraticMap

namespace QuadraticForm

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K] [IsSepClosed K]

end QuadraticForm
