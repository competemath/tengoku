/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import Tengoku.Compply.CompPoly.LinearAlgebra.Dense.Basic
public import Tengoku.Compply.CompPoly.LinearAlgebra.Dense.RowOps
public import Tengoku.Compply.CompPoly.LinearAlgebra.Dense.RowOpsCorrectness
public import Tengoku.Compply.CompPoly.LinearAlgebra.Dense.RrefSemantics
public import Tengoku.Compply.CompPoly.LinearAlgebra.Dense.RrefShape
public import Tengoku.Compply.CompPoly.LinearAlgebra.Dense.Kernel
public import Tengoku.Compply.CompPoly.LinearAlgebra.Dense.KernelInPlace
public import Tengoku.Compply.CompPoly.LinearAlgebra.Dense.KernelCorrectness
public import Tengoku.Compply.CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dense Linear Algebra

Facade module for dense row-major matrices, row operations, homogeneous-kernel
extraction, and their correctness contracts.
-/

@[expose] public section
