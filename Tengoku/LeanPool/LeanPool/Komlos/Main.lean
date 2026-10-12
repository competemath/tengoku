/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Tengoku.LeanPool.LeanPool.Komlos.Approximation
public import Tengoku.LeanPool.LeanPool.Komlos.GridCase
public import Tengoku

/-!
# The Komlós bound

Adapted for Lean Pool by changing module paths and selecting explicit imports.

A real matrix whose columns have Euclidean norm at most `1` has discrepancy at most `36`.
The file proves this for arbitrary finite row and column types, then gives the scaled bound
and the equivalent statements for vectors and colourings.

The proof uses `Komlos.discrepancy_le_of_grid`. Given `η > 0`, approximate each matrix entry
within `η / (n + 1)`, where `n` is the number of columns. A colouring for the approximation
has discrepancy at most `36 + η` for the original matrix. Letting `η` tend to zero gives the
bound.
-/

@[expose] public section

namespace Komlos

open Finset Matrix

end Komlos
