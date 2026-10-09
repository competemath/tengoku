/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.Complexitylib.Complexitylib.Circuits.SparseSynthesis.Internal.Matrix
public import Tengoku.Complexitylib.Complexitylib.Circuits.SparseSynthesis.Internal.Chunks

/-!
# Sparse truth-table synthesis

Each row is divided into short tuples of true columns. All possible tuples
are implemented once. The leading assembly cost is `weight / chunkSize`.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open scoped BigOperators

/-- Shared minterms, all `K`-tuples of columns, and one OR per selected sparse chunk. -/
def sparseTableBudget (k l K weight : ℕ) : ℕ :=
  (2 ^ k + 2 ^ l) * (2 * (k + l) + 1) + (2 ^ k + 1) ^ K * (K + 1) +
    weight / K + 4 * 2 ^ l + 1

end Complexity.CircuitSparseSynthesis.Internal
