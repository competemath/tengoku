/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.Complexitylib.Complexitylib.Circuits.SparseSynthesis.Internal.Matrix
public import Tengoku.Complexitylib.Complexitylib.Circuits.SparseSynthesis.Internal.Intervals
public import Tengoku.Complexitylib.Complexitylib.Circuits.SparseSynthesis.Internal.ExtensionBank

/-!
# Partial truth-table synthesis

Intervals containing few specified positions use a shared bank of total
extensions. Every extension is masked to its interval before the row is
assembled, so unconstrained values cannot affect another interval's data.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open scoped BigOperators

/-- Shared minterms, interval-masked extension bank, and one OR per partial chunk. -/
def partialTableBudget (k l K weight : ℕ) : ℕ :=
  (2 ^ k + 2 ^ l) * (2 * (k + l) + 1) +
    (2 ^ k + 1) ^ 3 * (4 * 2 ^ k + 1) * 2 ^ K + weight / K + 4 * 2 ^ l + 1

end Complexity.CircuitSparseSynthesis.Internal
