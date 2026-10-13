/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Identity.Internal

/-!
# Identity strong condensation

Ignoring a finite seed and retaining the source is an exact strong condenser
at the original source cap. A singleton seed therefore supplies a seed-free
initialization for block condensation. Empty seed alphabets and threshold
zero are also covered by the existing total finite-weight definitions.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Retaining the source preserves every cap with zero error, hence with any nonnegative error.
@isnad1 id=weighted.1h4v.s5.77e7052b3e9a from=translated src=- shape=65f4c46c vocab=2520b9ee
-/
theorem WeightedStrongSeededCondenser.id {X Seed : Type*}
    [Fintype X] [Fintype Seed] {K : Nat} {ε : ℝ} (nonnegative : 0 ≤ ε) :
    WeightedStrongSeededCondenser (fun x (_ : Seed) => x : X → Seed → X) K K ε :=
  Internal.weightedStrongSeededCondenser_id nonnegative

end Algebraic.Cutwidth.Extractor
