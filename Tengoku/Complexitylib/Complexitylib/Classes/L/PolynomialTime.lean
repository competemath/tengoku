/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Classes.L.PolynomialTime.Internal

/-!
# Log-space transducers run in polynomial time

The finite reduced-configuration theorem for one-way-output deterministic
transducers makes a logarithmic auxiliary-space bound into a polynomial time
bound. Consequently `L ⊆ P` and `FL ⊆ FP`.

## Main results

- `TM.transducerConfigBound_bigO_polynomial` — logarithmic space gives a
  polynomial reduced-configuration bound
- `L_subset_P` — deterministic log-space languages are polynomial-time
- `FL_subset_FP` — deterministic log-space functions are polynomial-time
-/

public section

namespace Complexity

namespace TM

variable {k : ℕ}

/-- The reduced-configuration count of a deterministic transducer using
`O(log n)` auxiliary space is polynomial in the input length.
@isnad1 id=ex.1h3v.s6.7d5ba4d990df from=translated src=- shape=30817e66 vocab=44b6d273
-/
theorem transducerConfigBound_bigO_polynomial
    (tm : TM k) {S : ℕ → ℕ}
    (hS : S =O (fun n => Nat.log 2 n)) :
    ∃ c : ℕ,
      (fun n => tm.transducerConfigBound n (S n)) =O
        ((· ^ (1 + (2 * c + 1) * k)) : ℕ → ℕ) :=
  tm.transducerConfigBound_bigO_polynomial_internal hS

end TM

/-- **`L ⊆ P`: every language decided by a deterministic log-space
transducer is decidable in polynomial time.**
@isnad1 id=le.0h0v.s2.e6cad42370b8 from=translated src=- shape=836e6cbb vocab=3e6bc7e2
-/
theorem L_subset_P : L ⊆ P :=
  L_subset_P_internal

/-- **`FL ⊆ FP`: every deterministic log-space transducer function is
computable in polynomial time.**
@isnad1 id=le.0h0v.s3.6e6d95fb1aeb from=translated src=- shape=1bd9911c vocab=0c3f4bc4
-/
theorem FL_subset_FP : FL ⊆ FP :=
  FL_subset_FP_internal

end Complexity
