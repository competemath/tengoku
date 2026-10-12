/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.Dissociated.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.BorderRank
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.Dissociated.Internal

/-!
# A single integer-entry tensor family of border rank `(7/3-o(1)) m`

The computable family `Dissociated.tensor m` is independent of epsilon, is defined
at every dimension by zero padding an odd core, and has coefficient binary length
at most `m+1`. Its complex border rank is eventually at least `(7/3-ε)m` for every
positive epsilon. In particular it eventually has border rank at least `17m/8`.

This uniformizes the checked periodic paired-cluster construction. The motivating
research note, *Distinct subset sums and explicit tensor border rank*, Revision 2,
uses the same dissociated-cluster and periodic coefficient ideas to approach `17/8`.
Here the existing stronger paired-cluster proof replaces its five-far-diagonal
branch. All tensor-theoretic inputs are proved in the library: substitution,
Koszul flattenings, block nonsingularity, and the deletion game.

The entry formula and bounded parameter search are computable, and their binary
output size is polynomial. A polynomial-time machine implementation is not proved
by these declarations; output-size bounds alone do not certify running time.
-/

public section

namespace Algebraic.Tensor3.Dissociated

open Filter

/-- The order search never exceeds the binary logarithm of the odd core dimension.
@isnad1 id=le.0h1v.s5.33bcc86c95ae from=translated src=- shape=4f9de1e6 vocab=47bb8278
-/
theorem order_le_log (k : ℕ) : order k ≤ Nat.log 2 (2 * k + 1) :=
  Internal.order_le_log k

/-- The admissible candidate set has at most logarithmically many elements.
@isnad1 id=le.0h1v.s5.2d593c3859c5 from=translated src=- shape=90860270 vocab=3d2a9caa
-/
theorem card_candidates_le (k : ℕ) : (candidates k).card ≤ Nat.log 2 (2 * k + 1) + 1 := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- Every fixed positive order eventually becomes admissible in the uniform search.
@isnad1 id=eventual.1h1v.s4.75905a43a230 from=translated src=- shape=d5c6bcbb vocab=77796bb0
-/
theorem eventually_admissible {p : ℕ} (hp : 1 ≤ p) : ∀ᶠ k in atTop, Admissible k p :=
  Internal.eventually_admissible hp

/-- The selected cluster order tends to infinity.
@isnad1 id=tendsto.0h0v.s3.2be88dc25f7f from=translated src=- shape=41b74a9e vocab=f0e5a994
-/
theorem order_tendsto : Tendsto order atTop atTop :=
  tendsto_atTop.2 Internal.eventually_le_order

/-- Every valid tensor coefficient has at most `m+1` binary digits.
@isnad1 id=le.0h4v.s5.d42184fe3039 from=translated src=- shape=6ced6e94 vocab=2d4caa0f
-/
theorem entry_size_le (m : ℕ) (a j l : Fin m) : (entry m a j l).size ≤ m + 1 :=
  Internal.entry_size_le a.isLt j l

/-- Every coordinate is a nonnegative integer with the stated binary-size bound.
@isnad1 id=ex.0h4v.s5.7ad794f684ed from=translated src=- shape=d923d15d vocab=e063428e
-/
theorem tensor_entry (m : ℕ) (a j l : Fin m) :
    ∃ v : ℕ, v.size ≤ m + 1 ∧ tensor m a j l = (v : ℂ) :=
  ⟨entry m a j l, entry_size_le m a j l, rfl⟩

/-- The dense coordinate array has polynomial total binary output size.
@isnad1 id=le.0h1v.s6.04ef269bfa23 from=translated src=- shape=27315945 vocab=40cbbe93
-/
theorem sum_entry_size_le (m : ℕ) :
    (∑ a : Fin m, ∑ j : Fin m, ∑ l : Fin m, (entry m a j l).size) ≤ m ^ 3 * (m + 1) := by
  calc
    _ ≤ ∑ _a : Fin m, ∑ _j : Fin m, ∑ _l : Fin m, (m + 1) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum fun l _ => entry_size_le m a j l
    _ = _ := by simp [pow_succ]; ring

end Algebraic.Tensor3.Dissociated
