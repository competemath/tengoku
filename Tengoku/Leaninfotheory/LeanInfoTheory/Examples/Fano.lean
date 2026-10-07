/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.Fano

/-!
# Fano inequality examples

This module exercises the finite Fano API with a perfect decoder, a singleton
source alphabet, a binary source observed through a constant, and the
uniform-source mutual-information and error-probability corollaries.
-/

namespace LeanInfoTheory
namespace Examples
namespace Fano

open Shannon

noncomputable section

namespace PerfectDecoder

/--
A diagonal Boolean joint law has zero conditional entropy under the identity
decoder. This specializes the expanded PMF form of Fano's inequality.
-/
theorem condEntropy_diagonal_eq_zero (p : PMF Bool) :
    condEntropy (p.map fun b => (b, b)) = 0 := by
  have herror :
      decodingErrorProbability (p.map fun b => (b, b)) id = 0 := by
    unfold decodingErrorProbability
    rw [PMF.map_comp]
    change
      ((p.map fun b : Bool => decodingErrorIndicator id b b) true).toReal = 0
    have hindicator :
        (fun b : Bool => decodingErrorIndicator id b b) =
          Function.const Bool false := by
      funext b
      simp [decodingErrorIndicator]
    rw [hindicator, PMF.map_const]
    simp
  apply le_antisymm
  · simpa [herror] using
      condEntropy_fano (p.map fun b => (b, b)) id
  · exact condEntropy_nonneg _

end PerfectDecoder

namespace SingletonSource

/--
Fano's q-ary form includes a singleton source alphabet without a public
cardinality lower bound. Every decoder is necessarily correct on that source.
-/
theorem condEntropy_eq_zero
    {beta : Type*} [Fintype beta]
    (p : PMF (Unit × beta)) (decoder : beta -> Unit) :
    condEntropy p = 0 := by
  have herror : decodingErrorProbability p decoder = 0 := by
    rw [decodingErrorProbability_eq_sum]
    apply Finset.sum_eq_zero
    intro z _hz
    simp [Subsingleton.elim (decoder z.2) z.1]
  apply le_antisymm
  · simpa [herror] using condEntropy_fano_qary p decoder
  · exact condEntropy_nonneg _

end SingletonSource

namespace BinaryConstantObservation

/--
For a fair Boolean source, a constant-false observation decoded by the
identity function has error probability `1/2`.
-/
theorem decodingErrorProbabilityOf_eq_half :
    decodingErrorProbabilityOf
        (PMF.uniformOfFintype Bool)
        id (fun _ => false) id =
      (1 / 2 : Real) := by
  unfold decodingErrorProbabilityOf decodingErrorProbability
  rw [PMF.map_comp]
  change
    (((PMF.uniformOfFintype Bool).map
      fun b : Bool => decodingErrorIndicator id b false) true).toReal =
      (1 / 2 : Real)
  have hindicator :
      (fun b : Bool => decodingErrorIndicator id b false) = id := by
    funext b
    cases b <;> simp [decodingErrorIndicator]
  rw [hindicator, PMF.map_id]
  norm_num [PMF.uniformOfFintype_apply]

/--
The random-variable expanded Fano theorem bounds the conditional entropy in
the constant-observation example by binary entropy at error probability
`1/2`.
-/
theorem condEntropyOf_le_binEntropy_half :
    condEntropyOf
        (PMF.uniformOfFintype Bool)
        id (fun _ => false) ≤
      Real.binEntropy (1 / 2 : Real) := by
  simpa [decodingErrorProbabilityOf_eq_half] using
    condEntropyOf_fano
      (PMF.uniformOfFintype Bool)
      id (fun _ => false) id

/--
The uniform-source mutual-information corollary specializes directly to the
binary constant-observation example.
-/
theorem mutualInfoOf_fano_lower_bound :
    Real.log 2 - Real.log 2 - (1 / 2 : Real) * Real.log 2 ≤
      mutualInfoOf
        (PMF.uniformOfFintype Bool)
        id (fun _ => false) := by
  have huniform :
      (PMF.uniformOfFintype Bool).map id =
        PMF.uniformOfFintype Bool :=
    PMF.map_id _
  simpa [decodingErrorProbabilityOf_eq_half] using
    mutualInfoOf_fano_lower_bound_of_uniform_source
      (PMF.uniformOfFintype Bool)
      id (fun _ => false) id huniform

/--
The normalized uniform-source converse gives a concrete lower bound on the
same binary decoding-error probability.
-/
theorem decodingErrorProbabilityOf_fano_lower_bound :
    1 -
          (mutualInfoOf
              (PMF.uniformOfFintype Bool)
              id (fun _ => false) +
            Real.log 2) /
            Real.log 2 ≤
      (1 / 2 : Real) := by
  have huniform :
      (PMF.uniformOfFintype Bool).map id =
        PMF.uniformOfFintype Bool :=
    PMF.map_id _
  simpa [decodingErrorProbabilityOf_eq_half] using
    decodingErrorProbabilityOf_fano_lower_bound_of_uniform_source
      (PMF.uniformOfFintype Bool)
      id (fun _ => false) id huniform (by norm_num)

end BinaryConstantObservation

end

end Fano
end Examples
end LeanInfoTheory
