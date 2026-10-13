/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.AuxiliaryUnary
public import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.Heuristic
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Incompressibility
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINKT.AuxiliaryUnary.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINKT.AuxiliaryUnary.Internal

/-!
# The auxiliary-unary distribution as canonical MINKT instances

Every seed in Hirahara's auxiliary-unary ensemble samples the canonical MINKT
code of its retained binary prefix and remaining unary clock. This module makes
that identity explicit and transfers exact decoding, membership, and point-mass
facts to MINKT notation.
-/

public section

namespace Complexity

namespace AuxiliaryUnarySeed

variable {tapes : ℕ}

/-- The sampled MINKT output is exactly the retained binary prefix.
@isnad1 id=eq.0h2v.s3.0f07ee74cc65 from=translated src=- shape=74e016e8 vocab=e07194c7
-/
@[simp] theorem minktInstance_output {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.output = seed.binary :=
  minktInstance_output_internal seed

/-- The sampled MINKT clock fills the part after the retained prefix.
@isnad1 id=eq.0h2v.s4.f909aabdaf52 from=translated src=- shape=8671fcf8 vocab=d92550cf
-/
@[simp] theorem minktInstance_time {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.time = m - seed.split :=
  minktInstance_time_internal seed

/-- The sampled instance's output length is the selected split.
@isnad1 id=eq.0h2v.s4.cf662b0bf212 from=translated src=- shape=bc52d39d vocab=0b938067
-/
theorem minktInstance_output_length {m : ℕ}
    (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.output.length = seed.split :=
  minktInstance_output_length_internal seed

/-- Every positive auxiliary-unary slice gives its MINKT instance a positive
clock.
@isnad1 id=lt.1h2v.s4.356a9b22a489 from=translated src=- shape=fe4d9e1a vocab=0d33f81c
-/
theorem minktInstance_time_pos {m : ℕ} (hm : 0 < m)
    (seed : AuxiliaryUnarySeed m) : 0 < seed.minktInstance.time :=
  minktInstance_time_pos_internal hm seed

/-- The auxiliary-unary sample is definitionally the canonical encoding of its
MINKT instance.
@isnad1 id=eq.0h2v.s3.a9b105ce2277 from=translated src=- shape=74e016e8 vocab=5a77ec97
-/
@[simp] theorem encode_minktInstance {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.encode = seed.sample :=
  encode_minktInstance_internal seed

/-- MINKT decoding of every auxiliary-unary sample succeeds exactly.
@isnad1 id=eq.0h2v.s4.4af084a12c77 from=translated src=- shape=20e2c586 vocab=d3e93eaa
-/
@[simp] theorem decode?_sample_minktInstance {m : ℕ}
    (seed : AuxiliaryUnarySeed m) :
    MINKT.Instance.decode? seed.sample = some seed.minktInstance :=
  decode?_sample_internal seed

/-- Auxiliary-unary sample membership is membership of the sampled canonical
MINKT instance.
@isnad1 id=iff.0h5v.s5.efc141a9afe9 from=translated src=- shape=c90911ec vocab=e941055e
-/
theorem sample_mem_minkt_iff {m : ℕ} (seed : AuxiliaryUnarySeed m)
    (machine : TM tapes) (threshold : ℕ → ℕ) :
    seed.sample ∈ MINKT machine threshold ↔
      seed.minktInstance.IsBelow machine threshold :=
  sample_mem_minkt_iff_internal seed machine threshold

/-- Expanded sample membership uses the selected prefix length and remaining
primitive clock directly.
@isnad1 id=iff.0h5v.s6.2c2c61e62568 from=translated src=- shape=6977fcd1 vocab=6a921456
-/
theorem sample_mem_minkt_iff_complexity {m : ℕ}
    (seed : AuxiliaryUnarySeed m) (machine : TM tapes)
    (threshold : ℕ → ℕ) :
    seed.sample ∈ MINKT machine threshold ↔
      machine.timeBoundedKolmogorovComplexity seed.binary
          (m - seed.split) <
        (threshold seed.split : WithTop ℕ) :=
  sample_mem_minkt_iff_complexity_internal seed machine threshold

/-- The MINKT event of a seed is exactly membership of its retained prefix in
the corresponding fixed-length strict-compressibility set.
@isnad1 id=iff.0h5v.s6.19b70b02ca31 from=translated src=- shape=54149471 vocab=3d78d35c
-/
theorem sample_mem_minkt_iff_mem_strictlyCompressible {m : ℕ}
    (seed : AuxiliaryUnarySeed m) (machine : TM tapes)
    (threshold : ℕ → ℕ) :
    seed.sample ∈ MINKT machine threshold ↔
      seed.binaryBits ∈ machine.timeBoundedStrictlyCompressibleStrings
        seed.split (m - seed.split) (threshold seed.split) :=
  sample_mem_minkt_iff_mem_strictlyCompressible_internal
    seed machine threshold

end AuxiliaryUnarySeed

namespace FiniteEnsemble

/-- The generic language-mass definition agrees exactly with the named MINKT
probability under the auxiliary-unary ensemble.
@isnad1 id=eq.0h4v.s4.2fb8bf6b25d8 from=translated src=- shape=bd4ad2bb vocab=ee8ed9bf
-/
theorem languageProbability_auxiliaryUnary_minkt
    {tapes : ℕ} (machine : TM tapes) (threshold : ℕ → ℕ) (m : ℕ) :
    auxiliaryUnary.languageProbability (MINKT machine threshold) m =
      auxiliaryUnaryMINKTProbability machine threshold m :=
  languageProbability_auxiliaryUnary_minkt_internal machine threshold m

/-- Exact conditioning identity for strict MINKT under a positive
auxiliary-unary slice: its probability is the uniform average of the
fixed-length strict-compressibility probabilities over all split lengths.
@isnad1 id=eq.1h4v.s6.50443c453825 from=translated src=- shape=b910feff vocab=e5bbb5f1
-/
theorem probability_auxiliaryUnary_minkt_eq_average
    {tapes m : ℕ} (hm : 0 < m) (machine : TM tapes)
    (threshold : ℕ → ℕ) :
    auxiliaryUnaryMINKTProbability machine threshold m =
      (1 / (m : ℚ)) * ∑ n : Fin m,
        eventProb (machine.timeBoundedStrictlyCompressibleStrings
          n.val (m - n.val) (threshold n.val)) :=
  probability_auxiliaryUnary_minkt_eq_average_internal hm machine threshold

/-- Strict incompressibility bounds the MINKT probability by the average of
the sharp per-length ratios `(2^r(n) - 1) / 2^n`.
@isnad1 id=le.1h4v.s6.6b057b0872a1 from=translated src=- shape=f207eae0 vocab=cd456327
-/
theorem probability_auxiliaryUnary_minkt_le_average_incompressibility
    {tapes m : ℕ} (hm : 0 < m) (machine : TM tapes)
    (threshold : ℕ → ℕ) :
    auxiliaryUnaryMINKTProbability machine threshold m ≤
      (1 / (m : ℚ)) * ∑ n : Fin m,
        ((2 ^ threshold n.val - 1 : ℕ) : ℚ) / (2 : ℚ) ^ n.val :=
  probability_auxiliaryUnary_minkt_le_average_incompressibility_internal
    hm machine threshold

/-- Any common upper bound on the strict incompressibility ratios bounds the
entire positive auxiliary-unary slice.
@isnad1 id=le.2h5v.s6.df733e3d57a5 from=translated src=- shape=da666df4 vocab=162bcd08
-/
theorem probability_auxiliaryUnary_minkt_le_of_pointwise
    {tapes m : ℕ} (hm : 0 < m) (machine : TM tapes)
    (threshold : ℕ → ℕ) (bound : ℚ)
    (hbound : ∀ n : Fin m,
      ((2 ^ threshold n.val - 1 : ℕ) : ℚ) / (2 : ℚ) ^ n.val ≤ bound) :
    auxiliaryUnaryMINKTProbability machine threshold m ≤ bound :=
  probability_auxiliaryUnary_minkt_le_of_pointwise_internal
    hm machine threshold bound hbound

/-- Exact point mass of a canonical MINKT instance in the auxiliary-unary
ensemble.
@isnad1 id=eq.1h3v.s6.5901c3f2cb48 from=translated src=- shape=854754f3 vocab=b8608203
-/
theorem mass_auxiliaryUnary_minktInstance {m n : ℕ} (hn : n < m)
    (output : Fin n → Bool) :
    auxiliaryUnary.mass m
        (MINKT.Instance.encode
          { output := List.ofFn output, time := m - n }) =
      1 / ((m : ℚ) * (2 : ℚ) ^ n) :=
  mass_auxiliaryUnary_minktInstance_internal hn output

end FiniteEnsemble

namespace MINKT

/-- An errorless MINKT heuristic rejects mass at least one minus the exact
MINKT mass and its failure mass on every auxiliary-unary slice.
@isnad1 id=le.1h5v.s5.ac68922baebd from=translated src=- shape=3e9a4b9b vocab=325c26fb
-/
theorem one_sub_auxiliaryUnaryProbability_sub_failure_le_reject
    {tapes m : ℕ} {machine : TM tapes} {threshold : ℕ → ℕ}
    {A : HeuristicAlgorithm}
    (herrorless : A.IsErrorlessFor (MINKT machine threshold)) :
    1 - FiniteEnsemble.auxiliaryUnaryMINKTProbability machine threshold m -
        A.failureProbability FiniteEnsemble.auxiliaryUnary m ≤
      A.answerProbability FiniteEnsemble.auxiliaryUnary .reject m :=
  one_sub_auxiliaryUnaryProbability_sub_failure_le_reject_internal herrorless

/-- The sharp incompressibility average gives an explicit lower bound on the
correct rejection mass of every errorless MINKT heuristic.
@isnad1 id=le.2h5v.s7.6c33a5df6e8d from=translated src=- shape=381956db vocab=b3d58039
-/
theorem auxiliaryUnary_rejectProbability_ge_average
    {tapes m : ℕ} (hm : 0 < m) {machine : TM tapes}
    {threshold : ℕ → ℕ} {A : HeuristicAlgorithm}
    (herrorless : A.IsErrorlessFor (MINKT machine threshold)) :
    1 - (1 / (m : ℚ)) * ∑ n : Fin m,
          ((2 ^ threshold n.val - 1 : ℕ) : ℚ) / (2 : ℚ) ^ n.val -
        A.failureProbability FiniteEnsemble.auxiliaryUnary m ≤
      A.answerProbability FiniteEnsemble.auxiliaryUnary .reject m :=
  auxiliaryUnary_rejectProbability_ge_average_internal hm herrorless

/-- If every split's low-complexity density is at most `low` and the heuristic
fails with probability at most `failure`, then it correctly rejects mass at
least `1 - low - failure`.
@isnad1 id=le.4h7v.s7.9d9e69e8bab8 from=translated src=- shape=a1d940bf vocab=4ecdac59
-/
theorem auxiliaryUnary_rejectProbability_ge_of_pointwise
    {tapes m : ℕ} (hm : 0 < m) {machine : TM tapes}
    {threshold : ℕ → ℕ} {A : HeuristicAlgorithm} (low failure : ℚ)
    (herrorless : A.IsErrorlessFor (MINKT machine threshold))
    (hlow : ∀ n : Fin m,
      ((2 ^ threshold n.val - 1 : ℕ) : ℚ) / (2 : ℚ) ^ n.val ≤ low)
    (hfailure : A.failureProbability FiniteEnsemble.auxiliaryUnary m ≤ failure) :
    1 - low - failure ≤
      A.answerProbability FiniteEnsemble.auxiliaryUnary .reject m :=
  auxiliaryUnary_rejectProbability_ge_of_pointwise_internal
    hm low failure herrorless hlow hfailure

end MINKT

end Complexity
