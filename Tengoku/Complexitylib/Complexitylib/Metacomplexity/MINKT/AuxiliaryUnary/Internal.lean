/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.AuxiliaryUnary.Internal
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINKT.AuxiliaryUnary.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINKT.Internal
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Incompressibility.Internal
import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.FiniteEnsemble
import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.Heuristic.Internal

/-!
# Auxiliary-unary MINKT instances -- proof internals

Proofs that auxiliary-unary samples are exact canonical MINKT codes, together
with their machine-relative membership and point-mass characterizations.
-/

public section

namespace Complexity

namespace AuxiliaryUnarySeed

variable {tapes : ℕ}

/--
@isnad1 id=eq.0h2v.s3.0f07ee74cc65 from=translated src=- shape=74e016e8 vocab=e07194c7
-/
theorem minktInstance_output_internal {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.output = seed.binary := rfl

/--
@isnad1 id=eq.0h2v.s4.f909aabdaf52 from=translated src=- shape=8671fcf8 vocab=d92550cf
-/
theorem minktInstance_time_internal {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.time = m - seed.split := rfl

/--
@isnad1 id=eq.0h2v.s4.cf662b0bf212 from=translated src=- shape=bc52d39d vocab=0b938067
-/
theorem minktInstance_output_length_internal {m : ℕ}
    (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.output.length = seed.split := by
  exact binary_length_internal seed

/--
@isnad1 id=lt.1h2v.s4.356a9b22a489 from=translated src=- shape=fe4d9e1a vocab=0d33f81c
-/
theorem minktInstance_time_pos_internal {m : ℕ} (hm : 0 < m)
    (seed : AuxiliaryUnarySeed m) : 0 < seed.minktInstance.time := by
  exact Nat.sub_pos_of_lt (split_lt_internal hm seed)

/--
@isnad1 id=eq.0h2v.s3.a9b105ce2277 from=translated src=- shape=74e016e8 vocab=5a77ec97
-/
theorem encode_minktInstance_internal {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    seed.minktInstance.encode = seed.sample := by
  rfl

/--
@isnad1 id=eq.0h2v.s4.4af084a12c77 from=translated src=- shape=20e2c586 vocab=d3e93eaa
-/
theorem decode?_sample_internal {m : ℕ} (seed : AuxiliaryUnarySeed m) :
    MINKT.Instance.decode? seed.sample = some seed.minktInstance := by
  rw [← encode_minktInstance_internal]
  exact MINKT.Instance.decode?_encode_internal seed.minktInstance

/--
@isnad1 id=iff.0h5v.s5.efc141a9afe9 from=translated src=- shape=c90911ec vocab=e941055e
-/
theorem sample_mem_minkt_iff_internal {m : ℕ} (seed : AuxiliaryUnarySeed m)
    (machine : TM tapes) (threshold : ℕ → ℕ) :
    seed.sample ∈ MINKT machine threshold ↔
      seed.minktInstance.IsBelow machine threshold := by
  rw [← encode_minktInstance_internal]
  simp [MINKT, MINKT.Instance.decode?_encode_internal]

/--
@isnad1 id=iff.0h5v.s6.2c2c61e62568 from=translated src=- shape=6977fcd1 vocab=6a921456
-/
theorem sample_mem_minkt_iff_complexity_internal {m : ℕ}
    (seed : AuxiliaryUnarySeed m) (machine : TM tapes)
    (threshold : ℕ → ℕ) :
    seed.sample ∈ MINKT machine threshold ↔
      machine.timeBoundedKolmogorovComplexity seed.binary
          (m - seed.split) <
        (threshold seed.split : WithTop ℕ) := by
  rw [sample_mem_minkt_iff_internal]
  simp only [MINKT.Instance.IsBelow, minktInstance_output_internal,
    minktInstance_time_internal, binary_length_internal]

/--
@isnad1 id=iff.0h5v.s6.19b70b02ca31 from=translated src=- shape=54149471 vocab=3d78d35c
-/
theorem sample_mem_minkt_iff_mem_strictlyCompressible_internal {m : ℕ}
    (seed : AuxiliaryUnarySeed m) (machine : TM tapes)
    (threshold : ℕ → ℕ) :
    seed.sample ∈ MINKT machine threshold ↔
      seed.binaryBits ∈ machine.timeBoundedStrictlyCompressibleStrings
        seed.split (m - seed.split) (threshold seed.split) := by
  rw [sample_mem_minkt_iff_complexity_internal,
    TM.mem_timeBoundedStrictlyCompressibleStrings_iff_internal]
  rfl

end AuxiliaryUnarySeed

namespace FiniteEnsemble

/--
@isnad1 id=eq.0h4v.s4.2fb8bf6b25d8 from=translated src=- shape=bd4ad2bb vocab=ee8ed9bf
-/
theorem languageProbability_auxiliaryUnary_minkt_internal
    {tapes : ℕ} (machine : TM tapes) (threshold : ℕ → ℕ) (m : ℕ) :
    auxiliaryUnary.languageProbability (MINKT machine threshold) m =
      auxiliaryUnaryMINKTProbability machine threshold m := by
  rfl

/--
@isnad1 id=eq.1h4v.s6.50443c453825 from=translated src=- shape=b910feff vocab=e5bbb5f1
-/
theorem probability_auxiliaryUnary_minkt_eq_average_internal
    {tapes m : ℕ} (hm : 0 < m) (machine : TM tapes)
    (threshold : ℕ → ℕ) :
    auxiliaryUnaryMINKTProbability machine threshold m =
      (1 / (m : ℚ)) * ∑ n : Fin m,
        eventProb (machine.timeBoundedStrictlyCompressibleStrings
          n.val (m - n.val) (threshold n.val)) := by
  classical
  let := auxiliaryUnary.seedFintype m
  let := auxiliaryUnary.seedDecidableEq m
  unfold auxiliaryUnaryMINKTProbability
  change uniformProbability
    (Finset.univ.filter fun seed : AuxiliaryUnarySeed m =>
      seed.sample ∈ MINKT machine threshold) = _
  rw [show
    Finset.univ.filter
        (fun seed : AuxiliaryUnarySeed m =>
          seed.sample ∈ MINKT machine threshold) =
      Finset.univ.filter
        (fun seed : AuxiliaryUnarySeed m =>
          seed.binaryBits ∈ machine.timeBoundedStrictlyCompressibleStrings
            seed.split (m - seed.split) (threshold seed.split)) by
    ext seed
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact AuxiliaryUnarySeed.sample_mem_minkt_iff_mem_strictlyCompressible_internal
      seed machine threshold]
  have haverage := AuxiliaryUnarySeed.split_prefix_event_probability_internal
    (m := m) (fun n => machine.timeBoundedStrictlyCompressibleStrings
      n (m - n) (threshold n))
  have hmax : Nat.max 1 m = m :=
    Nat.max_eq_right (Nat.succ_le_iff.mpr hm)
  let castSeed : AuxiliaryUnarySeed m ≃ (Fin m) × (Fin m → Bool) :=
    Equiv.prodCongr (finCongr hmax) (Equiv.refl (Fin m → Bool))
  let event (seed : (Fin m) × (Fin m → Bool)) : Prop :=
    (AuxiliaryUnarySeed.bitBlocks
      (Nat.le_of_lt seed.1.isLt) seed.2).1 ∈
        machine.timeBoundedStrictlyCompressibleStrings
          seed.1.val (m - seed.1.val) (threshold seed.1.val)
  calc
    uniformProbability
        (Finset.univ.filter fun seed : AuxiliaryUnarySeed m =>
          seed.binaryBits ∈ machine.timeBoundedStrictlyCompressibleStrings
            seed.split (m - seed.split) (threshold seed.split)) =
        uniformProbability
          (Finset.univ.filter fun seed : AuxiliaryUnarySeed m =>
            event (castSeed seed)) := by
      apply congrArg uniformProbability
      ext seed
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    _ = uniformProbability
        (Finset.univ.filter fun seed : (Fin m) × (Fin m → Bool) =>
          event seed) :=
      uniformProbability_equiv castSeed event
    _ = (1 / (m : ℚ)) * ∑ n : Fin m,
        eventProb (machine.timeBoundedStrictlyCompressibleStrings
          n.val (m - n.val) (threshold n.val)) := haverage

/--
@isnad1 id=le.1h4v.s6.6b057b0872a1 from=translated src=- shape=f207eae0 vocab=cd456327
-/
theorem probability_auxiliaryUnary_minkt_le_average_incompressibility_internal
    {tapes m : ℕ} (hm : 0 < m) (machine : TM tapes)
    (threshold : ℕ → ℕ) :
    auxiliaryUnaryMINKTProbability machine threshold m ≤
      (1 / (m : ℚ)) * ∑ n : Fin m,
        ((2 ^ threshold n.val - 1 : ℕ) : ℚ) / (2 : ℚ) ^ n.val := by
  rw [probability_auxiliaryUnary_minkt_eq_average_internal hm machine threshold]
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun n _hn =>
      TM.eventProb_timeBoundedStrictlyCompressibleStrings_le_internal
        machine n.val (m - n.val) (threshold n.val)
  · positivity

/--
@isnad1 id=le.2h5v.s6.df733e3d57a5 from=translated src=- shape=da666df4 vocab=162bcd08
-/
theorem probability_auxiliaryUnary_minkt_le_of_pointwise_internal
    {tapes m : ℕ} (hm : 0 < m) (machine : TM tapes)
    (threshold : ℕ → ℕ) (bound : ℚ)
    (hbound : ∀ n : Fin m,
      ((2 ^ threshold n.val - 1 : ℕ) : ℚ) / (2 : ℚ) ^ n.val ≤ bound) :
    auxiliaryUnaryMINKTProbability machine threshold m ≤ bound := by
  calc
    auxiliaryUnaryMINKTProbability machine threshold m ≤
        (1 / (m : ℚ)) * ∑ n : Fin m,
          ((2 ^ threshold n.val - 1 : ℕ) : ℚ) / (2 : ℚ) ^ n.val :=
      probability_auxiliaryUnary_minkt_le_average_incompressibility_internal
        hm machine threshold
    _ ≤ (1 / (m : ℚ)) * ∑ _n : Fin m, bound := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun n _hn => hbound n
      · positivity
    _ = bound := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
      field_simp

/--
@isnad1 id=eq.1h3v.s6.5901c3f2cb48 from=translated src=- shape=854754f3 vocab=b8608203
-/
theorem mass_auxiliaryUnary_minktInstance_internal {m n : ℕ} (hn : n < m)
    (output : Fin n → Bool) :
    auxiliaryUnary.mass m
        (MINKT.Instance.encode
          { output := List.ofFn output, time := m - n }) =
      1 / ((m : ℚ) * (2 : ℚ) ^ n) := by
  simpa [MINKT.Instance.encode, MINKT.Instance.unaryClock] using
    mass_auxiliaryUnary_pair_internal hn output

end FiniteEnsemble

namespace MINKT

/--
@isnad1 id=le.1h5v.s5.ac68922baebd from=translated src=- shape=3e9a4b9b vocab=325c26fb
-/
theorem one_sub_auxiliaryUnaryProbability_sub_failure_le_reject_internal
    {tapes m : ℕ} {machine : TM tapes} {threshold : ℕ → ℕ}
    {A : HeuristicAlgorithm}
    (herrorless : A.IsErrorlessFor (MINKT machine threshold)) :
    1 - FiniteEnsemble.auxiliaryUnaryMINKTProbability machine threshold m -
        A.failureProbability FiniteEnsemble.auxiliaryUnary m ≤
      A.answerProbability FiniteEnsemble.auxiliaryUnary .reject m := by
  have hreject :=
    herrorless.one_sub_languageProbability_sub_failure_le_reject_internal
      FiniteEnsemble.auxiliaryUnary m
  rw [FiniteEnsemble.languageProbability_auxiliaryUnary_minkt_internal] at hreject
  exact hreject

/--
@isnad1 id=le.2h5v.s7.6c33a5df6e8d from=translated src=- shape=381956db vocab=b3d58039
-/
theorem auxiliaryUnary_rejectProbability_ge_average_internal
    {tapes m : ℕ} (hm : 0 < m) {machine : TM tapes}
    {threshold : ℕ → ℕ} {A : HeuristicAlgorithm}
    (herrorless : A.IsErrorlessFor (MINKT machine threshold)) :
    1 - (1 / (m : ℚ)) * ∑ n : Fin m,
          ((2 ^ threshold n.val - 1 : ℕ) : ℚ) / (2 : ℚ) ^ n.val -
        A.failureProbability FiniteEnsemble.auxiliaryUnary m ≤
      A.answerProbability FiniteEnsemble.auxiliaryUnary .reject m := by
  have hreject :=
    one_sub_auxiliaryUnaryProbability_sub_failure_le_reject_internal
      (m := m) herrorless
  have hprob :=
    FiniteEnsemble.probability_auxiliaryUnary_minkt_le_average_incompressibility_internal
      hm machine threshold
  linarith

/--
@isnad1 id=le.4h7v.s7.9d9e69e8bab8 from=translated src=- shape=a1d940bf vocab=4ecdac59
-/
theorem auxiliaryUnary_rejectProbability_ge_of_pointwise_internal
    {tapes m : ℕ} (hm : 0 < m) {machine : TM tapes}
    {threshold : ℕ → ℕ} {A : HeuristicAlgorithm} (low failure : ℚ)
    (herrorless : A.IsErrorlessFor (MINKT machine threshold))
    (hlow : ∀ n : Fin m,
      ((2 ^ threshold n.val - 1 : ℕ) : ℚ) / (2 : ℚ) ^ n.val ≤ low)
    (hfailure : A.failureProbability FiniteEnsemble.auxiliaryUnary m ≤ failure) :
    1 - low - failure ≤
      A.answerProbability FiniteEnsemble.auxiliaryUnary .reject m := by
  have hreject :=
    one_sub_auxiliaryUnaryProbability_sub_failure_le_reject_internal
      (m := m) herrorless
  have hprob :=
    FiniteEnsemble.probability_auxiliaryUnary_minkt_le_of_pointwise_internal
      hm machine threshold low hlow
  linarith

end MINKT

end Complexity
