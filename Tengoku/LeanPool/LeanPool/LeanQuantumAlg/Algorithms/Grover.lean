/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Primitives.AmplitudeAmplification

/-!
# Grover search in the good/bad-plane model

Grover search evolves in the two-dimensional plane spanned by the uniform
superposition over bad indices and the uniform superposition over good indices.
In that plane the phase oracle and diffusion reflection form exactly the same
rotation used by amplitude amplification [dW19, qcnotes.tex:2768], and after
`k` Grover iterates the success probability is `sin((2k+1)θ)^2`
[dW19, qcnotes.tex:2817].

This file states the Grover specialization against an explicit plane model:
`phaseOracle`, `diffusion`, and the hypothesis that their product is the
standard amplification rotation on the invariant good/bad plane. Building the
full `n`-qubit oracle/diffusion implementation and rounding the optimal
iteration count are separate refinements; the correctness theorem here is the
closed-form rotation core used by those refinements.

## Main results

- `LeanPool.LeanQuantumAlg.GroverSearch.main` — exact good/bad-plane state after `k` Grover
  iterates.
- `LeanPool.LeanQuantumAlg.grover_success_probability` — corresponding marked-subspace
  measurement probability.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- The concrete Grover phase oracle for a marked-set predicate:
`|j⟩` receives phase `-1` exactly when `marked j` is true. -/
def phaseOracle {n : ℕ} (marked : Fin (2 ^ n) → Bool) : HilbertOperator n :=
  fun i j => if i = j then (if marked j then -1 else 1 : ℂ) else 0

/--
@isnad1 id=eq.0h3v.s7.efa448931eb6 from=translated src=- shape=53452bd2 vocab=de30cb91
-/
theorem phaseOracle_apply_ket {n : ℕ} (marked : Fin (2 ^ n) → Bool) (j : Fin (2 ^ n)) :
    HilbertOperator.applyVec (phaseOracle marked) (ket j : StateVector n) =
      ((if marked j then -1 else 1 : ℂ) • (ket j : StateVector n)) := by
  by_cases hm : marked j
  · conv_rhs =>
      simp [hm]
    apply WithLp.ofLp_injective
    funext i
    rw [show (HilbertOperator.applyVec (phaseOracle marked) (ket j : StateVector n)).ofLp i =
          HilbertOperator.applyVec (phaseOracle marked) (ket j : StateVector n) i from rfl,
      show ((-(ket j : StateVector n)).ofLp i) = (-(ket j : StateVector n)) i from rfl,
      HilbertOperator.applyVec_ket]
    by_cases hij : i = j
    · subst i
      simp [phaseOracle, hm, PureState.ket_apply]
    · simp [phaseOracle, PureState.ket_apply, hij]
  · conv_rhs =>
      simp [hm]
    apply WithLp.ofLp_injective
    funext i
    rw [show (HilbertOperator.applyVec (phaseOracle marked) (ket j : StateVector n)).ofLp i =
          HilbertOperator.applyVec (phaseOracle marked) (ket j : StateVector n) i from rfl,
      show ((ket j : StateVector n).ofLp i) = (ket j : StateVector n) i from rfl,
      HilbertOperator.applyVec_ket]
    by_cases hij : i = j
    · subst i
      simp [phaseOracle, hm, PureState.ket_apply]
    · simp [phaseOracle, PureState.ket_apply, hij]

/-- A Grover search instance restricted to its invariant two-dimensional
bad/good plane. The initial state is `amplitudeAmplificationState θ 0`, so the
initial marked-subspace probability is `sin θ ^ 2`; the oracle and diffusion
assumptions are the explicit theorem inputs. -/
structure GroverModel where
  /-- Initial angle from the bad axis; for `t` marked items among `N`, the
  textbook relation is `sin θ = sqrt (t / N)`. -/
  θ : ℝ
  /-- Phase oracle: reflection through the bad subspace in the good/bad plane. -/
  phaseOracle : Gate 1
  /-- Diffusion reflection through the prepared uniform/start state. -/
  diffusion : Gate 1
  /-- One Grover iterate, diffusion after phase oracle, is the standard
  amplitude-amplification rotation on the invariant plane. -/
  iterate_eq : diffusion * phaseOracle = amplitudeAmplificationStep θ

/-- Grover correctness in the accepted two-dimensional scope: under the explicit
oracle/diffusion rotation hypothesis, `k` Grover iterates produce the standard
closed-form state.
@isnad1 id=eq.0h2v.s7.fea0b6434e17 from=translated src=- shape=883d0aa1 vocab=25ecb0be
-/
theorem GroverSearch.main (M : GroverModel) (k : ℕ) :
    Gate.apply ((M.diffusion * M.phaseOracle) ^ k) (amplitudeAmplificationState M.θ 0) =
      amplitudeAmplificationState M.θ k := by
  rw [M.iterate_eq]
  exact amplitudeAmplificationStep_pow_apply M.θ k

/-- Every Grover plane model is an amplitude-amplification model with the phase
oracle as the good reflection and the diffusion operator as the start-state
reflection. -/
def GroverModel.toAmplitudeAmplificationModel (M : GroverModel) :
    AmplitudeAmplificationModel where
  θ := M.θ
  goodReflection := M.phaseOracle
  startReflection := M.diffusion
  iterate_eq := M.iterate_eq

namespace Grover

/-- The state after `k` Grover iterates, annotated with iterate cost `k`. -/
def timedIterate (M : GroverModel) (k : ℕ) : Timed (PureState 1) :=
  Timed.trusted k
    (Gate.apply ((M.diffusion * M.phaseOracle) ^ k)
      (amplitudeAmplificationState M.θ 0))

/--
@isnad1 id=eq.0h2v.s7.3bfd4ca26c62 from=translated src=- shape=2d4e5c36 vocab=da7bc982
-/
@[simp]
theorem timedIterate_ret (M : GroverModel) (k : ℕ) :
    (timedIterate M k).ret =
      Gate.apply ((M.diffusion * M.phaseOracle) ^ k)
        (amplitudeAmplificationState M.θ 0) := rfl

/--
@isnad1 id=eq.0h2v.s4.572ac5852e78 from=translated src=- shape=ed7f706e vocab=cc43d500
-/
@[simp]
theorem timedIterate_time (M : GroverModel) (k : ℕ) :
    (timedIterate M k).time = k := rfl

/-- Grover correctness, phrased through the TimeM return value.
@isnad1 id=eq.0h2v.s4.81d7f12f319a from=translated src=- shape=d56ce5a9 vocab=f9f3b8a1
-/
theorem timedIterate_correct (M : GroverModel) (k : ℕ) :
    (timedIterate M k).ret = amplitudeAmplificationState M.θ k := by
  exact GroverSearch.main M k

/-- The marked-subspace success probability after the timed Grover iterate.
@isnad1 id=eq.0h2v.s6.7d6fd3495d6a from=translated src=- shape=a5192b92 vocab=7f094dec
-/
theorem timedIterate_success_probability (M : GroverModel) (k : ℕ) :
    PureState.probOutcome (timedIterate M k).ret (1 : Fin (2 ^ 1)) =
      Real.sin (amplitudeAmplificationAngle M.θ k) ^ 2 := by
  rw [timedIterate_correct, amplitudeAmplificationState_good_probability]

/-- The timed Grover iterate has the same return value as its amplitude-amplification view.
@isnad1 id=eq.0h2v.s5.88ca3f1d97e6 from=translated src=- shape=051fc1a9 vocab=a70b20b6
-/
theorem timedIterate_ret_eq_amplitudeAmplification
    (M : GroverModel) (k : ℕ) :
    (timedIterate M k).ret =
      (AmplitudeAmplification.timedIterate
        M.toAmplitudeAmplificationModel k).ret := rfl

/-- Trusted public resource profile for `k` Grover iterations on `n` index
qubits: `k` oracle queries and a linear-in-`n` elementary-gate representative
per iterate. -/
def resourceProfile (n k : ℕ) : ResourceProfile where
  oracleQueries := k
  hadamardGates := 0
  elementaryGates := k * n
  classicalOps := 0

/--
@isnad1 id=hasexact.0h2v.s4.411d8490835e from=translated src=- shape=19fa900f vocab=d78f1bb3
-/
theorem resourceProfile_exact (n k : ℕ) :
    ResourceProfile.HasExactCounts (resourceProfile n k) k 0 (k * n) 0 := by
  simp [ResourceProfile.HasExactCounts, resourceProfile]

/-- Grover supporting theorem for the public marked-count statement. The
relation between the concrete `n`-qubit oracle and this good/bad plane remains
an explicit model hypothesis; under the marked-count angle relation, the timed
iterate has the public success probability and resource profile.
@isnad1 id=and.3h4v.s8.26fe5275ac5c from=translated src=- shape=ccd948ee vocab=554cc376
-/
theorem success_probability_with_resources
    (M : GroverModel) {n t k : ℕ}
    (_ht_pos : 0 < t) (_ht_le : t ≤ 2 ^ n)
    (hθ : M.θ = Real.arcsin (Real.sqrt ((t : ℝ) / ((2 ^ n : ℕ) : ℝ)))) :
    PureState.probOutcome (timedIterate M k).ret (1 : Fin (2 ^ 1)) =
        Real.sin (((2 : ℝ) * k + 1) *
          Real.arcsin (Real.sqrt ((t : ℝ) / ((2 ^ n : ℕ) : ℝ)))) ^ 2 ∧
      ResourceProfile.HasExactCounts (resourceProfile n k) k 0 (k * n) 0 := by
  constructor
  · rw [timedIterate_success_probability]
    simp [amplitudeAmplificationAngle, hθ]
  · exact resourceProfile_exact n k

end Grover

/-- Registered basis-action wrapper for the concrete Grover phase oracle.
@isnad1 id=eq.0h3v.s7.efa448931eb6 from=translated src=- shape=53452bd2 vocab=de30cb91
-/
theorem GroverSearch.main_phase_oracle_basis_action {n : ℕ}
    (marked : Fin (2 ^ n) → Bool) (j : Fin (2 ^ n)) :
    HilbertOperator.applyVec (phaseOracle marked) (ket j : StateVector n) =
      ((if marked j then -1 else 1 : ℂ) • (ket j : StateVector n)) := by
  exact phaseOracle_apply_ket marked j

/-- Registered resource wrapper for the marked-count Grover statement.
@isnad1 id=and.3h4v.s8.26fe5275ac5c from=translated src=- shape=ccd948ee vocab=554cc376
-/
theorem GroverSearch.main_success_probability_with_resources
    (M : GroverModel) {n t k : ℕ}
    (ht_pos : 0 < t) (ht_le : t ≤ 2 ^ n)
    (hθ : M.θ = Real.arcsin (Real.sqrt ((t : ℝ) / ((2 ^ n : ℕ) : ℝ)))) :
    PureState.probOutcome (Grover.timedIterate M k).ret (1 : Fin (2 ^ 1)) =
        Real.sin (((2 : ℝ) * k + 1) *
          Real.arcsin (Real.sqrt ((t : ℝ) / ((2 ^ n : ℕ) : ℝ)))) ^ 2 ∧
      ResourceProfile.HasExactCounts (Grover.resourceProfile n k) k 0 (k * n) 0 := by
  exact Grover.success_probability_with_resources M ht_pos ht_le hθ

end

end QuantumAlg
