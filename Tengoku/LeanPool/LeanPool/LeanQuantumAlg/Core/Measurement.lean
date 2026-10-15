/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Core.Gate
public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Util.FinPow

/-!
# Computational-basis measurement

Born rule for the computational-basis PVM `{|x><x|}` [dW19,
qcnotes.tex:406]: measuring a state vector `psi` yields outcome `x` with
probability `|psi x|^2`. For a `1 + n`-qubit register we also provide the
marginal probability of observing the first qubit, given by the projective
measurement `{|b><b| ⊗ I}` whose outcome probability is the squared norm of the
projected block [dW19, qcnotes.tex:433].

The raw `StateVector` definitions are available for algebraic intermediate
states. The `PureState` wrappers automatically form probability distributions,
because normalization is part of `PureState`.
-/

@[expose] public section

namespace QuantumAlg

namespace StateVector

section

variable {n : ℕ}

/-- Born rule [dW19, qcnotes.tex:406]: the probability of observing outcome `x`
when measuring `psi` in the computational basis. -/
noncomputable def probOutcome (psi : StateVector n) (x : Fin (2 ^ n)) : ℝ :=
  ‖psi x‖ ^ 2

/--
@isnad1 id=le.0h3v.s5.c11cf2a47e9a from=translated src=- shape=da5df60c vocab=334f521c
-/
theorem probOutcome_nonneg (psi : StateVector n) (x : Fin (2 ^ n)) :
    0 ≤ probOutcome psi x :=
  sq_nonneg _

/-- The Born-rule weights sum to the squared norm.
@isnad1 id=eq.0h2v.s7.f5b9896f38cc from=translated src=- shape=16c42bd6 vocab=57ffd941
-/
theorem sum_probOutcome (psi : StateVector n) :
    ∑ x, probOutcome psi x = ‖psi‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖psi i‖)]
  rfl

/--
@isnad1 id=eq.0h3v.s6.d43c67ace4f2 from=translated src=- shape=7cad6324 vocab=fb76635b
-/
@[simp]
theorem probOutcome_ket (x y : Fin (2 ^ n)) :
    probOutcome (PureState.ket x : StateVector n) y = if y = x then 1 else 0 := by
  rw [probOutcome, PureState.ket_apply]
  by_cases h : y = x
  · simp_all
  · simp_all

/-- Probability that measuring qubit 0 of a `1 + n`-qubit raw state vector
yields `b`, leaving the other qubits unobserved. -/
noncomputable def probQubit0 (psi : StateVector (1 + n)) (b : Fin (2 ^ 1)) : ℝ :=
  ∑ y : Fin (2 ^ n), ‖psi (prodEquiv (b, y))‖ ^ 2

/--
@isnad1 id=le.0h3v.s5.10ad54c0b90c from=translated src=- shape=bd5b1cea vocab=1187aa43
-/
theorem probQubit0_nonneg (psi : StateVector (1 + n)) (b : Fin (2 ^ 1)) :
    0 ≤ probQubit0 psi b :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Scaling a raw state vector scales the marginal probability by the squared
scalar norm.
@isnad1 id=eq.0h4v.s7.4abdf7df00cb from=translated src=- shape=d3167bb0 vocab=2892e83c
-/
theorem probQubit0_smul (c : ℂ) (psi : StateVector (1 + n)) (b : Fin (2 ^ 1)) :
    probQubit0 (c • psi) b = ‖c‖ ^ 2 * probQubit0 psi b := by
  rw [probQubit0, probQubit0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PiLp.smul_apply, smul_eq_mul, norm_mul, mul_pow]

end

end StateVector

namespace PureState

noncomputable section

variable {n : ℕ}

/-- Born-rule probability for a pure state. -/
def probOutcome (psi : PureState n) (x : Fin (2 ^ n)) : ℝ :=
  StateVector.probOutcome (psi : StateVector n) x

/--
@isnad1 id=eq.0h3v.s6.56205a247576 from=translated src=- shape=820e1148 vocab=6b61dcf5
-/
@[simp]
theorem probOutcome_ket (x y : Fin (2 ^ n)) :
    probOutcome (ket x) y = if y = x then 1 else 0 :=
  StateVector.probOutcome_ket x y

/-- Expectation value `<psi|O|psi>` of an observable `O`, represented as a real
number via the real part. Hermiticity is a property of the observable, not part
of the raw `HilbertOperator` type. -/
def expVal (psi : PureState n) (O : HilbertOperator n) : ℝ :=
  (inner ℂ (psi : StateVector n) (HilbertOperator.applyVec O (psi : StateVector n))).re

/-- Probability that measuring qubit 0 of a `1 + n`-qubit pure state yields
`b`, leaving the other qubits unobserved. -/
def probQubit0 (psi : PureState (1 + n)) (b : Fin (2 ^ 1)) : ℝ :=
  StateVector.probQubit0 (psi : StateVector (1 + n)) b

end

end PureState

end QuantumAlg
