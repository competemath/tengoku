/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Primitives.HadamardTest

/-!
# The SWAP test

The SWAP test estimates the overlap `|<psi|phi>|^2` of two `n`-qubit states:
run the Hadamard test with the unitary that swaps the two registers
[BCWdW01, main.tex:291]. Measuring the control yields outcome `1` with
probability `(1 - |<psi|phi>|^2)/2` [BCWdW01, main.tex:328].
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

variable {n : ℕ}

/-- The permutation of joint basis labels that exchanges two `n`-qubit registers. -/
def swapRegistersPerm (n : ℕ) : Equiv.Perm (Fin (2 ^ (n + n))) :=
  ((prodEquiv (m := n) (n := n)).symm.trans
    (Equiv.prodComm (Fin (2 ^ n)) (Fin (2 ^ n)))).trans prodEquiv

/-- The register-swap gate `SWAP : Gate (n + n)`. -/
def swapRegisters (n : ℕ) : Gate (n + n) := ofPerm (swapRegistersPerm n)

/--
@isnad1 id=mem.0h1v.s9.06077c37e2c9 from=translated src=- shape=a2356ab6 vocab=eb090132
-/
theorem swapRegisters_mem_unitaryGroup (n : ℕ) :
    (swapRegisters n : HilbertOperator (n + n))
      ∈ Matrix.unitaryGroup (Fin (2 ^ (n + n))) ℂ :=
  (swapRegisters n).unitary

/-- The register swap exchanges tensor factors.
@isnad1 id=eq.0h3v.s5.8b5ea7b6adb8 from=translated src=- shape=27dc3e5a vocab=90a8bcbf
-/
theorem swapRegisters_apply_tensor (psi phi : PureState n) :
    (swapRegisters n).apply (psi.tensor phi) = phi.tensor psi := by
  ext i
  rw [swapRegisters, ofPerm_apply, PureState.tensor_apply,
    PureState.tensor_apply, swapRegistersPerm]
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Equiv.symm_apply_apply,
    Prod.fst_swap, Prod.snd_swap]
  exact mul_comm _ _

/-- The SWAP test circuit: the Hadamard test of the register swap. -/
def swapTest (n : ℕ) : Gate (1 + (n + n)) :=
  hadamardTest (swapRegisters n)

/-- `Re <psi ⊗ phi, SWAP (psi ⊗ phi)> = |<psi|phi>|^2`.
@isnad1 id=eq.0h3v.s6.53354da222ad from=translated src=- shape=6a8cc5ac vocab=def079d0
-/
theorem re_inner_swapRegisters (psi phi : PureState n) :
    (inner ℂ (psi.tensor phi) ((swapRegisters n).apply (psi.tensor phi))).re
      = ‖inner ℂ psi phi‖ ^ 2 := by
  change (inner ℂ ((psi.tensor phi : PureState (n + n)) : StateVector (n + n))
      (((swapRegisters n).apply (psi.tensor phi) : PureState (n + n))
        : StateVector (n + n))).re
    = ‖inner ℂ (psi : StateVector n) (phi : StateVector n)‖ ^ 2
  rw [swapRegisters_apply_tensor]
  change (inner ℂ
      (StateVector.tensor (psi : StateVector n) (phi : StateVector n))
      (StateVector.tensor (phi : StateVector n) (psi : StateVector n))).re
    = ‖inner ℂ (psi : StateVector n) (phi : StateVector n)‖ ^ 2
  rw [StateVector.inner_tensor_tensor,
    ← inner_conj_symm (phi : StateVector n) (psi : StateVector n),
    Complex.mul_conj', ← Complex.ofReal_pow,
    Complex.ofReal_re]

/-- **SWAP test, outcome 0** [BCWdW01, main.tex:328].
@isnad1 id=eq.0h3v.s7.15fa10a2253d from=translated src=- shape=37ca9a0a vocab=1f1d078d
-/
theorem swapTest_probQubit0_zero (psi phi : PureState n) :
    probQubit0 ((swapTest n).apply (ket0.tensor (psi.tensor phi))) 0
      = (1 + ‖inner ℂ psi phi‖ ^ 2) / 2 := by
  rw [swapTest, HadamardTest.main, re_inner_swapRegisters]

/-- **SWAP test, outcome 1** [BCWdW01, main.tex:328].
@isnad1 id=eq.0h3v.s7.3298c2cf9a31 from=translated src=- shape=97011bed vocab=0463e45b
-/
theorem SwapTest.main (psi phi : PureState n) :
    probQubit0 ((swapTest n).apply (ket0.tensor (psi.tensor phi))) 1
      = (1 - ‖inner ℂ psi phi‖ ^ 2) / 2 := by
  rw [swapTest, hadamardTest_probQubit0_one, re_inner_swapRegisters]

end

end QuantumAlg
