/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Core.Components.Gates

/-!
# Controlled gates

`Gate.controlled U` is the `(1 + n)`-qubit gate that applies the `n`-qubit
gate `U` on the target register exactly when the control qubit is in `|1>`,
and does nothing when it is in `|0>` [CEMM98, cemm6.tex:127]. As a matrix it
is the block decomposition `c-U = |0><0| ⊗ 1 + |1><1| ⊗ U`.

The projectors `proj0` and `proj1` are `HilbertOperator`s, not gates.
-/

@[expose] public section

namespace QuantumAlg

namespace Gate

open PureState

noncomputable section

variable {n : ℕ}

/-- The one-qubit projector `|0><0| = [[1, 0], [0, 0]]`. -/
def proj0 : HilbertOperator 1 := !![(1 : ℂ), 0; 0, 0]

/-- The one-qubit projector `|1><1| = [[0, 0], [0, 1]]`. -/
def proj1 : HilbertOperator 1 := !![(0 : ℂ), 0; 0, 1]

/--
@isnad1 id=eq.0h0v.s6.2bfd648ca638 from=translated src=- shape=f1063a76 vocab=5273df61
-/
@[simp]
theorem proj0_conjTranspose : proj0.conjTranspose = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.conjTranspose_apply]

/--
@isnad1 id=eq.0h0v.s6.fbe08dfc5928 from=translated src=- shape=f1063a76 vocab=ec7e3002
-/
@[simp]
theorem proj1_conjTranspose : proj1.conjTranspose = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.conjTranspose_apply]

/--
@isnad1 id=eq.0h0v.s7.1e71d7744d58 from=translated src=- shape=f56f0670 vocab=e145e1d4
-/
theorem proj0_mul_proj0 : proj0 * proj0 = proj0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, Matrix.mul_apply]

/--
@isnad1 id=eq.0h0v.s8.cd63d4fa1648 from=translated src=- shape=a5831214 vocab=2e8accb1
-/
theorem proj0_mul_proj1 : proj0 * proj1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, proj1, Matrix.mul_apply]

/--
@isnad1 id=eq.0h0v.s8.b7fdaddbbec0 from=translated src=- shape=a5831214 vocab=2e8accb1
-/
theorem proj1_mul_proj0 : proj1 * proj0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj0, proj1, Matrix.mul_apply]

/--
@isnad1 id=eq.0h0v.s7.4b07e28e7d1a from=translated src=- shape=f56f0670 vocab=be3b7d97
-/
theorem proj1_mul_proj1 : proj1 * proj1 = proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [proj1, Matrix.mul_apply]

/--
@isnad1 id=eq.0h0v.s7.ffe0c383f4f1 from=translated src=- shape=3fff7b5d vocab=20544026
-/
theorem proj0_add_proj1 : proj0 + proj1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, Matrix.add_apply]

/--
@isnad1 id=eq.0h0v.s4.78655dedbfd8 from=translated src=- shape=294f98c8 vocab=df6e2483
-/
@[simp]
theorem proj0_applyVec_ket0 :
    HilbertOperator.applyVec proj0 (ket0 : StateVector 1) = (ket0 : StateVector 1) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [HilbertOperator.applyVec, proj0, ket0, PureState.ket]

/--
@isnad1 id=eq.0h0v.s7.18fdad742a42 from=translated src=- shape=bebbfd32 vocab=f5c273f6
-/
@[simp]
theorem proj0_applyVec_ket1 :
    HilbertOperator.applyVec proj0 (ket1 : StateVector 1) = 0 := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [HilbertOperator.applyVec, proj0, ket1, PureState.ket]

/--
@isnad1 id=eq.0h0v.s7.98e382ef2c24 from=translated src=- shape=bebbfd32 vocab=7e195ca7
-/
@[simp]
theorem proj1_applyVec_ket0 :
    HilbertOperator.applyVec proj1 (ket0 : StateVector 1) = 0 := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [HilbertOperator.applyVec, proj1, ket0, PureState.ket]

/--
@isnad1 id=eq.0h0v.s4.022fbdb2c735 from=translated src=- shape=294f98c8 vocab=10d6f9ac
-/
@[simp]
theorem proj1_applyVec_ket1 :
    HilbertOperator.applyVec proj1 (ket1 : StateVector 1) = (ket1 : StateVector 1) := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [HilbertOperator.applyVec, proj1, ket1, PureState.ket]

/-- Raw controlled-operator matrix. -/
def controlledOp (U : Gate n) : HilbertOperator (1 + n) :=
  HilbertOperator.tensor proj0 (1 : HilbertOperator n)
    + HilbertOperator.tensor proj1 (U : HilbertOperator n)

/-- The controlled gate `c-U`. -/
def controlled (U : Gate n) : Gate (1 + n) :=
  ofUnitary (controlledOp U) (by
    have hU : (U : HilbertOperator n) * (U : HilbertOperator n).conjTranspose = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.mp U.unitary
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    rw [controlledOp, Matrix.conjTranspose_add, HilbertOperator.conjTranspose_tensor,
      HilbertOperator.conjTranspose_tensor, proj0_conjTranspose, proj1_conjTranspose,
      Matrix.conjTranspose_one, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor,
      HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor, hU]
    simp only [Matrix.one_mul, Matrix.mul_one, proj0_mul_proj0, proj0_mul_proj1,
      proj1_mul_proj0, proj1_mul_proj1, HilbertOperator.zero_tensor,
      zero_add, add_zero]
    rw [← HilbertOperator.add_tensor, proj0_add_proj1, HilbertOperator.one_tensor_one])

/-- On the `|0>` control branch `c-U` does nothing.
@isnad1 id=eq.0h3v.s6.12aa2b94db73 from=translated src=- shape=c04ac205 vocab=ce8f214e
-/
@[simp]
theorem controlled_applyVec_ket0_tensor (U : Gate n) (psi : StateVector n) :
    HilbertOperator.applyVec (controlled U : HilbertOperator (1 + n))
        (StateVector.tensor (ket0 : StateVector 1) psi)
      = StateVector.tensor (ket0 : StateVector 1) psi := by
  apply WithLp.ofLp_injective
  funext i
  change HilbertOperator.applyVec (controlledOp U)
        (StateVector.tensor (ket0 : StateVector 1) psi) i
      = StateVector.tensor (ket0 : StateVector 1) psi i
  rw [controlledOp, HilbertOperator.add_applyVec, HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.tensor_applyVec_tensor, proj0_applyVec_ket0, proj1_applyVec_ket0,
    HilbertOperator.one_applyVec, StateVector.zero_tensor, PiLp.add_apply]
  simp

/-- On the `|1>` control branch `c-U` applies `U`.
@isnad1 id=eq.0h3v.s6.c9b98a83b996 from=translated src=- shape=a7466408 vocab=397997fc
-/
@[simp]
theorem controlled_applyVec_ket1_tensor (U : Gate n) (psi : StateVector n) :
    HilbertOperator.applyVec (controlled U : HilbertOperator (1 + n))
        (StateVector.tensor (ket1 : StateVector 1) psi)
      = StateVector.tensor (ket1 : StateVector 1) (U.applyVec psi) := by
  apply WithLp.ofLp_injective
  funext i
  change HilbertOperator.applyVec (controlledOp U)
        (StateVector.tensor (ket1 : StateVector 1) psi) i
      = StateVector.tensor (ket1 : StateVector 1)
        (HilbertOperator.applyVec (U : HilbertOperator n) psi) i
  rw [controlledOp, HilbertOperator.add_applyVec, HilbertOperator.tensor_applyVec_tensor,
    HilbertOperator.tensor_applyVec_tensor, proj0_applyVec_ket1, proj1_applyVec_ket1,
    StateVector.zero_tensor, PiLp.add_apply]
  simp

/-- On the `|0>` control branch `c-U` does nothing.
@isnad1 id=eq.0h3v.s5.3fb51cd57f4d from=translated src=- shape=b90e0f39 vocab=eba1f662
-/
@[simp]
theorem controlled_apply_ket0_tensor (U : Gate n) (psi : PureState n) :
    (controlled U).apply (ket0.tensor psi) = ket0.tensor psi := by
  ext i
  change HilbertOperator.applyVec (controlled U : HilbertOperator (1 + n))
        (StateVector.tensor (ket0 : StateVector 1) (psi : StateVector n)) i
      = StateVector.tensor (ket0 : StateVector 1) (psi : StateVector n) i
  rw [controlled_applyVec_ket0_tensor]

/-- On the `|1>` control branch `c-U` applies `U`.
@isnad1 id=eq.0h3v.s5.cde4ff0469cb from=translated src=- shape=1213dcd5 vocab=f7265ce1
-/
@[simp]
theorem controlled_apply_ket1_tensor (U : Gate n) (psi : PureState n) :
    (controlled U).apply (ket1.tensor psi) = ket1.tensor (U.apply psi) := by
  ext i
  change HilbertOperator.applyVec (controlled U : HilbertOperator (1 + n))
        (StateVector.tensor (ket1 : StateVector 1) (psi : StateVector n)) i
      = StateVector.tensor (ket1 : StateVector 1)
        (U.applyVec (psi : StateVector n)) i
  rw [controlled_applyVec_ket1_tensor]

/-- `c-U` is unitary.
@isnad1 id=mem.1h2v.s10.b2deee27a011 from=translated src=- shape=d572216d vocab=ff19c211
-/
theorem controlled_mem_unitaryGroup {U : Gate n}
    (_hU : (U : HilbertOperator n) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    (controlled U : HilbertOperator (1 + n))
      ∈ Matrix.unitaryGroup (Fin (2 ^ (1 + n))) ℂ :=
  (controlled U).unitary

/-- Sanity check: the controlled Pauli-X gate is exactly `CNOT`.
@isnad1 id=eq.0h0v.s4.65e3b7da778e from=translated src=- shape=d0b0bf6f vocab=3abc692c
-/
theorem controlled_X : controlled X = CNOT := by
  have hX : ∀ i j : Fin (2 ^ 1), (X : HilbertOperator 1) i j
      = if i = Equiv.swap 0 1 j then 1 else 0 := by
    intro i j
    rw [← apply_ket X j i, X, ofPerm_apply_ket, Equiv.swap_inv, PureState.ket_apply]
  have hC : ∀ i j : Fin (2 ^ 2), CNOT i j
      = if i = Equiv.swap 2 3 j then 1 else 0 := by
    intro i j
    rw [← apply_ket CNOT j i, CNOT_apply_ket, PureState.ket_apply]
  ext i j
  change controlledOp X i j = CNOT i j
  rw [hC]
  fin_cases i <;> fin_cases j <;>
    simp +decide [controlledOp, HilbertOperator.tensor_apply, proj0, proj1,
      hX, Matrix.one_apply, prodEquiv, finProdFinEquiv, finCongr,
      Fin.divNat, Fin.modNat]

end

end Gate

end QuantumAlg
