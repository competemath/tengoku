/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Core.Gate
public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Util.FinPow

/-!
# Tensor products of vectors, states, operators, and gates

Raw tensor products are defined at the `StateVector` and `HilbertOperator`
layers. `PureState.tensor` and `Gate.tensor` wrap these raw tensors with the
normalization/unitarity proofs needed to stay in their semantic types.
-/

@[expose] public section

namespace QuantumAlg

open Kronecker

variable {m n : ℕ}

namespace StateVector

section

/-- Tensor product of raw Hilbert-space vectors. -/
noncomputable def tensor (ψ : StateVector m) (φ : StateVector n) : StateVector (m + n) :=
  WithLp.toLp 2 fun i => ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2

/--
@isnad1 id=eq.0h5v.s11.bdbc6ff9f64d from=translated src=- shape=131b4fca vocab=7d4fa3c8
-/
@[simp]
theorem tensor_apply (ψ : StateVector m) (φ : StateVector n)
    (i : Fin (2 ^ (m + n))) :
    tensor ψ φ i = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2 :=
  rfl

/--
@isnad1 id=eq.0h6v.s10.ecaca7100269 from=translated src=- shape=113c4325 vocab=bc433f9e
-/
theorem tensor_apply_prod (ψ : StateVector m) (φ : StateVector n)
    (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    tensor ψ φ (prodEquiv (x, y)) = ψ x * φ y := by
  rw [tensor_apply, Equiv.symm_apply_apply]

/--
@isnad1 id=eq.0h5v.s8.db7bb7c544e8 from=translated src=- shape=e2c9ba8c vocab=f65a945f
-/
@[simp]
theorem add_tensor (ψ ψ' : StateVector m) (φ : StateVector n) :
    tensor (ψ + ψ') φ = tensor ψ φ + tensor ψ' φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (ψ + ψ') φ i = (tensor ψ φ + tensor ψ' φ) i
  simp [add_mul]

/--
@isnad1 id=eq.0h5v.s8.97adeadaf021 from=translated src=- shape=de2805cd vocab=3e88297e
-/
@[simp]
theorem sub_tensor (ψ ψ' : StateVector m) (φ : StateVector n) :
    tensor (ψ - ψ') φ = tensor ψ φ - tensor ψ' φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (ψ - ψ') φ i = (tensor ψ φ - tensor ψ' φ) i
  simp [sub_mul]

/--
@isnad1 id=eq.0h5v.s8.822e285aa08e from=translated src=- shape=f3387346 vocab=d1b10c27
-/
@[simp]
theorem smul_tensor (c : ℂ) (ψ : StateVector m) (φ : StateVector n) :
    tensor (c • ψ) φ = c • tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor (c • ψ) φ i = (c • tensor ψ φ) i
  simp [mul_assoc]

/--
@isnad1 id=eq.0h5v.s8.7e13b6c4218f from=translated src=- shape=b9df018d vocab=f65a945f
-/
@[simp]
theorem tensor_add (ψ : StateVector m) (φ φ' : StateVector n) :
    tensor ψ (φ + φ') = tensor ψ φ + tensor ψ φ' := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (φ + φ') i = (tensor ψ φ + tensor ψ φ') i
  simp [mul_add]

/--
@isnad1 id=eq.0h5v.s8.53bdac80e4eb from=translated src=- shape=6c5452e5 vocab=3e88297e
-/
@[simp]
theorem tensor_sub (ψ : StateVector m) (φ φ' : StateVector n) :
    tensor ψ (φ - φ') = tensor ψ φ - tensor ψ φ' := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (φ - φ') i = (tensor ψ φ - tensor ψ φ') i
  simp [mul_sub]

/--
@isnad1 id=eq.0h5v.s8.7952323d1ff1 from=translated src=- shape=3ce3d6e8 vocab=d1b10c27
-/
@[simp]
theorem tensor_smul (c : ℂ) (ψ : StateVector m) (φ : StateVector n) :
    tensor ψ (c • φ) = c • tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  change tensor ψ (c • φ) i = (c • tensor ψ φ) i
  simp [mul_left_comm]

/--
@isnad1 id=eq.0h4v.s8.d7a20d29dd50 from=translated src=- shape=0e45e110 vocab=b7966f81
-/
@[simp]
theorem neg_tensor (ψ : StateVector m) (φ : StateVector n) :
    tensor (-ψ) φ = -tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  simp_all

/--
@isnad1 id=eq.0h4v.s8.59e3a6a64fea from=translated src=- shape=56f0c68d vocab=b7966f81
-/
@[simp]
theorem tensor_neg (ψ : StateVector m) (φ : StateVector n) :
    tensor ψ (-φ) = -tensor ψ φ := by
  apply WithLp.ofLp_injective
  funext i
  simp_all

/--
@isnad1 id=eq.0h3v.s8.c7ad81739209 from=translated src=- shape=5cb894db vocab=f65a945f
-/
@[simp]
theorem zero_tensor (φ : StateVector n) :
    tensor (0 : StateVector m) φ = 0 := by
  apply WithLp.ofLp_injective
  funext i
  simp_all

/--
@isnad1 id=eq.0h3v.s8.f0bc41bec9a1 from=translated src=- shape=ef74edb5 vocab=f65a945f
-/
@[simp]
theorem tensor_zero (ψ : StateVector m) :
    tensor ψ (0 : StateVector n) = 0 := by
  apply WithLp.ofLp_injective
  funext i
  simp_all

/-- The norm is multiplicative under tensor products.
@isnad1 id=eq.0h4v.s8.ae0da7eb5575 from=translated src=- shape=de7a4f21 vocab=1799b965
-/
theorem norm_tensor (ψ : StateVector m) (φ : StateVector n) :
    ‖tensor ψ φ‖ = ‖ψ‖ * ‖φ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (show (0 : ℝ) ≤ ∑ i, ‖ψ i‖ ^ 2 from
      Finset.sum_nonneg fun i _ => sq_nonneg ‖ψ i‖)]
  congr 1
  rw [← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun i => ‖tensor ψ φ i‖ ^ 2),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, Equiv.symm_apply_apply, norm_mul, mul_pow]

/-- The inner product factors over tensor products.
@isnad1 id=eq.0h6v.s12.5c4dc1b599fb from=translated src=- shape=ce9de8c9 vocab=3954a330
-/
theorem inner_tensor_tensor (ψ ψ' : StateVector m) (φ φ' : StateVector n) :
    inner ℂ (tensor ψ φ) (tensor ψ' φ')
      = inner ℂ ψ ψ' * inner ℂ φ φ' := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun i => tensor ψ' φ' i * starRingEnd ℂ (tensor ψ φ i)),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, tensor_apply, Equiv.symm_apply_apply, map_mul,
    mul_mul_mul_comm]

end

end StateVector

namespace PureState

section

/-- Tensor product of pure states. -/
noncomputable def tensor (ψ : PureState m) (φ : PureState n) : PureState (m + n) :=
  ofVec (StateVector.tensor (ψ : StateVector m) (φ : StateVector n)) (by
    rw [StateVector.norm_tensor, ψ.norm_eq_one, φ.norm_eq_one, one_mul])

/--
@isnad1 id=eq.0h5v.s11.1c3cf0470503 from=translated src=- shape=52f5b1dd vocab=4f2591f0
-/
@[simp]
theorem tensor_apply (ψ : PureState m) (φ : PureState n)
    (i : Fin (2 ^ (m + n))) :
    ψ.tensor φ i = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2 := by
  change StateVector.tensor (ψ : StateVector m) (φ : StateVector n) i
      = ψ (prodEquiv.symm i).1 * φ (prodEquiv.symm i).2
  rfl

/--
@isnad1 id=eq.0h6v.s10.b683df80d922 from=translated src=- shape=6261efab vocab=8a0ab8f1
-/
theorem tensor_apply_prod (ψ : PureState m) (φ : PureState n)
    (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    ψ.tensor φ (prodEquiv (x, y)) = ψ x * φ y := by
  rw [tensor_apply, Equiv.symm_apply_apply]

-- Compatibility names for linear raw-vector tensor proofs.

/-- Basis kets tensor to basis kets: `|x⟩ ⊗ |y⟩ = |xy⟩`.
@isnad1 id=eq.0h4v.s8.9cf5966ccdf0 from=translated src=- shape=a35f91e0 vocab=7bac0a94
-/
theorem tensor_ket (x : Fin (2 ^ m)) (y : Fin (2 ^ n)) :
    (ket x).tensor (ket y) = ket (prodEquiv (x, y)) := by
  ext i
  rw [tensor_apply, ket_apply, ket_apply, ket_apply]
  by_cases h : i = prodEquiv (x, y)
  · simp_all
  · have h' : ¬((prodEquiv.symm i).1 = x ∧ (prodEquiv.symm i).2 = y) := by
      rintro ⟨h1, h2⟩
      exact h (by
        rw [← Equiv.apply_symm_apply (prodEquiv (m := m) (n := n)) i]
        exact congrArg prodEquiv (Prod.ext h1 h2))
    rw [ite_eq_right h]
    rcases not_and_or.mp h' with h1 | h2
    · rw [ite_eq_right h1, zero_mul]
    · rw [ite_eq_right h2, mul_zero]

end

end PureState

namespace HilbertOperator

section

/-- Tensor product of Hilbert-space operators. -/
noncomputable def tensor
    (G : HilbertOperator m) (K : HilbertOperator n) : HilbertOperator (m + n) :=
  Matrix.reindex prodEquiv prodEquiv (G ⊗ₖ K)

/--
@isnad1 id=eq.0h6v.s10.627210cf3319 from=translated src=- shape=2100111e vocab=b7ff966a
-/
@[simp]
theorem tensor_apply (G : HilbertOperator m) (K : HilbertOperator n)
    (i j : Fin (2 ^ (m + n))) :
    tensor G K i j
      = G (prodEquiv.symm i).1 (prodEquiv.symm j).1
        * K (prodEquiv.symm i).2 (prodEquiv.symm j).2 := rfl

/--
@isnad1 id=eq.0h3v.s7.0aeefe00cf1d from=translated src=- shape=5cb894db vocab=18740036
-/
@[simp]
theorem zero_tensor (K : HilbertOperator n) :
    tensor (0 : HilbertOperator m) K = 0 := by
  ext i j
  simp [tensor_apply]

/--
@isnad1 id=eq.0h3v.s7.d3d59342bd4f from=translated src=- shape=ef74edb5 vocab=18740036
-/
@[simp]
theorem tensor_zero (G : HilbertOperator m) :
    tensor G (0 : HilbertOperator n) = 0 := by
  ext i j
  simp [tensor_apply]

/--
@isnad1 id=eq.0h5v.s7.7b15d4605ef2 from=translated src=- shape=e2c9ba8c vocab=18740036
-/
theorem add_tensor (G G' : HilbertOperator m) (K : HilbertOperator n) :
    tensor (G + G') K = tensor G K + tensor G' K := by
  ext i j
  simp [tensor_apply, add_mul]

/--
@isnad1 id=eq.0h6v.s9.a099fdc06cf1 from=translated src=- shape=5807314c vocab=561955c5
-/
theorem tensor_mul_tensor (G G' : HilbertOperator m) (K K' : HilbertOperator n) :
    tensor G K * tensor G' K' = tensor (G * G') (K * K') := by
  rw [tensor, tensor, tensor, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul]

/--
@isnad1 id=eq.0h4v.s8.ded13364a6ec from=translated src=- shape=8950abc2 vocab=890a8bd7
-/
theorem conjTranspose_tensor (G : HilbertOperator m) (K : HilbertOperator n) :
    (tensor G K).conjTranspose = tensor G.conjTranspose K.conjTranspose := by
  rw [tensor, tensor, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]

/--
@isnad1 id=eq.0h2v.s7.92c83fe3767d from=translated src=- shape=06e2a3ff vocab=18740036
-/
@[simp]
theorem one_tensor_one : tensor (1 : HilbertOperator m) (1 : HilbertOperator n) = 1 := by
  rw [tensor, Matrix.one_kronecker_one, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv]

/--
@isnad1 id=mem.2h4v.s11.f0b7edf6186e from=translated src=- shape=05afa5bf vocab=a0843674
-/
theorem tensor_mem_unitaryGroup {G : HilbertOperator m} {K : HilbertOperator n}
    (hG : G ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ)
    (hK : K ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    tensor G K ∈ Matrix.unitaryGroup (Fin (2 ^ (m + n))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hG hK ⊢
  rw [tensor, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_kronecker, Matrix.submatrix_mul_equiv,
    ← Matrix.mul_kronecker_mul, hG, hK, Matrix.one_kronecker_one,
    Matrix.submatrix_one_equiv]

/--
@isnad1 id=eq.0h6v.s5.bc6e917ae59f from=translated src=- shape=8a3401d3 vocab=7ad0ac6c
-/
theorem tensor_applyVec_tensor (G : HilbertOperator m) (K : HilbertOperator n)
    (ψ : StateVector m) (φ : StateVector n) :
    applyVec (tensor G K) (StateVector.tensor ψ φ)
      = StateVector.tensor (applyVec G ψ) (applyVec K φ) := by
  apply WithLp.ofLp_injective
  funext i
  change applyVec (tensor G K) (StateVector.tensor ψ φ) i
      = StateVector.tensor (applyVec G ψ) (applyVec K φ) i
  rw [StateVector.tensor_apply, applyVec_apply, applyVec_apply, applyVec_apply,
    Finset.sum_mul_sum,
    ← Equiv.sum_comp (prodEquiv (m := m) (n := n))
      (fun j => tensor G K i j * StateVector.tensor ψ φ j),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [tensor_apply, StateVector.tensor_apply, Equiv.symm_apply_apply,
    mul_mul_mul_comm]

end

end HilbertOperator

namespace Gate

noncomputable section

/-- Tensor product of unitary gates. -/
def tensor (G : Gate m) (K : Gate n) : Gate (m + n) :=
  ofUnitary (HilbertOperator.tensor (G : HilbertOperator m) (K : HilbertOperator n))
    (HilbertOperator.tensor_mem_unitaryGroup G.unitary K.unitary)

/--
@isnad1 id=eq.0h6v.s10.23386c4f4aee from=translated src=- shape=3fc13306 vocab=9032b89f
-/
@[simp]
theorem tensor_apply (G : Gate m) (K : Gate n)
    (i j : Fin (2 ^ (m + n))) :
    G.tensor K i j
      = G (prodEquiv.symm i).1 (prodEquiv.symm j).1
        * K (prodEquiv.symm i).2 (prodEquiv.symm j).2 := rfl

/--
@isnad1 id=eq.0h2v.s6.8a68341f8a36 from=translated src=- shape=06e2a3ff vocab=2d63ec6e
-/
@[simp]
theorem one_tensor_one : (1 : Gate m).tensor (1 : Gate n) = 1 := by
  ext i j
  change HilbertOperator.tensor (1 : HilbertOperator m) (1 : HilbertOperator n) i j
      = (1 : HilbertOperator (m + n)) i j
  rw [HilbertOperator.one_tensor_one]

/--
@isnad1 id=eq.0h6v.s5.d362a876635b from=translated src=- shape=8a3401d3 vocab=5c453ed5
-/
theorem tensor_apply_tensor (G : Gate m) (K : Gate n)
    (ψ : PureState m) (φ : PureState n) :
    (G.tensor K).apply (ψ.tensor φ) = (G.apply ψ).tensor (K.apply φ) := by
  ext i
  change HilbertOperator.applyVec
      (HilbertOperator.tensor (G : HilbertOperator m) (K : HilbertOperator n))
      (StateVector.tensor (ψ : StateVector m) (φ : StateVector n)) i
    = StateVector.tensor
      (HilbertOperator.applyVec (G : HilbertOperator m) (ψ : StateVector m))
      (HilbertOperator.applyVec (K : HilbertOperator n) (φ : StateVector n)) i
  rw [HilbertOperator.tensor_applyVec_tensor]

/--
@isnad1 id=eq.0h6v.s5.7255f7d0a0bd from=translated src=- shape=8a3401d3 vocab=9b62ac63
-/
theorem tensor_applyVec_tensor (G : Gate m) (K : Gate n)
    (ψ : StateVector m) (φ : StateVector n) :
    (G.tensor K).applyVec (StateVector.tensor ψ φ)
      = StateVector.tensor (G.applyVec ψ) (K.applyVec φ) := by
  exact HilbertOperator.tensor_applyVec_tensor (G : HilbertOperator m)
    (K : HilbertOperator n) ψ φ

end

end Gate

end QuantumAlg
