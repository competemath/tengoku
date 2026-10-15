/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Core.Components.Oracle
public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Core.Components.Kets

/-!
# Walsh-Hadamard transform and the XOR phase-query pipeline

The reusable machinery shared by the single-query Hadamard-oracle-Hadamard
algorithms (Deutsch-Jozsa, Bernstein-Vazirani): the `n`-qubit Hadamard layer
in Walsh-Hadamard closed form [dW19, qcnotes.tex:1005-1006], and the
XOR-oracle phase-query pipeline that runs a Boolean oracle on the uniform
input register with a `|−⟩` target.

The central bridge `postOracleState_eq_afterPhaseQuery_tensor` rewrites the
actual XOR-oracle query as the phase pattern `(√(2^n))⁻¹ ∑ x (-1)^{f x}|x⟩`
tensored with the unchanged `|−⟩` target, so a single query followed by the
second Hadamard layer (`finalJointState`) factors through the input-register
`finalState`.

These pieces sit in a `Primitives` module so the Deutsch-Jozsa and
Bernstein-Vazirani algorithms can both build on them without importing one
another; each algorithm keeps only its target-specific content (the
constant/balanced promise and amplitude test for Deutsch-Jozsa; Walsh-character
orthogonality and string recovery for Bernstein-Vazirani).

## Main definitions

- `LeanPool.LeanQuantumAlg.WalshHadamard.Oracle n` — a Boolean function on `2^n` labels,
  queried through `Gate.xorOracle`.
- `LeanPool.LeanQuantumAlg.WalshHadamard.walshSign` — the Walsh-Hadamard sign `(-1)^{x·y}`,
  and `hadamardLayer` its closed-form `n`-qubit gate.
- `LeanPool.LeanQuantumAlg.WalshHadamard.uniformState` — the uniform superposition.
- `LeanPool.LeanQuantumAlg.WalshHadamard.finalJointState` — the post-circuit joint state,
  with `finalJointState_eq_finalState_tensor` factoring off the `|−⟩` target.
-/

@[expose] public section

namespace QuantumAlg

namespace WalshHadamard

open PureState Gate

noncomputable section

variable {n : ℕ}

/-- A Boolean oracle on `2^n` input labels. It is queried through
`Gate.xorOracle`, not through a separate oracle type. -/
abbrev Oracle (n : ℕ) : Type := Fin (2 ^ n) → Bool

/-- The standard XOR query gate for a Boolean oracle. -/
abbrev oracleGate (f : Oracle n) : Gate (n + 1) := Gate.xorOracle f

/-- The phase `(-1)^{f x}`, written as a complex scalar. -/
def phaseSign (f : Oracle n) (x : Fin (2 ^ n)) : ℂ :=
  if f x then -1 else 1

/-! ### The Walsh-Hadamard transform -/

/-- The bit of a basis label used in the Walsh-Hadamard character. The bit
order only affects nonzero rows; the zero row used by Deutsch-Jozsa is
independent of it. -/
def bit (x : Fin (2 ^ n)) (k : Fin n) : Bool := x.val.testBit k.val

/-- Parity of the bitwise inner product of two basis labels. -/
def dotParity (x y : Fin (2 ^ n)) : Bool :=
  Odd ((Finset.univ.filter fun k : Fin n => bit x k && bit y k).card)

/-- The Walsh-Hadamard sign `(-1)^{x · y}`. -/
def walshSign (x y : Fin (2 ^ n)) : ℂ := if dotParity x y then -1 else 1

/-- `(√(2^n))⁻¹`, the normalization scalar of the `n`-qubit Hadamard layer. -/
def invSqrtCard (n : ℕ) : ℂ := (Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ)⁻¹

/--
@isnad1 id=eq.0h1v.s5.299a539fa9c1 from=translated src=- shape=0a9af14d vocab=3813e922
-/
@[simp]
theorem star_invSqrtCard (n : ℕ) : star (invSqrtCard n) = invSqrtCard n := by
  rw [invSqrtCard, star_inv₀, Complex.star_def, Complex.conj_ofReal]

/--
@isnad1 id=eq.0h1v.s5.09b6c971fdaf from=translated src=- shape=44743426 vocab=caac3ad9
-/
@[simp]
theorem norm_invSqrtCard (n : ℕ) :
    ‖invSqrtCard n‖ = (Real.sqrt ((2 ^ n : ℕ) : ℝ))⁻¹ := by
  rw [invSqrtCard, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/--
@isnad1 id=eq.0h1v.s5.33f9f6a2490d from=translated src=- shape=b93d0e5f vocab=f55ebd67
-/
theorem norm_sq_invSqrtCard (n : ℕ) :
    ‖invSqrtCard n‖ ^ 2 = (((2 ^ n : ℕ) : ℝ)⁻¹) := by
  rw [norm_invSqrtCard, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))]

/--
@isnad1 id=eq.0h2v.s6.a91209668ed4 from=translated src=- shape=bfffb9a5 vocab=1dbffb71
-/
@[simp]
theorem walshSign_zero_left (x : Fin (2 ^ n)) :
    walshSign (0 : Fin (2 ^ n)) x = 1 := by
  unfold walshSign dotParity bit
  simp

/--
@isnad1 id=eq.0h2v.s6.c334f5ffc111 from=translated src=- shape=f3b25266 vocab=1dbffb71
-/
@[simp]
theorem walshSign_zero_right (x : Fin (2 ^ n)) :
    walshSign x (0 : Fin (2 ^ n)) = 1 := by
  unfold walshSign dotParity bit
  simp

/--
@isnad1 id=eq.0h3v.s5.a328cce087db from=translated src=- shape=b87f2eb2 vocab=bca3c068
-/
theorem dotParity_comm (x y : Fin (2 ^ n)) : dotParity x y = dotParity y x := by
  have hset : (Finset.univ.filter fun k : Fin n => bit x k && bit y k)
      = Finset.univ.filter fun k : Fin n => bit y k && bit x k := by
    apply Finset.filter_congr
    intro k _
    rw [Bool.and_comm]
  unfold dotParity
  rw [hset]

/--
@isnad1 id=eq.0h3v.s5.6a3c9ce655cf from=translated src=- shape=b87f2eb2 vocab=1dbffb71
-/
theorem walshSign_comm (x y : Fin (2 ^ n)) : walshSign x y = walshSign y x := by
  unfold walshSign
  rw [dotParity_comm]

/--
@isnad1 id=eq.0h3v.s6.91fd66ba024e from=translated src=- shape=86276452 vocab=edabde8f
-/
@[simp]
theorem walshSign_mul_self (x y : Fin (2 ^ n)) :
    walshSign x y * walshSign x y = 1 := by
  unfold walshSign
  by_cases h : dotParity x y <;> simp [h]

/--
@isnad1 id=eq.0h3v.s6.da6fb7e74e96 from=translated src=- shape=76ca4387 vocab=ec02c623
-/
@[simp]
theorem star_walshSign (x y : Fin (2 ^ n)) :
    star (walshSign x y) = walshSign x y := by
  unfold walshSign
  by_cases h : dotParity x y <;> simp [h]

/--
@isnad1 id=eq.0h3v.s5.5b6768c94f06 from=translated src=- shape=9fb389ca vocab=068a3d2e
-/
@[simp]
theorem norm_walshSign (x y : Fin (2 ^ n)) : ‖walshSign x y‖ = 1 := by
  unfold walshSign
  by_cases h : dotParity x y <;> simp [h]

/-! ### Walsh-character orthogonality -/

/-- Flip bit `k` of a basis label. -/
def flipBit (x : Fin (2 ^ n)) (k : Fin n) : Fin (2 ^ n) :=
  ⟨x.val ^^^ 2 ^ k.val,
    Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right one_lt_two k.isLt)⟩

/--
@isnad1 id=eq.0h4v.s5.14119926088f from=translated src=- shape=c382f986 vocab=7d91ca78
-/
theorem bit_flipBit (x : Fin (2 ^ n)) (k k' : Fin n) :
    bit (flipBit x k) k' = (bit x k' ^^ decide (k = k')) := by
  change (x.val ^^^ 2 ^ k.val).testBit k'.val = (bit x k' ^^ decide (k = k'))
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  congr 1
  rw [decide_eq_decide]
  exact Fin.val_inj

/--
@isnad1 id=eq.0h3v.s5.09a163e944a1 from=translated src=- shape=616d8564 vocab=888b4a58
-/
theorem flipBit_flipBit (x : Fin (2 ^ n)) (k : Fin n) :
    flipBit (flipBit x k) k = x := by
  unfold flipBit
  ext
  simp [Nat.xor_assoc]

/--
@isnad1 id=ne.0h3v.s5.a3e7e28c86b1 from=translated src=- shape=e54f5098 vocab=888b4a58
-/
theorem flipBit_ne (x : Fin (2 ^ n)) (k : Fin n) : flipBit x k ≠ x := by
  intro h
  have hb := congrArg (fun y : Fin (2 ^ n) => bit y k) h
  simp [bit_flipBit] at hb

/-- Flipping bit `k` of `x` toggles the parity `x · z` exactly when bit `k`
of `z` is set.
@isnad1 id=eq.0h4v.s5.3bf1d88dffb3 from=translated src=- shape=3042ad04 vocab=a409fb41
-/
theorem dotParity_flipBit (x z : Fin (2 ^ n)) (k : Fin n) :
    dotParity (flipBit x k) z = (dotParity x z ^^ bit z k) := by
  unfold dotParity
  cases hz : bit z k
  · rw [Bool.xor_false]
    have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
        = Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
      apply Finset.filter_congr
      intro k' _
      rcases eq_or_ne k k' with rfl | hk
      · simp [bit_flipBit, hz]
      · simp [bit_flipBit, hk]
    rw [hset]
  · rw [Bool.xor_true]
    by_cases hx : bit x k
    · have hmem : k ∈ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
        simp [hx, hz]
      have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
          = (Finset.univ.filter fun k' : Fin n => bit x k' && bit z k').erase k := by
        ext k'
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
        rcases eq_or_ne k' k with rfl | hk
        · simp [bit_flipBit, hx]
        · simp [bit_flipBit, hk, Ne.symm hk]
      rw [hset, ← decide_not, decide_eq_decide,
        ← Finset.card_erase_add_one hmem, Nat.odd_add_one, not_not]
    · have hnot : k ∉ Finset.univ.filter fun k' : Fin n => bit x k' && bit z k' := by
        simp [hx]
      have hset : (Finset.univ.filter fun k' : Fin n => bit (flipBit x k) k' && bit z k')
          = insert k (Finset.univ.filter fun k' : Fin n => bit x k' && bit z k') := by
        ext k'
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
        rcases eq_or_ne k' k with rfl | hk
        · simp [bit_flipBit, hx, hz]
        · simp [bit_flipBit, hk, Ne.symm hk]
      rw [hset, Finset.card_insert_of_notMem hnot, ← decide_not,
        decide_eq_decide, Nat.odd_add_one]

/-- Two distinct labels differ at some bit.
@isnad1 id=ex.1h3v.s6.c0b520a5a4f4 from=translated src=- shape=c81939e9 vocab=c2cb361a
-/
theorem exists_bit_ne {y s : Fin (2 ^ n)} (h : y ≠ s) :
    ∃ k : Fin n, bit y k ≠ bit s k := by
  by_contra hall
  push Not at hall
  refine h (Fin.val_injective (Nat.eq_of_testBit_eq fun i => ?_))
  by_cases hi : i < n
  · exact hall ⟨i, hi⟩
  · push Not at hi
    have hy : y.val < 2 ^ i := lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num) hi)
    have hs : s.val < 2 ^ i := lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by norm_num) hi)
    rw [Nat.testBit_lt_two_pow hy, Nat.testBit_lt_two_pow hs]

private theorem if_xor_true (a : Bool) :
    (if (a ^^ true) = true then (-1 : ℂ) else 1) = -(if a = true then -1 else 1) := by
  cases a <;> simp

/-- Flipping a bit on which `y` and `s` disagree negates the product of their
Walsh signs.
@isnad1 id=eq.1h5v.s6.a397f5d41da0 from=translated src=- shape=474f9b38 vocab=f5162131
-/
theorem walshSign_mul_walshSign_flipBit {y s : Fin (2 ^ n)} {k : Fin n}
    (hk : bit y k ≠ bit s k) (x : Fin (2 ^ n)) :
    walshSign y (flipBit x k) * walshSign s (flipBit x k)
      = -(walshSign y x * walshSign s x) := by
  unfold walshSign
  simp only [dotParity_comm y (flipBit x k), dotParity_comm s (flipBit x k),
    dotParity_flipBit, dotParity_comm x y, dotParity_comm x s]
  cases hy : bit y k <;> cases hs : bit s k
  · exact absurd (hy.trans hs.symm) hk
  · rw [Bool.xor_false, if_xor_true]
    ring
  · rw [Bool.xor_false, if_xor_true]
    ring
  · exact absurd (hy.trans hs.symm) hk

/-- Walsh-character orthogonality: for `y ≠ s` the signed sum over all basis
labels cancels in pairs under the bit-flip involution.
@isnad1 id=eq.1h3v.s7.37dfd2147a4c from=translated src=- shape=9f7f3636 vocab=c8a4507c
-/
theorem sum_walshSign_mul_walshSign {y s : Fin (2 ^ n)} (h : y ≠ s) :
    ∑ x, walshSign y x * walshSign s x = 0 := by
  obtain ⟨k, hk⟩ := exists_bit_ne h
  refine Finset.sum_involution (fun x _ => flipBit x k)
    (fun x _ => ?_) (fun x _ _ => flipBit_ne x k)
    (fun x _ => Finset.mem_univ _) (fun x _ => flipBit_flipBit x k)
  rw [walshSign_mul_walshSign_flipBit hk x]
  ring

/--
@isnad1 id=eq.0h3v.s7.b66cd673fef6 from=translated src=- shape=f203e04f vocab=0a015e93
-/
theorem sum_walshSign_mul_walshSign_eq (y s : Fin (2 ^ n)) :
    ∑ x, walshSign y x * walshSign s x =
      if y = s then ((2 ^ n : ℕ) : ℂ) else 0 := by
  by_cases hys : y = s
  · simp_all
  · rw [ite_eq_right hys, sum_walshSign_mul_walshSign hys]

/--
@isnad1 id=eq.0h1v.s5.38a8350df9ed from=translated src=- shape=8c758db9 vocab=3eb2b197
-/
@[simp]
theorem invSqrtCard_mul_self (n : ℕ) :
    invSqrtCard n * invSqrtCard n = (((2 ^ n : ℕ) : ℂ)⁻¹) := by
  rw [invSqrtCard, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))]
  norm_num

/-- A Boolean phase has unit norm.
@isnad1 id=eq.0h3v.s5.cd8c28de5969 from=translated src=- shape=6dc32815 vocab=66f08e8b
-/
@[simp]
theorem norm_phaseSign (f : Oracle n) (x : Fin (2 ^ n)) :
    ‖phaseSign f x‖ = 1 := by
  unfold phaseSign
  by_cases h : f x <;> simp [h]

/-- Raw `n`-qubit Hadamard layer in Walsh-Hadamard closed form. -/
def hadamardLayerOp (n : ℕ) : HilbertOperator n :=
  fun y x => invSqrtCard n * walshSign y x

/-- The Walsh-Hadamard closed-form matrix is unitary.
@isnad1 id=mem.0h1v.s9.dc4bd6aae2ef from=translated src=- shape=6e34e85c vocab=8368c484
-/
theorem hadamardLayerOp_mem_unitaryGroup (n : ℕ) :
    hadamardLayerOp n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext y s
  rw [Matrix.mul_apply]
  calc
    ∑ x, hadamardLayerOp n y x * star (hadamardLayerOp n) x s
        = ∑ x, (invSqrtCard n * invSqrtCard n)
            * (walshSign y x * walshSign s x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [hadamardLayerOp, Matrix.star_apply]
          rw [star_mul, star_invSqrtCard, star_walshSign]
          ring
    _ = (invSqrtCard n * invSqrtCard n)
          * ∑ x, walshSign y x * walshSign s x := by
          rw [Finset.mul_sum]
    _ = (((2 ^ n : ℕ) : ℂ)⁻¹)
          * (if y = s then ((2 ^ n : ℕ) : ℂ) else 0) := by
          rw [invSqrtCard_mul_self, sum_walshSign_mul_walshSign_eq]
    _ = (1 : HilbertOperator n) y s := by
          by_cases hys : y = s
          · subst s
            simp_all
          · rw [ite_eq_right hys, Matrix.one_apply_ne hys, mul_zero]

/-- The `n`-qubit Hadamard layer as a unitary gate. -/
def hadamardLayer (n : ℕ) : Gate n :=
  Gate.ofUnitary (hadamardLayerOp n) (hadamardLayerOp_mem_unitaryGroup n)

/-- Raw uniform input-register vector produced by the first Hadamard layer. -/
def uniformStateVec (n : ℕ) : StateVector n :=
  WithLp.toLp 2 fun _ => invSqrtCard n

/-- The uniform input-register vector has unit norm.
@isnad1 id=eq.0h1v.s6.880483ea9c83 from=translated src=- shape=7aab2fa7 vocab=9b56f9c8
-/
theorem norm_uniformStateVec (n : ℕ) : ‖uniformStateVec n‖ = 1 := by
  rw [uniformStateVec, EuclideanSpace.norm_eq]
  simp_all

/-- The uniform input-register state produced by the first Hadamard layer. -/
def uniformState (n : ℕ) : PureState n :=
  PureState.ofVec (uniformStateVec n) (norm_uniformStateVec n)

/--
@isnad1 id=eq.0h2v.s6.a4eb3463f020 from=translated src=- shape=e60353b8 vocab=a562cf5b
-/
@[simp]
theorem uniformState_apply (x : Fin (2 ^ n)) : uniformState n x = invSqrtCard n :=
  rfl

/-- The first Hadamard layer sends `|0^n⟩` to the uniform superposition.
@isnad1 id=eq.0h1v.s5.c53f1c13bd4b from=translated src=- shape=dad61bba vocab=6425afe9
-/
theorem hadamardLayer_apply_zero :
    (hadamardLayer n).apply (ket (0 : Fin (2 ^ n))) = uniformState n := by
  ext i
  rw [Gate.apply_ket]
  simp [hadamardLayer, hadamardLayerOp]

/-! ### The XOR phase-query pipeline -/

/-- The pre-Hadamard joint basis state `|0^n⟩ ⊗ |−⟩`. -/
def initialBasisState (n : ℕ) : PureState (n + 1) :=
  (ket (0 : Fin (2 ^ n))).tensor ketMinus

/-- The joint state queried by the XOR oracle, obtained by applying the first
Hadamard layer to the input register and leaving the `|−⟩` target alone. -/
def initialState (n : ℕ) : PureState (n + 1) :=
  ((hadamardLayer n).tensor (1 : Gate 1)).apply (initialBasisState n)

/-- The queried state is the uniform input register tensored with `|−⟩`.
@isnad1 id=eq.0h1v.s4.d2434fdf8afd from=translated src=- shape=6c2bedd1 vocab=b0350d84
-/
theorem initialState_eq_uniform_tensor :
    initialState n = (uniformState n).tensor ketMinus := by
  rw [initialState, initialBasisState, Gate.tensor_apply_tensor,
    hadamardLayer_apply_zero, Gate.one_apply]

/-- The actual post-query joint state, using the XOR oracle gate. -/
def postOracleState (f : Oracle n) : PureState (n + 1) :=
  (oracleGate f).apply (initialState n)

/-- The input-register state after rewriting the oracle query by phase
kickback: `(√(2^n))⁻¹ ∑ x, (-1)^{f x}|x⟩`. -/
def afterPhaseQueryVec (f : Oracle n) : StateVector n :=
  WithLp.toLp 2 fun x => invSqrtCard n * phaseSign f x

/-- The phase-query vector has unit norm.
@isnad1 id=eq.0h2v.s6.c42225f5bf0b from=translated src=- shape=a01a8b7d vocab=38bad945
-/
theorem norm_afterPhaseQueryVec (f : Oracle n) : ‖afterPhaseQueryVec f‖ = 1 := by
  rw [afterPhaseQueryVec, EuclideanSpace.norm_eq]
  simp_all

/-- The input register after the XOR oracle has been converted into a phase query. -/
def afterPhaseQuery (f : Oracle n) : PureState n :=
  PureState.ofVec (afterPhaseQueryVec f) (norm_afterPhaseQueryVec f)

/-- The actual XOR-oracle query on the uniform input register and `|−⟩`
target is exactly the phase-query state tensored with the unchanged target.
@isnad1 id=eq.0h2v.s5.b59d6a60c9dc from=translated src=- shape=1a61d479 vocab=05d2a5e4
-/
theorem postOracleState_eq_afterPhaseQuery_tensor (f : Oracle n) :
    postOracleState f = (afterPhaseQuery f).tensor ketMinus := by
  ext i
  rcases (prodEquiv (m := n) (n := 1)).surjective i with ⟨⟨x, b⟩, rfl⟩
  rw [postOracleState, initialState_eq_uniform_tensor, oracleGate,
    Gate.xorOracle_apply, PureState.tensor_apply_prod, afterPhaseQuery]
  simp only [Equiv.symm_apply_apply, Gate.xorPerm_apply]
  by_cases h : f x
  · fin_cases b <;> simp [uniformState, uniformStateVec, afterPhaseQueryVec,
      h, phaseSign, ketMinus_apply]
  · simp [uniformState, uniformStateVec, afterPhaseQueryVec, h, phaseSign]

/-- The final input-register state after the second Hadamard layer, in the
phase-query view. -/
def finalState (f : Oracle n) : PureState n :=
  (hadamardLayer n).apply (afterPhaseQuery f)

/-- The actual final joint state: apply the second Hadamard layer to the
input register and leave the target qubit alone. -/
def finalJointState (f : Oracle n) : PureState (n + 1) :=
  ((hadamardLayer n).tensor (1 : Gate 1)).apply (postOracleState f)

/-- The actual final joint state factors as the final input-register state
and the unchanged `|−⟩` target.
@isnad1 id=eq.0h2v.s5.644a77ab517b from=translated src=- shape=1a61d479 vocab=b9c0c2a8
-/
theorem finalJointState_eq_finalState_tensor (f : Oracle n) :
    finalJointState f = (finalState f).tensor ketMinus := by
  rw [finalJointState, postOracleState_eq_afterPhaseQuery_tensor,
    Gate.tensor_apply_tensor, Gate.one_apply, finalState]

end

end WalshHadamard

end QuantumAlg
