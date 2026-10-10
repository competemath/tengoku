import Tengoku

/-!
# Spectral Reflection Machinery — operator parity `(−1)^T` as a function of the total number operator

This file provides the *family-agnostic* algebraic machinery used to prove the
parity/Bogoliubov identity for the momentum-mode Fourier transform.
It is generic over any `{R : Type*} [Ring R] [Algebra ℂ R]` and does **not** depend on
the Jordan–Wigner / momentum-mode specifics.

The core fact (`noncommProd_one_sub_two_smul_eq_parityFn`): for a family of pairwise
commuting idempotents `p` over a finset `s`, the reflection product
`∏_{i∈s} (1 − 2·p i)` equals `parityFn (Σ_{i∈s} p i) s.card`, a fixed *function of the
total operator* `T = Σ p i`. Consequently two idempotent families with equal cardinality
and equal sum produce equal reflection products — even when the two families do not
commute across each other.

## Main definitions
- `binomOp T j`: the operator binomial coefficient `(1/j!)·(descPochhammer ℂ j)(T)`.
- `parityFn T n`: the function-of-`T` form of the reflection product,
  `Σ_{j=0}^{n} (−2)^j·binomOp T j` (`= (−1)^T` when `spec T ⊆ {0,…,n}`).

## Main statements
- `descPochhammer_card_succ_annihilate`: `(descPochhammer ℂ (|s|+1))(Σ p) = 0` (nilpotency).
- `aeval_add_idem_split`: `f(p + T) = p·f(1 + T) + (1 − p)·f(T)` for idempotent `p ∥ T`.
- `binomOp_idem_pascal`: the operator binomial Pascal recurrence.
- `noncommProd_map_embedding`: reindexing a `noncommProd` along an embedding.
- `noncommProd_one_sub_two_smul_eq_parityFn`: the product↔function-of-`T` identity.
-/

namespace QAOA.IsingChain.JordanWigner

open scoped BigOperators

noncomputable section

-- ============================================================================
-- BLOCK A — the parity Fourier/Bogoliubov spectral machinery (generic over R)
--
-- For a family of pairwise commuting idempotents, the reflection product
-- `∏ (1 − 2 pᵢ)` is a fixed FUNCTION of the total operator `T = Σ pᵢ` (the operator
-- `(−1)^T`, encoded via the binomial expansion `Σⱼ (−2)ʲ · binom(T, j)`), so two
-- families with equal cardinality and equal sum give equal products.
-- ============================================================================

section BlockA

variable {R : Type*} [Ring R] [Algebra ℂ R]

omit [Algebra ℂ R] in
/-- `p · (p + T)^m = p · (1 + T)^m` for an idempotent `p` commuting with `T`. -/
theorem idem_mul_add_pow {p T : R} (hp : p * p = p) (hpT : Commute p T) (m : ℕ) :
    p * (p + T) ^ m = p * (1 + T) ^ m := by
  have hp1T : Commute p (1 + T) := (Commute.one_right p).add_right hpT
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, ih, pow_succ, mul_assoc]
    -- goal: p * ((1+T)^m * (p+T)) = p * ((1+T)^m * (1+T))
    have hppow : p * (1 + T) ^ m * p = p * (1 + T) ^ m := by
      rw [mul_assoc, show (1 + T) ^ m * p = p * (1 + T) ^ m from (hp1T.symm.pow_left m).eq,
        ← mul_assoc, hp]
    calc p * ((1 + T) ^ m * (p + T))
        = p * (1 + T) ^ m * p + p * ((1 + T) ^ m * T) := by
          rw [mul_add (((1:R) + T) ^ m) p T, mul_add, ← mul_assoc]
      _ = p * (1 + T) ^ m + p * ((1 + T) ^ m * T) := by rw [hppow]
      _ = p * ((1 + T) ^ m * (1 + T)) := by
          rw [mul_add (((1:R) + T) ^ m) 1 T, mul_one, mul_add]

omit [Algebra ℂ R] in
/-- `(1 − p) · (p + T)^m = (1 − p) · T^m` for an idempotent `p` commuting with `T`. -/
theorem one_sub_idem_mul_add_pow {p T : R} (hp : p * p = p) (hpT : Commute p T) (m : ℕ) :
    (1 - p) * (p + T) ^ m = (1 - p) * T ^ m := by
  have hsp : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp, sub_self]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, ih, pow_succ, mul_assoc]
    -- goal: (1-p) * (T^m * (p+T)) = (1-p) * (T^m * T)
    have hkey : (1 - p) * (T ^ m * p) = 0 := by
      rw [show T ^ m * p = p * T ^ m from (hpT.symm.pow_left m).eq, ← mul_assoc, hsp, zero_mul]
    calc (1 - p) * (T ^ m * (p + T))
        = (1 - p) * (T ^ m * p) + (1 - p) * (T ^ m * T) := by rw [mul_add, mul_add]
      _ = (1 - p) * (T ^ m * T) := by rw [hkey, zero_add]

omit [Algebra ℂ R] in
/-- The **power split identity**: for an idempotent `p` commuting with `T`,
`(p + T)^m = p·(1 + T)^m + (1 − p)·T^m`. Decompose `1 = p + (1 − p)` on the left. -/
theorem add_idem_pow_split {p T : R} (hp : p * p = p) (hpT : Commute p T) (m : ℕ) :
    (p + T) ^ m = p * (1 + T) ^ m + (1 - p) * T ^ m := by
  have : (p + T) ^ m = (p + (1 - p)) * (p + T) ^ m := by rw [add_sub_cancel, one_mul]
  rw [this, add_mul, idem_mul_add_pow hp hpT, one_sub_idem_mul_add_pow hp hpT]

/-- The **polynomial split identity**: for an idempotent `p` commuting with `T` and any
`f : Polynomial ℂ`, `f(p + T) = p·f(1 + T) + (1 − p)·f(T)` (operator functional calculus
respects the orthogonal `p / (1−p)` decomposition). -/
theorem aeval_add_idem_split {p T : R} (hp : p * p = p) (hpT : Commute p T)
    (f : Polynomial ℂ) :
    (Polynomial.aeval (p + T)) f
      = p * (Polynomial.aeval (1 + T)) f + (1 - p) * (Polynomial.aeval T) f := by
  induction f using Polynomial.induction_on with
  | C a =>
    simp only [Polynomial.aeval_C]
    -- algebraMap a is central; p·(alg a) + (1-p)·(alg a) = alg a
    rw [show p * (algebraMap ℂ R) a + (1 - p) * (algebraMap ℂ R) a
        = (p + (1 - p)) * (algebraMap ℂ R) a by rw [add_mul], add_sub_cancel, one_mul]
  | add f g hf hg =>
    rw [Polynomial.aeval_add, Polynomial.aeval_add, Polynomial.aeval_add, hf, hg]
    rw [mul_add, mul_add]; abel
  | monomial n a _ =>
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    rw [add_idem_pow_split hp hpT]
    -- (alg a) * (p·A + (1-p)·B) = p·((alg a)·A) + (1-p)·((alg a)·B)
    have hca : ∀ x : R, (algebraMap ℂ R) a * x = x * (algebraMap ℂ R) a :=
      fun x => (Algebra.commutes a x)
    rw [mul_add]
    congr 1
    · rw [hca, mul_assoc, ← hca]
    · rw [hca, mul_assoc, ← hca]

/-- The forward-shift identity for the descending Pochhammer evaluated at `1 + T`:
`(descPochhammer ℂ (m+1))(1 + T) = (1 + T)·(descPochhammer ℂ m)(T)`. -/
theorem aeval_descPochhammer_shift (T : R) (m : ℕ) :
    (Polynomial.aeval (1 + T)) (descPochhammer ℂ (m + 1))
      = (1 + T) * (Polynomial.aeval T) (descPochhammer ℂ m) := by
  rw [descPochhammer_succ_left, map_mul, Polynomial.aeval_X, Polynomial.aeval_comp]
  congr 2
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_one, add_sub_cancel_left]

variable {ι : Type*}

/-- If `p` commutes with `T`, it commutes with any polynomial in `T`. -/
theorem commute_aeval_of_commute {p T : R} (hpT : Commute p T) (f : Polynomial ℂ) :
    Commute p ((Polynomial.aeval T) f) := by
  induction f using Polynomial.induction_on with
  | C a => rw [Polynomial.aeval_C]; exact Algebra.commute_algebraMap_right a p
  | add f g hf hg => rw [Polynomial.aeval_add]; exact hf.add_right hg
  | monomial n a _ =>
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    exact (Algebra.commute_algebraMap_right a p).mul_right (hpT.pow_right (n + 1))

/-- **Operator falling-factorial Pascal.** For an idempotent `p` commuting with `T`,
`(dP (j+1))(p + T) = (dP (j+1))(T) + (j+1)·(p · (dP j)(T))`. -/
theorem aeval_descPochhammer_idem_pascal {p T : R} (hp : p * p = p) (hpT : Commute p T)
    (j : ℕ) :
    (Polynomial.aeval (p + T)) (descPochhammer ℂ (j + 1))
      = (Polynomial.aeval T) (descPochhammer ℂ (j + 1))
        + ((j : ℂ) + 1) • (p * (Polynomial.aeval T) (descPochhammer ℂ j)) := by
  -- Xj := (dP j)(T), commutes with p and T
  have hpXj : Commute p ((Polynomial.aeval T) (descPochhammer ℂ j)) :=
    commute_aeval_of_commute hpT _
  have hTXj : Commute T ((Polynomial.aeval T) (descPochhammer ℂ j)) :=
    commute_aeval_of_commute (Commute.refl T) _
  have hcast : (Polynomial.aeval T) (Polynomial.X - (j : Polynomial ℂ)) = T - (j : ℂ) • 1 := by
    simp [Algebra.smul_def]
  -- the polynomial-split + shift + succ_right rewrites
  rw [aeval_add_idem_split hp hpT, aeval_descPochhammer_shift, descPochhammer_succ_right, map_mul,
    hcast]
  set Xj := (Polynomial.aeval T) (descPochhammer ℂ j) with hXj
  have hpXjeq : p * Xj = Xj * p := hpXj.eq
  have hTXjeq : T * Xj = Xj * T := hTXj.eq
  have hpTXj : p * (T * Xj) = p * Xj * T := by
    rw [hTXjeq, ← mul_assoc]
  have step1 : p * ((1 + T) * Xj) = p * Xj + p * Xj * T := by
    rw [add_mul, one_mul, mul_add, hpTXj]
  have hXjsub : Xj * (T - (j : ℂ) • 1) = Xj * T - (j : ℂ) • Xj := by
    rw [mul_sub, mul_smul_comm, mul_one]
  have hpXjT : p * (Xj * (T - (j : ℂ) • 1)) = p * Xj * T - (j : ℂ) • (p * Xj) := by
    rw [hXjsub, mul_sub, ← mul_assoc, mul_smul_comm]
  have step2 : (1 - p) * (Xj * (T - (j : ℂ) • 1))
      = Xj * (T - (j : ℂ) • 1) - (p * Xj * T - (j : ℂ) • (p * Xj)) := by
    rw [sub_mul, one_mul, hpXjT]
  rw [step1, step2]
  module

/-- The operator binomial coefficient `binomOp T j = (1/j!)·(dP j)(T)`. For commuting
idempotents summed to `T`, `binomOp T j` is the elementary symmetric polynomial of
degree `j`; here we only need its Pascal recurrence and `binomOp T 0 = 1`. -/
def binomOp (T : R) (j : ℕ) : R :=
  (1 / (j.factorial : ℂ)) • (Polynomial.aeval T) (descPochhammer ℂ j)

theorem binomOp_zero (T : R) : binomOp T 0 = 1 := by
  rw [binomOp, descPochhammer_zero, map_one, Nat.factorial_zero, Nat.cast_one, div_one, one_smul]

/-- **Operator binomial Pascal.** `binomOp (p + T) (j+1) = binomOp T (j+1) + p · binomOp T j`
for an idempotent `p` commuting with `T`. -/
theorem binomOp_idem_pascal {p T : R} (hp : p * p = p) (hpT : Commute p T) (j : ℕ) :
    binomOp (p + T) (j + 1) = binomOp T (j + 1) + p * binomOp T j := by
  rw [binomOp, binomOp, binomOp, aeval_descPochhammer_idem_pascal hp hpT, smul_add]
  congr 1
  -- (1/(j+1)!)•((j+1)•(p·X)) = p·((1/j!)•X)
  rw [smul_smul, mul_smul_comm]
  congr 1
  have hfac : ((j + 1).factorial : ℂ) = ((j : ℂ) + 1) * (j.factorial : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hne1 : ((j : ℂ) + 1) ≠ 0 := by
    have : ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast Nat.succ_ne_zero j
  have hnefac : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [hfac]
  field_simp

/-- The function-of-`T` form of the reflection product: `parityFn T n = Σ_{j=0}^{n} (−2)^j·binomOp T j`,
which equals `(−1)^T` when `T`'s spectrum is `⊆ {0,…,n}`. -/
def parityFn (T : R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range (n + 1), ((-2 : ℂ)) ^ j • binomOp T j

/-- `1 − 2·a` and `1 − 2·b` commute when `a` and `b` do. -/
theorem commute_one_sub_two_smul_gen {a b : R} (h : Commute a b) :
    Commute (1 - (2 : ℂ) • a) (1 - (2 : ℂ) • b) := by
  apply Commute.sub_left
  · exact Commute.one_left _
  · apply Commute.sub_right
    · exact Commute.one_right _
    · exact (h.smul_left 2).smul_right 2

/-- For a commuting idempotent family, the factors `1 − 2·p i` pairwise commute. -/
theorem one_sub_two_smul_pairwise_commute (s : Finset ι) (p : ι → R)
    (hcomm : (s : Set ι).Pairwise (Function.onFun Commute p)) :
    (s : Set ι).Pairwise (Function.onFun Commute (fun i => 1 - (2 : ℂ) • p i)) := by
  intro i hi j hj hij
  exact commute_one_sub_two_smul_gen (hcomm hi hj hij)

variable {κ : Type*}

omit [Algebra ℂ R] in
/-- Reindexing a `noncommProd` along a bijection: `∏_{k ∈ s.map e} g k = ∏_{i ∈ s} g (e i)`.
The underlying multisets coincide (`Multiset.map_map`), so the products are equal. -/
theorem noncommProd_map_embedding (s : Finset ι) (e : ι ↪ κ) (g : κ → R)
    (comm : ((s.map e : Finset κ) : Set κ).Pairwise (Function.onFun Commute g)) :
    (s.map e).noncommProd g comm
      = s.noncommProd (fun i => g (e i))
          (fun _ hi _ hj hij => comm (Finset.mem_map_of_mem e hi)
            (Finset.mem_map_of_mem e hj) (fun h => hij (e.injective h))) := by
  simp only [Finset.noncommProd, Finset.map_val, Multiset.map_map, Function.comp_def]

end BlockA

end

end QAOA.IsingChain.JordanWigner
