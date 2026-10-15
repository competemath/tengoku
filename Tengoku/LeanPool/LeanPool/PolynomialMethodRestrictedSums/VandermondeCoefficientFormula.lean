/-
Copyright (c) 2026 Nick Adfor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Adfor
-/
module

public import Tengoku

/-!
# The Vandermonde coefficient formula

Lemma 3.1 of Alon-Nathanson-Ruzsa: a closed form for the coefficient of
`∏ i, X i ^ c i` in `(X 0 + ⋯ + X k) ^ m * ∏_{i > j} (X i - X j)`,
culminating in `Vandermonde_coefficient_formula`.
-/

@[expose] public section

open MvPolynomial
open AddMonoidAlgebra (coeff)
open Finset
open Matrix
open BigOperators

variable {k : ℕ}

/-- Falling factorial (s)_r = s(s-1)...(s-r + 1) -/
def fallingFactorial (s : ℕ) (r : ℕ) : ℕ :=
  if r = 0 then 1
  else ∏ i ∈ range r, (s - i)

/-- Vandermonde matrix (c^j) -/
def vandermondeMatrix (c : Fin (k + 1) → ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  Matrix.of (fun i j : Fin (k + 1) => (c i : ℚ) ^ (j : ℕ))

/-- Falling factorial matrix ((c)_j) -/
def fallingFactorialMatrix (c : Fin (k + 1) → ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  Matrix.of (fun i j : Fin (k + 1) => (fallingFactorial (c i) j : ℚ))

/-- Expected value: m! / (∏ c!) * ∏_{i>j} (c - c) -/
def expectedValue (c : Fin (k + 1) → ℕ) (m : ℕ) : ℚ :=
  (m.factorial : ℚ) * (∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
    if j.val < i.val then ((c i : ℚ) - (c j : ℚ)) else 1) /
    (∏ i : Fin (k + 1), ((c i).factorial : ℚ))

/-- Convert a function c : Fin (k + 1) → ℕ to Finsupp -/
def toFinsupp (c : Fin (k + 1) → ℕ) : (Fin (k + 1)) →₀ ℕ :=
  ⟨Finset.univ.filter (fun i => c i ≠ 0), c, fun i => by simp⟩

/- Vandermonde Coefficient Formula (Lemma 3.1):
    Let c₀, ..., cₖ be nonnegative integers and suppose that ∑ᵢ cᵢ = m + (k + 1 choose 2),
    where m is a nonnegative integer. Then the coefficient of ∏ᵢ xᵢ^{cᵢ} in the polynomial
    (x₀ + x₁ + ⋯ + xₖ)^m ∏_{i>j} (xᵢ - xⱼ) is
    (m! / ∏ᵢ cᵢ!) ∏_{i>j} (cᵢ - cⱼ).

    Proof (from the paper):
    The product ∏_{k ≥ i > j ≥ 0} (xᵢ - xⱼ) is precisely the Vandermonde determinant
    det(xᵢ^j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k} which is equal to the sum
    ∑_{σ∈S_{k + 1}} (-1)^{sign(σ)} ∏_{i=0}^k xᵢ^{σ(i)},
    where S_{k + 1} denotes the set of all permutations of the k + 1 symbols 0, ..., k.

    It thus follows that the required coefficient, which we denote by C, is given by
    C = ∑_{σ∈S_{k + 1}} (-1)^{sign(σ)} m! / ((c₀ - σ(0))!(c₁ - σ(1))!⋯(cₖ - σ(k))!).

    Similarly, the product ∏_{k ≥ i > j ≥ 0} (cᵢ - cⱼ) is the Vandermonde determinant
    det(cᵢ^j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k}.

    For two integers r ≥ 1 and s let (s)_r denote the product s(s-1)⋯(s-r + 1) and define
    also (s)_₀ = 1 for all s. Observe that the matrix ((cᵢ)_j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k}
    can be obtained from the matrix (cᵢ^j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k} by subtracting
    appropriate linear combinations of the columns with indices less than j from the
    column indexed by j, for each j = k, k-1, ..., 1. Therefore, these two matrices
    have the same determinant.

    It thus follows that
    (m! / ∏ᵢ cᵢ!) ∏_{i>j} (cᵢ - cⱼ) = (m! / ∏ᵢ cᵢ!) det((cᵢ)_j)_{0 ≤ i ≤ k, 0 ≤ j ≤ k}
    = (m! / ∏ᵢ cᵢ!) ∑_{σ∈S_{k + 1}} (-1)^{sign(σ)} (c₀)_{σ(0)}(c₁)_{σ(1)}⋯(cₖ)_{σ(k)}
    = ∑_{σ∈S_{k + 1}} (-1)^{sign(σ)} m! / ((c₀ - σ(0))!(c₁ - σ(1))!⋯(cₖ - σ(k))!) = C,
    completing the proof. □
-/
noncomputable section AristotleLemmas

/--
@isnad1 id=eq.0h2v.s6.66e17027bf45 from=translated src=- shape=6040750a vocab=e3984b84
-/
lemma det_fallingFactorial_eq_det_vandermonde (c : Fin (k + 1) → ℕ) :
  (fallingFactorialMatrix c).det = (vandermondeMatrix c).det := by
    -- By definition of $V$, we can write $F$ as $V * M$ where $M$ is an upper triangular matrix
    -- with ones on the diagonal.
    obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ,
        fallingFactorialMatrix c = vandermondeMatrix c * M ∧ (∀ i, M i i = 1) ∧
            (∀ i j, i > j → M i j = 0) := by
      -- For each $j$, we can express $(falling\_factorial (c i) j)$ as a linear combination of $c
      -- i^l$ for $l \leq j$.
      have h_comb : ∀ i j, fallingFactorial (c i) j = ∑ l ∈ Finset.range (j + 1),
          (Polynomial.coeff
              (Polynomial.C 1 * (∏ m ∈ Finset.range j, (Polynomial.X - Polynomial.C (m : ℚ))))
              l) * (c i : ℚ) ^ l := by
        intro i j
        have h_poly :
            (∏ m ∈ Finset.range j, (Polynomial.X - Polynomial.C (m : ℚ))) =
              ∑ l ∈ Finset.range (j + 1),
                Polynomial.C ((Polynomial.coeff
                    (∏ m ∈ Finset.range j, (Polynomial.X - Polynomial.C (m : ℚ))) l) : ℚ) *
                  Polynomial.X ^ l := by
          nth_rw 1 [Polynomial.as_sum_range_C_mul_X_pow (∏ m ∈ Finset.range j,
              (Polynomial.X - Polynomial.C (m : ℚ)))]
          rw [Polynomial.natDegree_prod]
              <;> norm_num [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
          exact fun i hi => Polynomial.X_sub_C_ne_zero _
        replace h_poly := congr_arg (Polynomial.eval (c i : ℚ)) h_poly
        simp_all +decide only [map_natCast, Polynomial.eval_prod, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_natCast, Polynomial.eval_finsetSum,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, map_one,
          one_mul]
        unfold fallingFactorial
        simp_all only [Nat.cast_ite, Nat.cast_one, Nat.cast_prod]
        split
        next h =>
          subst h
          simp_all only [range_zero, prod_empty, zero_add, range_one, Polynomial.coeff_one,
              ite_mul, pow_zero,
            mul_one, zero_mul, sum_ite_eq', mem_singleton, ↓reduceIte]
        next h =>
          by_cases hi : c i < j <;> simp_all +decide only [prod_range, not_lt]
          · -- both products vanish since the factor at index ⟨c i, hi⟩ is c i - c i = 0
            rw [← h_poly]
            rw [Finset.prod_eq_zero (i := (⟨c i, hi⟩ : Fin j))
                  (Finset.mem_univ _)
                  (by change ((c i - ↑(⟨c i, hi⟩ : Fin j) : ℕ) : ℚ) = 0
                      simp)]
            symm
            apply Finset.prod_eq_zero (i := (⟨c i, hi⟩ : Fin j)) (Finset.mem_univ _)
            change (↑(c i) - ↑↑(⟨c i, hi⟩ : Fin j) : ℚ) = 0
            simp
          · exact Eq.trans
              (Finset.prod_congr rfl fun _ _ => by
                rw [Nat.cast_sub (by linarith [Fin.is_lt ‹_›])])
              h_poly
      -- Let $M$ be the matrix whose $(i, j)$-th entry is the coefficient of $c_i^l$ in the
      -- expansion of $(falling\_factorial (c i) j)$.
      use Matrix.of (fun i j => Polynomial.coeff (Polynomial.C 1 * (∏ m ∈ Finset.range j,
          (Polynomial.X - Polynomial.C (m : ℚ)))) i)
      -- aesop used to split the conjunction and simplify Polynomial.C 1 * _; do this explicitly
      simp only [Polynomial.C_1, one_mul] at h_comb ⊢
      refine ⟨?_, ?_, ?_⟩
      · ext i j
        simp +decide only [fallingFactorialMatrix, Matrix.of_apply, map_natCast, Matrix.mul_apply]
        convert h_comb i j using 1
        rw [Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Fin.is_le j)))]
        · rw [Finset.sum_range]
          simp +decide [mul_comm, vandermondeMatrix]
        · intro x a a_1
          simp_all only [Nat.succ_eq_add_one, mem_range, not_lt, mul_eq_zero, pow_eq_zero_iff',
              Nat.cast_eq_zero, ne_eq]
          exact Or.inl <| Polynomial.coeff_eq_zero_of_natDegree_lt <| by
            erw [Polynomial.natDegree_prod _ _ fun i hi => Polynomial.X_sub_C_ne_zero _]
            simpa [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] using by linarith
      · intro i
        simp only [Matrix.of_apply]
        -- The leading coefficient of the product of linear factors is 1.
        have h_leading_coeff :
            Polynomial.leadingCoeff (∏ x ∈ Finset.range i.val,
                (Polynomial.X - Polynomial.C (x : ℚ))) = 1 := by
          rw [Polynomial.leadingCoeff_prod]
          exact Finset.prod_eq_one fun _ _ => Polynomial.leadingCoeff_X_sub_C _
        rw [Polynomial.leadingCoeff,
            Polynomial.natDegree_prod _ _ fun x hx => Polynomial.X_sub_C_ne_zero _]
          at h_leading_coeff
        simp_all only [map_natCast]
        simpa [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] using h_leading_coeff
      · intro i j hij
        simp only [Matrix.of_apply]
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
        erw [Polynomial.natDegree_prod _ _ fun x hx => Polynomial.X_sub_C_ne_zero _]
        erw [Finset.sum_congr rfl fun _ _ => Polynomial.natDegree_X_sub_C _]
        simp_all only [sum_const, card_range, smul_eq_mul, mul_one, Fin.val_fin_lt]
    -- Since $M$ is upper triangular with ones on the diagonal, its determinant is 1.
    have h_det_M : Matrix.det M = 1 := by
      rw [Matrix.det_of_isUpperTriangular]
      · simp_all only [gt_iff_lt, prod_const_one]
      · simp_all only [gt_iff_lt]
        obtain ⟨left, right⟩ := hM
        obtain ⟨left_1, right⟩ := right
        exact right
    simp_all only [gt_iff_lt, det_mul, mul_one]

/--
@isnad1 id=eq.0h2v.s5.237752dd102f from=translated src=- shape=f6331ba5 vocab=15525733
-/
lemma fallingFactorial_eq_factorial_div (n k : ℕ) :
  fallingFactorial n k = if k ≤ n then n.factorial / (n - k).factorial else 0 := by
    unfold fallingFactorial
    rcases le_or_gt k n with hn | hk
    · simp_all only [↓reduceIte]
      split
      next h =>
        subst h
        simp_all only [zero_le, tsub_zero]
        rw [Nat.div_self (Nat.factorial_pos _)]
      next h =>
        rw [Nat.div_eq_of_eq_mul_right]
        · positivity
        · rw [← Nat.choose_mul_factorial_mul_factorial hn]
          rw [mul_comm]
          congr 1
          rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
          rw [Nat.descFactorial_eq_prod_range]
    · split
      next h =>
        subst h
        simp_all only [not_lt_zero]
      next h =>
        split
        next h_1 =>
          linarith
        next h_1 =>
          simp_all only [not_le]
          rw [Finset.prod_eq_zero_iff]
          simp_all only [mem_range]
          exact ⟨n, hk, by simp⟩

/-- Symmetric group sum expression C = ∑_{σ∈S_{k + 1}} (-1)^{sign(σ)} * m! / ∏ᵢ (cᵢ - σ(i))!
    Corrected to use proper sign and handle 0 case. -/
def symmetricSumFixed (c : Fin (k + 1) → ℕ) (m : ℕ) : ℚ :=
  ∑ σ : Equiv.Perm (Fin (k + 1)),
    if (∀ i, σ i ≤ c i) then
      ((σ.sign : ℤ) : ℚ) *
      ((m.factorial : ℚ) / ∏ i : Fin (k + 1), ((c i - (σ i : ℕ)).factorial : ℚ))
    else 0

/--
@isnad1 id=eq.0h3v.s4.ea68c75a0976 from=translated src=- shape=930423c8 vocab=2c568bcc
-/
lemma symmetricSumFixed_eq_expectedValue (c : Fin (k + 1) → ℕ) (m : ℕ) :
  symmetricSumFixed c m = expectedValue c m := by
    -- By definition of $expected\_value$, we know that
    -- $expected\_value c m = \frac{m!}{\prod_{i=0}^k c_i!} \cdot \prod_{i > j} (c_i - c_j)$.
    have h_def : expectedValue c m = (m.factorial : ℚ) *
        Matrix.det (vandermondeMatrix c) / (∏ i, ((c i).factorial : ℚ)) := by
      -- The determinant of the Vandermonde matrix is the product of (c_i - c_j) for i > j.
      have h_det_vandermonde : Matrix.det (vandermondeMatrix c) = ∏ i, ∏ j,
          if j.val < i.val then ((c i : ℚ) - (c j : ℚ)) else 1 := by
        -- By definition of Vandermonde matrix, we know that its determinant is given by the product
        -- of the differences of the entries.
        have h_vandermonde_det : ∀ (x : Fin (k + 1) → ℚ),
            Matrix.det (Matrix.of (fun i j => x i ^ j.val)) = ∏ i : Fin (k + 1), ∏ j : Fin (k + 1),
            if j.val < i.val then (x i - x j) else 1 := by
          intro x
          erw [Matrix.det_vandermonde]
          rw [Finset.prod_comm]
          simp +decide [Finset.prod_ite, Finset.filter_lt_eq_Ioi]
        convert h_vandermonde_det (fun i => c i) using 2 with i j
        simp [vandermondeMatrix]
      unfold expectedValue
      simp_all only [Fin.val_fin_lt]
    unfold symmetricSumFixed
    -- We'll use the fact that $\det(\text{falling\_factorial\_matrix} c) = \sum_{\sigma}
    -- \text{sgn}(\sigma) \prod_i (c_i)_{\sigma(i)}$.
    have h_det_fallingFactorial : Matrix.det (fallingFactorialMatrix c) = ∑ σ :
        Equiv.Perm (Fin (k + 1)), (Equiv.Perm.sign σ : ℚ) *
        (∏ i, (fallingFactorial (c i) (σ i).val : ℚ)) := by
      rw [Matrix.det_apply']
      refine Finset.sum_bij (fun σ _ => σ.symm) ?_ ?_ ?_ ?_
      · intro a ha
        simp_all only [mem_univ]
      · intro a₁ ha₁ a₂ ha₂ a
        simp_all only [mem_univ]
        simpa using congr_arg Equiv.symm a
      · intro b a
        simp_all only [mem_univ, exists_const]
        exact ⟨b.symm, by simp +decide⟩
      · intro a ha
        simp_all only [Equiv.Perm.sign_symm, mul_eq_mul_left_iff, Int.cast_eq_zero, Units.ne_zero,
            or_false]
        simp_all only [mem_univ]
        conv_rhs => rw [← Equiv.prod_comp a]
        exact Finset.prod_congr rfl fun i _ => by
          simp_all only [mem_univ, Equiv.symm_apply_apply]
          rfl
    -- By definition of $falling\_factorial$, we know that $\prod_i (c_i)_{\sigma(i)} = \prod_i
    -- \frac{c_i!}{(c_i - \sigma(i))!}$ if $\forall i, \sigma(i) \le c_i$, else 0.
    have h_fallingFactorial : ∀ σ : Equiv.Perm (Fin (k + 1)),
        (∏ i, (fallingFactorial (c i) (σ i).val : ℚ)) = if ∀ i,
        (σ i).val ≤ c i then (∏ i, ((c i).factorial : ℚ)) / (∏ i,
            ((c i - (σ i).val).factorial : ℚ)) else 0 := by
      intro σ; split_ifs
          <;> simp_all? (config := {decide := Bool.true}) [fallingFactorial_eq_factorial_div]
      · rw [← Finset.prod_div_distrib, Finset.prod_congr rfl]
        intros
        rw [Nat.cast_div (Nat.factorial_dvd_factorial <| Nat.sub_le _ _) (by positivity)]
      · rw [Finset.prod_eq_zero_iff]
        rename_i h
        simp_all only [mem_univ, ite_eq_right_iff, Nat.cast_eq_zero, Nat.div_eq_zero_iff, true_and]
        obtain ⟨w, h⟩ := h
        exact ⟨w, fun hw => False.elim <| h.not_ge hw⟩
    -- By combining the results from h_det_fallingFactorial and h_fallingFactorial, we can
    -- conclude the proof.
    have h_final : Matrix.det (vandermondeMatrix c) = (∏ i, ((c i).factorial : ℚ)) *
        (∑ σ : Equiv.Perm (Fin (k + 1)), (Equiv.Perm.sign σ : ℚ) * (if ∀ i,
            (σ i).val ≤ c i then 1 / (∏ i, ((c i - (σ i).val).factorial : ℚ)) else 0)) := by
      convert h_det_fallingFactorial using 1
      · convert det_fallingFactorial_eq_det_vandermonde c |> Eq.symm
      · rw [Finset.mul_sum _ _ _]; exact Finset.sum_congr rfl fun _ _ =>
          by rw [h_fallingFactorial]; split_ifs <;> ring
    have hfactorials : (∏ i, ((c i).factorial : ℚ)) ≠ 0 := by
      norm_num [Finset.prod_eq_zero_iff, Nat.factorial_ne_zero]
    rw [h_def, h_final, mul_left_comm, mul_div_cancel_left₀ _ hfactorials, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    split_ifs <;> ring

end AristotleLemmas
