/-
OEIS A347722: pure algebra. Any `D`, `F` satisfying the boundary values `hD0`, `hF0` and the
recurrences `hDs`, `hFs` have closed forms in terms of `h` and `f`; in particular
`D n n = f n`, and `D n n - F n n` is the alternating binomial sum occurring in `formula`.
-/
import Tengoku.OeisLean.OeisLean.A347722.Defs
import Tengoku.Seed.Algebra.BigOperators.Intervals
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms A347722.diff_eq_sum` (it only prints; the queue checks the axioms of every declaration). -/

namespace A347722

namespace Closed

open Finset

/-- `mu c j = C(c, 2j) (2j-1)!!`, the number of `j`-edge matchings on `c` points.-/
def mu (c j : ℕ) : ℤ := (c.choose (2 * j) : ℤ) * (Nat.doubleFactorial (2 * j - 1) : ℤ)

theorem mu_zero (c : ℕ) : mu c 0 = 1 := by simp [mu]

theorem mu_eq_zero {c j : ℕ} (hcj : c < 2 * j) : mu c j = 0 := by
  simp [mu, Nat.choose_eq_zero_of_lt hcj]

theorem mu_succ (c j : ℕ) : mu (c + 1) (j + 1) = mu c (j + 1) + c * mu (c - 1) j := by
  have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
  have e2 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have hk : (c.choose (2 * j + 1) : ℤ) * (2 * j + 1) = c * ((c - 1).choose (2 * j) : ℤ) := by
    cases c with
    | zero => simp
    | succ c =>
      have := Nat.add_one_mul_choose_eq c (2 * j)
      simp only [Nat.add_sub_cancel]
      exact_mod_cast this.symm
  have hd : (Nat.doubleFactorial (2 * j + 1) : ℤ)
      = (2 * j + 1) * (Nat.doubleFactorial (2 * j - 1) : ℤ) := by
    exact_mod_cast Nat.doubleFactorial_add_one (2 * j)
  unfold mu
  rw [e2, e1, Nat.choose_succ_succ, hd]
  push_cast
  linear_combination (Nat.doubleFactorial (2 * j - 1) : ℤ) * hk

/-- The sum defining `f`, with free parameters: `Sum_{j<N} (-1)^j mu(c,j) h(n-2j)`.-/
def T (c n N : ℕ) : ℤ := ∑ j ∈ range N, (-1) ^ j * mu c j * (h (n - 2 * j) : ℤ)

theorem T_succ (c n M : ℕ) :
    T (c + 1) n (M + 1) = T c n (M + 1) - c * T (c - 1) (n - 2) M := by
  unfold T
  rw [sum_range_succ', sum_range_succ', mul_sum]
  simp only [mu_zero]
  have : ∑ j ∈ range M, (-1 : ℤ) ^ (j + 1) * mu (c + 1) (j + 1) * (h (n - 2 * (j + 1)) : ℤ)
      = ∑ j ∈ range M, (-1 : ℤ) ^ (j + 1) * mu c (j + 1) * (h (n - 2 * (j + 1)) : ℤ)
        - ∑ j ∈ range M, (c : ℤ) * ((-1) ^ j * mu (c - 1) j * (h (n - 2 - 2 * j) : ℤ)) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    have e : n - 2 - 2 * j = n - 2 * (j + 1) := by omega
    rw [e, mu_succ]
    ring
  linarith

/-- Closed form of `D`.-/
theorem D_eq (D' : ℕ → ℕ → ℕ)
    (hD0 : ∀ n, D' n 0 = h n)
    (hDs : ∀ n c, c < n → D' n (c + 1) + c * D' (n - 2) (c - 1) = D' n c) :
    ∀ c n N, c ≤ n → c < 2 * N → (D' n c : ℤ) = T c n N := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro n N hcn hcN
    cases c with
    | zero =>
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      unfold T
      rw [sum_range_succ', sum_eq_zero, hD0]
      · simp [mu_zero]
      · intro j _
        rw [mu_eq_zero (by omega)]
        ring
    | succ c =>
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      have h1 : (D' n (c + 1) : ℤ) + c * (D' (n - 2) (c - 1) : ℤ) = D' n c := by
        exact_mod_cast hDs n c (by omega)
      have h2 : (D' n c : ℤ) = T c n (M + 1) := ih c (by omega) n (M + 1) (by omega) (by omega)
      have h3 : (c : ℤ) * (D' (n - 2) (c - 1) : ℤ) = c * T (c - 1) (n - 2) M := by
        cases c with
        | zero => simp
        | succ c =>
          rw [ih (c + 1 - 1) (by omega) (n - 2) M (by omega) (by omega)]
      rw [T_succ]
      linarith

theorem T_self (n : ℕ) : T n n (n / 2 + 1) = f n := by
  unfold T f
  refine sum_congr rfl fun j _ => ?_
  unfold mu
  ring

/-- Closed form of `F`, given `D n n = f n`.-/
theorem F_eq (D' F' : ℕ → ℕ → ℕ)
    (hDf : ∀ n, (D' n n : ℤ) = f n)
    (hF0 : ∀ n, F' n 0 = D' n n)
    (hFs : ∀ n d, d ≤ n → F' (n + 1) (d + 1) + F' n d = F' (n + 1) d) :
    ∀ d n, d ≤ n →
      (F' n d : ℤ) = ∑ i ∈ range (d + 1), (-1) ^ i * (d.choose i : ℤ) * f (n - i) := by
  intro d
  induction d with
  | zero =>
    intro n _
    rw [hF0, hDf]
    simp
  | succ d ih =>
    intro n hdn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 : (F' (m + 1) (d + 1) : ℤ) + F' m d = F' (m + 1) d := by
      exact_mod_cast hFs m d (by omega)
    have h2 := ih (m + 1) (by omega)
    have h3 := ih m (by omega)
    -- peel the `i = 0` term of the sum for `(d, m+1)`, extended by a vanishing top term
    have e1 : ∑ i ∈ range (d + 1), (-1 : ℤ) ^ i * (d.choose i : ℤ) * f (m + 1 - i)
        = ∑ i ∈ range (d + 1), (-1 : ℤ) ^ (i + 1) * (d.choose (i + 1) : ℤ) * f (m + 1 - (i + 1))
          + f (m + 1) := by
      have a := sum_range_succ (fun i => (-1 : ℤ) ^ i * (d.choose i : ℤ) * f (m + 1 - i)) (d + 1)
      have b := sum_range_succ' (fun i => (-1 : ℤ) ^ i * (d.choose i : ℤ) * f (m + 1 - i)) (d + 1)
      simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero] at a
      simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] at b
      rw [← a, b]
    have e2 : ∑ i ∈ range (d + 1),
          (-1 : ℤ) ^ (i + 1) * ((d + 1).choose (i + 1) : ℤ) * f (m + 1 - (i + 1))
        = ∑ i ∈ range (d + 1), (-1 : ℤ) ^ (i + 1) * (d.choose (i + 1) : ℤ) * f (m + 1 - (i + 1))
          - ∑ i ∈ range (d + 1), (-1 : ℤ) ^ i * (d.choose i : ℤ) * f (m - i) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [Nat.choose_succ_succ, Nat.add_sub_add_right]
      push_cast
      ring
    rw [sum_range_succ']
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    linarith

end Closed

open Closed in
/-- Pure algebra: if `D` starts at `h` and satisfies the "forbid one more bad point" recurrence,
and `F` starts at the diagonal of `D` and satisfies the "forbid one more isolated point"
recurrence, then `D n n = f n` and `D n n - F n n` is the alternating sum of `formula`.-/
theorem diff_eq_sum (D F : ℕ → ℕ → ℕ)
    (hD0 : ∀ n, D n 0 = h n)
    (hDs : ∀ n c, c < n → D n (c + 1) + c * D (n - 2) (c - 1) = D n c)
    (hF0 : ∀ n, F n 0 = D n n)
    (hFs : ∀ n d, d ≤ n → F (n + 1) (d + 1) + F n d = F (n + 1) d)
    (n : ℕ) :
    (D n n : ℤ) - (F n n : ℤ)
      = ∑ i ∈ Finset.Icc 1 n, (-1) ^ (i + 1) * (n.choose i : ℤ) * f (n - i) := by
  have hDf : ∀ n, (D n n : ℤ) = f n := fun n => by
    rw [D_eq D hD0 hDs n n (n / 2 + 1) le_rfl (by omega), T_self]
  have hI : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [F_eq D F hDf hF0 hFs n n le_rfl, hDf, Finset.sum_range_succ', hI,
    Finset.sum_Ico_eq_sum_range]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
    Nat.add_sub_cancel]
  have : ∑ k ∈ Finset.range n, (-1 : ℤ) ^ (1 + k + 1) * (n.choose (1 + k) : ℤ) * f (n - (1 + k))
      = -∑ k ∈ Finset.range n, (-1 : ℤ) ^ (k + 1) * (n.choose (k + 1) : ℤ) * f (n - (k + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.add_comm 1 k]
    ring
  linarith

end A347722

