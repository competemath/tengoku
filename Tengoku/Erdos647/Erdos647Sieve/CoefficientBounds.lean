/-
Finite coefficient estimates for the accepted weighted Bonferroni representation.
NEW IMPLEMENTATION: not compiled in the assistant environment.
All existing source files are left unchanged. No prime-counting theorem is used.
-/
import Tengoku.Erdos647.Erdos647Sieve.Bonferroni

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve.Bonferroni

/-- The constant and linear terms of (s+a)^(q+1) give a lower bound for
nonnegative s,a. This finite induction avoids a binomial-sum API.-/
theorem pow_add_linear_le (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (q : ℕ) :
    s ^ (q + 1) + ((q : ℝ) + 1) * a * s ^ q ≤ (s + a) ^ (q + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hextra : 0 ≤ ((q : ℝ) + 1) * a * a * s ^ q := by positivity
      have hmul := mul_le_mul_of_nonneg_right ih (add_nonneg hs ha)
      simp only [Nat.cast_succ]
      calc
        s ^ (q + 1 + 1) + (((q : ℝ) + 1) + 1) * a * s ^ (q + 1)
            ≤ (s ^ (q + 1 + 1) + (((q : ℝ) + 1) + 1) * a * s ^ (q + 1)) +
                ((q : ℝ) + 1) * a * a * s ^ q :=
          le_add_of_nonneg_right hextra
        _ = (s ^ (q + 1) + ((q : ℝ) + 1) * a * s ^ q) * (s + a) := by
          simp only [pow_succ]
          ring
        _ ≤ (s + a) ^ (q + 1) * (s + a) := hmul
        _ = (s + a) ^ (q + 1 + 1) := (pow_succ _ _).symm

/-- q! times the elementary symmetric coefficient is bounded by the q-th
power of the sum. Repeated weights are retained, not converted to a finset.-/
theorem factorial_mul_elementary_le_pow_sum : ∀ (xs : List ℝ),
    (∀ a ∈ xs, 0 ≤ a) → ∀ q : ℕ,
    (Nat.factorial q : ℝ) * elementary xs q ≤ xs.sum ^ q := by
  intro xs
  induction xs with
  | nil =>
      intro _ q
      cases q <;> simp [elementary]
  | cons a xs ih =>
      intro h q
      have ha : 0 ≤ a := h a (by simp)
      have hxs : ∀ b ∈ xs, 0 ≤ b := fun b hb => h b (by simp [hb])
      have hs : 0 ≤ xs.sum := List.sum_nonneg hxs
      cases q with
      | zero => simp
      | succ q =>
          have htop := ih hxs (q + 1)
          have hprev := ih hxs q
          have hcoef : 0 ≤ ((q : ℝ) + 1) * a := by positivity
          calc
            (Nat.factorial (q + 1) : ℝ) * elementary (a :: xs) (q + 1)
                = (Nat.factorial (q + 1) : ℝ) * elementary xs (q + 1) +
                  (((q : ℝ) + 1) * a) *
                    ((Nat.factorial q : ℝ) * elementary xs q) := by
                  simp only [elementary, Nat.factorial_succ, Nat.cast_mul,
                    Nat.cast_add, Nat.cast_one]
                  ring
            _ ≤ xs.sum ^ (q + 1) + (((q : ℝ) + 1) * a) * xs.sum ^ q :=
              add_le_add htop (mul_le_mul_of_nonneg_left hprev hcoef)
            _ ≤ (xs.sum + a) ^ (q + 1) := pow_add_linear_le xs.sum a hs ha q
            _ = (a :: xs).sum ^ (q + 1) := by rw [List.sum_cons, add_comm]

/-- The factorial denominator is positive, including at q=0.-/
theorem elementary_le_pow_sum_div_factorial (xs : List ℝ)
    (h : ∀ a ∈ xs, 0 ≤ a) (q : ℕ) :
    elementary xs q ≤ xs.sum ^ q / (Nat.factorial q : ℝ) := by
  have hfact : 0 < (Nat.factorial q : ℝ) := by
    exact_mod_cast Nat.factorial_pos q
  apply (le_div_iff₀ hfact).mpr
  simpa only [mul_comm] using factorial_mul_elementary_le_pow_sum xs h q

end Erdos647Sieve.Bonferroni
end
