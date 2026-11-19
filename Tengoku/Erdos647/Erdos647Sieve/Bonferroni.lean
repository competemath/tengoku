/-
Algebraic weighted Bonferroni component.
STATUS: PATCHED AFTER USER COMPILER FEEDBACK; NOT RECOMPILED HERE.
No theorem in this file is being reported as kernel-verified.

The recursive definitions are ordinary finite algebra. `truncation_eq_sum`
connects the recurrence to the alternating elementary-symmetric sum. The
remaining sieve work must connect the list coefficients to prime subsets.
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve.Bonferroni

/-- Elementary symmetric coefficients of a finite list of weights.-/
def elementary : List ℝ → ℕ → ℝ
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | a :: xs, j + 1 => elementary xs (j + 1) + a * elementary xs j

/-- Product of the complementary weights.-/
def avoidProduct : List ℝ → ℝ
  | [] => 1
  | a :: xs => (1 - a) * avoidProduct xs

/-- Alternating truncation, expressed by its insertion recurrence.-/
def truncation : List ℝ → ℕ → ℝ
  | [], _ => 1
  | _ :: _, 0 => 1
  | a :: xs, j + 1 => truncation xs (j + 1) - a * truncation xs j

/--
@isnad1 id=eq.0h1v.s4.445a8b9555fe from=translated src=- shape=18650b26 vocab=425dfa31
-/
@[simp] theorem elementary_zero (xs : List ℝ) : elementary xs 0 = 1 := by
  cases xs <;> rfl

/--
@isnad1 id=eq.0h1v.s4.e2f2a44dec57 from=translated src=- shape=18650b26 vocab=e1612af9
-/
@[simp] theorem truncation_zero (xs : List ℝ) : truncation xs 0 = 1 := by
  cases xs <;> rfl

/--
@isnad1 id=le.1h2v.s5.b7cdad05c909 from=translated src=- shape=bb038013 vocab=916a6691
-/
theorem elementary_nonneg : ∀ (xs : List ℝ),
    (∀ a ∈ xs, 0 ≤ a) → ∀ j, 0 ≤ elementary xs j := by
  intro xs
  induction xs with
  | nil =>
      intro _ j
      cases j <;> norm_num [elementary]
  | cons a xs ih =>
      intro h j
      have ha : 0 ≤ a := h a (by simp)
      have hxs : ∀ b ∈ xs, 0 ≤ b := fun b hb => h b (by simp [hb])
      cases j with
      | zero => norm_num
      | succ j =>
          exact add_nonneg (ih hxs (j + 1)) (mul_nonneg ha (ih hxs j))

/--
@isnad1 id=and.1h1v.s5.ecab2bb58e91 from=translated src=- shape=7bca0277 vocab=339d0740
-/
theorem avoidProduct_bounds : ∀ (xs : List ℝ),
    (∀ a ∈ xs, 0 ≤ a ∧ a ≤ 1) →
    0 ≤ avoidProduct xs ∧ avoidProduct xs ≤ 1 := by
  intro xs
  induction xs with
  | nil => intro _; norm_num [avoidProduct]
  | cons a xs ih =>
      intro h
      have ha := h a (by simp)
      have hxs : ∀ b ∈ xs, 0 ≤ b ∧ b ≤ 1 := fun b hb => h b (by simp [hb])
      obtain ⟨h0, h1⟩ := ih hxs
      change 0 ≤ (1 - a) * avoidProduct xs ∧ (1 - a) * avoidProduct xs ≤ 1
      constructor
      · exact mul_nonneg (sub_nonneg.mpr ha.2) h0
      · calc
          (1 - a) * avoidProduct xs ≤ 1 * 1 :=
            mul_le_mul (by linarith : 1 - a ≤ 1) h1 h0 (by norm_num)
          _ = 1 := by ring

/-- Link the recursive complementary product to the ordinary list product.
@isnad1 id=eq.0h1v.s4.134af5b1d969 from=translated src=- shape=55a91afa vocab=3158822f
-/
theorem avoidProduct_eq_prod (xs : List ℝ) :
    avoidProduct xs = (xs.map (fun a => 1 - a)).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [avoidProduct, List.map_cons, List.prod_cons, ih]

/-- The difference between consecutive truncations is the next signed coefficient.
@isnad1 id=eq.0h2v.s6.59654a915ef6 from=translated src=- shape=9e9b7e76 vocab=439ec11e
-/
theorem truncation_step (xs : List ℝ) (j : ℕ) :
    truncation xs (j + 1) = truncation xs j +
      (-1 : ℝ) ^ (j + 1) * elementary xs (j + 1) := by
  induction xs generalizing j with
  | nil => simp [truncation, elementary]
  | cons a xs ih =>
      cases j with
      | zero =>
          -- Normalize the zero exponent case explicitly; do not ask linarith
          -- to expand a product with the unreduced exponent 0 + 1.
          have h : truncation xs 1 = 1 - elementary xs 1 := by
            simpa [sub_eq_add_neg] using ih 0
          change truncation xs 1 - a * truncation xs 0 =
            1 + (-1 : ℝ) ^ 1 * (elementary xs 1 + a * elementary xs 0)
          rw [h, truncation_zero, elementary_zero]
          ring
      | succ j =>
          simp only [truncation, elementary]
          simp only [ih (j + 1), ih j, pow_succ]
          ring

/--
@isnad1 id=eq.0h2v.s5.2cddb3f83438 from=translated src=- shape=baa821cf vocab=4eb99b24
-/
theorem truncation_eq_sum (xs : List ℝ) (J : ℕ) :
    truncation xs J =
      ∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j * elementary xs j := by
  induction J with
  | zero => simp
  | succ J ih =>
      calc
        truncation xs (J + 1) = truncation xs J +
            (-1 : ℝ) ^ (J + 1) * elementary xs (J + 1) := truncation_step xs J
        _ = (∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j * elementary xs j) +
            (-1 : ℝ) ^ (J + 1) * elementary xs (J + 1) := by rw [ih]
        _ = ∑ j ∈ Finset.range (J + 1 + 1),
            (-1 : ℝ) ^ j * elementary xs j := (Finset.sum_range_succ _ _).symm

/-- All parities at once; the sign is the central Bonferroni invariant.
@isnad1 id=le.1h2v.s6.568d848dd827 from=translated src=- shape=0c5244d9 vocab=3358a6f0
-/
theorem signedError_nonneg : ∀ (xs : List ℝ),
    (∀ a ∈ xs, 0 ≤ a ∧ a ≤ 1) → ∀ J,
    0 ≤ (-1 : ℝ) ^ J * (truncation xs J - avoidProduct xs) := by
  intro xs
  induction xs with
  | nil => intro _ J; simp [truncation, avoidProduct]
  | cons a xs ih =>
      intro h J
      have ha := h a (by simp)
      have hxs : ∀ b ∈ xs, 0 ≤ b ∧ b ≤ 1 := fun b hb => h b (by simp [hb])
      cases J with
      | zero =>
          have hp := (avoidProduct_bounds (a :: xs) h).2
          simpa only [pow_zero, truncation_zero, one_mul] using sub_nonneg.mpr hp
      | succ J =>
          have hnext := ih hxs (J + 1)
          have hprev := mul_nonneg ha.1 (ih hxs J)
          calc
            0 ≤ (-1 : ℝ) ^ (J + 1) * (truncation xs (J + 1) - avoidProduct xs) +
                a * ((-1 : ℝ) ^ J * (truncation xs J - avoidProduct xs)) :=
              add_nonneg hnext hprev
            _ = (-1 : ℝ) ^ (J + 1) *
                (truncation (a :: xs) (J + 1) - avoidProduct (a :: xs)) := by
              simp only [truncation, avoidProduct, pow_succ]
              ring

/-- Weighted Bonferroni, including the empty list and arbitrary even truncation order.
@isnad1 id=and.2h2v.s6.ecdda7081f26 from=translated src=- shape=1f12b1e1 vocab=5ae027ad
-/
theorem even_bounds (xs : List ℝ) (h : ∀ a ∈ xs, 0 ≤ a ∧ a ≤ 1)
    (J : ℕ) (hJ : Even J) :
    avoidProduct xs ≤ truncation xs J ∧
      truncation xs J ≤ avoidProduct xs + elementary xs (J + 1) := by
  have hs : (-1 : ℝ) ^ J = 1 := hJ.neg_one_pow
  have hsnext : (-1 : ℝ) ^ (J + 1) = -1 := by rw [pow_succ, hs]; ring
  have hlo := signedError_nonneg xs h J
  have hhi := signedError_nonneg xs h (J + 1)
  have hstep := truncation_step xs J
  rw [hs] at hlo
  rw [hsnext] at hhi hstep
  constructor <;> linarith

/-- The same result stated as actual alternating sums, not only a recursive surrogate.
@isnad1 id=and.2h2v.s7.dea9303dfc47 from=translated src=- shape=19c4e5f3 vocab=87ad0dfa
-/
theorem even_sum_bounds (xs : List ℝ) (h : ∀ a ∈ xs, 0 ≤ a ∧ a ≤ 1)
    (J : ℕ) (hJ : Even J) :
    avoidProduct xs ≤ (∑ j ∈ Finset.range (J + 1),
      (-1 : ℝ) ^ j * elementary xs j) ∧
    (∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j * elementary xs j)
      ≤ avoidProduct xs + elementary xs (J + 1) := by
  simpa only [← truncation_eq_sum] using even_bounds xs h J hJ

end Erdos647Sieve.Bonferroni
end
