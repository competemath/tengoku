/-
Complementary-product exponential bound for the finite moment.
NEW IMPLEMENTATION: not compiled in the assistant environment.
Separate from the coefficient bound so compiler diagnostics are independent.
-/
import Tengoku.Erdos647.Erdos647Sieve.Bonferroni

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
noncomputable section
namespace Erdos647Sieve.Bonferroni

/-- The complementary product is at most exp of minus the total weight.
The nonnegative product condition is kept explicit in the induction.
@isnad1 id=le.1h1v.s5.4939383cd1d6 from=translated src=- shape=5cd4b4d7 vocab=ab65a8cb
-/
theorem avoidProduct_le_exp_neg_sum : ∀ (xs : List ℝ),
    (∀ a ∈ xs, 0 ≤ a ∧ a ≤ 1) →
    avoidProduct xs ≤ Real.exp (-xs.sum) := by
  intro xs
  induction xs with
  | nil => intro _; simp [avoidProduct]
  | cons a xs ih =>
      intro h
      have hxs : ∀ b ∈ xs, 0 ≤ b ∧ b ≤ 1 := fun b hb => h b (by simp [hb])
      calc
        avoidProduct (a :: xs) = (1 - a) * avoidProduct xs := rfl
        _ ≤ Real.exp (-a) * Real.exp (-xs.sum) :=
          mul_le_mul (Real.one_sub_le_exp_neg a) (ih hxs)
            (avoidProduct_bounds xs hxs).1 (Real.exp_nonneg (-a))
        _ = Real.exp (-(a :: xs).sum) := by
          rw [← Real.exp_add, List.sum_cons]
          congr 1
          ring

end Erdos647Sieve.Bonferroni
end
