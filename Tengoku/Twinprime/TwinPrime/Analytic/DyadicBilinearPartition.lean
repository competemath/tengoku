import Tengoku.Twinprime.TwinPrime.Analytic.DyadicNatPartition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact dyadic partitions for supported bilinear sums

An upper support bound eliminates the padding mask. Applying the resulting
one-variable identity twice partitions a bilinear sum into global dyadic
boxes, without changing either lower cutoff or a product restriction.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

theorem sum_Ioc_eq_dyadic_of_support {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (T : ℕ) (hf : ∀ n, T < n → f n = 0) :
    (∑ n ∈ Ioc 0 T, f n) =
      ∑ k ∈ range (dyadicNatDepth T), ∑ n ∈ Ico (2 ^ k) (2 ^ k + 2 ^ k), f n := by
  rw [sum_Ioc_eq_dyadic_masked f T]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro n _
  by_cases hn : n ≤ T
  · simp [hn]
  · simp [hn, hf n (Nat.lt_of_not_ge hn)]

theorem sum_Ioc_product_eq_dyadic_of_support {α : Type*} [AddCommMonoid α]
    (f : ℕ → ℕ → α) (T : ℕ)
    (hf : ∀ m n, T < m ∨ T < n → f m n = 0) :
    (∑ m ∈ Ioc 0 T, ∑ n ∈ Ioc 0 T, f m n) =
      ∑ k ∈ range (dyadicNatDepth T), ∑ j ∈ range (dyadicNatDepth T),
        ∑ m ∈ Ico (2 ^ k) (2 ^ k + 2 ^ k),
          ∑ n ∈ Ico (2 ^ j) (2 ^ j + 2 ^ j), f m n := by
  have hinner (m : ℕ) := sum_Ioc_eq_dyadic_of_support (f m) T
    (fun n hn => hf m n (Or.inr hn))
  calc
    _ = ∑ k ∈ range (dyadicNatDepth T), ∑ m ∈ Ico (2 ^ k) (2 ^ k + 2 ^ k),
        ∑ n ∈ Ioc 0 T, f m n :=
      sum_Ioc_eq_dyadic_of_support (fun m => ∑ n ∈ Ioc 0 T, f m n) T
        (fun m hm => sum_eq_zero fun n _ => hf m n (Or.inl hm))
    _ = ∑ k ∈ range (dyadicNatDepth T), ∑ m ∈ Ico (2 ^ k) (2 ^ k + 2 ^ k),
        ∑ j ∈ range (dyadicNatDepth T), ∑ n ∈ Ico (2 ^ j) (2 ^ j + 2 ^ j), f m n := by
      simp_rw [hinner]
    _ = _ := by
      apply sum_congr rfl
      intro k _
      rw [sum_comm]

end TwinPrime.Analytic
