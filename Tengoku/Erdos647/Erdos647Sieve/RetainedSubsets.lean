/-
Quantitative counting of the truncated prime-subset family.
New proof source: not compiled in the assistant environment.
Each subset is counted once, not once for every truncation degree.
-/
import Tengoku.Erdos647.Erdos647Sieve.PrimeSubsetProducts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve

/-- All retained subsets, regardless of their degree.-/
def retainedSubsets (P : Finset ℕ) (J : ℕ) : Finset (Finset ℕ) := by
  classical
  exact P.powerset.filter (fun S : Finset ℕ => S.card ≤ J)

/--
@isnad1 id=iff.0h3v.s5.4033a9410d49 from=translated src=- shape=e616f302 vocab=f8339b00
-/
theorem mem_retainedSubsets (P S : Finset ℕ) (J : ℕ) :
    S ∈ retainedSubsets P J ↔ S ⊆ P ∧ S.card ≤ J := by
  classical
  simp only [retainedSubsets, Finset.mem_filter, Finset.mem_powerset]

/-- The degree partition carries no factor J+1.
@isnad1 id=eq.0h3v.s5.ad1284a8c624 from=translated src=- shape=7715630b vocab=209f5f8f
-/
theorem sum_powersetCard_le_eq_retained (P : Finset ℕ) (J : ℕ)
    (f : Finset ℕ → ℝ) :
    (∑ j ∈ Finset.range (J + 1), ∑ S ∈ P.powersetCard j, f S) =
      ∑ S ∈ retainedSubsets P J, f S := by
  classical
  simpa only [Finset.powersetCard_eq_filter, retainedSubsets,
    Finset.mem_range, Nat.lt_succ_iff] using
    (Finset.sum_fiberwise_eq_sum_filter P.powerset (Finset.range (J + 1))
      (fun S : Finset ℕ => S.card) f)

/-- Elementary monotonicity in the exponent, with its base condition explicit.
@isnad1 id=le.2h3v.s5.9cdba7af3558 from=translated src=- shape=b70361c3 vocab=7ff6bede
-/
theorem real_pow_mono_of_one_le (x : ℝ) (hx : 1 ≤ x)
    (a b : ℕ) (hab : a ≤ b) : x ^ a ≤ x ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  have hc : 1 ≤ x ^ c := by
    induction c with
    | zero => simp
    | succ c ih =>
      rw [pow_succ]
      exact one_le_mul_of_one_le_of_one_le ih hx
  rw [pow_add]
  exact le_mul_of_one_le_right (pow_nonneg (by linarith : 0 ≤ x) a) hc

/-- Products of selected primes satisfy the exact real cutoff y^J.
@isnad1 id=le.3h4v.s6.c5c060da1354 from=translated src=- shape=ade03d2a vocab=35f955b8
-/
theorem retained_primeSubsetProduct_le (H : ℕ) (y : ℝ) (J : ℕ)
    (hH : 1 ≤ H) (hy : (H : ℝ) < y) (S : Finset ℕ)
    (hS : S ∈ retainedSubsets (selectedPrimes H y) J) :
    (primeSubsetProduct S : ℝ) ≤ y ^ J := by
  classical
  obtain ⟨hSP, hcard⟩ := (mem_retainedSubsets _ S J).mp hS
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hy1 : 1 ≤ y := le_trans hHr hy.le
  have hy0 : 0 ≤ y := by linarith
  have hle : ∀ p ∈ S, (p : ℝ) ≤ y := by
    intro p hp
    have hm : p ∈ (Finset.Icc (H + 1) (Nat.floor y)).filter Nat.Prime := hSP hp
    have hpfloor := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
    have hc : (p : ℝ) ≤ (Nat.floor y : ℝ) := by exact_mod_cast hpfloor
    exact hc.trans (Nat.floor_le hy0)
  calc
    (primeSubsetProduct S : ℝ) = ∏ p ∈ S, (p : ℝ) := by
      simp only [primeSubsetProduct, Nat.cast_prod]
    _ ≤ ∏ _p ∈ S, y := Finset.prod_le_prod
      (fun p _hp => Nat.cast_nonneg p) hle
    _ = y ^ S.card := Finset.prod_const y
    _ ≤ y ^ J := real_pow_mono_of_one_le y hy1 _ _ hcard

/-- Injective product encoding bounds the complete truncated family at once.
@isnad1 id=le.2h3v.s5.718236b1d2df from=translated src=- shape=b6985d82 vocab=356606cb
-/
theorem card_retainedSubsets_le_floor (H : ℕ) (y : ℝ) (J : ℕ)
    (hH : 1 ≤ H) (hy : (H : ℝ) < y) :
    (retainedSubsets (selectedPrimes H y) J).card ≤ Nat.floor (y ^ J) := by
  classical
  apply card_primeSubsetFamily_le (selectedPrimes H y)
  · intro p hp
    have hm : p ∈ (Finset.Icc (H + 1) (Nat.floor y)).filter Nat.Prime := hp
    exact (Finset.mem_filter.mp hm).2
  · intro S hS
    exact ((mem_retainedSubsets _ S J).mp hS).1
  · intro S hS
    exact Nat.le_floor (retained_primeSubsetProduct_le H y J hH hy S hS)

/--
@isnad1 id=le.2h3v.s5.988ac599751b from=translated src=- shape=e8aaea33 vocab=c2888c36
-/
theorem card_retainedSubsets_cast_le (H : ℕ) (y : ℝ) (J : ℕ)
    (hH : 1 ≤ H) (hy : (H : ℝ) < y) :
    ((retainedSubsets (selectedPrimes H y) J).card : ℝ) ≤ y ^ J := by
  have hc : ((retainedSubsets (selectedPrimes H y) J).card : ℝ) ≤
      (Nat.floor (y ^ J) : ℝ) := by
    exact_mod_cast card_retainedSubsets_le_floor H y J hH hy
  have hy0 : 0 ≤ y := le_trans (Nat.cast_nonneg H) hy.le
  exact hc.trans (Nat.floor_le (pow_nonneg hy0 J))

end Erdos647Sieve
end
