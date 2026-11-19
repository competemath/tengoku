/-
Uniform discrepancy of the ACTUAL simultaneous-prime-hit count.
New proof source: not compiled in the assistant environment.
No root-count or distribution estimate is assumed as a theorem premise.
-/
import Tengoku.Erdos647.Erdos647Sieve.ProgressionCount
import Tengoku.Erdos647.Erdos647Sieve.WindowCRT
import Tengoku.Erdos647.Erdos647Sieve.SubsetWeightIdentities

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve

/-- The actual subset-hit count is the count of the actual root residue set.-/
theorem subsetHitCount_eq_windowRootResidues_count
    (I : Finset ℤ) (H : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    subsetHitCount I H S =
      (I.filter (fun n : ℤ => (n : ZMod (primeSubsetProduct S)) ∈
        windowRootResidues H (primeSubsetProduct S))).card := by
  classical
  rw [subsetHitCount_eq_modulus_count I H S hS]
  apply congrArg Finset.card
  apply Finset.ext
  intro n
  simp only [Finset.mem_filter,
    intCast_mem_windowRootResidues_iff H (primeSubsetProduct S)
      (primeSubsetProduct_pos S hS) n]

/-- One error at most one for each of the H^|S| roots.
A is any integer and X may be zero. Empty prime subsets are included.-/
theorem subsetHitCount_error_le
    (A : ℤ) (X H : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ H < p) :
    |(subsetHitCount (Finset.Icc (A + 1) (A + (X : ℤ))) H S : ℝ) -
      (X : ℝ) * ((H : ℝ) ^ S.card / (primeSubsetProduct S : ℝ))| ≤
        (H : ℝ) ^ S.card := by
  classical
  have hpr : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  have hd := primeSubsetProduct_pos S hpr
  have he := residueSetCount_error_le_card A X (primeSubsetProduct S)
    (windowRootResidues H (primeSubsetProduct S)) hd
  rw [← subsetHitCount_eq_windowRootResidues_count _ H S hpr,
    card_windowRootResidues_primeSubsetProduct H S hS] at he
  simpa only [Nat.cast_pow] using he

/-- The same exact discrepancy for a subset of the selected primes.-/
theorem selected_subsetHitCount_error_le
    (A : ℤ) (X H : ℕ) (y : ℝ) (S : Finset ℕ)
    (hS : S ⊆ selectedPrimes H y) :
    |(subsetHitCount (Finset.Icc (A + 1) (A + (X : ℤ))) H S : ℝ) -
      (X : ℝ) * ((H : ℝ) ^ S.card / (primeSubsetProduct S : ℝ))| ≤
        (H : ℝ) ^ S.card := by
  apply subsetHitCount_error_le
  intro p hp
  have hm : p ∈ (Finset.Icc (H + 1) (Nat.floor y)).filter Nat.Prime := hS hp
  obtain ⟨hI, hprime⟩ := Finset.mem_filter.mp hm
  exact ⟨hprime, by have := (Finset.mem_Icc.mp hI).1; omega⟩

end Erdos647Sieve
end
