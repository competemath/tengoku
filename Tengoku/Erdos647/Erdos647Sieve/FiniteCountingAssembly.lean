/-
Finite counting assembly for the protected version-2 specification.
STATUS: v3 REPAIR DRAFT; not recompiled in the assistant environment.
The v2 user run compiled WeightedCounting but rejected this assembly module.
This file still does not prove the two unconditional sieve inputs.

The main declaration has EXPLICIT BudgetDebitClaim and FiniteMomentClaim
premises. Neither premise is proved here or exported as an axiom. The
unconditional gate continues to require budgetDebit, finiteMoment, and
finiteCounting, which this module intentionally does not declare.
-/
import Tengoku.Erdos647.Erdos647Sieve.Specification
import Tengoku.Erdos647.Erdos647Sieve.WeightedCounting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve

theorem candidate_prefix {n H : ℕ} (hc : Candidate n) (hH : H < n) : Prefix H n := by
  refine ⟨hH, ?_⟩
  intro k hk hkH
  exact hc.2 k hk (lt_of_le_of_lt hkH hH)

/-- Exclude zero from the counting range using the ACTUAL candidate predicate.-/
theorem candidateCount_eq_filter_Icc (X : ℕ) [DecidablePred Candidate] :
    candidateCount X = ((Finset.Icc 1 X).filter Candidate).card := by
  classical
  -- Prove equality of the actual finsets under `card` directly. This avoids
  -- rewriting with an auxiliary filter equality whose decidability instance
  -- need not match the instance captured by the definition of candidateCount.
  unfold candidateCount
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hn, hc⟩
    have hn24 : 24 < n := hc.1
    exact ⟨⟨by omega, by omega⟩, hc⟩
  · rintro ⟨⟨_, hn⟩, hc⟩
    exact ⟨by omega, hc⟩

/-- Convert the positive natural interval to the identical integer interval.-/
theorem sum_nat_Icc_eq_int (X : ℕ) (f : ℤ → ℝ) :
    (∑ n ∈ Finset.Icc 1 X, f (n : ℤ)) =
      ∑ n ∈ Finset.Icc (1 : ℤ) (X : ℤ), f n := by
  classical
  refine Finset.sum_bij (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hn1, by exact_mod_cast hnX⟩
  · intro n _ m _ hnm
    change (n : ℤ) = (m : ℤ) at hnm
    exact_mod_cast hnm
  · intro n hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 ≤ n := by omega
    have heq : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
    refine ⟨n.toNat, ?_, heq⟩
    apply Finset.mem_Icc.mpr
    constructor
    · have h : (1 : ℤ) ≤ (n.toNat : ℤ) := by rw [heq]; exact hn1
      exact_mod_cast h
    · have h : (n.toNat : ℤ) ≤ (X : ℤ) := by rw [heq]; exact hnX
      exact_mod_cast h
  · intro n _
    rfl

/-- Negative signed budgets exclude all prefix survivors, conditional on the debit lemma.-/
theorem no_prefix_of_negative_budget (hDebit : BudgetDebitClaim)
    (n H : ℕ) (y : ℝ) (hH : 1 ≤ H) (hy : (H : ℝ) < y)
    (hneg : correctedBudget H < 0) : ¬ Prefix H n := by
  intro hprefix
  have hbound := hDebit n H y hH hy hprefix
  have hnonneg : (0 : ℤ) ≤ (hitCount H y (n : ℤ) : ℤ) := by
    exact_mod_cast Nat.zero_le (hitCount H y (n : ℤ))
  omega

/-- Assemble exactly the requested finite bound from its two explicit missing inputs.
This does NOT discharge BudgetDebitClaim or FiniteMomentClaim.-/
theorem finiteCounting_of_budgetDebit_of_finiteMoment
    (hDebit : BudgetDebitClaim) (hMoment : FiniteMomentClaim) : FiniteCountingClaim := by
  classical
  intro X H y z J hX hH hy hz hz1 hJ _hB
  have hK : 0 ≤ Real.exp ((-Real.log z) * (correctedBudget H : ℝ)) :=
    (Real.exp_pos _).le
  have hw : ∀ n ∈ Finset.Icc 1 X, 0 ≤ z ^ hitCount H y (n : ℤ) := by
    intro n _
    exact pow_nonneg hz.le _
  have hcover : ∀ n ∈ Finset.Icc 1 X, Candidate n →
      n ∉ Finset.Icc 1 H →
      1 ≤ Real.exp ((-Real.log z) * (correctedBudget H : ℝ)) *
        z ^ hitCount H y (n : ℤ) := by
    intro n hn hc hne
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hHn : H < n := by
      by_contra hnot
      exact hne (Finset.mem_Icc.mpr ⟨hn1, by omega⟩)
    have hprefix : Prefix H n := candidate_prefix hc hHn
    exact one_le_budget_weight z hz hz1 (correctedBudget H)
      (hitCount H y (n : ℤ)) (hDebit n H y hH hy hprefix)
  have hcount := count_le_exceptions_add_weight
    (Finset.Icc 1 X) (Finset.Icc 1 H) Candidate
    (fun n : ℕ => z ^ hitCount H y (n : ℤ))
    (Real.exp ((-Real.log z) * (correctedBudget H : ℝ))) hK hw hcover
  have hcard : ((Finset.Icc 1 H).card : ℝ) = (H : ℝ) := by
    simp [Nat.card_Icc]
  rw [hcard] at hcount
  have hm : (∑ n ∈ Finset.Icc 1 X, z ^ hitCount H y (n : ℤ)) ≤
      momentBound X H y z J := by
    rw [sum_nat_Icc_eq_int X (fun n => z ^ hitCount H y n)]
    simpa only [zero_add] using hMoment 0 X H y z J hX hH hy hz hz1 hJ
  rw [candidateCount_eq_filter_Icc]
  exact hcount.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hm hK))

/-- The negative-budget branch of the actual candidate count, with the debit premise explicit.-/
theorem candidateCount_le_window_of_negative_budget (hDebit : BudgetDebitClaim)
    (X H : ℕ) (y : ℝ) (hH : 1 ≤ H) (hy : (H : ℝ) < y)
    (hneg : correctedBudget H < 0) : candidateCount X ≤ H := by
  classical
  rw [candidateCount_eq_filter_Icc]
  have hsub : (Finset.Icc 1 X).filter Candidate ⊆ Finset.Icc 1 H := by
    intro n hn
    obtain ⟨hnX, hc⟩ := Finset.mem_filter.mp hn
    have hn1 := (Finset.mem_Icc.mp hnX).1
    apply Finset.mem_Icc.mpr
    refine ⟨hn1, ?_⟩
    by_contra hnot
    have hp := candidate_prefix hc (by omega : H < n)
    exact no_prefix_of_negative_budget hDebit n H y hH hy hneg hp
  have hcard := Finset.card_le_card hsub
  simpa [Nat.card_Icc] using hcard

end Erdos647Sieve
end
