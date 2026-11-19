/-
Consequences of the new unconditional budget implementation.
New source, not compiled in the assistant environment.
The moment estimate remains an EXPLICIT premise of the counting consequence.
-/
import Tengoku.Erdos647.Erdos647Sieve.BudgetDebit
import Tengoku.Erdos647.Erdos647Sieve.FiniteCountingAssembly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section
namespace Erdos647Sieve

/-- No Mertens or moment input is needed for negative-budget exclusion.-/
theorem no_prefix_of_negative_correctedBudget
    (n H : ℕ) (y : ℝ) (hH : 1 ≤ H) (hy : (H : ℝ) < y)
    (hneg : correctedBudget H < 0) : ¬ Prefix H n :=
  no_prefix_of_negative_budget budgetDebit n H y hH hy hneg

/-- Remove the budget premise from the previously compiled assembly.
The finite moment is still a substantial, unproved, explicit hypothesis.-/
theorem finiteCounting_of_finiteMoment (hMoment : FiniteMomentClaim) : FiniteCountingClaim :=
  finiteCounting_of_budgetDebit_of_finiteMoment budgetDebit hMoment

/-- The negative-budget candidate-count branch, now without a debit premise.-/
theorem candidateCount_le_window_of_negative_correctedBudget
    (X H : ℕ) (y : ℝ) (hH : 1 ≤ H) (hy : (H : ℝ) < y)
    (hneg : correctedBudget H < 0) : candidateCount X ≤ H :=
  candidateCount_le_window_of_negative_budget budgetDebit X H y hH hy hneg

end Erdos647Sieve
end
