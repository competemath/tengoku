/-
Version-2 Erdős #647 sieve: proposed specification, NOT COMPILED HERE.
This file defines statements. It does not prove the finite sieve or endpoint.
Keep this file separate from implementation and review changes explicitly.
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve

/-- Positive-divisor count; all mathematical uses below have a positive argument.-/
def tau (m : ℕ) : ℕ := m.divisors.card

/-- The actual predicate, not a frozen-prime relaxation.-/
def Candidate (n : ℕ) : Prop :=
  24 < n ∧ ∀ k : ℕ, 1 ≤ k → k < n → tau (n - k) ≤ k + 2

/-- Surviving a finite window includes the positivity guard.-/
def Prefix (H n : ℕ) : Prop :=
  H < n ∧ ∀ k : ℕ, 1 ≤ k → k ≤ H → tau (n - k) ≤ k + 2

def candidateCount (X : ℕ) : ℕ := by
  classical
  exact ((Finset.range (X + 1)).filter Candidate).card

/-- INTEGER subtraction is essential in the unrestricted finite moment.-/
def windowPolynomial (H : ℕ) (n : ℤ) : ℤ :=
  ∏ k ∈ Finset.Icc 1 H, (n - (k : ℤ))

def selectedPrimes (H : ℕ) (y : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc (H + 1) (Nat.floor y)).filter Nat.Prime

def hitCount (H : ℕ) (y : ℝ) (n : ℤ) : ℕ := by
  classical
  exact ((selectedPrimes H y).filter
    (fun p => (p : ℤ) ∣ windowPolynomial H n)).card

def logBudget (H : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 H,
    Int.floor (Real.log ((k : ℝ) + 2) / Real.log 2)

def smallPrimeDebit (H : ℕ) : ℕ := by
  classical
  exact ∑ p ∈ (Finset.Icc 2 H).filter Nat.Prime, H / p

/-- Signed subtraction: a negative budget must NOT be truncated to zero.-/
def correctedBudget (H : ℕ) : ℤ :=
  logBudget H - (smallPrimeDebit H : ℤ)

def primeMass (H : ℕ) (y : ℝ) : ℝ :=
  (H : ℝ) * ∑ p ∈ selectedPrimes H y, (1 : ℝ) / (p : ℝ)

def momentBound (X H : ℕ) (y z : ℝ) (J : ℕ) : ℝ :=
  let mu := (1 - z) * primeMass H y
  (X : ℝ) * (Real.exp (-mu) + mu ^ (J + 1) / (Nat.factorial (J + 1) : ℝ))
    + ((H : ℝ) * y) ^ J

/-- Manuscript Lemma 1, including arbitrary integer translations.-/
def FiniteMomentClaim : Prop :=
  ∀ (A : ℤ) (X H : ℕ) (y z : ℝ) (J : ℕ),
    1 ≤ X → 1 ≤ H → (H : ℝ) < y → 0 < z → z < 1 → Even J →
    (∑ n ∈ Finset.Icc (A + 1) (A + (X : ℤ)), z ^ hitCount H y n)
      ≤ momentBound X H y z J

/-- Manuscript Lemma 2; Q_H-D_H is an integer.-/
def BudgetDebitClaim : Prop :=
  ∀ (n H : ℕ) (y : ℝ),
    1 ≤ H → (H : ℝ) < y → Prefix H n →
    (hitCount H y (n : ℤ) : ℤ) ≤ correctedBudget H

/-- Finite counting bound (7), in its nonnegative-budget case.-/
def FiniteCountingClaim : Prop :=
  ∀ (X H : ℕ) (y z : ℝ) (J : ℕ),
    1 ≤ X → 1 ≤ H → (H : ℝ) < y → 0 < z → z < 1 → Even J →
    0 ≤ correctedBudget H →
    (candidateCount X : ℝ) ≤ (H : ℝ) +
      Real.exp ((-Real.log z) * (correctedBudget H : ℝ)) * momentBound X H y z J

def endpointExponent : ℝ := Real.log 2 / (1 + Real.log 2)

def windowLength (X : ℕ) : ℕ :=
  Nat.floor (Real.rpow (Real.log (X : ℝ)) endpointExponent)

/-- Exactly 2*ceil(H/100) for natural H; prove the bridge before using it.-/
def truncationOrder (X : ℕ) : ℕ := 2 * ((windowLength X + 99) / 100)

def primeCutoff (X : ℕ) : ℝ :=
  Real.rpow (X : ℝ) ((1 : ℝ) / (4 * (truncationOrder X : ℝ)))

def momentT (X : ℕ) : ℝ :=
  (1 : ℝ) / (1000 * Real.log (Real.log (X : ℝ)))

def endpointRHS (X : ℕ) : ℝ :=
  (X : ℝ) * Real.exp
    (-(Real.rpow (Real.log (X : ℝ)) endpointExponent /
       ((1000 : ℝ) * Real.log (Real.log (X : ℝ)))))

/-- The requested unconditional eventual theorem; no analytic hypothesis is a parameter.-/
def EndpointClaim : Prop :=
  ∃ X0 : ℕ, 3 ≤ X0 ∧
    ∀ X : ℕ, X0 ≤ X → (candidateCount X : ℝ) ≤ endpointRHS X

def prefixCount (A X H : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc (A + 1) (A + X)).filter (Prefix H)).card

/-- The onset is uniform in A, not a separate onset for each A.-/
def TranslatedEndpointClaim : Prop :=
  ∃ X0 : ℕ, 3 ≤ X0 ∧
    ∀ X : ℕ, X0 ≤ X →
    ∀ A : ℕ, windowLength X ≤ A →
      (prefixCount A X (windowLength X) : ℝ) ≤ endpointRHS X

end Erdos647Sieve
end
