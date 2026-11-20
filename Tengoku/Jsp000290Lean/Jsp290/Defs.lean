import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Indexed subset sums and deletion thresholds

The index set, rather than the set of values, records occurrences. In particular,
the two initial ones of the Fibonacci sequence are distinct available terms.
The mathematical source is J. Geneson, arXiv:2609.25107v1, Sections 2--4.
-/

namespace Jsp290

open Finset

abbrev Sequence := ℕ → ℤ

/-- A finite sum of distinct indexed occurrences.-/
def Represents (a : Sequence) (x : ℤ) : Prop :=
  ∃ s : Finset ℕ, ∑ i ∈ s, a i = x

/-- The sum uses only the first `N` occurrences, indexed `0,...,N-1`.-/
def PrefixRep (a : Sequence) (N : ℕ) (x : ℤ) : Prop :=
  ∃ s : Finset ℕ, s ⊆ range N ∧ ∑ i ∈ s, a i = x

def PrefixSum (a : Sequence) (N : ℕ) : ℤ := ∑ i ∈ range N, a i

/-- Completeness is eventual, with an unrestricted finite exceptional prefix.-/
def Complete (a : Sequence) : Prop :=
  ∃ T : ℤ, ∀ x : ℤ, T ≤ x → Represents a x

/-- Deletion removes indices; equal-valued occurrences remain distinct.-/
def RepresentsAfter (a : Sequence) (D : Finset ℕ) (x : ℤ) : Prop :=
  ∃ s : Finset ℕ, Disjoint s D ∧ ∑ i ∈ s, a i = x

def CompleteAfter (a : Sequence) (D : Finset ℕ) : Prop :=
  ∃ T : ℤ, ∀ x : ℤ, T ≤ x → RepresentsAfter a D x

/-- The full original existence question for a pair of deletion sizes.-/
def Admissible (m n : ℕ) : Prop :=
  ∃ a : Sequence, Monotone a ∧
    (∀ D : Finset ℕ, D.card = m → CompleteAfter a D) ∧
    (∀ D : Finset ℕ, D.card = n → ¬ CompleteAfter a D)

/-- The uniform central interval property uses the same threshold `T`.-/
def CentralIntervals (a : Sequence) (T : ℤ) : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ x : ℤ, T ≤ x → x ≤ PrefixSum a N - T → PrefixRep a N x

/-- Prefix slack tends to positive infinity, in an explicit threshold form.-/
def DivergingSlack (a : Sequence) : Prop :=
  ∀ C : ℤ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C ≤ PrefixSum a N - a N

end Jsp290
