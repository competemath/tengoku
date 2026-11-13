import Tengoku.Seed.Data.Fintype.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finsets of a prescribed size as a type

`ExactRowSubset α k` is the subtype of `Finset α` of cardinality exactly `k`. It is the
sample space of uniform sampling without replacement (`uniformExactRowSubsetPMF`) and the index
type of compound matrices in Cauchy–Binet (`SizedSubset k r` is `ExactRowSubset k (card r)`).
Mathlib has the finset `Finset.powersetCard k s` but no named subtype. Moved from
`NLAlib.Sketching.Sampling.UniformSamplingCoupling` (adapted from
Rerandomized-Subsampled-Trigonometric-Transforms, MIT licence, Diar Heidary).
-/

namespace NLAlib

/-- The finite sample space of literal size-`k` subsets.
Source: operator re-derivation `sh:convex-sampling`.-/
abbrev ExactRowSubset (α : Type*) (k : ℕ) := {T : Finset α // T.card = k}

/-- Exact-size subsets exist when the requested size is at most the population.
Source: operator re-derivation `sh:convex-sampling`.
@isnad1 id=nonempty.1h2v.s4.3c753e1001ad from=translated src=- shape=7e4cc14d vocab=26e8611c
-/
theorem exactRowSubset_nonempty {α : Type*} [Fintype α] {k : ℕ}
    (hk : k ≤ Fintype.card α) : Nonempty (ExactRowSubset α k) := by
  obtain ⟨T, _, hT⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset α))
    (by simpa using hk)
  exact ⟨T, hT⟩

end NLAlib
