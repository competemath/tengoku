import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Maxima of bounded natural-valued pair statistics

Phylogenetic trees are represented by a dependent inductive structure rather than by a
pre-existing finite type of graph isomorphism classes.  The set of possible quartet distances
is nevertheless a nonempty bounded set of natural numbers.  This file packages the elementary
`Nat.sSup` argument which turns pairwise bounds and witnesses into statements about its maximum.
-/

namespace QuartetDistance

/-- The possible values of a pair statistic, with `0` included to make the set nonempty even
when the carrier type is empty.-/
def pairValueSet (f : T → T → ℕ) : Set ℕ :=
  {d | d = 0 ∨ ∃ a b, d = f a b}

/-- Maximum of a bounded natural-valued pair statistic.-/
noncomputable def maxPairValue (f : T → T → ℕ) : ℕ := sSup (pairValueSet f)

/--
@isnad1 id=mem.0h2v.s4.7ec69cdb302c from=translated src=- shape=37bab909 vocab=f619acbf
-/
theorem zero_mem_pairValueSet (f : T → T → ℕ) : 0 ∈ pairValueSet f := by
  exact Or.inl rfl

/--
@isnad1 id=mem.0h4v.s4.41f79e7d7b26 from=translated src=- shape=5c2742fc vocab=f619acbf
-/
theorem value_mem_pairValueSet (f : T → T → ℕ) (a b : T) :
    f a b ∈ pairValueSet f := by
  exact Or.inr ⟨a, b, rfl⟩

/--
@isnad1 id=bddabove.1h3v.s4.78c410aa0114 from=translated src=- shape=7a814dba vocab=52783825
-/
theorem pairValueSet_bddAbove (f : T → T → ℕ) {B : ℕ}
    (hB : ∀ a b, f a b ≤ B) : BddAbove (pairValueSet f) := by
  refine ⟨B, ?_⟩
  intro d hd
  rcases hd with rfl | ⟨a, b, rfl⟩
  · exact Nat.zero_le _
  · exact hB a b

/--
@isnad1 id=le.1h3v.s4.f2a3d95dcbd4 from=translated src=- shape=8d59bdfc vocab=28e892cb
-/
theorem maxPairValue_le (f : T → T → ℕ) {B : ℕ}
    (hB : ∀ a b, f a b ≤ B) : maxPairValue f ≤ B := by
  apply csSup_le ⟨0, zero_mem_pairValueSet f⟩
  intro d hd
  rcases hd with rfl | ⟨a, b, rfl⟩
  · exact Nat.zero_le _
  · exact hB a b

/--
@isnad1 id=le.1h5v.s5.90383cdef93d from=translated src=- shape=40abf29f vocab=28e892cb
-/
theorem value_le_maxPairValue (f : T → T → ℕ) {B : ℕ}
    (hB : ∀ a b, f a b ≤ B) (a b : T) :
    f a b ≤ maxPairValue f := by
  exact le_csSup (pairValueSet_bddAbove f hB) (value_mem_pairValueSet f a b)

/-- The supremum is an actual value (or the deliberately adjoined zero).
@isnad1 id=or.1h3v.s5.45e59243b145 from=translated src=- shape=c02d19e3 vocab=28e892cb
-/
theorem maxPairValue_eq_zero_or_exists (f : T → T → ℕ) {B : ℕ}
    (hB : ∀ a b, f a b ≤ B) :
    maxPairValue f = 0 ∨ ∃ a b, maxPairValue f = f a b := by
  exact Nat.sSup_mem ⟨0, zero_mem_pairValueSet f⟩ (pairValueSet_bddAbove f hB)

/--
@isnad1 id=le.2h6v.s5.3fb9b580d660 from=translated src=- shape=89c7f0b5 vocab=28e892cb
-/
theorem lower_bound_maxPairValue (f : T → T → ℕ) {B L : ℕ}
    (hB : ∀ a b, f a b ≤ B) {a b : T} (hL : L ≤ f a b) :
    L ≤ maxPairValue f :=
  hL.trans (value_le_maxPairValue f hB a b)

end QuartetDistance
