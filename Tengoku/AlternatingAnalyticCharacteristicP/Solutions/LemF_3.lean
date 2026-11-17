import Tengoku.Seed.Data.List.Infix
import Tengoku.Seed.Data.Set.Finite.Basic
import Tengoku.Seed.Data.Fintype.Defs
import Tengoku
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.ChainGap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proof of Lemma F.3

Uses `ChainGap.labelChain_inter_subsingleton` and `ChainGap.iInter_nonempty_of_cofinite_on_chains`
from `AlternatingAnalytic/Scalar/ChainGap.lean`.
-/

namespace AlternatingAnalyticChallenge.LemF_3

universe u

/-- `T` is a `j`-chain: the set of words of a sequence `s₀, s₁, …` with `s_r j ⪯ s_{r+1}` in the
prefix order.-/
def IsLabelChain {L : Type u} (j : L) (T : Set (List L)) : Prop :=
  ∃ s : ℕ → List L, (∀ r, s r ++ [j] <+: s (r + 1)) ∧ T = Set.range s

/-- Lemma F.3, part 1: chains with different labels have at most one common word.
@isnad1 id=subsingl.3h5v.s5.90e4be62bf95 from=translated src=- shape=f9e246a5 vocab=452f0896
-/
theorem labelChain_inter_subsingleton
    {L : Type u} [Fintype L] [Nonempty L] {j h : L} (hjh : j ≠ h)
    {T T' : Set (List L)} (hT : IsLabelChain j T) (hT' : IsLabelChain h T') :
    (T ∩ T').Subsingleton := by
  exact AlternatingAnalytic.ChainGap.labelChain_inter_subsingleton hjh hT hT'

/-- Lemma F.3, part 2: if each `a j` contains all but finitely many words of every `j`-chain, then
the sets `a j` have a common word.
@isnad1 id=nonempty.1h2v.s5.76da7de4c18c from=translated src=- shape=67426268 vocab=cd1a24fe
-/
theorem iInter_nonempty_of_cofinite_on_chains
    {L : Type u} [Fintype L] [Nonempty L] (a : L → Set (List L))
    (ha : ∀ j : L, ∀ T : Set (List L), IsLabelChain j T → (T \ a j).Finite) :
    (⋂ j, a j).Nonempty := by
  exact AlternatingAnalytic.ChainGap.iInter_nonempty_of_cofinite_on_chains a ha

end AlternatingAnalyticChallenge.LemF_3
