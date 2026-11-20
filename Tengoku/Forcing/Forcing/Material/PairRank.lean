/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Seed.SetTheory.ZFC.Rank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rank descent through a coded branch

One fact, shared by every recursion on coded branches: a Kuratowski pair sits three levels above
its second component, so a branch `⟨c, z⟩ ∈ w` puts `z` at strictly smaller rank than `w`.

Factored here on its second consumer — the atomic recursion (`Forcing/Material/Recursion.lean`)
and the maximal name presentation (`Forcing/Material/MaximalNames.lean`) both recurse on it.
-/

universe u

namespace Forcing

/-- A branch code sits three Kuratowski levels above the subname code it carries, so the
subname code has strictly smaller rank. *Rank only* — nothing about any domain.
@isnad1 id=lt.1h3v.s4.6cc123cd8afd from=translated src=- shape=658fe7bb vocab=3ea4f679
-/
theorem rank_lt_of_pair_mem {c z w : ZFSet.{u}} (h : ZFSet.pair c z ∈ w) : z.rank < w.rank := by
  have h₁ : z.rank < ({c, z} : ZFSet.{u}).rank :=
    ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inr rfl))
  have h₂ : ({c, z} : ZFSet.{u}).rank < (ZFSet.pair c z).rank :=
    ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inr rfl))
  exact (h₁.trans h₂).trans (ZFSet.rank_lt_of_mem h)

end Forcing
