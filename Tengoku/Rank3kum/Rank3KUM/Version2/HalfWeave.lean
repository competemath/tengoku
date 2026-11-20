import Tengoku.Rank3kum.Rank3KUM.HalfWeave.ParallelClasses

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Rank3KUM.Version2.HalfWeave.woven_successor_blocks_ne` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Rank3KUM.Version2.HalfWeave.rankTwoWoven_successor_isBase` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Rank3KUM.Version2.HalfWeave.cyclicRankTwoBasisOrderingOfUniformlyDense` (it only prints; the queue checks the axioms of every declaration). -/

namespace Rank3KUM.Version2.HalfWeave

open Set
open Rank3KUM.HalfWeave

noncomputable section

variable {α : Type*}

/--
The v2 half-weave hypothesis.  Blocks are contiguous and each has size at
most `k`; only the block containing the first position is required to be
largest.  No ordering condition is imposed on the remaining block sizes.-/
structure LargestFirstBlockModel (k m : ℕ) where
  block : Fin (2 * k) → Fin m
  monotone_block : Monotone block
  fiber_card_le :
    ∀ c, (fiberFinset block c).card ≤ k
  first_fiber_largest :
    ∀ (hk : 0 < k) c,
      (fiberFinset block c).card ≤
        (fiberFinset block
          (block (firstIndex k (zeroFin k hk)))).card

/-- Every fully sorted block model is, in particular, largest-first.-/
def LargestFirstBlockModel.ofSorted
    {k m : ℕ}
    (S : SortedBlockModel k m) :
    LargestFirstBlockModel k m where
  block := S.block
  monotone_block := S.monotone_block
  fiber_card_le := S.fiber_card_le
  first_fiber_largest := by
    intro hk c
    obtain ⟨j, rfl⟩ := S.surjective_block c
    apply S.fiber_card_antitone
    apply S.monotone_block
    change 0 ≤ j.val
    omega

/-- Paired first- and second-half indices cross blocks under the weak model.
@isnad1 id=ne.0h4v.s4.12cba788c299 from=translated src=- shape=24c36568 vocab=a261dd56
-/
theorem first_second_blocks_ne
    {k m : ℕ}
    (S : LargestFirstBlockModel k m)
    (i : Fin k) :
    S.block (firstIndex k i) ≠
      S.block (secondIndex k i) := by
  intro heq
  have hab : firstIndex k i ≤ secondIndex k i := by
    change i.val ≤ k + i.val
    omega
  have hlower :=
    fiber_card_ge_interval S.block S.monotone_block hab heq
  have hupper := S.fiber_card_le (S.block (firstIndex k i))
  have hlower' :
      k + 1 ≤
        (fiberFinset S.block
          (S.block (firstIndex k i))).card := by
    simpa [firstIndex, secondIndex] using hlower
  omega

/--
For a nonfinal `i`, the bridge from the second half to the next first-half
position crosses blocks.  This is the step where only "largest first" is
needed; no antitonicity of all block sizes is used.
@isnad1 id=ne.2h4v.s5.208233aa3081 from=translated src=- shape=7a82d105 vocab=51caac33
-/
theorem second_next_blocks_ne_nonfinal
    {k m : ℕ}
    (hk : 0 < k)
    (S : LargestFirstBlockModel k m)
    (i : Fin k)
    (hi : i ≠ lastFin k hk) :
    S.block (secondIndex k i) ≠
      S.block (firstIndex k (cyclicSucc k hk i)) := by
  intro heq_ba
  let z : Fin (2 * k) := firstIndex k (zeroFin k hk)
  let p : Fin (2 * k) := firstIndex k i
  let a : Fin (2 * k) := firstIndex k (cyclicSucc k hk i)
  let b : Fin (2 * k) := secondIndex k i

  have hsuccval :
      (cyclicSucc k hk i).val = i.val + 1 :=
    cyclicSucc_val_of_ne_last k hk i hi
  have hi_succ_lt : i.val + 1 < k := by
    have hneval : i.val ≠ k - 1 := by
      intro hval
      apply hi
      apply Fin.ext
      simpa [lastFin] using hval
    omega

  have hab : a ≤ b := by
    change (cyclicSucc k hk i).val ≤ k + i.val
    rw [hsuccval]
    omega
  have heq_ab : S.block a = S.block b := heq_ba.symm
  have hmid_lower_raw :=
    fiber_card_ge_interval S.block S.monotone_block hab heq_ab
  change
    (k + i.val) - (cyclicSucc k hk i).val + 1 ≤
      (fiberFinset S.block (S.block a)).card
    at hmid_lower_raw
  rw [hsuccval] at hmid_lower_raw
  have hmid_lower :
      k ≤ (fiberFinset S.block (S.block a)).card := by
    omega
  have hmid_upper := S.fiber_card_le (S.block a)
  have hmid_eq :
      (fiberFinset S.block (S.block a)).card = k := by
    omega

  have hfirst_lower :
      k ≤ (fiberFinset S.block (S.block z)).card := by
    have hlarge := S.first_fiber_largest hk (S.block a)
    rw [hmid_eq] at hlarge
    simpa [z] using hlarge
  have hfirst_upper := S.fiber_card_le (S.block z)
  have hfirst_eq :
      (fiberFinset S.block (S.block z)).card = k := by
    omega

  have hza : S.block z = S.block a := by
    by_contra hza_ne
    have hza_le : z ≤ a := by
      change 0 ≤ (cyclicSucc k hk i).val
      omega
    have hlabel_lt : S.block z < S.block a :=
      lt_of_le_of_ne (S.monotone_block hza_le) hza_ne
    have hfirst_sub :
        fiberFinset S.block (S.block z) ⊆ Finset.Iic p := by
      intro j hj
      have hjlabel : S.block j = S.block z := by
        simpa [fiberFinset] using hj
      rw [Finset.mem_Iic]
      by_contra hnot
      have hp_lt_j : p < j := lt_of_not_ge hnot
      have ha_le_j : a ≤ j := by
        change (cyclicSucc k hk i).val ≤ j.val
        change i.val < j.val at hp_lt_j
        rw [hsuccval]
        omega
      have hbad : S.block a ≤ S.block z := by
        have hjmono := S.monotone_block ha_le_j
        simpa [hjlabel] using hjmono
      exact (not_le_of_gt hlabel_lt) hbad
    have hfirst_card_upper := Finset.card_le_card hfirst_sub
    have hIic : (Finset.Iic p).card = p.val + 1 := by simp
    rw [hIic] at hfirst_card_upper
    have hsmall :
        (fiberFinset S.block (S.block z)).card ≤ i.val + 1 := by
      simpa [p, firstIndex] using hfirst_card_upper
    omega

  have hzb : S.block z = S.block b := hza.trans heq_ab
  have hzb_order : z ≤ b := by
    change 0 ≤ k + i.val
    omega
  have hlong :=
    fiber_card_ge_interval S.block S.monotone_block hzb_order hzb
  change
    (k + i.val) - 0 + 1 ≤
      (fiberFinset S.block (S.block z)).card
    at hlong
  have htoo_many :
      k + 1 ≤ (fiberFinset S.block (S.block z)).card := by
    omega
  omega

/-- The cyclic join crosses blocks under the weak model.
@isnad1 id=ne.1h3v.s5.7c6a05ffb3a0 from=translated src=- shape=b0b5eb53 vocab=90c164df
-/
theorem wraparound_blocks_ne
    {k m : ℕ}
    (hk : 0 < k)
    (S : LargestFirstBlockModel k m) :
    S.block (secondIndex k (lastFin k hk)) ≠
      S.block (firstIndex k (zeroFin k hk)) := by
  intro heq_ba
  let a : Fin (2 * k) := firstIndex k (zeroFin k hk)
  let b : Fin (2 * k) := secondIndex k (lastFin k hk)
  have hab : a ≤ b := by
    change 0 ≤ k + (k - 1)
    omega
  have heq_ab : S.block a = S.block b := heq_ba.symm
  have hlong :=
    fiber_card_ge_interval S.block S.monotone_block hab heq_ab
  change
    (k + (k - 1)) - 0 + 1 ≤
      (fiberFinset S.block (S.block a)).card
    at hlong
  have htwo :
      2 * k ≤ (fiberFinset S.block (S.block a)).card := by
    omega
  have hupper := S.fiber_card_le (S.block a)
  omega

/-- Every successor adjacency in the half weave crosses blocks.
@isnad1 id=ne.1h4v.s7.ee631ede1e05 from=translated src=- shape=2d0d1a9e vocab=7ae23698
-/
theorem woven_successor_blocks_ne
    {k m : ℕ}
    (hk : 0 < k)
    (S : LargestFirstBlockModel k m)
    (p : Fin k × Bool) :
    S.block (halfWeaveEquiv k hk p) ≠
      S.block (halfWeaveEquiv k hk (weaveNext k hk p)) := by
  have hadj :=
    woven_successor_adjacency k hk (Equiv.refl (Fin (2 * k))) p
  rcases hadj with ⟨i, _hp, hpair⟩ | ⟨i, _hp, hpair⟩
  · have hindex :
        (halfWeaveEquiv k hk p,
         halfWeaveEquiv k hk (weaveNext k hk p)) =
        (firstIndex k i, secondIndex k i) := by
      simpa [woven] using hpair
    have hfirst' : halfWeaveEquiv k hk p = firstIndex k i := by
      simpa using congrArg Prod.fst hindex
    have hsecond' :
        halfWeaveEquiv k hk (weaveNext k hk p) = secondIndex k i := by
      simpa using congrArg Prod.snd hindex
    intro heq
    apply first_second_blocks_ne S i
    rw [← hfirst', ← hsecond']
    exact heq
  · have hindex :
        (halfWeaveEquiv k hk p,
         halfWeaveEquiv k hk (weaveNext k hk p)) =
        (secondIndex k i, firstIndex k (cyclicSucc k hk i)) := by
      simpa [woven] using hpair
    have hfirst' : halfWeaveEquiv k hk p = secondIndex k i := by
      simpa using congrArg Prod.fst hindex
    have hsecond' :
        halfWeaveEquiv k hk (weaveNext k hk p) =
          firstIndex k (cyclicSucc k hk i) := by
      simpa using congrArg Prod.snd hindex
    intro heq
    have hstandard :
        S.block (secondIndex k i) =
          S.block (firstIndex k (cyclicSucc k hk i)) := by
      rw [← hfirst', ← hsecond']
      exact heq
    by_cases hi : i = lastFin k hk
    · subst i
      apply wraparound_blocks_ne hk S
      simpa using hstandard
    · exact (second_next_blocks_ne_nonfinal hk S i hi) hstandard

/-- Construction data for the v2 rank-two proof.-/
structure RankTwoLargestFirstEnumeration
    (M : Matroid α) (k m : ℕ) where
  y : Fin (2 * k) ≃ M.E
  blockModel : LargestFirstBlockModel k m
  indep_of_blocks_ne :
    ∀ a b : Fin (2 * k),
      blockModel.block a ≠ blockModel.block b →
        M.Indep ({((y a : M.E) : α), ((y b : M.E) : α)} : Set α)

/-- The legacy fully sorted construction supplies the weaker v2 data.-/
def RankTwoLargestFirstEnumeration.ofSorted
    {M : Matroid α} {k m : ℕ}
    (D : Rank3KUM.HalfWeave.RankTwoSortedEnumeration M k m) :
    RankTwoLargestFirstEnumeration M k m where
  y := D.y
  blockModel := LargestFirstBlockModel.ofSorted D.sortedBlocks
  indep_of_blocks_ne := D.indep_of_blocks_ne

/-- Apply the half weave to a largest-first block enumeration.-/
def rankTwoWoven
    {M : Matroid α} {k m : ℕ}
    (D : RankTwoLargestFirstEnumeration M k m)
    (hk : 0 < k) :
    Fin k × Bool ≃ M.E :=
  woven k hk D.y

/-- Every woven successor pair is independent.
@isnad1 id=indep.1h6v.s7.a7d2692363a0 from=translated src=- shape=68f4d8d4 vocab=b427be1a
-/
theorem rankTwoWoven_successor_indep
    {M : Matroid α} {k m : ℕ}
    (D : RankTwoLargestFirstEnumeration M k m)
    (hk : 0 < k)
    (p : Fin k × Bool) :
    M.Indep
      ({((rankTwoWoven D hk p : M.E) : α),
        ((rankTwoWoven D hk (weaveNext k hk p) : M.E) : α)} : Set α) := by
  have hblocks := woven_successor_blocks_ne hk D.blockModel p
  simpa [rankTwoWoven, woven] using
    D.indep_of_blocks_ne
      (halfWeaveEquiv k hk p)
      (halfWeaveEquiv k hk (weaveNext k hk p))
      hblocks

/-- Every woven successor pair is a basis in rank two.
@isnad1 id=isbase.2h6v.s7.fb4d0802c0f7 from=translated src=- shape=d9409adb vocab=ad87c97d
-/
theorem rankTwoWoven_successor_isBase
    (M : Matroid α)
    {k m : ℕ}
    (D : RankTwoLargestFirstEnumeration M k m)
    (hk : 0 < k)
    (hRank : M.eRank = 2)
    (p : Fin k × Bool) :
    M.IsBase
      ({((rankTwoWoven D hk p : M.E) : α),
        ((rankTwoWoven D hk (weaveNext k hk p) : M.E) : α)} : Set α) := by
  have hne :
      ((rankTwoWoven D hk p : M.E) : α) ≠
        ((rankTwoWoven D hk (weaveNext k hk p) : M.E) : α) := by
    intro heq
    have hsubtype :
        rankTwoWoven D hk p = rankTwoWoven D hk (weaveNext k hk p) := by
      apply Subtype.ext
      exact heq
    have hblocks := woven_successor_blocks_ne hk D.blockModel p
    apply hblocks
    have hindices :
        halfWeaveEquiv k hk p =
          halfWeaveEquiv k hk (weaveNext k hk p) := by
      apply D.y.injective
      simpa [rankTwoWoven, woven] using hsubtype
    exact congrArg D.blockModel.block hindices
  exact
    Rank3KUM.HalfWeave.pair_isBase_of_indep_of_eRank_eq_two
      M hRank hne (rankTwoWoven_successor_indep D hk p)

/-- Clean output interface corresponding to paper v2, Definition 4.1.-/
structure CyclicRankTwoBasisOrdering
    (M : Matroid α) (k : ℕ) (hk : 0 < k) where
  order : Fin k × Bool ≃ M.E
  adjacent_isBase :
    ∀ p : Fin k × Bool,
      M.IsBase
        ({((order p : M.E) : α),
          ((order (weaveNext k hk p) : M.E) : α)} : Set α)

/-- Largest-first block data yields a cyclic rank-two basis ordering.-/
def cyclicRankTwoBasisOrderingOfLargestFirst
    (M : Matroid α)
    {k m : ℕ}
    (hk : 0 < k)
    (hRank : M.eRank = 2)
    (D : RankTwoLargestFirstEnumeration M k m) :
    CyclicRankTwoBasisOrdering M k hk where
  order := rankTwoWoven D hk
  adjacent_isBase := rankTwoWoven_successor_isBase M D hk hRank

/--
Paper v2, Proposition 4.2.  The canonical construction still chooses the
legacy fully sorted block order, but after this point the proof uses only the
strictly weaker largest-first block hypothesis.-/
def cyclicRankTwoBasisOrderingOfUniformlyDense
    (M : Matroid α)
    (k : ℕ)
    [Fintype M.E]
    [DecidableEq M.E]
    (hk : 0 < k)
    (hcard : Fintype.card M.E = 2 * k)
    (hDense : UniformlyDense M k)
    (hRank : M.eRank = 2) :
    CyclicRankTwoBasisOrdering M k hk := by
  have hLoopless : M.Loopless :=
    loopless_of_uniformlyDense M k hk hDense
  let Dold :=
    Rank3KUM.HalfWeave.rankTwoSortedEnumerationOfUniformlyDense
      M k hcard hDense hLoopless hRank
  let D := RankTwoLargestFirstEnumeration.ofSorted Dold
  exact cyclicRankTwoBasisOrderingOfLargestFirst M hk hRank D

end

end Rank3KUM.Version2.HalfWeave
