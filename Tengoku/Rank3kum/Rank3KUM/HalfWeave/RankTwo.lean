import Tengoku.Rank3kum.Rank3KUM.HalfWeave.SortedBlocks
import Tengoku.Seed.Combinatorics.Matroid.Rank.ENat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Rank3KUM.HalfWeave.exists_pair_closure_ne_of_eRank_eq_two` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Rank3KUM.HalfWeave.pair_indep_of_closure_ne` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Rank3KUM.HalfWeave.RankTwoSortedEnumeration.ofClosureBlocks` (it only prints; the queue checks the axioms of every declaration). -/

namespace Rank3KUM.HalfWeave

/-- A finite independent pair of distinct elements is a base in rank two.
@isnad1 id=isbase.3h4v.s5.6200359ad7e9 from=translated src=- shape=2ae9dbfd vocab=23a846cb
-/
theorem pair_isBase_of_indep_of_eRank_eq_two
    {α : Type*}
    (M : Matroid α)
    (hRank : M.eRank = 2)
    {e f : α}
    (hef : e ≠ f)
    (hpair : M.Indep ({e, f} : Set α)) :
    M.IsBase ({e, f} : Set α) := by
  apply hpair.isBase_of_eRk_ge (Set.toFinite {e, f})
  rw [hRank, hpair.eRk_eq_encard, Set.encard_pair hef]

/--
Data needed to apply the sorted-block half-weave theorem to a matroid.
Different block labels must give an independent pair after coercion to `α`.-/
structure RankTwoSortedEnumeration
    {α : Type*}
    (M : Matroid α)
    (k m : ℕ) where
  y : Fin (2 * k) ≃ M.E
  sortedBlocks : SortedBlockModel k m
  indep_of_blocks_ne :
    ∀ a b : Fin (2 * k),
      sortedBlocks.block a ≠ sortedBlocks.block b →
        M.Indep
          ({((y a : M.E) : α),
            ((y b : M.E) : α)} : Set α)

/--
In a loopless matroid, elements in different singleton-closure classes form
an independent pair.
@isnad1 id=indep.4h4v.s6.b641daa7a25e from=translated src=- shape=7e9b5aef vocab=6639351a
-/
theorem pair_indep_of_closure_ne
    {α : Type*}
    (M : Matroid α)
    (hLoopless : M.Loopless)
    {e f : α}
    (he : e ∈ M.E)
    (hf : f ∈ M.E)
    (hclosure :
      M.closure ({e} : Set α) ≠
        M.closure ({f} : Set α)) :
    M.Indep ({e, f} : Set α) := by
  let : M.Loopless := hLoopless
  have heNonloop : M.IsNonloop e :=
    Matroid.isNonloop_of_loopless he
  have hfNonloop : M.IsNonloop f :=
    Matroid.isNonloop_of_loopless hf
  by_contra hdep
  apply hclosure
  exact
    (heNonloop.closure_eq_closure_iff_eq_or_dep
      hfNonloop).2 (Or.inr hdep)

/-- A rank-two matroid has two ground elements in different singleton-closure classes.
@isnad1 id=ex.1h2v.s6.9b385a07ab61 from=translated src=- shape=a850d205 vocab=c156de9a
-/
theorem exists_pair_closure_ne_of_eRank_eq_two
    {α : Type*}
    (M : Matroid α)
    (hRank : M.eRank = 2) :
    ∃ e f : α,
      e ∈ M.E ∧ f ∈ M.E ∧
        M.closure ({e} : Set α) ≠
          M.closure ({f} : Set α) := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  have hBcard : B.encard = 2 := by
    rw [hB.encard_eq_eRank, hRank]
  obtain ⟨e, f, hef, rfl⟩ :=
    Set.encard_eq_two.mp hBcard
  have heE : e ∈ M.E :=
    hB.subset_ground (by simp)
  have hfE : f ∈ M.E :=
    hB.subset_ground (by simp)
  refine ⟨e, f, heE, hfE, ?_⟩
  intro hclosure
  have heNonloop : M.IsNonloop e :=
    hB.indep.isNonloop_of_mem (by simp)
  have hfNonloop : M.IsNonloop f :=
    hB.indep.isNonloop_of_mem (by simp)
  rcases
      (heNonloop.closure_eq_closure_iff_eq_or_dep
        hfNonloop).1 hclosure with heq | hdep
  · exact hef heq
  · exact hdep hB.indep

/--
To construct a sorted rank-two enumeration, it is enough to label exactly
the singleton-closure classes.  The matroid independence field is then
automatic from looplessness.-/
def RankTwoSortedEnumeration.ofClosureBlocks
    {α : Type*}
    (M : Matroid α)
    {k m : ℕ}
    (hLoopless : M.Loopless)
    (y : Fin (2 * k) ≃ M.E)
    (S : SortedBlockModel k m)
    (hblock :
      ∀ a b : Fin (2 * k),
        S.block a = S.block b ↔
          M.closure
              ({((y a : M.E) : α)} : Set α) =
            M.closure
              ({((y b : M.E) : α)} : Set α)) :
    RankTwoSortedEnumeration M k m where
  y := y
  sortedBlocks := S
  indep_of_blocks_ne := by
    intro a b hab
    apply pair_indep_of_closure_ne
      M hLoopless (y a).property (y b).property
    intro hclosure
    exact hab ((hblock a b).2 hclosure)

/-- The ground-set enumeration obtained by applying the half weave.-/
def rankTwoWoven
    {α : Type*}
    {M : Matroid α}
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k) :
    Fin k × Bool ≃ M.E :=
  woven k hk D.y

/--
@isnad1 id=eq.1h6v.s7.04040ff6adb2 from=translated src=- shape=f21d4760 vocab=64c43bb6
-/
@[simp] theorem rankTwoWoven_false
    {α : Type*}
    {M : Matroid α}
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k)
    (i : Fin k) :
    rankTwoWoven D hk (i, false) =
      D.y (firstIndex k i) := by
  simp [rankTwoWoven]

/--
@isnad1 id=eq.1h6v.s7.28efd6ac9a16 from=translated src=- shape=f21d4760 vocab=c9ff9e74
-/
@[simp] theorem rankTwoWoven_true
    {α : Type*}
    {M : Matroid α}
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k)
    (i : Fin k) :
    rankTwoWoven D hk (i, true) =
      D.y (secondIndex k i) := by
  simp [rankTwoWoven]

/-- Successive woven values are distinct in the ground-set subtype.
@isnad1 id=ne.1h6v.s7.8149e15ef10f from=translated src=- shape=83941a98 vocab=0a61f85c
-/
theorem rankTwoWoven_successor_ne
    {α : Type*}
    {M : Matroid α}
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k)
    (p : Fin k × Bool) :
    rankTwoWoven D hk p ≠
      rankTwoWoven D hk (weaveNext k hk p) := by
  have hblocks :=
    woven_successor_blocks_ne hk D.sortedBlocks p
  intro heq
  apply hblocks
  have hindices :
      halfWeaveEquiv k hk p =
        halfWeaveEquiv k hk (weaveNext k hk p) := by
    apply D.y.injective
    simpa [rankTwoWoven, woven] using heq
  exact congrArg D.sortedBlocks.block hindices

/-- Successive woven values remain distinct after coercion to `α`.
@isnad1 id=ne.1h6v.s7.f9edd8ea3cde from=translated src=- shape=fb5d7eac vocab=a873c379
-/
theorem rankTwoWoven_successor_coe_ne
    {α : Type*}
    {M : Matroid α}
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k)
    (p : Fin k × Bool) :
    ((rankTwoWoven D hk p : M.E) : α) ≠
      ((rankTwoWoven D hk (weaveNext k hk p) : M.E) : α) := by
  intro heq
  apply rankTwoWoven_successor_ne D hk p
  apply Subtype.ext
  exact heq

/-- Every successor pair in the woven enumeration is independent.
@isnad1 id=indep.1h6v.s7.20ddc9b711f6 from=translated src=- shape=68f4d8d4 vocab=b24ac1e5
-/
theorem rankTwoWoven_successor_indep
    {α : Type*}
    {M : Matroid α}
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k)
    (p : Fin k × Bool) :
    M.Indep
      ({((rankTwoWoven D hk p : M.E) : α),
        ((rankTwoWoven D hk
          (weaveNext k hk p) : M.E) : α)} : Set α) := by
  have hblocks :=
    woven_successor_blocks_ne hk D.sortedBlocks p
  simpa [rankTwoWoven, woven] using
    D.indep_of_blocks_ne
      (halfWeaveEquiv k hk p)
      (halfWeaveEquiv k hk (weaveNext k hk p))
      hblocks

/-- In rank two, every woven successor pair is a base.
@isnad1 id=isbase.2h6v.s7.d6c6129add13 from=translated src=- shape=d9409adb vocab=c4c24d05
-/
theorem rankTwoWoven_successor_isBase
    {α : Type*}
    (M : Matroid α)
    {k m : ℕ}
    (D : RankTwoSortedEnumeration M k m)
    (hk : 0 < k)
    (hRank : M.eRank = 2)
    (p : Fin k × Bool) :
    M.IsBase
      ({((rankTwoWoven D hk p : M.E) : α),
        ((rankTwoWoven D hk
          (weaveNext k hk p) : M.E) : α)} : Set α) := by
  exact pair_isBase_of_indep_of_eRank_eq_two
    M hRank
    (rankTwoWoven_successor_coe_ne D hk p)
    (rankTwoWoven_successor_indep D hk p)

/--
A supplied sorted block enumeration produces a cyclic ground-set enumeration
whose every successor pair is a base.
@isnad1 id=ex.2h5v.s7.c8e232a78cbd from=translated src=- shape=5165b286 vocab=58ee220f
-/
theorem exists_cyclic_adjacent_base_order_of_sortedEnumeration
    {α : Type*}
    (M : Matroid α)
    {k m : ℕ}
    (hk : 0 < k)
    (hRank : M.eRank = 2)
    (D : RankTwoSortedEnumeration M k m) :
    ∃ order : Fin k × Bool ≃ M.E,
      ∀ p : Fin k × Bool,
        M.IsBase
          ({((order p : M.E) : α),
            ((order (weaveNext k hk p) : M.E) : α)} : Set α) := by
  refine ⟨rankTwoWoven D hk, ?_⟩
  intro p
  exact rankTwoWoven_successor_isBase M D hk hRank p

end Rank3KUM.HalfWeave
