import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.Tree
import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.CircularQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Edge intervals and pointwise boundary restriction

This file isolates the deterministic ``ribbon'' facts used in the
Bandelt--Dress argument.  A boundary word of a rotated binary tree lists the
leaves below every edge consecutively.  The other side of the same edge is
consecutive after passing through the end of the word, hence is a circular
interval.

The second part records a pointwise version of restriction and suppression:
filtering one chosen boundary word gives a boundary word of the pruned tree.
The earlier multiset identity retains the additional multiplicity
information, but is not needed by users of the pointwise statement.
-/

namespace QuartetDistance.RibbonRestriction

open Tree

/-! ## Linear and circular intervals in boundary words -/

/-- `S` occurs as one consecutive (possibly empty) block of `word`.-/
def LinearInterval [DecidableEq α] (S : Finset α) (word : List α) : Prop :=
  ∃ before middle after,
    word = before ++ middle ++ after ∧ middle.toFinset = S

/-- `S` is consecutive on the circle obtained by joining the ends of
`word`.  The second disjunct is the block which crosses the chosen cut.-/
def CircularInterval [DecidableEq α] (S : Finset α) (word : List α) : Prop :=
  ∃ before middle after,
    word = before ++ middle ++ after ∧
      (middle.toFinset = S ∨ (after ++ before).toFinset = S)

/--
@isnad1 id=circular.1h3v.s4.85a831ec3cb5 from=translated src=- shape=f15eaebe vocab=8584e2e9
-/
theorem LinearInterval.circular [DecidableEq α] {S : Finset α} {word : List α}
    (h : LinearInterval S word) : CircularInterval S word := by
  obtain ⟨before, middle, after, hword, hmiddle⟩ := h
  exact ⟨before, middle, after, hword, Or.inl hmiddle⟩

/-! ## Subtrees are edge-side blocks -/

/-- `u` is a rooted subtree of `t`.  Apart from the reflexive case, choosing
such a subtree is the same as choosing one side of a downward edge.-/
inductive IsSubtree : Tree.FullTree α → Tree.FullTree α → Prop where
  | here (t : Tree.FullTree α) : IsSubtree t t
  | left {u l : Tree.FullTree α} (r : Tree.FullTree α) :
      IsSubtree u l → IsSubtree u (.fork l r)
  | right (l : Tree.FullTree α) {u r : Tree.FullTree α} :
      IsSubtree u r → IsSubtree u (.fork l r)

/-- A selected frontier of an embedded subtree is a literal contiguous block
inside every selected frontier of the whole tree.
@isnad1 id=ex.2h4v.s6.46248645c934 from=translated src=- shape=944cbdf6 vocab=bec1fa75
-/
theorem frontier_block_of_isSubtree {u t : Tree.FullTree α}
    (hut : IsSubtree u t) {word : List α}
    (hword : word ∈ t.frontierProfile) :
    ∃ middle, middle ∈ u.frontierProfile ∧
      ∃ before after, word = before ++ middle ++ after := by
  induction hut generalizing word with
  | here t =>
      exact ⟨word, hword, [], [], by simp⟩
  | left r hut ih =>
      simp only [Tree.FullTree.frontierProfile_fork,
        Tree.FullTree.joinProfile, Multiset.mem_bind] at hword
      obtain ⟨leftWord, hleft, rightWord, hright, hword⟩ := hword
      simp at hword
      obtain ⟨middle, hmiddle, before, after, hleftEq⟩ := ih hleft
      rcases hword with rfl | rfl
      · refine ⟨middle, hmiddle, before, after ++ rightWord, ?_⟩
        simp [hleftEq, List.append_assoc]
      · refine ⟨middle, hmiddle, rightWord ++ before, after, ?_⟩
        simp [hleftEq, List.append_assoc]
  | right l hut ih =>
      simp only [Tree.FullTree.frontierProfile_fork,
        Tree.FullTree.joinProfile, Multiset.mem_bind] at hword
      obtain ⟨leftWord, hleft, rightWord, hright, hword⟩ := hword
      simp at hword
      obtain ⟨middle, hmiddle, before, after, hrightEq⟩ := ih hright
      rcases hword with rfl | rfl
      · refine ⟨middle, hmiddle, leftWord ++ before, after, ?_⟩
        simp [hrightEq, List.append_assoc]
      · refine ⟨middle, hmiddle, before, after ++ leftWord, ?_⟩
        simp [hrightEq, List.append_assoc]

/-- The labels below a selected edge form a linear interval in every
frontier word, independently of all rotations.
@isnad1 id=linearin.2h4v.s5.abfbdb9aa556 from=translated src=- shape=ffaa7b66 vocab=235a3e33
-/
theorem linearInterval_leaves_of_isSubtree [DecidableEq α]
    {u t : Tree.FullTree α} (hut : IsSubtree u t) {word : List α}
    (hword : word ∈ t.frontierProfile) :
    LinearInterval u.leaves.toFinset word := by
  obtain ⟨middle, hmiddle, before, after, hEq⟩ :=
    frontier_block_of_isSubtree hut hword
  refine ⟨before, middle, after, hEq, ?_⟩
  exact List.toFinset_eq_of_perm middle u.leaves
    (u.mem_frontierProfile_perm hmiddle)

private theorem outside_block_toFinset [DecidableEq α]
    (before middle after : List α)
    (hn : (before ++ middle ++ after).Nodup) :
    (after ++ before).toFinset =
      (before ++ middle ++ after).toFinset \ middle.toFinset := by
  have hbeforeMiddle : before.Disjoint middle :=
    ((List.nodup_append.mp hn).1).disjoint
  have hbeforeMiddleAfter : (before ++ middle).Disjoint after := hn.disjoint
  have hmiddleAfter : middle.Disjoint after := by
    rw [List.disjoint_left] at hbeforeMiddleAfter ⊢
    intro a haMiddle haAfter
    exact hbeforeMiddleAfter (by simp [haMiddle]) haAfter
  ext a
  simp only [List.mem_toFinset, List.mem_append, Finset.mem_sdiff]
  constructor
  · intro ha
    constructor
    · rcases ha with ha | ha
      · exact Or.inr ha
      · exact Or.inl (Or.inl ha)
    · rcases ha with ha | ha
      · exact (List.disjoint_left.mp hmiddleAfter.symm) ha
      · exact (List.disjoint_left.mp hbeforeMiddle) ha
  · rintro ⟨ha, hnot⟩
    rcases ha with (ha | ha) | ha
    · exact Or.inr ha
    · exact False.elim (hnot ha)
    · exact Or.inl ha

/-- For a noduplicated tree labelling, the complementary side of the same
edge is the circular block crossing the cut of the linear frontier.
@isnad1 id=circular.3h4v.s5.2611d5c948d7 from=translated src=- shape=760b8973 vocab=e754ca18
-/
theorem circularInterval_complement_of_isSubtree [DecidableEq α]
    {u t : Tree.FullTree α} (hut : IsSubtree u t) {word : List α}
    (hword : word ∈ t.frontierProfile) (hn : word.Nodup) :
    CircularInterval (t.leaves.toFinset \ u.leaves.toFinset) word := by
  obtain ⟨middle, hmiddle, before, after, hEq⟩ :=
    frontier_block_of_isSubtree hut hword
  have hmiddleFinset : middle.toFinset = u.leaves.toFinset :=
    List.toFinset_eq_of_perm middle u.leaves
      (u.mem_frontierProfile_perm hmiddle)
  have hwholeFinset : word.toFinset = t.leaves.toFinset :=
    List.toFinset_eq_of_perm word t.leaves
      (t.mem_frontierProfile_perm hword)
  refine ⟨before, middle, after, hEq, Or.inr ?_⟩
  calc
    (after ++ before).toFinset = word.toFinset \ middle.toFinset := by
      rw [hEq]
      exact outside_block_toFinset before middle after (hEq ▸ hn)
    _ = t.leaves.toFinset \ u.leaves.toFinset := by
      rw [hwholeFinset, hmiddleFinset]

/-! ## Pointwise restriction and suppression -/

/-- Filtering one chosen frontier gives a frontier of the pruned optional
tree.  This is the deterministic, pointwise content behind the profile
identity (which additionally counts all forgotten rotation bits).
@isnad1 id=mem.1h4v.s5.eb16de70b06d from=translated src=- shape=e22d9c60 vocab=c85446c3
-/
theorem restrictList_mem_optionProfile_of_mem_frontier [DecidableEq α]
    (t : Tree.FullTree α) (S : Finset α) {word : List α}
    (hword : word ∈ t.frontierProfile) :
    Tree.FullTree.restrictList S word ∈
      Tree.FullTree.optionProfile (Tree.FullTree.prune t S) := by
  have hmapped : Tree.FullTree.restrictList S word ∈
      t.frontierProfile.map (Tree.FullTree.restrictList S) :=
    Multiset.mem_map.mpr ⟨word, hword, rfl⟩
  rw [Tree.FullTree.map_restrictList_frontierProfile] at hmapped
  exact (Multiset.mem_nsmul.mp hmapped).2

/-- Conversely, every frontier word of the suppressed tree is the exact
filter of at least one frontier word of the original tree.  The lift is not
canonical because suppressed forks forget rotation bits.
@isnad1 id=ex.1h4v.s5.81e9f37586a6 from=translated src=- shape=c2a7217d vocab=c85446c3
-/
theorem exists_frontier_lift_of_mem_optionProfile [DecidableEq α]
    (t : Tree.FullTree α) (S : Finset α) {restricted : List α}
    (hrestricted : restricted ∈
      Tree.FullTree.optionProfile (Tree.FullTree.prune t S)) :
    ∃ word, word ∈ t.frontierProfile ∧
      Tree.FullTree.restrictList S word = restricted := by
  have hpositive : 2 ^ Tree.FullTree.suppressedForks t S ≠ 0 := by
    positivity
  have hscaled : restricted ∈
      (2 ^ Tree.FullTree.suppressedForks t S) •
        Tree.FullTree.optionProfile (Tree.FullTree.prune t S) :=
    Multiset.mem_nsmul.mpr ⟨hpositive, hrestricted⟩
  rw [← Tree.FullTree.map_restrictList_frontierProfile] at hscaled
  exact Multiset.mem_map.mp hscaled

/-! ## Unrooted phylogenetic boundary words -/

/-- Every boundary word chosen from the rooted-at-a-leaf representation is
also one of the two top-fork frontiers of the restored full tree.
@isnad1 id=mem.1h3v.s5.7c8ce3a77956 from=translated src=- shape=02196bb3 vocab=ca97f33d
-/
theorem mem_asFullTree_frontierProfile_of_mem_boundaryProfile
    [Fintype α] [DecidableEq α] (T : Tree.PhyloTree α)
    {word : List α} (hword : word ∈ T.boundaryProfile) :
    word ∈ T.asFullTree.frontierProfile := by
  simp only [Tree.PhyloTree.boundaryProfile, Multiset.mem_map] at hword
  obtain ⟨crownWord, hcrown, rfl⟩ := hword
  rw [T.asFullTree_frontierProfile]
  apply Multiset.mem_bind.mpr
  refine ⟨crownWord, hcrown, ?_⟩
  simp

/-- The restored full tree contains every label, so its leaf set is the
ambient finite universe.
@isnad1 id=eq.0h2v.s4.d4b5352a228b from=translated src=- shape=3eee2401 vocab=dc1faa13
-/
theorem asFullTree_leaves_toFinset_eq_univ
    [Fintype α] [DecidableEq α] (T : Tree.PhyloTree α) :
    T.asFullTree.leaves.toFinset = Finset.univ := by
  ext a
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  exact T.mem_asFullTree_leaves a

/-- Literal edge-interval lemma for an unrooted phylogenetic tree: either
side selected as a subtree of the cut-open full tree is consecutive in every
chosen boundary word.
@isnad1 id=linearin.2h4v.s5.8512a09a7beb from=translated src=- shape=5ff7f4f6 vocab=92598e17
-/
theorem boundary_linearInterval_edgeSide [Fintype α] [DecidableEq α]
    (T : Tree.PhyloTree α) {u : Tree.FullTree α}
    (hu : IsSubtree u T.asFullTree) {word : List α}
    (hword : word ∈ T.boundaryProfile) :
    LinearInterval u.leaves.toFinset word :=
  linearInterval_leaves_of_isSubtree hu
    (mem_asFullTree_frontierProfile_of_mem_boundaryProfile T hword)

/-- The opposite side of an unrooted edge is consecutive cyclically.
@isnad1 id=circular.2h4v.s5.1872b71736a2 from=translated src=- shape=48b082c2 vocab=ca4ed387
-/
theorem boundary_circularInterval_oppositeEdgeSide
    [Fintype α] [DecidableEq α]
    (T : Tree.PhyloTree α) {u : Tree.FullTree α}
    (hu : IsSubtree u T.asFullTree) {word : List α}
    (hword : word ∈ T.boundaryProfile) :
    CircularInterval (Finset.univ \ u.leaves.toFinset) word := by
  have h := circularInterval_complement_of_isSubtree hu
    (mem_asFullTree_frontierProfile_of_mem_boundaryProfile T hword)
    (T.mem_boundaryProfile_nodup hword)
  rwa [asFullTree_leaves_toFinset_eq_univ T] at h

/-- Pointwise restriction/suppression for a chosen global boundary outcome:
its exact restriction to a quartet is a frontier of the induced four-leaf
tree.
@isnad1 id=mem.2h4v.s6.013a56d2378c from=translated src=- shape=3dea1cda vocab=7a31f54b
-/
theorem restrict_boundary_mem_restrictedTree_frontier
    [Fintype α] [DecidableEq α]
    (T : Tree.PhyloTree α) (Q : Finset α) (hQ : Q.card = 4)
    {word : List α} (hword : word ∈ T.boundaryProfile) :
    Tree.FullTree.restrictList Q word ∈
      (T.restrictedTree Q hQ).frontierProfile := by
  have hfull := mem_asFullTree_frontierProfile_of_mem_boundaryProfile T hword
  have hpruned := restrictList_mem_optionProfile_of_mem_frontier
    T.asFullTree Q hfull
  rw [T.prune_asFullTree_eq_restrictedTree Q hQ] at hpruned
  exact hpruned

/-- Applying the crossing readout to the preceding pointwise restriction
lands in the crossing profile of the induced quartet.
@isnad1 id=mem.2h4v.s6.3e73b07ab55a from=translated src=- shape=4cb8bf16 vocab=9769d5c8
-/
theorem crossing_restriction_mem_restrictedTree_crossingProfile
    [Fintype α] [DecidableEq α]
    (T : Tree.PhyloTree α) (Q : Finset α) (hQ : Q.card = 4)
    {word : List α} (hword : word ∈ T.boundaryProfile) :
    Tree.FullTree.crossingList (Tree.FullTree.restrictList Q word) ∈
      (T.restrictedTree Q hQ).crossingProfile := by
  apply Multiset.mem_map.mpr
  exact ⟨Tree.FullTree.restrictList Q word,
    restrict_boundary_mem_restrictedTree_frontier T Q hQ hword, rfl⟩

end QuartetDistance.RibbonRestriction
