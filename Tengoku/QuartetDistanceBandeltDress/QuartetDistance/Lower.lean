import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.Upper

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The random-labelling lower bound

This file proves the elementary lower half of the Bandelt--Dress estimate.
Relabelling is defined on the concrete rooted-tree model, and a three-cycle
supported on a fixed quartet gives a free cyclic action on its three displayed
topology channels.  Consequently every fixed quartet has the exact uniform
`8/24` local law (and its global-permutation analogue), so one relabelling has
distance at least two thirds of all quartets.
-/

namespace QuartetDistance.Lower

open Tree

universe u v w

/-! ## Relabelling concrete rooted phylogenetic trees -/

/-- An equivalence carries the labels different from `r` to the labels
different from `e r`.-/
def awayEquiv (e : α ≃ β) (r : α) :
    {a : α // a ≠ r} ≃ {b : β // b ≠ e r} where
  toFun a := ⟨e a.1, fun h => a.2 (e.injective h)⟩
  invFun b := ⟨e.symm b.1, fun h => b.2 (by simpa using congrArg e h)⟩
  left_inv a := by ext; simp
  right_inv b := by ext; simp

/--
@isnad1 id=eq.0h5v.s8.95f408077ff8 from=translated src=- shape=4fb3b3a5 vocab=e6c15296
-/
@[simp] theorem awayEquiv_coe (e : α ≃ β) (r : α) (a : {a : α // a ≠ r}) :
    (awayEquiv e r a : β) = e a := rfl

/-- Relabel every leaf of a rooted phylogenetic tree by an equivalence.-/
def relabel [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (T : PhyloTree α) : PhyloTree β where
  root := e T.root
  crown := T.crown.map (awayEquiv e T.root)
  nodup_leaves := by
    rw [Tree.FullTree.leaves_map]
    exact T.nodup_leaves.map (awayEquiv e T.root).injective
  exhaustive := by
    intro b
    let a : {a : α // a ≠ T.root} := (awayEquiv e T.root).symm b
    have ha := T.exhaustive a
    rw [Tree.FullTree.leaves_map, List.mem_map]
    exact ⟨a, ha, (awayEquiv e T.root).apply_symm_apply b⟩

/--
@isnad1 id=eq.0h4v.s5.a501f881a04f from=translated src=- shape=8b42bc84 vocab=c9127fd8
-/
@[simp] theorem relabel_root [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (T : PhyloTree α) :
    (relabel e T).root = e T.root := rfl

private theorem fullTree_map_congr {α : Type u} {β : Type v} {f g : α → β}
    (h : ∀ a, f a = g a) (t : FullTree α) : t.map f = t.map g := by
  induction t with
  | leaf a => simp [Tree.FullTree.map, h a]
  | fork l r ihl ihr => simp [Tree.FullTree.map, ihl, ihr]

private theorem fullTree_map_map {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β) (g : β → γ)
    (t : FullTree α) : (t.map f).map g = t.map (g ∘ f) := by
  induction t with
  | leaf => rfl
  | fork l r ihl ihr => simp [Tree.FullTree.map, ihl, ihr]

/--
@isnad1 id=eq.0h6v.s6.469c6aca18d2 from=translated src=- shape=e3dfc788 vocab=af0e8026
-/
theorem relabel_trans [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (e : α ≃ β) (f : β ≃ γ) (T : PhyloTree α) :
    relabel f (relabel e T) = relabel (e.trans f) T := by
  cases T with
  | mk root crown nodup exhaustive =>
      simp only [relabel]
      congr 1
      rw [fullTree_map_map]
      apply fullTree_map_congr
      intro a
      exact Subtype.ext (by rfl)

/-! ## Naturality of restriction and displayed quartet splits -/

/--
@isnad1 id=eq.0h5v.s6.b7fb304d4c0e from=translated src=- shape=83e7835f vocab=3a862d71
-/
theorem prune_map_equiv [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (t : FullTree α) (S : Finset α) :
    (t.map e).prune (S.map e.toEmbedding) =
      (t.prune S).map (fun u => u.map e) := by
  induction t with
  | leaf a => simp [Tree.FullTree.map, Tree.FullTree.prune]
  | fork l r ihl ihr =>
      simp only [Tree.FullTree.map, Tree.FullTree.prune, ihl, ihr]
      cases l.prune S <;> cases r.prune S <;> rfl

/--
@isnad1 id=eq.0h4v.s6.e79d1c944263 from=translated src=- shape=6e92e2cd vocab=6045362c
-/
theorem asFullTree_relabel [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (T : PhyloTree α) :
    (relabel e T).asFullTree = T.asFullTree.map e := by
  cases T with
  | mk root crown nodup exhaustive =>
      simp only [relabel, Tree.PhyloTree.asFullTree, Tree.FullTree.map]
      congr 1
      rw [fullTree_map_map, fullTree_map_map]
      apply fullTree_map_congr
      intro a
      rfl

/--
@isnad1 id=eq.0h7v.s6.7abe17140946 from=translated src=- shape=59bcdb27 vocab=61189c2b
-/
theorem mapSplit_blockSplit [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a b c d : α) :
    Circular.mapSplit e.toEmbedding (Tree.FullTree.blockSplit a b c d) =
      Tree.FullTree.blockSplit (e a) (e b) (e c) (e d) := by
  ext A
  simp [Tree.FullTree.blockSplit, Circular.mapSplit, Circular.splitOf,
    Circular.pair]

/-- On a genuine four-leaf tree, applying an equivalence to all leaf labels
applies the same equivalence to its displayed split.
@isnad1 id=eq.2h4v.s6.286e8a797603 from=translated src=- shape=ae7d799e vocab=e8c548f8
-/
theorem displayedSplit_map_equiv [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (t : FullTree α)
    (hlen : t.leaves.length = 4) (hnodup : t.leaves.Nodup) :
    (t.map e).displayedSplit =
      Circular.mapSplit e.toEmbedding t.displayedSplit := by
  obtain ⟨a, b, c, d, hs⟩ := Tree.FullTree.shape_of_leaves_length_eq_four t hlen
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_one_three a b c d hn]
    rw [show (FullTree.fork (FullTree.leaf a)
        (FullTree.fork (FullTree.leaf b) (FullTree.fork (FullTree.leaf c)
          (FullTree.leaf d)))).map e =
        FullTree.fork (FullTree.leaf (e a))
          (FullTree.fork (FullTree.leaf (e b))
            (FullTree.fork (FullTree.leaf (e c)) (FullTree.leaf (e d)))) by rfl]
    rw [Tree.FullTree.displayedSplit_shape_one_three]
    · exact (mapSplit_blockSplit e a b c d).symm
    · exact hn.map e.injective
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_one_twone a b c d hn]
    rw [show (FullTree.fork (FullTree.leaf a)
        (FullTree.fork (FullTree.fork (FullTree.leaf b) (FullTree.leaf c))
          (FullTree.leaf d))).map e =
        FullTree.fork (FullTree.leaf (e a))
          (FullTree.fork (FullTree.fork (FullTree.leaf (e b))
            (FullTree.leaf (e c))) (FullTree.leaf (e d))) by rfl]
    rw [Tree.FullTree.displayedSplit_shape_one_twone]
    · exact (mapSplit_blockSplit e a d b c).symm
    · exact hn.map e.injective
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_two_two a b c d hn]
    rw [show (FullTree.fork (FullTree.fork (FullTree.leaf a) (FullTree.leaf b))
        (FullTree.fork (FullTree.leaf c) (FullTree.leaf d))).map e =
        FullTree.fork (FullTree.fork (FullTree.leaf (e a)) (FullTree.leaf (e b)))
          (FullTree.fork (FullTree.leaf (e c)) (FullTree.leaf (e d))) by rfl]
    rw [Tree.FullTree.displayedSplit_shape_two_two]
    · exact (mapSplit_blockSplit e a b c d).symm
    · exact hn.map e.injective
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_threetwo_one a b c d hn]
    rw [show (FullTree.fork
        (FullTree.fork (FullTree.leaf a)
          (FullTree.fork (FullTree.leaf b) (FullTree.leaf c)))
        (FullTree.leaf d)).map e =
        FullTree.fork
          (FullTree.fork (FullTree.leaf (e a))
            (FullTree.fork (FullTree.leaf (e b)) (FullTree.leaf (e c))))
          (FullTree.leaf (e d)) by rfl]
    rw [Tree.FullTree.displayedSplit_shape_threetwo_one]
    · exact (mapSplit_blockSplit e a d b c).symm
    · exact hn.map e.injective
  · have hn : [a, b, c, d].Nodup := by simpa using hnodup
    rw [Tree.FullTree.displayedSplit_shape_three_one a b c d hn]
    rw [show (FullTree.fork
        (FullTree.fork (FullTree.fork (FullTree.leaf a) (FullTree.leaf b))
          (FullTree.leaf c)) (FullTree.leaf d)).map e =
        FullTree.fork
          (FullTree.fork (FullTree.fork (FullTree.leaf (e a))
            (FullTree.leaf (e b))) (FullTree.leaf (e c)))
          (FullTree.leaf (e d)) by rfl]
    rw [Tree.FullTree.displayedSplit_shape_three_one]
    · exact (mapSplit_blockSplit e a b c d).symm
    · exact hn.map e.injective

/--
@isnad1 id=eq.1h5v.s6.a0fb6982badb from=translated src=- shape=98915974 vocab=bc8bbcec
-/
theorem restrictedTree_relabel [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (T : PhyloTree α)
    (Q : Finset α) (hQ : Q.card = 4) :
    (relabel e T).restrictedTree (Q.map e.toEmbedding)
        (by simpa using hQ) =
      (T.restrictedTree Q hQ).map e := by
  have hm := prune_map_equiv e T.asFullTree Q
  rw [← asFullTree_relabel e T] at hm
  rw [(relabel e T).prune_asFullTree_eq_restrictedTree
      (Q.map e.toEmbedding) (by simpa using hQ),
    T.prune_asFullTree_eq_restrictedTree Q hQ] at hm
  simpa using hm

/-- Relabelling transports the true split on an image quartet.
@isnad1 id=eq.1h5v.s6.c33b405c0600 from=translated src=- shape=df9a9497 vocab=b065c59b
-/
theorem displayedSplitOn_relabel [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (T : PhyloTree α)
    (Q : Finset α) (hQ : Q.card = 4) :
    (relabel e T).displayedSplitOn (Q.map e.toEmbedding)
        (by simpa using hQ) =
      Circular.mapSplit e.toEmbedding (T.displayedSplitOn Q hQ) := by
  unfold Tree.PhyloTree.displayedSplitOn
  rw [restrictedTree_relabel]
  exact displayedSplit_map_equiv e (T.restrictedTree Q hQ)
    (T.restrictedTree_leaves_length Q hQ) (T.restrictedTree_nodup Q hQ)

/--
@isnad1 id=eq.1h3v.s5.eb193d1e852f from=translated src=- shape=ea9606d4 vocab=8dbd9750
-/
theorem restrictedTree_toFinset [Fintype α] [DecidableEq α]
    (T : PhyloTree α) (Q : Finset α) (hQ : Q.card = 4) :
    (T.restrictedTree Q hQ).leaves.toFinset = Q := by
  rw [T.restrictedTree_leaves Q hQ]
  ext a
  simp [Tree.FullTree.restrictList, T.mem_referenceLeaves a]

/-! ## The three-cycle supported on one quartet -/

/-- Fix slot `0` and cycle the other three slots.-/
def slotCycle : Circular.Perm4 :=
  Circular.perm4OfTuples 0 2 3 1 0 3 1 2 (by decide) (by decide)

/-- The induced cycle of the three canonical topology channels.-/
def topologyCycle : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide
  right_inv := by decide

/-- Extend `slotCycle` by the identity away from the range of `q`.-/
noncomputable def quartetCycle (q : Upper.Quartet n) : Equiv.Perm (Fin n) :=
  slotCycle.extendDomain (Upper.quartetEmbedding q).toEquivRange

/--
@isnad1 id=eq.0h3v.s6.375590f7b7bf from=translated src=- shape=f42bff7d vocab=547d6967
-/
@[simp] theorem quartetCycle_apply (q : Upper.Quartet n) (i : Circular.Four) :
    quartetCycle q (Upper.quartetEmbedding q i) =
      Upper.quartetEmbedding q (slotCycle i) := by
  exact Equiv.Perm.extendDomain_apply_image slotCycle
    (Upper.quartetEmbedding q).toEquivRange i

/-- The whole displayed-topology vector after a global relabelling.-/
def relabelTopologies (T : PhyloTree (Fin n))
    (pi : Equiv.Perm (Fin n)) (q : Upper.Quartet n) : Fin 3 :=
  Upper.displayedTopology (relabel pi T) q

/-- Right composition by a fixed permutation is a permutation of the global
relabelling sample space.-/
def rightTrans (g : Equiv.Perm α) : Equiv.Perm α ≃ Equiv.Perm α where
  toFun pi := pi.trans g
  invFun pi := pi.trans g.symm
  left_inv pi := by ext x; simp
  right_inv pi := by ext x; simp

/-! ## Extracting a relabelling at least as good as the average -/

/-! ## A concrete nonempty family of tree shapes -/

/-- The right-comb full tree with leaf word `a :: xs`.-/
def caterpillar : (a : α) → List α → FullTree α
  | a, [] => .leaf a
  | a, b :: xs => .fork (.leaf a) (caterpillar b xs)

/--
@isnad1 id=eq.0h3v.s4.ec5d12e5e881 from=translated src=- shape=4e2dc77a vocab=1899ff33
-/
@[simp] theorem caterpillar_leaves (a : α) (xs : List α) :
    (caterpillar a xs).leaves = a :: xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih => simp [caterpillar, ih]

/-- For every `n ≥ 4` the concrete rooted model is inhabited.  The witness
is the caterpillar whose distinguished root is `0` and whose crown starts at
`1`; the remaining labels are taken from the finite universe exactly once.
@isnad1 id=nonempty.1h1v.s4.fbb578b818fa from=translated src=- shape=74fbb319 vocab=197e0a7b
-/
theorem nonempty_phyloTree_fin (n : ℕ) (hn : 4 ≤ n) :
    Nonempty (PhyloTree (Fin n)) := by
  let r : Fin n := ⟨0, by omega⟩
  let a₀ : {a : Fin n // a ≠ r} :=
    ⟨⟨1, by omega⟩, by
      intro h
      have := congrArg Fin.val h
      norm_num at this⟩
  let xs : List {a : Fin n // a ≠ r} :=
    ((Finset.univ : Finset {a : Fin n // a ≠ r}).erase a₀).toList
  refine ⟨⟨r, caterpillar a₀ xs, ?_, ?_⟩⟩
  · rw [caterpillar_leaves]
    rw [List.nodup_cons]
    constructor
    · simp [xs]
    · exact Finset.nodup_toList _
  · intro a
    rw [caterpillar_leaves]
    simp only [List.mem_cons]
    by_cases h : a = a₀
    · exact Or.inl h
    · right
      rw [show xs = ((Finset.univ : Finset {a : Fin n // a ≠ r}).erase a₀).toList
        from rfl, Finset.mem_toList]
      simp [h]

end QuartetDistance.Lower
