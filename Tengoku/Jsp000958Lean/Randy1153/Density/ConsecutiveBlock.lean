import Tengoku.Jsp000958Lean.Randy1153.Collapse.Definition
import Tengoku.Jsp000958Lean.Randy1153.Density.Damping
import Tengoku.Seed.Order.Interval.Finset.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The central sparse indices form a consecutive block

For an ordered node family, the preimage of the interval `J₁` is an interval
of indices.  This file identifies its increasing `Finset` enumeration with
the literal offset enumeration used by `Collapse.ConsecutiveBlock`.
-/

namespace Randy1153.Density

open Set
open Randy1153.Collapse

noncomputable section

/-- Membership in `sparseIndices` is order-convex for ordered nodes.
@isnad1 id=mem.4h7v.s6.51c44c6e5d2d from=translated src=- shape=52614a2a vocab=6405d710
-/
lemma sparseIndices_mem_of_between {n : ℕ} (nodes : OrderedNodes n) (a b : ℝ)
    {i j k : Fin n} (hi : i ∈ sparseIndices nodes.toNodeFamily a b)
    (hk : k ∈ sparseIndices nodes.toNodeFamily a b) (hij : i ≤ j) (hjk : j ≤ k) :
    j ∈ sparseIndices nodes.toNodeFamily a b := by
  have hi' : nodes.point i ∈ Set.Icc (j1Left a b) (j1Right a b) := by
    simpa only [sparseIndices, mem_insideIndices] using hi
  have hk' : nodes.point k ∈ Set.Icc (j1Left a b) (j1Right a b) := by
    simpa only [sparseIndices, mem_insideIndices] using hk
  have hleft : nodes.point i ≤ nodes.point j := nodes.strictMono.monotone hij
  have hright : nodes.point j ≤ nodes.point k := nodes.strictMono.monotone hjk
  simpa only [sparseIndices, mem_insideIndices] using
    (show nodes.point j ∈ Set.Icc (j1Left a b) (j1Right a b) from
      ⟨hi'.1.trans hleft, hright.trans hk'.2⟩)

/-- A nonempty sparse index set is exactly the finite index interval between
its minimum and maximum.
@isnad1 id=eq.1h4v.s6.fefbf00e3fd6 from=translated src=- shape=c6a69bf3 vocab=ee713681
-/
lemma sparseIndices_eq_Icc_min'_max' {n : ℕ} (nodes : OrderedNodes n) (a b : ℝ)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty) :
    sparseIndices nodes.toNodeFamily a b =
      Finset.Icc
        ((sparseIndices nodes.toNodeFamily a b).min' hS)
        ((sparseIndices nodes.toNodeFamily a b).max' hS) := by
  let S := sparseIndices nodes.toNodeFamily a b
  ext i
  constructor
  · intro hi
    exact Finset.mem_Icc.mpr ⟨S.min'_le i hi, S.le_max' i hi⟩
  · intro hi
    have hi' := Finset.mem_Icc.mp hi
    exact sparseIndices_mem_of_between nodes a b
      (S.min'_mem hS) (S.max'_mem hS) hi'.1 hi'.2

/-- The literal consecutive block occupied by a nonempty sparse index set.-/
noncomputable def sparseConsecutiveBlock {n : ℕ} (nodes : OrderedNodes n) (a b : ℝ)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty) :
    ConsecutiveBlock n (sparseIndices nodes.toNodeFamily a b).card where
  start := ((sparseIndices nodes.toNodeFamily a b).min' hS).val
  fits := by
    let S := sparseIndices nodes.toNodeFamily a b
    let lo := S.min' hS
    let hi := S.max' hS
    have hSI : S = Finset.Icc lo hi := sparseIndices_eq_Icc_min'_max' nodes a b hS
    have hcard : S.card = hi.val + 1 - lo.val := by
      rw [hSI, Fin.card_Icc]
    have hlohi : lo.val ≤ hi.val := by
      exact_mod_cast S.min'_le_max' hS
    have hhilt : hi.val < n := hi.isLt
    change lo.val + S.card ≤ n
    omega

/--
@isnad1 id=eq.1h4v.s5.080adaae97cb from=translated src=- shape=45b2b68d vocab=216b5465
-/
@[simp]
lemma sparseConsecutiveBlock_start {n : ℕ} (nodes : OrderedNodes n) (a b : ℝ)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty) :
    (sparseConsecutiveBlock nodes a b hS).start =
      ((sparseIndices nodes.toNodeFamily a b).min' hS).val :=
  rfl

/-- Every literal block index belongs to the sparse index set.
@isnad1 id=mem.1h5v.s6.ca0560a6337b from=translated src=- shape=1b7741ef vocab=e133cb46
-/
lemma sparseConsecutiveBlock_index_mem {n : ℕ} (nodes : OrderedNodes n) (a b : ℝ)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty)
    (k : Fin (sparseIndices nodes.toNodeFamily a b).card) :
    (sparseConsecutiveBlock nodes a b hS).index k ∈
      sparseIndices nodes.toNodeFamily a b := by
  let S := sparseIndices nodes.toNodeFamily a b
  let lo := S.min' hS
  let hi := S.max' hS
  have hSI : S = Finset.Icc lo hi := sparseIndices_eq_Icc_min'_max' nodes a b hS
  have hcard : S.card = hi.val + 1 - lo.val := by
    rw [hSI, Fin.card_Icc]
  have hlohi : lo.val ≤ hi.val := by
    exact_mod_cast S.min'_le_max' hS
  change (sparseConsecutiveBlock nodes a b hS).index k ∈ S
  rw [hSI, Finset.mem_Icc]
  constructor
  · simp only [Fin.le_iff_val_le_val, Collapse.ConsecutiveBlock.index_val,
      sparseConsecutiveBlock_start]
    exact Nat.le_add_right lo.val k.val
  · simp only [Fin.le_iff_val_le_val, Collapse.ConsecutiveBlock.index_val,
      sparseConsecutiveBlock_start]
    have hk : k.val < S.card := by simpa only [S] using k.isLt
    change lo.val + k.val ≤ hi.val
    omega

/-- The block's offset enumeration is the canonical increasing enumeration
of the sparse finset.
@isnad1 id=eq.1h5v.s7.b984ac70de1b from=translated src=- shape=188ee3fd vocab=436af951
-/
lemma sparseConsecutiveBlock_index_eq_orderEmbOfFin {n : ℕ}
    (nodes : OrderedNodes n) (a b : ℝ)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty)
    (k : Fin (sparseIndices nodes.toNodeFamily a b).card) :
    (sparseConsecutiveBlock nodes a b hS).index k =
      (sparseIndices nodes.toNodeFamily a b).orderEmbOfFin rfl k := by
  let e : Fin (sparseIndices nodes.toNodeFamily a b).card ↪o Fin n :=
    OrderEmbedding.ofStrictMono
      (sparseConsecutiveBlock nodes a b hS).index
      (sparseConsecutiveBlock nodes a b hS).index_strictMono
  have he : e = (sparseIndices nodes.toNodeFamily a b).orderEmbOfFin rfl :=
    Finset.orderEmbOfFin_unique' rfl fun i ↦ by
      simpa only [e, OrderEmbedding.coe_ofStrictMono] using
        sparseConsecutiveBlock_index_mem nodes a b hS i
  exact DFunLike.congr_fun he k

/-- Membership in the sparse finset is exactly membership in the literal
offset block; there are no omitted indices or extra block indices.
@isnad1 id=iff.1h5v.s6.b9d60686a386 from=translated src=- shape=726b5ea3 vocab=6b2042e7
-/
lemma mem_sparseIndices_iff_sparseConsecutiveBlock_Mem {n : ℕ}
    (nodes : OrderedNodes n) (a b : ℝ)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty) (i : Fin n) :
    i ∈ sparseIndices nodes.toNodeFamily a b ↔
      (sparseConsecutiveBlock nodes a b hS).Mem i := by
  let S := sparseIndices nodes.toNodeFamily a b
  let block := sparseConsecutiveBlock nodes a b hS
  constructor
  · intro hi
    let x : S := ⟨i, hi⟩
    let k : Fin S.card := (S.orderIsoOfFin rfl).symm x
    have henum : S.orderEmbOfFin rfl k = i := by
      rw [← Finset.coe_orderIsoOfFin_apply]
      rw [show S.orderIsoOfFin rfl k = x from (S.orderIsoOfFin rfl).apply_symm_apply x]
    have hblock : block.index k = i := by
      rw [sparseConsecutiveBlock_index_eq_orderEmbOfFin nodes a b hS]
      exact henum
    rw [← hblock]
    exact block.mem_index k
  · intro hi
    have hindex : block.index (block.localIndex i hi) = i := block.index_localIndex i hi
    rw [← hindex]
    exact sparseConsecutiveBlock_index_mem nodes a b hS (block.localIndex i hi)

/-- Positive cardinality is the arithmetic form of the constructor's
nonemptiness hypothesis.-/
noncomputable def sparseConsecutiveBlockOfCardPos {n : ℕ}
    (nodes : OrderedNodes n) (a b : ℝ)
    (hcard : 0 < (sparseIndices nodes.toNodeFamily a b).card) :
    ConsecutiveBlock n (sparseIndices nodes.toNodeFamily a b).card :=
  sparseConsecutiveBlock nodes a b (Finset.card_pos.mp hcard)

/--
@isnad1 id=eq.1h5v.s7.5f27cae522b1 from=translated src=- shape=c6aaa432 vocab=9aa229a6
-/
@[simp]
lemma sparseConsecutiveBlockOfCardPos_index {n : ℕ}
    (nodes : OrderedNodes n) (a b : ℝ)
    (hcard : 0 < (sparseIndices nodes.toNodeFamily a b).card)
    (k : Fin (sparseIndices nodes.toNodeFamily a b).card) :
    (sparseConsecutiveBlockOfCardPos nodes a b hcard).index k =
      (sparseIndices nodes.toNodeFamily a b).orderEmbOfFin rfl k :=
  sparseConsecutiveBlock_index_eq_orderEmbOfFin nodes a b
    (Finset.card_pos.mp hcard) k

/-- Every point indexed by the block lies in `J₁`.  In particular this
contains both endpoints of every internal block gap.
@isnad1 id=mem.1h5v.s6.29a8aa553a2e from=translated src=- shape=c676bcf6 vocab=4bb95448
-/
lemma sparseConsecutiveBlock_point_mem_j1 {n : ℕ}
    (nodes : OrderedNodes n) (a b : ℝ)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty)
    (k : Fin (sparseIndices nodes.toNodeFamily a b).card) :
    nodes.point ((sparseConsecutiveBlock nodes a b hS).index k) ∈
      Set.Icc (j1Left a b) (j1Right a b) := by
  simpa only [sparseIndices, mem_insideIndices] using
    sparseConsecutiveBlock_index_mem nodes a b hS k

/-- Every point indexed by the block lies in the original interval.
@isnad1 id=mem.2h5v.s6.a0a07c3d52b3 from=translated src=- shape=4ce22d3d vocab=5e2527ec
-/
lemma sparseConsecutiveBlock_point_mem_Icc {n : ℕ}
    (nodes : OrderedNodes n) {a b : ℝ} (hab : a < b)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty)
    (k : Fin (sparseIndices nodes.toNodeFamily a b).card) :
    nodes.point ((sparseConsecutiveBlock nodes a b hS).index k) ∈
      Set.Icc a b :=
  j1_subset_Icc hab (sparseConsecutiveBlock_point_mem_j1 nodes a b hS k)

/-- The closed hull between any two block nodes stays in `J₁`.  This
form is also useful when the chosen two nodes are not adjacent.
@isnad1 id=le.1h6v.s6.8711bbad6838 from=translated src=- shape=459c7ec6 vocab=3f84d23f
-/
lemma sparseConsecutiveBlock_hull_subset_j1 {n : ℕ}
    (nodes : OrderedNodes n) (a b : ℝ)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty)
    (i j : Fin (sparseIndices nodes.toNodeFamily a b).card) :
    Set.Icc
        (nodes.point ((sparseConsecutiveBlock nodes a b hS).index i))
        (nodes.point ((sparseConsecutiveBlock nodes a b hS).index j)) ⊆
      Set.Icc (j1Left a b) (j1Right a b) := by
  intro x hx
  have hi := sparseConsecutiveBlock_point_mem_j1 nodes a b hS i
  have hj := sparseConsecutiveBlock_point_mem_j1 nodes a b hS j
  exact ⟨hi.1.trans hx.1, hx.2.trans hj.2⟩

/-- The same closed hull stays in `[a,b]`.
@isnad1 id=le.2h6v.s6.3f6ae06962cc from=translated src=- shape=1c23dea3 vocab=bfa587e4
-/
lemma sparseConsecutiveBlock_hull_subset_Icc {n : ℕ}
    (nodes : OrderedNodes n) {a b : ℝ} (hab : a < b)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty)
    (i j : Fin (sparseIndices nodes.toNodeFamily a b).card) :
    Set.Icc
        (nodes.point ((sparseConsecutiveBlock nodes a b hS).index i))
        (nodes.point ((sparseConsecutiveBlock nodes a b hS).index j)) ⊆
      Set.Icc a b :=
  (sparseConsecutiveBlock_hull_subset_j1 nodes a b hS i j).trans
    (j1_subset_Icc hab)

/-- A local internal gap of the sparse block, regarded as the corresponding
global nodal gap.-/
def sparseConsecutiveBlockGapIndex {n : ℕ}
    (nodes : OrderedNodes n) (a b : ℝ)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty)
    (g : Fin ((sparseIndices nodes.toNodeFamily a b).card - 1)) : Fin (n - 1) :=
  ⟨(sparseConsecutiveBlock nodes a b hS).start + g.val, by
    have hg := g.isLt
    have hfits := (sparseConsecutiveBlock nodes a b hS).fits
    omega⟩

/--
@isnad1 id=eq.1h5v.s6.adf8a6272cb5 from=translated src=- shape=55dfae4a vocab=522a2f67
-/
@[simp]
lemma sparseConsecutiveBlockGapIndex_val {n : ℕ}
    (nodes : OrderedNodes n) (a b : ℝ)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty)
    (g : Fin ((sparseIndices nodes.toNodeFamily a b).card - 1)) :
    (sparseConsecutiveBlockGapIndex nodes a b hS g).val =
      (sparseConsecutiveBlock nodes a b hS).start + g.val :=
  rfl

/--
@isnad1 id=eq.1h5v.s6.673b785b848d from=translated src=- shape=db7c7509 vocab=a83a8ed9
-/
lemma gapLeftIndex_sparseConsecutiveBlockGapIndex {n : ℕ}
    (nodes : OrderedNodes n) (a b : ℝ)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty)
    (g : Fin ((sparseIndices nodes.toNodeFamily a b).card - 1)) :
    gapLeftIndex (sparseConsecutiveBlockGapIndex nodes a b hS g) =
      (sparseConsecutiveBlock nodes a b hS).index (gapLeftIndex g) := by
  apply Fin.ext
  simp only [gapLeftIndex_val, sparseConsecutiveBlockGapIndex_val,
    Collapse.ConsecutiveBlock.index_val]

/--
@isnad1 id=eq.1h5v.s6.caacfe8a911c from=translated src=- shape=db7c7509 vocab=7b24687b
-/
lemma gapRightIndex_sparseConsecutiveBlockGapIndex {n : ℕ}
    (nodes : OrderedNodes n) (a b : ℝ)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty)
    (g : Fin ((sparseIndices nodes.toNodeFamily a b).card - 1)) :
    gapRightIndex (sparseConsecutiveBlockGapIndex nodes a b hS g) =
      (sparseConsecutiveBlock nodes a b hS).index (gapRightIndex g) := by
  apply Fin.ext
  simp only [gapRightIndex_val, sparseConsecutiveBlockGapIndex_val,
    Collapse.ConsecutiveBlock.index_val]
  omega

/-- Every internal closed nodal gap of the sparse block lies in `J₁`.
@isnad1 id=le.1h5v.s6.f511f8380d81 from=translated src=- shape=62a08730 vocab=043ede50
-/
lemma sparseConsecutiveBlock_closedGap_subset_j1 {n : ℕ}
    (nodes : OrderedNodes n) (a b : ℝ)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty)
    (g : Fin ((sparseIndices nodes.toNodeFamily a b).card - 1)) :
    closedGap nodes (sparseConsecutiveBlockGapIndex nodes a b hS g) ⊆
      Set.Icc (j1Left a b) (j1Right a b) := by
  rw [closedGap, gapLeftIndex_sparseConsecutiveBlockGapIndex,
    gapRightIndex_sparseConsecutiveBlockGapIndex]
  exact sparseConsecutiveBlock_hull_subset_j1 nodes a b hS
    (gapLeftIndex g) (gapRightIndex g)

/-- Every internal closed nodal gap of the sparse block lies in `[a,b]`.
@isnad1 id=le.2h5v.s6.9c4ce61e4b7f from=translated src=- shape=3d8fe970 vocab=8c407521
-/
lemma sparseConsecutiveBlock_closedGap_subset_Icc {n : ℕ}
    (nodes : OrderedNodes n) {a b : ℝ} (hab : a < b)
    (hS : (sparseIndices nodes.toNodeFamily a b).Nonempty)
    (g : Fin ((sparseIndices nodes.toNodeFamily a b).card - 1)) :
    closedGap nodes (sparseConsecutiveBlockGapIndex nodes a b hS g) ⊆
      Set.Icc a b :=
  (sparseConsecutiveBlock_closedGap_subset_j1 nodes a b hS g).trans
    (j1_subset_Icc hab)

end

end Randy1153.Density
