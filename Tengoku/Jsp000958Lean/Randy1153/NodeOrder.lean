import Tengoku.Jsp000958Lean.Randy1153.Basic
import Tengoku.Seed.Algebra.Polynomial.Roots
import Tengoku.Seed.Data.Finset.Sort

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordering and reindexing node families

The public `NodeFamily` remains permutation invariant.  This module supplies
an internal strictly increasing representation, together with checked
transport lemmas showing that Lagrange and Lebesgue data do not depend on the
enumeration.
-/

namespace Randy1153

open Polynomial

noncomputable section

namespace NodeFamily

/-- Reindex a node family by a permutation of `Fin n`.-/
def reindex {n : ℕ} (nodes : NodeFamily n) (e : Equiv.Perm (Fin n)) : NodeFamily n where
  point := nodes.point ∘ e
  injective := nodes.injective.comp e.injective
  mem_Icc i := nodes.mem_Icc (e i)

/--
@isnad1 id=eq.0h4v.s5.e7f18af377e9 from=translated src=- shape=88dc6672 vocab=10090716
-/
@[simp]
lemma reindex_point {n : ℕ} (nodes : NodeFamily n) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    (nodes.reindex e).point i = nodes.point (e i) :=
  rfl

/--
@isnad1 id=eq.0h2v.s3.460a584804b9 from=translated src=- shape=582cfbec vocab=78ecfa9f
-/
@[simp]
lemma reindex_refl {n : ℕ} (nodes : NodeFamily n) :
    nodes.reindex (Equiv.refl (Fin n)) = nodes := by
  apply NodeFamily.ext
  rfl

/-- Successive reindexings compose in the order in which indices are read.
@isnad1 id=eq.0h4v.s5.3b15e11d30fa from=translated src=- shape=48712972 vocab=5ab9ce27
-/
lemma reindex_reindex {n : ℕ} (nodes : NodeFamily n) (e f : Equiv.Perm (Fin n)) :
    (nodes.reindex e).reindex f = nodes.reindex (f.trans e) := by
  apply NodeFamily.ext
  rfl

end NodeFamily

/-- Reindexing carries the fundamental function indexed by `k` to the
fundamental function indexed by `e k`.
@isnad1 id=eq.0h5v.s5.9a0e3f8cfd85 from=translated src=- shape=c3871ebe vocab=6f7abeb7
-/
lemma lagrangeFundamental_reindex {n : ℕ} (nodes : NodeFamily n)
    (e : Equiv.Perm (Fin n)) (k : Fin n) (t : ℝ) :
    lagrangeFundamental (nodes.reindex e) k t =
      lagrangeFundamental nodes (e k) t := by
  classical
  simp only [lagrangeFundamental, NodeFamily.reindex_point]
  apply Finset.prod_equiv e
  · intro i
    simp
  · intro i _
    rfl

/-- Polynomial form of permutation invariance of the Lagrange basis.
@isnad1 id=eq.0h4v.s5.18eb186a58ec from=translated src=- shape=777de872 vocab=d500d4df
-/
lemma lagrangeBasis_reindex {n : ℕ} (nodes : NodeFamily n)
    (e : Equiv.Perm (Fin n)) (k : Fin n) :
    lagrangeBasis (nodes.reindex e) k = lagrangeBasis nodes (e k) := by
  apply Polynomial.funext
  intro t
  rw [lagrangeBasis_eval, lagrangeBasis_eval, lagrangeFundamental_reindex]

/-- The Lebesgue function is independent of the enumeration of its nodes.
@isnad1 id=eq.0h4v.s4.d0d7f81aa8e5 from=translated src=- shape=d692867a vocab=a6e724b0
-/
lemma lebesgueFunction_reindex {n : ℕ} (nodes : NodeFamily n)
    (e : Equiv.Perm (Fin n)) (t : ℝ) :
    lebesgueFunction (nodes.reindex e) t = lebesgueFunction nodes t := by
  simp only [lebesgueFunction, lagrangeFundamental_reindex]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- The interval supremum of the Lebesgue function is permutation invariant.
@isnad1 id=eq.0h5v.s4.d6911465ec05 from=translated src=- shape=a315a940 vocab=bd0b53f8
-/
lemma lebesgueOn_reindex {n : ℕ} (nodes : NodeFamily n)
    (e : Equiv.Perm (Fin n)) (a b : ℝ) :
    lebesgueOn (nodes.reindex e) a b = lebesgueOn nodes a b := by
  simp only [lebesgueOn, lebesgueFunction_reindex]

/-- An internally ordered node family.  The public theorem will obtain this
from an arbitrary `NodeFamily` by the canonical sorting construction below.-/
structure OrderedNodes (n : ℕ) extends NodeFamily n where
  strictMono : StrictMono point

namespace OrderedNodes

/-- Forget the ordering proof when an arbitrary node family is expected.-/
instance {n : ℕ} : Coe (OrderedNodes n) (NodeFamily n) :=
  ⟨OrderedNodes.toNodeFamily⟩

/--
@isnad1 id=eq.0h3v.s4.809d66136483 from=translated src=- shape=4909777f vocab=8e7d46a0
-/
@[simp]
lemma coe_point {n : ℕ} (nodes : OrderedNodes n) (i : Fin n) :
    (nodes : NodeFamily n).point i = nodes.point i :=
  rfl

/-- Earlier indices of an ordered family give strictly smaller nodes.
@isnad1 id=lt.1h4v.s5.7f56bb78516b from=translated src=- shape=ee063282 vocab=afd79040
-/
lemma point_lt {n : ℕ} (nodes : OrderedNodes n) {i j : Fin n} (hij : i < j) :
    nodes.point i < nodes.point j :=
  nodes.strictMono hij

/-- Every ordered node retains the lower endpoint bound.
@isnad1 id=le.0h3v.s4.da9e7047d4c3 from=translated src=- shape=dc09e7ff vocab=cd6ffc86
-/
lemma neg_one_le {n : ℕ} (nodes : OrderedNodes n) (i : Fin n) :
    (-1 : ℝ) ≤ nodes.point i :=
  (nodes.mem_Icc i).1

/-- Every ordered node retains the upper endpoint bound.
@isnad1 id=le.0h3v.s4.ad02b2df8185 from=translated src=- shape=5efa48d0 vocab=b1b2bd53
-/
lemma le_one {n : ℕ} (nodes : OrderedNodes n) (i : Fin n) :
    nodes.point i ≤ (1 : ℝ) :=
  (nodes.mem_Icc i).2

end OrderedNodes

namespace NodeFamily

/-- The finite set underlying a node family.-/
def nodeFinset {n : ℕ} (nodes : NodeFamily n) : Finset ℝ :=
  Finset.univ.image nodes.point

/--
@isnad1 id=iff.0h3v.s5.c5b76f29c952 from=translated src=- shape=e932c8c3 vocab=2cc61c7d
-/
@[simp]
lemma mem_nodeFinset {n : ℕ} (nodes : NodeFamily n) (x : ℝ) :
    x ∈ nodes.nodeFinset ↔ ∃ i : Fin n, nodes.point i = x := by
  simp [nodeFinset]

/-- Injectivity ensures that the set of nodes has cardinality exactly `n`.
@isnad1 id=eq.0h2v.s3.75ed554176a2 from=translated src=- shape=37d26c04 vocab=d34acbea
-/
@[simp]
lemma card_nodeFinset {n : ℕ} (nodes : NodeFamily n) : nodes.nodeFinset.card = n := by
  classical
  rw [nodeFinset, Finset.card_image_of_injOn nodes.injective.injOn,
    Finset.card_univ, Fintype.card_fin]

/-- The increasing enumeration of the underlying finite set of nodes.-/
def sortedPoint {n : ℕ} (nodes : NodeFamily n) : Fin n ↪o ℝ :=
  nodes.nodeFinset.orderEmbOfFin (card_nodeFinset nodes)

/--
@isnad1 id=mem.0h3v.s5.932ca87294fd from=translated src=- shape=5a604606 vocab=4b12e77f
-/
@[simp]
lemma sortedPoint_mem_nodeFinset {n : ℕ} (nodes : NodeFamily n) (i : Fin n) :
    nodes.sortedPoint i ∈ nodes.nodeFinset :=
  Finset.orderEmbOfFin_mem _ _ _

/-- Canonically sort an arbitrary node family into a strictly increasing one.-/
def sorted {n : ℕ} (nodes : NodeFamily n) : OrderedNodes n where
  point := nodes.sortedPoint
  injective := nodes.sortedPoint.injective
  mem_Icc i := by
    rcases (mem_nodeFinset nodes (nodes.sortedPoint i)).mp
      (sortedPoint_mem_nodeFinset nodes i) with ⟨j, hj⟩
    rw [← hj]
    exact nodes.mem_Icc j
  strictMono := nodes.sortedPoint.strictMono

/--
@isnad1 id=eq.0h3v.s5.3e37be7991b7 from=translated src=- shape=6714f7f1 vocab=741d7772
-/
@[simp]
lemma sorted_point {n : ℕ} (nodes : NodeFamily n) (i : Fin n) :
    nodes.sorted.point i = nodes.sortedPoint i :=
  rfl

/-- The original enumeration is equivalent to its finite range.-/
def rangeEquiv {n : ℕ} (nodes : NodeFamily n) : Fin n ≃ ↥nodes.nodeFinset :=
  Equiv.ofBijective
    (fun i => ⟨nodes.point i, (mem_nodeFinset nodes _).2 ⟨i, rfl⟩⟩)
    ⟨fun i j h => nodes.injective (congrArg Subtype.val h), fun y => by
      rcases (mem_nodeFinset nodes y).mp y.property with ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩⟩

/--
@isnad1 id=eq.0h3v.s7.e9304d83c1c4 from=translated src=- shape=bef458e7 vocab=fc3d351d
-/
@[simp]
lemma coe_rangeEquiv_apply {n : ℕ} (nodes : NodeFamily n) (i : Fin n) :
    ((nodes.rangeEquiv i : nodes.nodeFinset) : ℝ) = nodes.point i :=
  rfl

/-- The permutation which reads the original nodes in increasing order.-/
def sortingPerm {n : ℕ} (nodes : NodeFamily n) : Equiv.Perm (Fin n) :=
  nodes.nodeFinset.orderIsoOfFin (card_nodeFinset nodes) |>.toEquiv |>.trans
    nodes.rangeEquiv.symm

/-- Applying `sortingPerm` to the old enumeration gives the canonical sorted
enumeration pointwise.
@isnad1 id=eq.0h3v.s5.92fc72bf5009 from=translated src=- shape=59660ff0 vocab=f17de591
-/
lemma point_sortingPerm {n : ℕ} (nodes : NodeFamily n) (i : Fin n) :
    nodes.point (nodes.sortingPerm i) = nodes.sorted.point i := by
  simpa only [sortingPerm, Equiv.trans_apply, OrderIso.coe_toEquiv, coe_rangeEquiv_apply, sorted_point,
    sortedPoint, Finset.coe_orderIsoOfFin_apply] using
    congrArg Subtype.val
      (nodes.rangeEquiv.apply_symm_apply
        (nodes.nodeFinset.orderIsoOfFin (card_nodeFinset nodes) i))

/-- The canonical sorted family really is a reindexing, rather than a new set
of nodes.
@isnad1 id=eq.0h2v.s4.56a797384c90 from=translated src=- shape=e34425d3 vocab=a83af1f9
-/
lemma reindex_sortingPerm {n : ℕ} (nodes : NodeFamily n) :
    nodes.reindex nodes.sortingPerm = nodes.sorted.toNodeFamily := by
  apply NodeFamily.ext
  funext i
  exact point_sortingPerm nodes i

/-- Sorting preserves the full Lebesgue function.
@isnad1 id=eq.0h3v.s4.97666a472a53 from=translated src=- shape=56ed178e vocab=be81a8ad
-/
lemma lebesgueFunction_sorted {n : ℕ} (nodes : NodeFamily n) (t : ℝ) :
    lebesgueFunction nodes.sorted.toNodeFamily t = lebesgueFunction nodes t := by
  rw [← reindex_sortingPerm nodes, lebesgueFunction_reindex]

/-- Sorting preserves every interval supremum of the Lebesgue function.
@isnad1 id=eq.0h4v.s4.0bf4ccaefcdb from=translated src=- shape=6f33675f vocab=317c6401
-/
lemma lebesgueOn_sorted {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) :
    lebesgueOn nodes.sorted.toNodeFamily a b = lebesgueOn nodes a b := by
  rw [← reindex_sortingPerm nodes, lebesgueOn_reindex]

end NodeFamily

end

end Randy1153
