import Tengoku.Jsp000937Lean.Erdos1153.Basic
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

namespace Erdos1153

open Polynomial

noncomputable section

namespace NodeFamily

/-- Reindex a node family by a permutation of `Fin n`.-/
def reindex {n : ℕ} (nodes : NodeFamily n) (e : Equiv.Perm (Fin n)) : NodeFamily n where
  point := nodes.point ∘ e
  injective := nodes.injective.comp e.injective
  mem_Icc i := nodes.mem_Icc (e i)

/--
@isnad1 id=eq.0h4v.s5.bf5a9e9d51c2 from=translated src=- shape=88dc6672 vocab=9df0e1bf
-/
@[simp]
lemma reindex_point {n : ℕ} (nodes : NodeFamily n) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    (nodes.reindex e).point i = nodes.point (e i) :=
  rfl

/--
@isnad1 id=eq.0h2v.s3.4849a940ba61 from=translated src=- shape=582cfbec vocab=8c619269
-/
@[simp]
lemma reindex_refl {n : ℕ} (nodes : NodeFamily n) :
    nodes.reindex (Equiv.refl (Fin n)) = nodes := by
  apply NodeFamily.ext
  rfl

/-- Successive reindexings compose in the order in which indices are read.
@isnad1 id=eq.0h4v.s5.b4a8bdbbbe03 from=translated src=- shape=48712972 vocab=28cecaee
-/
lemma reindex_reindex {n : ℕ} (nodes : NodeFamily n) (e f : Equiv.Perm (Fin n)) :
    (nodes.reindex e).reindex f = nodes.reindex (f.trans e) := by
  apply NodeFamily.ext
  rfl

end NodeFamily

/-- Reindexing carries the fundamental function indexed by `k` to the
fundamental function indexed by `e k`.
@isnad1 id=eq.0h5v.s5.744dcf93a795 from=translated src=- shape=c3871ebe vocab=a63584ec
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
@isnad1 id=eq.0h4v.s5.2cf158fc4dd8 from=translated src=- shape=777de872 vocab=debe1ab4
-/
lemma lagrangeBasis_reindex {n : ℕ} (nodes : NodeFamily n)
    (e : Equiv.Perm (Fin n)) (k : Fin n) :
    lagrangeBasis (nodes.reindex e) k = lagrangeBasis nodes (e k) := by
  apply Polynomial.funext
  intro t
  rw [lagrangeBasis_eval, lagrangeBasis_eval, lagrangeFundamental_reindex]

/-- The Lebesgue function is independent of the enumeration of its nodes.
@isnad1 id=eq.0h4v.s4.acc1f04f0b34 from=translated src=- shape=d692867a vocab=0a259e7f
-/
lemma lebesgueFunction_reindex {n : ℕ} (nodes : NodeFamily n)
    (e : Equiv.Perm (Fin n)) (t : ℝ) :
    lebesgueFunction (nodes.reindex e) t = lebesgueFunction nodes t := by
  simp only [lebesgueFunction, lagrangeFundamental_reindex]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- The interval supremum of the Lebesgue function is permutation invariant.
@isnad1 id=eq.0h5v.s4.40a433027bfd from=translated src=- shape=a315a940 vocab=dc8e51b3
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
@isnad1 id=eq.0h3v.s4.b11a3ce51a31 from=translated src=- shape=4909777f vocab=ff604cbf
-/
@[simp]
lemma coe_point {n : ℕ} (nodes : OrderedNodes n) (i : Fin n) :
    (nodes : NodeFamily n).point i = nodes.point i :=
  rfl

/-- Earlier indices of an ordered family give strictly smaller nodes.
@isnad1 id=lt.1h4v.s5.f2009944352a from=translated src=- shape=ee063282 vocab=fd933772
-/
lemma point_lt {n : ℕ} (nodes : OrderedNodes n) {i j : Fin n} (hij : i < j) :
    nodes.point i < nodes.point j :=
  nodes.strictMono hij

/-- Every ordered node retains the lower endpoint bound.
@isnad1 id=le.0h3v.s4.0ccfcfe7a0e4 from=translated src=- shape=dc09e7ff vocab=a1ca1dd5
-/
lemma neg_one_le {n : ℕ} (nodes : OrderedNodes n) (i : Fin n) :
    (-1 : ℝ) ≤ nodes.point i :=
  (nodes.mem_Icc i).1

/-- Every ordered node retains the upper endpoint bound.
@isnad1 id=le.0h3v.s4.b126fc25e0db from=translated src=- shape=5efa48d0 vocab=7c4bb4c2
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
@isnad1 id=iff.0h3v.s5.854b3a71b04c from=translated src=- shape=e932c8c3 vocab=fceca345
-/
@[simp]
lemma mem_nodeFinset {n : ℕ} (nodes : NodeFamily n) (x : ℝ) :
    x ∈ nodes.nodeFinset ↔ ∃ i : Fin n, nodes.point i = x := by
  simp [nodeFinset]

/-- Injectivity ensures that the set of nodes has cardinality exactly `n`.
@isnad1 id=eq.0h2v.s3.ef7100fd6983 from=translated src=- shape=37d26c04 vocab=eb01dc18
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
@isnad1 id=mem.0h3v.s5.f0b2915b9e4b from=translated src=- shape=5a604606 vocab=411c7a85
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
@isnad1 id=eq.0h3v.s5.ca94c9310ebf from=translated src=- shape=6714f7f1 vocab=d4a87731
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
@isnad1 id=eq.0h3v.s7.25daa3029331 from=translated src=- shape=bef458e7 vocab=d3347de2
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
@isnad1 id=eq.0h3v.s5.5b6916d37b2d from=translated src=- shape=59660ff0 vocab=f36d8305
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
@isnad1 id=eq.0h2v.s4.528c16e9ff32 from=translated src=- shape=e34425d3 vocab=c1f93224
-/
lemma reindex_sortingPerm {n : ℕ} (nodes : NodeFamily n) :
    nodes.reindex nodes.sortingPerm = nodes.sorted.toNodeFamily := by
  apply NodeFamily.ext
  funext i
  exact point_sortingPerm nodes i

/-- Sorting preserves the full Lebesgue function.
@isnad1 id=eq.0h3v.s4.95275f9ae352 from=translated src=- shape=56ed178e vocab=d664e103
-/
lemma lebesgueFunction_sorted {n : ℕ} (nodes : NodeFamily n) (t : ℝ) :
    lebesgueFunction nodes.sorted.toNodeFamily t = lebesgueFunction nodes t := by
  rw [← reindex_sortingPerm nodes, lebesgueFunction_reindex]

/-- Sorting preserves every interval supremum of the Lebesgue function.
@isnad1 id=eq.0h4v.s4.c25404ae41dd from=translated src=- shape=6f33675f vocab=692484bc
-/
lemma lebesgueOn_sorted {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) :
    lebesgueOn nodes.sorted.toNodeFamily a b = lebesgueOn nodes a b := by
  rw [← reindex_sortingPerm nodes, lebesgueOn_reindex]

end NodeFamily

end

end Erdos1153
