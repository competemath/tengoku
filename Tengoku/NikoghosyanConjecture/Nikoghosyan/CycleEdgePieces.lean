/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Tengoku.NikoghosyanConjecture.Nikoghosyan.PathBlockInsertion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/CycleEdgePieces.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
Generic cycle-piece callback: insert an omitted original block into a
complementary path that retains an actual original edge.

If `r` is an original path that omits a block `Q` (`Disjoint Q.support
r.support`) and retains an original edge `u—v` as an actual walk-edge —
supplied by a `PrefixEdgeFactor`, not inferred from `u, v ∈ r.support` —
then `insertBlock` places all of `Q` onto `r` across the original seams
`u—Q.start` and `Q.finish—v`, without changing original-`A` incidences.

G2 must derive actual membership `s(u,v) ∈ r.edges` in the complement
from the exact complement-edge identity in `CycleEdgeRetention`
(filtered closed edges with both endpoints outside `Q.support`, or the
equivalent delete-`Q`-edges / delete-two-seams form). An edge-subset of
a prescribed cycle does not prove that a chosen old edge survives. This
module does not reconstruct leftover runs, does not prove same-sign
wrapping, and does not close `prof:thm:protected`.
-/


open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphPath

variable {r : GraphPath G} {u v : V}

/-- The retained dart is the actual factor edge, not a support pair.
@isnad1 id=mem.0h6v.s5.e6b2a7eb3772 from=translated src=- shape=c860ef5f vocab=f16105c6
-/
lemma retained_old_edge (F : PrefixEdgeFactor r u v) :
    s(u, v) ∈ r.edges :=
  F.old_mem_edges

/-- Insert an omitted outside block `Q` into a complementary path `r` at
the actual retained dart `u—v`.-/
def insertOmittedBlock (F : PrefixEdgeFactor r u v) (Q : GraphPath G)
    (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) : GraphPath G :=
  F.insertBlock Q hd hs hf

/--
@isnad1 id=eq.3h7v.s6.f00095ece946 from=translated src=- shape=c10f546c vocab=0f3c8b95
-/
lemma insertOmittedBlock_start (F : PrefixEdgeFactor r u v) (Q : GraphPath G)
    (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    (insertOmittedBlock F Q hd hs hf).start = r.start :=
  F.insertBlock_start Q hd hs hf

/--
@isnad1 id=eq.3h7v.s6.c80657adff5f from=translated src=- shape=cb019d1d vocab=0f3c8b95
-/
lemma insertOmittedBlock_finish (F : PrefixEdgeFactor r u v) (Q : GraphPath G)
    (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    (insertOmittedBlock F Q hd hs hf).finish = r.finish :=
  F.insertBlock_finish Q hd hs hf

/-- The operation puts all of `Q` onto the complementary path.
@isnad1 id=eq.3h7v.s6.059996b5fccf from=translated src=- shape=197fbeea vocab=3d547531
-/
theorem insertOmittedBlock_support (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    (insertOmittedBlock F Q hd hs hf).support = r.support ∪ Q.support :=
  F.insertBlock_support Q hd hs hf

/-- Exact outside-block sdiff: after insertion the complement vertices
are recovered by deleting `Q`.
@isnad1 id=eq.3h7v.s6.5032edd5c714 from=translated src=- shape=d661812a vocab=23f66160
-/
theorem insertOmittedBlock_support_sdiff (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    (insertOmittedBlock F Q hd hs hf).support \ Q.support = r.support := by
  rw [insertOmittedBlock_support]
  ext x
  simp only [mem_sdiff, mem_union]
  constructor
  · intro ⟨hx, hxQ⟩
    exact hx.resolve_right hxQ
  · intro hx
    exact ⟨Or.inl hx, disjoint_right.1 hd hx⟩

/--
@isnad1 id=mem.4h8v.s6.1275e6a40e63 from=translated src=- shape=ae226d30 vocab=763a0615
-/
lemma insertOmittedBlock_start_mem_A (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) {A : Finset V}
    (hA : r.start ∈ A) :
    (insertOmittedBlock F Q hd hs hf).start ∈ A := by
  simpa [insertOmittedBlock_start] using hA

/--
@isnad1 id=mem.4h8v.s6.0b5415f515e6 from=translated src=- shape=84c7e2f3 vocab=763a0615
-/
lemma insertOmittedBlock_finish_mem_A (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) {A : Finset V}
    (hA : r.finish ∈ A) :
    (insertOmittedBlock F Q hd hs hf).finish ∈ A := by
  simpa [insertOmittedBlock_finish] using hA

/--
@isnad1 id=le.3h7v.s6.48ab884579db from=translated src=- shape=c85a4806 vocab=071199f6
-/
lemma insertOmittedBlock_contains_block (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    Q.support ⊆ (insertOmittedBlock F Q hd hs hf).support :=
  F.block_support_subset_insertBlock Q hd hs hf

/--
@isnad1 id=eq.3h7v.s7.6715526e5cc4 from=translated src=- shape=2d931ec8 vocab=035c0a73
-/
theorem insertOmittedBlock_edges (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) :
    (insertOmittedBlock F Q hd hs hf).edges =
      r.edges.erase s(u, v) ∪ Q.edges ∪
        {s(u, Q.start), s(Q.finish, v)} :=
  F.insertBlock_edges Q hd hs hf

/-- Original-`A` incidences, including original `A` seams of `r`, are
exactly unchanged. Block edges and the two new seams meet no vertex of
`A`.
@isnad1 id=eq.6h8v.s7.4416a4cbf57e from=translated src=- shape=b9b0e3d5 vocab=ffb47fc7
-/
theorem insertOmittedBlock_AIncident (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) {A : Finset V}
    (huA : u ∉ A) (hvA : v ∉ A) (hAQ : Disjoint Q.support A) :
    (insertOmittedBlock F Q hd hs hf).AIncident A = r.AIncident A :=
  F.AIncident_insertBlock Q hd hs hf huA hvA hAQ

/--
@isnad1 id=eq.7h9v.s7.bbe53cae8ca1 from=translated src=- shape=9aa62d87 vocab=298b0705
-/
theorem insertOmittedBlock_incidentEdges (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v) {A : Finset V} {b : V}
    (hbA : b ∈ A) (huA : u ∉ A) (hvA : v ∉ A)
    (hAQ : Disjoint Q.support A) :
    (insertOmittedBlock F Q hd hs hf).incidentEdges b = r.incidentEdges b :=
  F.incidentEdges_insertBlock Q hd hs hf hbA huA hvA hAQ

/--
@isnad1 id=protecte.7h9v.s7.37b86f202bf7 from=translated src=- shape=46a4a73f vocab=757f87a7
-/
theorem protectedAt_insertOmittedBlock (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v)
    {c : GraphCycle G} {A : Finset V}
    (huA : u ∉ A) (hvA : v ∉ A) (hAQ : Disjoint Q.support A)
    (hP : r.ProtectedAt c A) :
    (insertOmittedBlock F Q hd hs hf).ProtectedAt c A :=
  F.protectedAt_insertBlock Q hd hs hf huA hvA hAQ hP

/-- If after insertion the path spans the prescribed cycle, the exact
internal-2 / endpoint-1 bridge applies. The complementary path is not
assumed to span the cycle before insertion.
@isnad1 id=and.9h9v.s8.aef7a6f83881 from=translated src=- shape=039a2324 vocab=1f7b3032
-/
theorem protected_exact_of_insertOmittedBlock (F : PrefixEdgeFactor r u v)
    (Q : GraphPath G) (hd : Disjoint Q.support r.support)
    (hs : G.Adj u Q.start) (hf : G.Adj Q.finish v)
    (c : GraphCycle G) {A : Finset V}
    (hsup : (insertOmittedBlock F Q hd hs hf).support = c.support)
    (hA : A ⊆ (insertOmittedBlock F Q hd hs hf).support)
    (huA : u ∉ A) (hvA : v ∉ A) (hAQ : Disjoint Q.support A)
    (hP : r.ProtectedAt c A) :
    (insertOmittedBlock F Q hd hs hf).ProtectedAt c A ∧
      (insertOmittedBlock F Q hd hs hf).start = r.start ∧
        (insertOmittedBlock F Q hd hs hf).finish = r.finish ∧
          (∀ b ∈ A,
            (insertOmittedBlock F Q hd hs hf).incidentEdges b =
              r.incidentEdges b) ∧
            (∀ b ∈ A, b ≠ r.start → b ≠ r.finish →
              (insertOmittedBlock F Q hd hs hf).incidentEdges b =
                c.incidentEdges b) := by
  obtain ⟨hProt, hst, hfin, hinc, hinter, _, _⟩ :=
    F.protected_exact_of_insertBlock Q hd hs hf c hsup hA huA hvA hAQ hP
  exact ⟨hProt, hst, hfin, hinc, hinter⟩

end GraphPath

end Nikoghosyan
