import Tengoku.NikoghosyanConjecture.Nikoghosyan.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/Paths.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
Original-edge paths: nonempty simple walks in `G`, including singletons.
-/


open Classical
open Finset SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- A simple path of `G` using only original edges. The nil walk is the
singleton path at its unique vertex.-/
structure GraphPath where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath

namespace GraphPath

variable {G}

/-- Vertex support of a path, as an original-vertex finset.-/
def support (p : GraphPath G) : Finset V :=
  p.walk.support.toFinset

/--
@isnad1 id=mem.0h3v.s5.17700a1b14cb from=translated src=- shape=b9c081f1 vocab=6cb30d5c
-/
lemma start_mem_support (p : GraphPath G) : p.start ∈ p.support := by
  simp [support, Walk.start_mem_support]

/--
@isnad1 id=mem.0h3v.s5.80d16c3ec0ce from=translated src=- shape=b9c081f1 vocab=d6d6ca19
-/
lemma finish_mem_support (p : GraphPath G) : p.finish ∈ p.support := by
  simp [support, Walk.end_mem_support]

/--
@isnad1 id=nonempty.0h3v.s4.440c50a16a73 from=translated src=- shape=628ae653 vocab=ca8c1c90
-/
lemma support_nonempty (p : GraphPath G) : p.support.Nonempty :=
  ⟨p.start, p.start_mem_support⟩

/-- The singleton path at `v`.-/
def singleton (v : V) : GraphPath G where
  start := v
  finish := v
  walk := Walk.nil
  isPath := Walk.IsPath.nil

/--
@isnad1 id=eq.0h3v.s4.1c0651c0781e from=translated src=- shape=ba4b5e04 vocab=f81856c5
-/
@[simp]
lemma support_singleton (v : V) : (singleton (G := G) v).support = {v} := by
  simp [singleton, support]

/-- Reversal preserves the original-edge path structure.-/
def reverse (p : GraphPath G) : GraphPath G where
  start := p.finish
  finish := p.start
  walk := p.walk.reverse
  isPath := p.isPath.reverse

/--
@isnad1 id=eq.0h3v.s4.1ec7036ce777 from=translated src=- shape=b1e85df5 vocab=a14e224a
-/
@[simp]
lemma support_reverse (p : GraphPath G) : p.reverse.support = p.support := by
  simp [reverse, support, Walk.support_reverse]

/--
@isnad1 id=not.1h4v.s5.a1b17539331a from=translated src=- shape=531c1d83 vocab=88d14ddd
-/
lemma not_mem_list_support {x : V} {p : GraphPath G} (hx : x ∉ p.support) :
    x ∉ p.walk.support := by
  simpa [support] using hx

/-- Concatenate an original edge at the start of a path.-/
def consAdj {x : V} (p : GraphPath G) (h : G.Adj x p.start) (hx : x ∉ p.support) :
    GraphPath G where
  start := x
  finish := p.finish
  walk := Walk.cons h p.walk
  isPath := p.isPath.cons (not_mem_list_support hx)

/--
@isnad1 id=eq.2h4v.s6.add9a411d798 from=translated src=- shape=2ce49108 vocab=0a32a9c4
-/
@[simp]
lemma support_consAdj {x : V} (p : GraphPath G) (h : G.Adj x p.start)
    (hx : x ∉ p.support) :
    (p.consAdj h hx).support = insert x p.support := by
  simp [consAdj, support]

/-- Concatenate an original edge at the finish of a path.-/
def concatAdj {x : V} (p : GraphPath G) (h : G.Adj p.finish x) (hx : x ∉ p.support) :
    GraphPath G where
  start := p.start
  finish := x
  walk := p.walk.concat h
  isPath := p.isPath.concat (not_mem_list_support hx) h

/--
@isnad1 id=eq.2h4v.s6.10a9d4d3d262 from=translated src=- shape=2a739c3e vocab=0403c445
-/
@[simp]
lemma support_concatAdj {x : V} (p : GraphPath G) (h : G.Adj p.finish x)
    (hx : x ∉ p.support) :
    (p.concatAdj h hx).support = insert x p.support := by
  simp [concatAdj, support]

end GraphPath

end Nikoghosyan
