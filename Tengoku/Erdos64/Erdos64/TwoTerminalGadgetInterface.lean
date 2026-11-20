import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A cubic graph equipped with two distinct terminals and two supplied
    terminal-to-terminal paths.  The two path interiors are required to be
    disjoint; no existence of such data is asserted.-/
structure CubicTwoTerminalCompletion {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] where
  gadgetEndpointLeft : V
  gadgetEndpointRight : V
  gadgetEndpointLeft_ne_gadgetEndpointRight :
    gadgetEndpointLeft ≠ gadgetEndpointRight
  cubic : ∀ v, G.degree v = 3
  gadget : G.Walk gadgetEndpointLeft gadgetEndpointRight
  returnPath : G.Walk gadgetEndpointLeft gadgetEndpointRight
  gadget_isPath : gadget.IsPath
  returnPath_isPath : returnPath.IsPath
  interiors_disjoint :
    ∀ z, z ∈ gadget.support → z ∈ returnPath.support →
      z = gadgetEndpointLeft ∨ z = gadgetEndpointRight
  gadget_length_gt_one : 1 < gadget.length

private theorem cubicTwoTerminalCompletion_isCycle
    {V : Type u} {G : SimpleGraph V} {a b : V}
    {p q : G.Walk a b}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ z, z ∈ p.support → z ∈ q.support → z = a ∨ z = b)
    (hlong : 1 < p.length) :
    (p.append q.reverse).IsCycle := by
  have ha : a ∉ p.support.tail := by
    have hn : (a :: p.support.tail).Nodup := by
      rw [p.cons_tail_support]
      exact hp.support_nodup
    exact (List.nodup_cons.mp hn).1
  have hb : b ∉ q.reverse.support.tail := by
    have hn : (b :: q.reverse.support.tail).Nodup := by
      rw [q.reverse.cons_tail_support]
      exact hq.reverse.support_nodup
    exact (List.nodup_cons.mp hn).1
  have htails : p.support.tail.Disjoint q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro z hzp hzq
    have hzq' : z ∈ q.support := by
      have hmem := List.mem_of_mem_tail hzq
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hmem
    rcases hinter z (List.mem_of_mem_tail hzp) hzq' with hza | hzb
    · exact ha (hza ▸ hzp)
    · exact hb (hzb ▸ hzq)
  exact hp.isCycle_append hq.reverse htails (Or.inl hlong)

/-- The supplied two paths form the completion cycle, with its exact length.
@isnad1 id=and.0h3v.s7.28610d203c75 from=translated src=- shape=37a58800 vocab=f638798d
-/
theorem CubicTwoTerminalCompletion.completion_cycle
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (T : CubicTwoTerminalCompletion G) :
    (T.gadget.append T.returnPath.reverse).IsCycle ∧
      (T.gadget.append T.returnPath.reverse).length =
        T.gadget.length + T.returnPath.length := by
  refine ⟨cubicTwoTerminalCompletion_isCycle T.gadget_isPath
      T.returnPath_isPath T.interiors_disjoint T.gadget_length_gt_one, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]

/-- A dyadic completion cycle traversing the supplied gadget yields the exact
    terminal-path length equation.  This is only a bookkeeping implication.
@isnad1 id=eq.1h4v.s7.c7035bdc24d4 from=translated src=- shape=b34e256f vocab=d9221a1c
-/
theorem CubicTwoTerminalCompletion.terminal_length_equation
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (T : CubicTwoTerminalCompletion G) {k : ℕ}
    (hdyadic : (T.gadget.append T.returnPath.reverse).length = 2 ^ k) :
    T.gadget.length + T.returnPath.length = 2 ^ k := by
  simpa only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    using hdyadic

end Erdos64
