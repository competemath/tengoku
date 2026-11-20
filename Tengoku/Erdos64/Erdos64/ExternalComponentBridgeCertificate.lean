import Tengoku.Erdos64.Erdos64.ExternalComponentBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/- The genuine bridge branch exposes the two complementary arc lengths and
   one exact cycle-length witness. The arithmetic needed to make a witness
   dyadic remains a separate premise. -/
/--
@isnad1 id=ex.2h4v.s9.33649ebe0036 from=translated src=- shape=e0f0f64f vocab=344d924d
-/
theorem externalComponent_bridge_branch_cycle_length_certificate
    {V : Type u} {G : SimpleGraph V} {s : V}
    [DecidableEq V] {C : G.Walk s s} (hC : C.IsCycle)
    (hbridge : ∃ bridge : CycleBridgePath G C, True) :
    ∃ (bridge : CycleBridgePath G C)
      (p : G.Path bridge.left bridge.right)
      (q : G.Path bridge.right bridge.left),
      (p : G.Walk bridge.left bridge.right).append
          (q : G.Walk bridge.right bridge.left) =
        C.rotate bridge.left bridge.left_mem_cycle ∧
      (p : G.Walk bridge.left bridge.right).length +
          (q : G.Walk bridge.right bridge.left).length = C.length ∧
      ((p : G.Walk bridge.left bridge.right).length > 1 ∨
        (q : G.Walk bridge.right bridge.left).length > 1) ∧
      ((∃ c : G.Walk bridge.left bridge.left,
          c.IsCycle ∧
            c.length = bridge.path.length +
              (p : G.Walk bridge.left bridge.right).length) ∨
       (∃ c : G.Walk bridge.right bridge.right,
          c.IsCycle ∧
            c.length = bridge.path.length +
              (q : G.Walk bridge.right bridge.left).length)) := by
  rcases hbridge with ⟨bridge, _⟩
  obtain ⟨p, q, hdecomp, hlonger⟩ :=
    bridge.exists_complementary_arc_longer_than_one hC
  have hsum := bridge.complementary_arcs_length_add hdecomp
  refine ⟨bridge, p, q, hdecomp, hsum, hlonger, ?_⟩
  rcases hlonger with hp | hq
  · left
    obtain ⟨c, hc, hlength⟩ :=
      bridge.cycle_of_extracted_arc hdecomp (Or.inr hp)
    exact ⟨c, hc, hlength⟩
  · right
    have hq_sub_cycle :
        (q : G.Walk bridge.right bridge.left).support ⊆ C.support := by
      intro z hz
      have hzappend : z ∈
          ((p : G.Walk bridge.left bridge.right).append
            (q : G.Walk bridge.right bridge.left)).support := by
        simp [hz]
      rw [hdecomp] at hzappend
      exact (SimpleGraph.Walk.mem_support_rotate_iff C bridge.left
        bridge.left_mem_cycle).mp hzappend
    have hdisjoint :=
      bridge.reverse.tails_disjoint_of_arc_support_subset
        q.property hq_sub_cycle
    obtain ⟨c, hc, hlength⟩ :=
      bridge.reverse.cycle_of_arc q.property hdisjoint (Or.inr hq)
    refine ⟨c, hc, ?_⟩
    simpa [CycleBridgePath.reverse, SimpleGraph.Walk.length_reverse]
      using hlength

end Erdos64
