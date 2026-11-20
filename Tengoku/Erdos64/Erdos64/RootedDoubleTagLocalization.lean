import Tengoku.Erdos64.Erdos64.RootedDouble
import Tengoku.Erdos64.Erdos64.RootedDoubleNeighbors
import Tengoku.Erdos64.Erdos64.RootedDoubleNonroot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Every nonroot vertex on a simple rooted-double cycle belongs to one
Boolean-tagged copy.  The shared root is deliberately excluded from the
conclusion, making this support predicate suitable for later local projection
arguments.-/
theorem rootedDouble_cycle_common_tag
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {r : V}
    {x : RootedDoubleVertex V r}
    (p : (rootedDoubleGraph G r).Walk x x) (hp : p.IsCycle) :
    ∃ b : Bool, ∀ z, z ∈ p.support → z ≠ none →
      ∃ v : {v : V // v ≠ r}, z = some (b, v) := by
  classical
  let Adj := (rootedDoubleGraph G r).Adj
  have tag_chain : ∀ (l : List (RootedDoubleVertex V r)),
      l.IsChain Adj → (∀ z ∈ l, z ≠ none) →
        ∃ b : Bool, ∀ z ∈ l,
          ∃ v : {v : V // v ≠ r}, z = some (b, v) := by
    intro l
    induction l with
    | nil =>
        intro _ _
        exact ⟨false, by simp⟩
    | cons a l ih =>
        intro hchain hnon
        cases l with
        | nil =>
            have ha : a ≠ none := hnon a (by simp)
            cases a with
            | none => exact (ha rfl).elim
            | some av =>
                refine ⟨av.1, ?_⟩
                intro z hz
                simp only [List.mem_singleton] at hz
                subst z
                exact ⟨av.2, rfl⟩
        | cons c l =>
            have hac : Adj a c := by
              cases hchain with
              | cons_cons h _ => exact h
            have hchain_tail : (c :: l).IsChain Adj := by
              cases hchain with
              | cons_cons _ h => exact h
            have hnon_tail : ∀ z ∈ c :: l, z ≠ none := by
              intro z hz
              exact hnon z (List.mem_cons_of_mem a hz)
            obtain ⟨b, hb⟩ := ih hchain_tail hnon_tail
            have ha : a ≠ none := hnon a (by simp)
            cases a with
            | none => exact (ha rfl).elim
            | some av =>
                obtain ⟨cv, hcv⟩ := hb c (by simp)
                have htag : av.1 = b := by
                  cases c with
                  | none =>
                      cases hcv
                  | some cw =>
                      have hac' : av.1 = cw.1 := by
                        simpa [Adj, rootedDoubleGraph,
                          rootedDoubleCompatible] using hac.2
                      have hcb : cw.1 = b := by
                        exact congrArg Prod.fst (Option.some.inj hcv)
                      exact hac'.trans hcb
                refine ⟨av.1, ?_⟩
                intro z hz
                simp only [List.mem_cons] at hz
                rcases hz with rfl | hz
                · exact ⟨av.2, rfl⟩
                · obtain ⟨v, hv⟩ := hb z (by simp [hz])
                  exact ⟨v, by rw [hv, htag]⟩
  have rooted_cycle : ∀ {c : (rootedDoubleGraph G r).Walk none none},
      c.IsCycle →
        ∃ b : Bool, ∀ z, z ∈ c.support → z ≠ none →
          ∃ v : {v : V // v ≠ r}, z = some (b, v) := by
    intro c hc
    have hcnil : ¬ c.Nil := hc.not_nil
    have htail_eq : c.support.tail = c.tail.support :=
      (c.support_tail_of_not_nil hcnil).symm
    have htailne : c.support.tail ≠ [] := by
      rw [htail_eq]
      simp
    have htail_chain : c.support.tail.IsChain Adj := by
      exact (c.isChain_adj_support).tail
    have hdrop_chain : c.support.tail.dropLast.IsChain Adj := by
      exact htail_chain.dropLast
    have hlast : c.support.tail.getLast htailne = none := by
      simpa only [htail_eq] using c.tail.getLast_support
    have hdrop_nodup : (c.support.tail.dropLast ++
        [c.support.tail.getLast htailne]).Nodup := by
      rw [List.dropLast_append_getLast htailne]
      exact hc.support_nodup
    have hdrop_nonroot : ∀ z ∈ c.support.tail.dropLast, z ≠ none := by
      intro z hz hznone
      have hdj : List.Disjoint c.support.tail.dropLast
          [c.support.tail.getLast htailne] :=
        List.Nodup.disjoint hdrop_nodup
      exact (List.disjoint_left.mp hdj hz) (by simp [hlast, hznone])
    obtain ⟨b, hb⟩ := tag_chain _ hdrop_chain hdrop_nonroot
    refine ⟨b, ?_⟩
    intro z hz hzne
    have hztail : z ∈ c.support.tail := by
      rw [c.mem_support_iff] at hz
      rcases hz with rfl | hz
      · exact (hzne rfl).elim
      · exact hz
    have hzlast : z ≠ c.support.tail.getLast htailne := by
      simpa [hlast] using hzne
    exact hb z (List.mem_dropLast_of_mem_of_ne_getLast hztail hzlast)
  by_cases hroot : none ∈ p.support
  · let c := p.rotate none hroot
    obtain ⟨b, hc⟩ := rooted_cycle (c := c) (hp.rotate hroot)
    refine ⟨b, ?_⟩
    intro z hz hzne
    apply hc z ?_ hzne
    exact (SimpleGraph.Walk.mem_support_rotate_iff p none hroot).mpr hz
  · have hnon : ∀ z ∈ p.support, z ≠ none := by
      intro z hz
      exact fun hznone => hroot (hznone ▸ hz)
    obtain ⟨b, hb⟩ := tag_chain p.support p.isChain_adj_support hnon
    exact ⟨b, fun z hz _ => hb z hz⟩

end Erdos64
