import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- An explicitly decomposed terminal path can be rerouted through an ear.

The original route is `prefix ++ segment ++ suffix`; the ear has the same
endpoints as `segment`.  The support hypotheses are intentionally stated at
the level needed by the path and cycle constructors.  In particular, this
lemma does not infer an ear from connectivity or assert any equal-length
rerouting.
@isnad1 id=ex.10h10v.s8.4581ac04afa4 from=translated src=- shape=670c5456 vocab=a2c64cca
-/
theorem terminal_path_reroute_of_ear
    {V : Type u} {G : SimpleGraph V}
    {a b x y : V}
    (pre : G.Walk a x)
    (segment : G.Walk x y)
    (suffix : G.Walk y b)
    (ear : G.Walk x y)
    (hpre : pre.IsPath)
    (hsegment : segment.IsPath)
    (hsuffix : suffix.IsPath)
    (hear : ear.IsPath)
    (hprefix_segment :
      pre.support.Disjoint segment.support.tail)
    (hsegment_ear :
      segment.support.tail.Disjoint ear.reverse.support.tail)
    (horiginal_suffix :
      (pre.append segment).support.Disjoint suffix.support.tail)
    (hrerouted_prefix :
      pre.support.Disjoint ear.support.tail)
    (hrerouted_suffix :
      (pre.append ear).support.Disjoint suffix.support.tail)
    (hlong : 1 < segment.length ∨ 1 < ear.length) :
    ∃ rerouted : G.Walk a b, rerouted.IsPath ∧
      rerouted.length =
        pre.length + ear.length + suffix.length ∧
      ∃ cycle : G.Walk x x, cycle.IsCycle ∧
        cycle.length = segment.length + ear.length := by
  have original_prefix : (pre.append segment).IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
    have hdisjoint :
        ∀ z ∈ pre.support, ∀ w ∈ segment.support.tail, z ≠ w :=
      by
        intro z hz w hw hzw
        subst w
        exact (List.disjoint_left.mp hprefix_segment hz) hw
    exact List.nodup_append.mpr
      ⟨hpre.support_nodup, hsegment.support_nodup.tail,
        hdisjoint⟩
  have original : ((pre.append segment).append suffix).IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
    have hdisjoint :
        ∀ z ∈ (pre.append segment).support, ∀ w ∈ suffix.support.tail, z ≠ w :=
      by
        intro z hz w hw hzw
        subst w
        exact (List.disjoint_left.mp horiginal_suffix hz) hw
    exact List.nodup_append.mpr
      ⟨original_prefix.support_nodup, hsuffix.support_nodup.tail,
        hdisjoint⟩
  have rerouted_prefix : (pre.append ear).IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
    have hdisjoint :
        ∀ z ∈ pre.support, ∀ w ∈ ear.support.tail, z ≠ w :=
      by
        intro z hz w hw hzw
        subst w
        exact (List.disjoint_left.mp hrerouted_prefix hz) hw
    exact List.nodup_append.mpr
      ⟨hpre.support_nodup, hear.support_nodup.tail,
        hdisjoint⟩
  have rerouted : ((pre.append ear).append suffix).IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
    have hdisjoint :
        ∀ z ∈ (pre.append ear).support, ∀ w ∈ suffix.support.tail, z ≠ w :=
      by
        intro z hz w hw hzw
        subst w
        exact (List.disjoint_left.mp hrerouted_suffix hz) hw
    exact List.nodup_append.mpr
      ⟨rerouted_prefix.support_nodup, hsuffix.support_nodup.tail,
        hdisjoint⟩
  let cycle : G.Walk x x := segment.append ear.reverse
  have hcycle : cycle.IsCycle := by
    dsimp [cycle]
    exact hsegment.isCycle_append hear.reverse hsegment_ear
      (by simpa [SimpleGraph.Walk.length_reverse] using hlong)
  refine ⟨(pre.append ear).append suffix, rerouted, ?_, cycle, hcycle, ?_⟩
  · simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  · simp [cycle, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse]

end Erdos64
