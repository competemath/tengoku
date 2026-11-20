import Tengoku.Erdos64.Erdos64.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

private theorem path_start_not_mem_tail
    {V : Type u} {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} (hp : p.IsPath) : a ∉ p.support.tail := by
  have hn : (a :: p.support.tail).Nodup := by
    rw [p.cons_tail_support]
    exact hp.support_nodup
  exact (List.nodup_cons.mp hn).1

/-- Replacing a segment of a simple path by a fresh simple ear preserves
simplicity and produces the segment-ear cycle. A single simplicity hypothesis
on the original path and a single intersection condition supply all the
support disjointness needed for both constructions. No ear existence or
length relation is inferred.
@isnad1 id=and.5h10v.s7.8a606dba849e from=translated src=- shape=8cbb7b70 vocab=8d2ae70d
-/
theorem terminal_path_reroute_of_fresh_ear
    {V : Type u} {G : SimpleGraph V} {a b x y : V}
    (pre : G.Walk a x) (segment : G.Walk x y)
    (suffix : G.Walk y b) (ear : G.Walk x y)
    (horiginal : ((pre.append segment).append suffix).IsPath)
    (hear : ear.IsPath) (hxy : x ≠ y)
    (hfresh : ∀ z, z ∈ ear.support →
      z ∈ ((pre.append segment).append suffix).support → z = x ∨ z = y)
    (hlong : 1 < segment.length ∨ 1 < ear.length) :
    ((pre.append ear).append suffix).IsPath ∧
      (segment.append ear.reverse).IsCycle := by
  have hpreseg := horiginal.of_append_left
  have hpre := hpreseg.of_append_left
  have hsegment := hpreseg.of_append_right
  have hsuffix := horiginal.of_append_right
  have hps : pre.support.Disjoint segment.support.tail := by
    have hn := hpreseg.support_nodup
    rw [SimpleGraph.Walk.support_append] at hn
    exact List.disjoint_of_nodup_append hn
  have hpss : (pre.append segment).support.Disjoint suffix.support.tail := by
    have hn := horiginal.support_nodup
    rw [SimpleGraph.Walk.support_append] at hn
    exact List.disjoint_of_nodup_append hn
  have hpe : pre.support.Disjoint ear.support.tail := by
    rw [List.disjoint_left]
    intro z hzpre hzear
    have hzorig : z ∈ ((pre.append segment).append suffix).support := by
      simp only [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl (Or.inl hzpre)
    rcases hfresh z (List.mem_of_mem_tail hzear) hzorig with rfl | rfl
    · exact path_start_not_mem_tail hear hzear
    · exact (List.disjoint_left.mp hps hzpre)
        (segment.end_mem_tail_support_of_ne hxy)
  have hpes : (pre.append ear).support.Disjoint suffix.support.tail := by
    rw [List.disjoint_left]
    intro z hzpreear hzsuf
    rcases (SimpleGraph.Walk.mem_support_append_iff pre ear).mp hzpreear with
      hzpre | hzear
    · exact (List.disjoint_left.mp hpss
        ((SimpleGraph.Walk.mem_support_append_iff pre segment).mpr (Or.inl hzpre)))
        hzsuf
    · have hzorig : z ∈ ((pre.append segment).append suffix).support := by
        exact (SimpleGraph.Walk.mem_support_append_iff _ _).mpr
          (Or.inr (List.mem_of_mem_tail hzsuf))
      rcases hfresh z hzear hzorig with rfl | rfl
      · exact (List.disjoint_left.mp hpss
          ((SimpleGraph.Walk.mem_support_append_iff pre segment).mpr
            (Or.inl pre.end_mem_support))) hzsuf
      · exact path_start_not_mem_tail hsuffix hzsuf
  have hse : segment.support.tail.Disjoint ear.reverse.support.tail := by
    rw [List.disjoint_left]
    intro z hzseg hzear
    have hzorig : z ∈ ((pre.append segment).append suffix).support := by
      simp only [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl (Or.inr (List.mem_of_mem_tail hzseg))
    have hzear' : z ∈ ear.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
        List.mem_of_mem_tail hzear
    rcases hfresh z hzear' hzorig with rfl | rfl
    · exact path_start_not_mem_tail hsegment hzseg
    · exact path_start_not_mem_tail hear.reverse hzear
  have hpreear : (pre.append ear).IsPath := by
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
    exact List.Nodup.append hpre.support_nodup hear.support_nodup.tail hpe
  refine ⟨?_, hsegment.isCycle_append hear.reverse hse ?_⟩
  · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
    exact List.Nodup.append hpreear.support_nodup hsuffix.support_nodup.tail hpes
  · simpa only [SimpleGraph.Walk.length_reverse] using hlong

/-- A fresh ear that shortens a dyadic terminal path by exactly two edges
forces a dyadic cycle through the common root. The original path and ear
must both avoid that root.
@isnad1 id=haspower.10h12v.s8.a95e6b11edce from=translated src=- shape=6b02ba3e vocab=b19b733c
-/
theorem hasPowerOfTwoCycle_of_two_edge_shortening_ear
    {V : Type u} {G : SimpleGraph V} {r a b x y : V}
    (pre : G.Walk a x) (segment : G.Walk x y)
    (suffix : G.Walk y b) (ear : G.Walk x y)
    (horiginal : ((pre.append segment).append suffix).IsPath)
    (hear : ear.IsPath)
    (hfresh : ∀ z, z ∈ ear.support →
      z ∈ ((pre.append segment).append suffix).support → z = x ∨ z = y)
    (hroot : r ∉ ((pre.append segment).append suffix).support)
    (hrootear : r ∉ ear.support)
    (hra : G.Adj r a) (hrb : G.Adj r b)
    {k : ℕ} (hk : 2 ≤ k)
    (hdyadic : ((pre.append segment).append suffix).length = 2 ^ k)
    (hshorten : ear.length + 2 = segment.length) :
    HasPowerOfTwoCycle G := by
  have hsegment := horiginal.of_append_left.of_append_right
  have hxy : x ≠ y := by
    intro hxy
    have hzero := SimpleGraph.Walk.length_eq_zero_iff.mpr
      (hsegment.nil_iff_eq.mpr hxy)
    omega
  have hab : a ≠ b := by
    intro hab
    have hzero := SimpleGraph.Walk.length_eq_zero_iff.mpr
      (horiginal.nil_iff_eq.mpr hab)
    have hpow := four_le_pow_two hk
    omega
  have hroute := (terminal_path_reroute_of_fresh_ear pre segment suffix ear
    horiginal hear hxy hfresh (Or.inl (by omega))).1
  have hreroot : r ∉ ((pre.append ear).append suffix).support := by
    simp only [SimpleGraph.Walk.mem_support_append_iff] at hroot ⊢
    tauto
  have hlength : ((pre.append ear).append suffix).length + 2 = 2 ^ k := by
    simp only [SimpleGraph.Walk.length_append] at hdyadic ⊢
    omega
  have hlong : 1 < ((pre.append ear).append suffix).length := by
    have hpow := four_le_pow_two hk
    omega
  obtain ⟨cycle, hcycle, hcyclelength⟩ :=
    endpoint_fan_cycle_certificate hroute hra hrb hreroot hab hlong
  exact ⟨k, a, cycle, hk, hcycle, hcyclelength.trans hlength⟩

/-- The local ear cycle is already forbidden whenever the replaced segment
and ear lengths sum to a power of two.
@isnad1 id=haspower.6h11v.s7.c7c951b7b788 from=translated src=- shape=16d774cb vocab=6a593c44
-/
theorem hasPowerOfTwoCycle_of_dyadic_fresh_ear
    {V : Type u} {G : SimpleGraph V} {a b x y : V}
    (pre : G.Walk a x) (segment : G.Walk x y)
    (suffix : G.Walk y b) (ear : G.Walk x y)
    (horiginal : ((pre.append segment).append suffix).IsPath)
    (hear : ear.IsPath) (hxy : x ≠ y)
    (hfresh : ∀ z, z ∈ ear.support →
      z ∈ ((pre.append segment).append suffix).support → z = x ∨ z = y)
    {k : ℕ} (hk : 2 ≤ k)
    (hdyadic : segment.length + ear.length = 2 ^ k) :
    HasPowerOfTwoCycle G := by
  have hpow := four_le_pow_two hk
  have hlong : 1 < segment.length ∨ 1 < ear.length := by omega
  have hcycle := (terminal_path_reroute_of_fresh_ear pre segment suffix ear
    horiginal hear hxy hfresh hlong).2
  refine ⟨k, x, segment.append ear.reverse, hk, hcycle, ?_⟩
  simpa only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] using
    hdyadic

end Erdos64
