import Tengoku.Erdos64.Erdos64.RootedDouble
import Tengoku.Erdos64.Erdos64.RootedDoubleTagLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- The rooted-double projection is injective on the support of a simple
cycle. This is support-local only: the two tagged copies still collapse to
the same original vertices away from a cycle support.
@isnad1 id=injon.1h5v.s6.c4a6620a3531 from=translated src=- shape=902aff8f vocab=c12b5b02
-/
theorem rootedDouble_cycle_projection_injOn
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {r : V}
    {x : RootedDoubleVertex V r}
    (p : (rootedDoubleGraph G r).Walk x x) (hp : p.IsCycle) :
    Set.InjOn rootedDoubleProjection {z | z ∈ p.support} := by
  classical
  obtain ⟨b, hcopy⟩ := rootedDouble_cycle_common_tag p hp
  intro a ha c hc hproj
  cases a with
  | none =>
      cases c with
      | none => rfl
      | some cw =>
          exact (cw.2.2 (by
            simpa [rootedDoubleProjection] using hproj.symm)).elim
  | some av =>
      cases c with
      | none =>
          exact (av.2.2 (by
            simpa [rootedDoubleProjection] using hproj)).elim
      | some cw =>
          have hav := hcopy (some av) ha (by simp)
          have hcw := hcopy (some cw) hc (by simp)
          obtain ⟨v, hav⟩ := hav
          obtain ⟨w, hcw⟩ := hcw
          have hav' : av = (b, v) := Option.some.inj hav
          have hcw' : cw = (b, w) := Option.some.inj hcw
          have hv : av.2 = cw.2 := by
            apply Subtype.ext
            simpa [rootedDoubleProjection] using hproj
          have htag : av.1 = cw.1 := by
            exact (congrArg Prod.fst hav').trans
              (congrArg Prod.fst hcw').symm
          exact congrArg some (Prod.ext htag hv)

/-- A simple rooted-double cycle projects to a simple cycle, with exactly the
same length, using only the support-local injectivity established above.
@isnad1 id=and.1h5v.s7.15406d8060e8 from=translated src=- shape=bcf92bb2 vocab=8565099c
-/
theorem rootedDouble_cycle_projection
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {r : V}
    {x : RootedDoubleVertex V r}
    (p : (rootedDoubleGraph G r).Walk x x) (hp : p.IsCycle) :
    (p.map rootedDoubleProjectionHom).IsCycle ∧
      (p.map rootedDoubleProjectionHom).length = p.length := by
  classical
  have hinj := rootedDouble_cycle_projection_injOn p hp
  have htail_inj : Set.InjOn rootedDoubleProjection
      {z | z ∈ p.tail.support} := by
    intro a ha c hc h
    change a ∈ p.tail.support at ha
    change c ∈ p.tail.support at hc
    apply hinj ?_ ?_ h
    · exact List.mem_of_mem_tail (by
        simpa only [p.support_tail_of_not_nil hp.not_nil] using ha)
    · exact List.mem_of_mem_tail (by
        simpa only [p.support_tail_of_not_nil hp.not_nil] using hc)
  have htail_path : (p.tail.map rootedDoubleProjectionHom).IsPath :=
    rootedDouble_projection_path_of_support_injective p.tail
      hp.isPath_tail htail_inj
  have hmapped_cycle : (p.map rootedDoubleProjectionHom).IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, ?_⟩
    · cases p with
      | nil => exact (hp.not_nil (by simp)).elim
      | cons h q =>
          simpa using htail_path
    · exact (rootedDouble_projection_length p).symm ▸ hp.three_le_length
  exact ⟨hmapped_cycle, rootedDouble_projection_length p⟩

end Erdos64
