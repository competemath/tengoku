import Tengoku.Erdos64.Erdos64.RootedDoubleCycleLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Simple-cycle lengths are unchanged by rooted doubling.  The forward
direction uses global copy localization and projection; the reverse direction
uses one fixed Boolean copy, with the root sent to the shared vertex.
@isnad1 id=iff.0h4v.s4.b25676debee1 from=translated src=- shape=0c6e7efe vocab=6785aee1
-/
theorem hasSimpleCycleOfLength_rootedDouble_iff
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {r : V} (n : ℕ) :
    HasSimpleCycleOfLength (rootedDoubleGraph G r) n ↔
      HasSimpleCycleOfLength G n := by
  constructor
  · rintro ⟨z, c, hc, hlen⟩
    obtain ⟨hc', hprojlen⟩ := rootedDouble_cycle_localization_projection c hc
    exact ⟨rootedDoubleProjectionHom z, c.map rootedDoubleProjectionHom, hc',
      hprojlen.trans hlen⟩
  · rintro ⟨v, c, hc, hlen⟩
    let b : Bool := false
    let e : G ↪g rootedDoubleGraph G r :=
      { toFun := fun w =>
          if hw : w = r then none else some (b, ⟨w, hw⟩)
        inj' := by
          intro w w' h
          by_cases hw : w = r
          · subst w
            by_cases hw' : w' = r
            · subst w'
              rfl
            · simp [hw'] at h
          · by_cases hw' : w' = r
            · simp [hw, hw'] at h
            · have h' : (b, (⟨w, hw⟩ : {w : V // w ≠ r})) =
                  (b, ⟨w', hw'⟩) := by
                simpa [hw, hw'] using h
              exact congrArg Subtype.val (congrArg Prod.snd h')
        map_rel_iff' := by
          intro w w'
          by_cases hw : w = r <;> by_cases hw' : w' = r <;>
            simp [hw, hw', b, rootedDoubleGraph, rootedDoubleProjection,
              rootedDoubleCompatible] }
    refine ⟨e v, c.map e.toHom, hc.map e.injective, ?_⟩
    rw [SimpleGraph.Walk.length_map, hlen]

end Erdos64
