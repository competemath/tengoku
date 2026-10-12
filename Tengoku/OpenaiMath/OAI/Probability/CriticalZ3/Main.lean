import Tengoku.OpenaiMath.OAI.Probability.CriticalZ3.Subunit

namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical

namespace SignedSymmetry

theorem bondConnected_map (S : SignedSymmetry) (ω : BondConfig) (x y : Vertex) :
    BondConnected (fun e => ω (S.bond e)) x y ↔ BondConnected ω (S.vertex x) (S.vertex y) :=
  rtg_equiv_iff S.vertex (S.bondOpen_map ω) x y

theorem siteConnected_map (S : SignedSymmetry) (ω : SiteConfig) (x y : Vertex) :
    SiteConnected (fun e => ω (S.vertex e)) x y ↔ SiteConnected ω (S.vertex x) (S.vertex y) :=
  and_congr_right (fun _ => rtg_equiv_iff S.vertex (S.siteOpen_map ω) x y)

theorem bondInfiniteAt_map (S : SignedSymmetry) (ω : BondConfig) (x : Vertex) :
    (fun e => ω (S.bond e)) ∈ bondInfiniteAt x ↔ ω ∈ bondInfiniteAt (S.vertex x) := by
  have he : bondCluster (fun e => ω (S.bond e)) x = S.vertex ⁻¹' bondCluster ω (S.vertex x) := by
    ext y
    exact S.bondConnected_map ω x y
  change (bondCluster (fun e => ω (S.bond e)) x).Infinite ↔ _
  rw [he]
  constructor
  · intro hi hf
    exact hi (Set.Finite.preimage S.vertex.injective.injOn hf)
  · intro hi
    exact hi.preimage (fun y _ => S.vertex.surjective y)

theorem siteInfiniteAt_map (S : SignedSymmetry) (ω : SiteConfig) (x : Vertex) :
    (fun e => ω (S.vertex e)) ∈ siteInfiniteAt x ↔ ω ∈ siteInfiniteAt (S.vertex x) := by
  have he : siteCluster (fun e => ω (S.vertex e)) x = S.vertex ⁻¹' siteCluster ω (S.vertex x) := by
    ext y
    exact S.siteConnected_map ω x y
  change (siteCluster (fun e => ω (S.vertex e)) x).Infinite ↔ _
  rw [he]
  constructor
  · intro hi hf
    exact hi (Set.Finite.preimage S.vertex.injective.injOn hf)
  · intro hi
    exact hi.preimage (fun y _ => S.vertex.surjective y)
end SignedSymmetry

end CriticalZ3

end OAI
