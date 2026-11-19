import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.RigidFullFan
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.RigidTorso
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.CoreFarFan
import Tengoku.Linearhadwiger.HadwigerLean.Graph.SetMengerTheorem
import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor.LeftCutGluing
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace HadwigerLean
namespace Linkedness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A full near-shore fan into a linked rigid far shore links all roots.-/
theorem rootedLinked_of_rigid_full_near_fan
    (G : SimpleGraph V) (S : VertexSeparation G) [Fintype S.left]
    (X : Finset V) (hX : (X : Set V) ⊆ S.left)
    {n : ℕ} (P : IndexedPairs (Fin n) S.left)
    (L : IndexedLinkage (G.induce S.left) P)
    (hstarts : Finset.univ.image P.start = torsoRootFinset S X)
    (hfinish : ∀ i, P.finish i ∈ torsoBoundaryFinset G S)
    (hfar : RootedLinked (G.induce S.right)
      (separationBoundaryFinset S)) :
    RootedLinked G X := by
  classical
  let P' : IndexedPairs (Fin n) V :=
    ⟨fun i => (P.start i : V), fun i => (P.finish i : V)⟩
  let L' : IndexedLinkage G P' := L.mapInduce
  have hrooted : RootedLinked G (Finset.univ.image P'.start) :=
    rootedLinked_of_full_fan_to_rigid_far S P' L'
      (fun i => (P.start i).property)
      (fun i => (mem_torsoBoundaryFinset G S _).mp (hfinish i)) hfar
  have hYimage : (torsoRootFinset S X).image Subtype.val = X := by
    ext x
    constructor
    · intro hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact (mem_torsoRootFinset S X u).mp hu
    · intro hx
      exact Finset.mem_image.mpr ⟨⟨x,hX hx⟩,
        (mem_torsoRootFinset S X _).mpr hx,rfl⟩
  have hrootset : Finset.univ.image P'.start = X := by
    calc
      Finset.univ.image P'.start =
          (Finset.univ.image P.start).image Subtype.val := by
            rw [Finset.image_image]
            rfl
      _ = X := by rw [hstarts, hYimage]
  exact hrootset ▸ hrooted

end Linkedness
end HadwigerLean
