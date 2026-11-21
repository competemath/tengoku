import Tengoku.Erdos64.Erdos64.ComponentAttachments
import Tengoku.Erdos64.Erdos64.ExternalBranches

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/- The ambient external-component dichotomy feeds its genuine two-attachment
   branch into the explicit bridge constructor. The unique-root branch is
   preserved as a separate alternative and is not analyzed here. -/
/--
@isnad1 id=or.3h5v.s7.7a64cfc5a2eb from=translated src=- shape=f50fa616 vocab=b3798860
-/
theorem externalComponent_bridge_or_unique_root
    {V : Type u} {G : SimpleGraph V} {s : V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {C : G.Walk s s} (hC : C.IsCycle) (hG : G.Connected)
    {x : V} (hx : x ∉ C.support) :
    (∃ bridge : CycleBridgePath G C, True) ∨
      ∃ r, r ∈ C.support ∧
        ∀ b, b ∈ C.support →
          ((∃ v, v ∈ externalComponent G C x hx ∧ G.Adj b v) ↔ b = r) := by
  let K : Set V := externalComponent G C x hx
  have hKconn : (G.induce K).Connected := by
    simpa [K] using externalComponent_induced_connected hx
  have hK_external : ∀ v, v ∈ K → v ∉ C.support := by
    intro v hv
    exact (show v ∈ externalComponent G C x hx from by simpa [K] using hv).1
  rcases externalComponent_two_attachments_or_unique_root hC hG hx with htwo | hroot
  · left
    rcases htwo with ⟨a, b, u, v, ha, hb, hab, hu, hv, hau, hbv⟩
    exact ⟨CycleBridgePath.of_connected_external_set hC K hKconn
      ha hb hab (by simpa [K] using hu) (by simpa [K] using hv)
      hau hbv hK_external, trivial⟩
  · exact Or.inr hroot

end Erdos64
