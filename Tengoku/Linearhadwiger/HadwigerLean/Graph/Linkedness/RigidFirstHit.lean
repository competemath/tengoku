import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.CoreFarFan

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace HadwigerLean
namespace Linkedness

/-- The first visit to the far side of a separation lies in its adhesion.
@isnad1 id=mem.1h7v.s6.bc8cd75d2a9d from=translated src=- shape=0590fe28 vocab=979dcca4
-/
theorem FirstHit.finish_mem_separator_of_right
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G) [Fintype S.right]
    {s t : V} (p : G.Path s t) (hs : s ∈ S.left)
    (F : FirstHit p S.right.toFinset) :
    F.finish ∈ S.separator := by
  classical
  have hboundary : ∀ x ∈ (F.path : G.Walk s F.finish).support,
      x ∈ S.separator → x = F.finish := by
    intro x hx hxSep
    exact F.unique_hit x hx (by simpa using hxSep.2)
  have hleft := S.path_support_subset_left_of_boundary_only_at_finish
    (F.path : G.Walk s F.finish) F.path.property hs hboundary
  exact ⟨hleft F.finish (F.path : G.Walk s F.finish).end_mem_support,
    by simpa using F.finish_mem⟩

/-- Trim a path to its first far-side vertex; the endpoint is on the adhesion.
@isnad1 id=ex.2h6v.s6.21d0c91ca71a from=translated src=- shape=5679ba40 vocab=979dcca4
-/
theorem exists_first_right_hit_in_separator
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G) [Fintype S.right]
    {s t : V} (p : G.Path s t) (hs : s ∈ S.left)
    (ht : t ∈ S.right) :
    ∃ F : FirstHit p S.right.toFinset, F.finish ∈ S.separator := by
  classical
  obtain ⟨F⟩ := FirstHit.exists_of_finish_mem p S.right.toFinset (by simpa using ht)
  exact ⟨F,F.finish_mem_separator_of_right S p hs⟩

end Linkedness
end HadwigerLean
