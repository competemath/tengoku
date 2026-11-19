import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.CoreFanRooted
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.PairSlots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A trimmed fan transfers rooted linkedness from the core to its starts
-/

namespace HadwigerLean
namespace Linkedness

/-- Rooted linkedness at precisely the fan arrival set suffices for
rooted linkedness at all fan starts.
@isnad1 id=rootedli.3h6v.s7.921ddd7c3bdb from=translated src=- shape=9a715322 vocab=8444da63
-/
theorem rootedLinked_of_trimmed_fan_to_arrivals
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    (P : IndexedPairs (Fin r) V) (F : IndexedLinkage G P)
    (J : Finset V)
    (hfinish : ∀ t, P.finish t ∈ J)
    (hfirst : ∀ t x, x ∈ pathVertexSet (F.path t) →
      x ∈ J → x = P.finish t)
    (hcore : RootedLinked (G.induce (J : Set V))
      (fanArrivalFinset P J hfinish)) :
    RootedLinked G (Finset.univ.image P.start) := by
  classical
  intro n Q hQ hne hX
  obtain ⟨slot, hslot, hstart, hfinish'⟩ :=
    exists_pair_slots P Q hQ hne hX
  exact rooted_linkage_of_core_fan_slots P F J hfinish hfirst hcore
    slot hslot Q hstart hfinish'
/-- If a fan from all roots reaches a core without meeting that core before
its last vertex, and the core links every arrival set, then the original
root set is linked with path interiors avoiding the other roots.
@isnad1 id=rootedli.3h6v.s7.8fc8fbf5c524 from=translated src=- shape=781d297b vocab=079c8aac
-/
theorem rootedLinked_of_trimmed_fan_to_core
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    (P : IndexedPairs (Fin r) V) (F : IndexedLinkage G P)
    (J : Finset V)
    (hfinish : ∀ t, P.finish t ∈ J)
    (hfirst : ∀ t x, x ∈ pathVertexSet (F.path t) →
      x ∈ J → x = P.finish t)
    (hcore : ∀ Y : Finset (J : Set V), Y.card ≤ r →
      RootedLinked (G.induce (J : Set V)) Y) :
    RootedLinked G (Finset.univ.image P.start) := by
  exact rootedLinked_of_trimmed_fan_to_arrivals P F J hfinish hfirst
    (hcore (fanArrivalFinset P J hfinish)
      (fanArrivalFinset_card_le P J hfinish))

end Linkedness
end HadwigerLean
