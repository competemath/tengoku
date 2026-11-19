import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor.MengerAlternatives
import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor.ABSeparation
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.Massed
import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.FirstHit
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Linking roots to a large linked core, or finding a small separator
-/

namespace HadwigerLean
namespace Linkedness

/-- Set Menger with a prescribed enumeration of the starts and an
arbitrary target set.
@isnad1 id=or.1h5v.s6.2343c2e99cd3 from=translated src=- shape=f425c0a5 vocab=47e16280
-/
theorem root_set_linkage_or_separator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {r : ℕ}
    (root : Fin r → V) (hroot : Function.Injective root)
    (J : Finset V) :
    (∃ (P : IndexedPairs (Fin r) V) (L : IndexedLinkage G P),
      (∀ i, P.start i = root i) ∧ (∀ i, P.finish i ∈ J)) ∨
    ∃ Q : Finset V, Q.card < r ∧
      SetMenger.IsABSeparator G (Finset.univ.image root) J Q := by
  classical
  let R : Finset V := Finset.univ.image root
  obtain ⟨Q, n, P, L, hQ, hAB, hcard, _⟩ :=
    SetMenger.finite_set_menger G R J
  by_cases hn : r ≤ n
  · left
    let e : Fin r ↪ Fin n := Fin.castLEEmb hn
    let P' := P.reindex e
    let L' : IndexedLinkage G P' := L.reindex e
    let F : Finset V := Finset.univ.image P'.finish
    have hFcard : F.card = r := by
      simp [F, Finset.card_image_of_injective _ L'.finish_injective]
    have hAB' : SetMenger.IsABLinkage L' R F := by
      constructor
      · intro i
        exact hAB.1 (e i)
      · intro i
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨P'', L'', hstart, hfinish, _⟩ :=
      reindex_root_target_linkage root hroot F hFcard L' hAB'
    refine ⟨P'', L'', hstart, ?_⟩
    intro i
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hfinish i)
    exact hj ▸ hAB.2 (e j)
  · right
    exact ⟨Q, by omega, hQ⟩

end Linkedness
end HadwigerLean
