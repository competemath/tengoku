import Tengoku.Linearhadwiger.HadwigerLean.Woven.MixedFanOutput
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The projected mixed fan: all proxies and one residual start per pair
-/

namespace HadwigerLean
namespace Woven

variable {V : Type*} [Fintype V] [DecidableEq V] {a : ℕ}

/-- Data obtained after removing an auxiliary pair vertex from one path.-/
structure RightProjectedPath (G : SimpleGraph V)
    (source : Fin a × Fin 2 → V) (i : Fin a) (t : V)
    (p : (pairedFanGraph G source).Path (.inr i) (.inl t)) where
  bit : Fin 2
  start : V
  path : G.Path start t
  source_eq : source (i,bit) = start
  support_subset : ∀ v ∈ pathVertexSet path,
    Sum.inl v ∈ pathVertexSet p

noncomputable def chooseRightProjectedPath
    (G : SimpleGraph V) (source : Fin a × Fin 2 → V)
    (i : Fin a) (t : V)
    (p : (pairedFanGraph G source).Path (.inr i) (.inl t))
    (hright : ∀ j : Fin a,
      (Sum.inr j : PairedFanVertex V a) ∈ pathVertexSet p → j = i) :
    RightProjectedPath G source i t p := by
  classical
  apply Classical.choice
  obtain ⟨b,u,q,hb,hq⟩ :=
    exists_pairedFanProjectRightPath G source i t p hright
  exact ⟨⟨b,u,q,hb,hq⟩⟩

variable {G : SimpleGraph V} {Z U H : Finset V}
  {P : IndexedPairs (Fin a × Fin 2) V}

end Woven
end HadwigerLean
