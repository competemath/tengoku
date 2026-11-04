import Tengoku.ErdosLean.ErdosLean.Erdos612All.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős 612 (all `r`), part: windows of `(List.range N).map G`

Generic bookkeeping: layers, left layers and three-layer windows of a layer sequence given by
an index function, and concatenation of two such sequences.
-/

namespace Erdos612All

open Erdos612

/--
@isnad1 id=eq.0h3v.s5.769fe4d4401c from=translated src=- shape=e78a8247 vocab=a7e68fc5
-/
theorem lay_map_range (N : ℕ) (G : ℕ → List ℕ) (ℓ : ℕ) :
    Layers.lay ((List.range N).map G) ℓ = if ℓ < N then G ℓ else [] := by
  simp only [Layers.lay, List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · simp [List.getElem?_range h]
  · rw [List.getElem?_eq_none (by simpa using (not_lt.mp h))]
    rfl

/--
@isnad1 id=eq.0h3v.s6.21e93848b4ab from=translated src=- shape=e089ddc5 vocab=8d5abc8f
-/
theorem lft_map_range (N : ℕ) (G : ℕ → List ℕ) (ℓ : ℕ) :
    Layers.lft ((List.range N).map G) ℓ =
      if ℓ = 0 then [] else if ℓ ≤ N then G (ℓ - 1) else [] := by
  rcases ℓ with _ | i
  · rfl
  · simp only [Layers.lft, List.getD_cons_succ, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    have := lay_map_range N G i
    simp only [Layers.lay] at this
    rw [this]
    split_ifs <;> first | rfl | omega

/--
@isnad1 id=iff.0h3v.s7.1c5799d5004b from=translated src=- shape=47706b22 vocab=c50eebe5
-/
theorem allWin_map_range {Q : List ℕ → List ℕ → List ℕ → Prop} (N : ℕ) (G : ℕ → List ℕ) :
    AllWin Q ((List.range N).map G) ↔
      ∀ ℓ, ℓ < N → Q (if ℓ = 0 then [] else G (ℓ - 1)) (G ℓ)
        (if ℓ + 1 < N then G (ℓ + 1) else []) := by
  unfold AllWin
  simp only [List.length_map, List.length_range, lay_map_range, lft_map_range]
  refine forall_congr' fun ℓ => imp_congr_right fun h => ?_
  by_cases h0 : ℓ = 0
  · subst h0; simp [h]
  · simp [h0, h, h.le]

/--
@isnad1 id=iff.0h3v.s7.dfe5245cda6a from=translated src=- shape=f76b4607 vocab=9e903dbe
-/
theorem someWin_map_range {Q : List ℕ → List ℕ → List ℕ → Prop} (N : ℕ) (G : ℕ → List ℕ) :
    SomeWin Q ((List.range N).map G) ↔
      ∃ ℓ, ℓ < N ∧ Q (if ℓ = 0 then [] else G (ℓ - 1)) (G ℓ)
        (if ℓ + 1 < N then G (ℓ + 1) else []) := by
  unfold SomeWin
  simp only [List.length_map, List.length_range, lay_map_range, lft_map_range]
  refine exists_congr fun ℓ => and_congr_right fun h => ?_
  by_cases h0 : ℓ = 0
  · subst h0; simp [h]
  · simp [h0, h, h.le]

/--
@isnad1 id=eq.0h4v.s6.9bee1de818d2 from=translated src=- shape=43c5d620 vocab=416be2b7
-/
theorem map_range_append (a b : ℕ) (F H : ℕ → List ℕ) :
    (List.range a).map F ++ (List.range b).map H =
      (List.range (a + b)).map (fun ℓ => if ℓ < a then F ℓ else H (ℓ - a)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_append, List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range]
    by_cases hi : i < a
    · rw [List.getElem_append_left (by simpa using hi)]
      simp [hi]
    · rw [List.getElem_append_right (by simpa using hi)]
      simp [hi]

end Erdos612All
