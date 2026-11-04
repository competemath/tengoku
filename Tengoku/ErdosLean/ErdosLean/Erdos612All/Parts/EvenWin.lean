import Tengoku.ErdosLean.ErdosLean.Erdos612All.Parts.RangeWin
import Tengoku.ErdosLean.ErdosLean.Erdos612All.Parts.EvenDeg
import Tengoku.ErdosLean.ErdosLean.Erdos612All.Parts.EvenCliq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős 612 (all `r`), part (i): the window conditions of the two-period family

`fam [] (evPer s) [] 2 = evPer s ++ evPer s = (List.range (2(6s+1))).map G` with
`G ℓ = if ℓ < 6s+1 then evBlock s ℓ else evBlock s (ℓ - (6s+1))` (`map_range_append`);
then `allWin_map_range` / `someWin_map_range` and the block lemmas (`m = ℓ` or
`m = ℓ - (6s+1)`; at the junction the outside neighbours are `[1]`, at the ends `[]`).
-/

namespace Erdos612All

open Erdos612

/--
@isnad1 id=eq.0h1v.s7.718aed2c761e from=translated src=- shape=42ad5257 vocab=6c25b608
-/
theorem ev_fam (s : ℕ) : fam [] (evPer s) [] 2 = (List.range (6 * s + 1 + (6 * s + 1))).map
    (fun ℓ => if ℓ < 6 * s + 1 then evBlock s ℓ else evBlock s (ℓ - (6 * s + 1))) := by
  rw [← map_range_append]; simp [fam, evPer]

/-- Every window of the two-period family is a block window with admissible outside context.
@isnad1 id=allwin.0h3v.s7.97e2ecf027a0 from=translated src=- shape=8fb4159a vocab=9511493b
-/
theorem ev_win (s : ℕ) {Q : List ℕ → List ℕ → List ℕ → Prop}
    (hQ : ∀ m, m ≤ 6 * s → ∀ a c : List ℕ, (m ≠ 0 → a = evBlock s (m - 1)) →
      (m ≠ 6 * s → c = evBlock s (m + 1)) → (m = 6 * s → c.length ≤ 1) → Q a (evBlock s m) c) :
    AllWin Q (fam [] (evPer s) [] 2) := by
  rw [ev_fam, allWin_map_range]
  intro ℓ hℓ
  by_cases h : ℓ < 6 * s + 1
  · simp only [h, ite_true]
    apply hQ ℓ (by omega)
    · intro h0; simp [h0, show ℓ - 1 < 6 * s + 1 by omega]
    · intro h6
      simp [show ℓ + 1 < 6 * s + 1 by omega, show ℓ + 1 < 6 * s + 1 + (6 * s + 1) by omega]
    · intro h6
      subst h6
      simp [evBlock]
  · simp only [h, ite_false]
    apply hQ (ℓ - (6 * s + 1)) (by omega)
    · intro h0
      simp [show ℓ ≠ 0 by omega, show ¬ (ℓ - 1 < 6 * s + 1) by omega,
        show ℓ - 1 - (6 * s + 1) = ℓ - (6 * s + 1) - 1 by omega]
    · intro h6
      simp [show ℓ + 1 < 6 * s + 1 + (6 * s + 1) by omega, show ¬ (ℓ + 1 < 6 * s + 1) by omega,
        show ℓ + 1 - (6 * s + 1) = ℓ - (6 * s + 1) + 1 by omega]
    · intro h6
      simp [show ¬ (ℓ + 1 < 6 * s + 1 + (6 * s + 1)) by omega]

/--
@isnad1 id=allwin.1h1v.s4.00439f8c2a94 from=translated src=- shape=b8fb77b4 vocab=0556fd0f
-/
theorem ev_pos (s : ℕ) (hs : 1 ≤ s) : AllWin PosQ (fam [] (evPer s) [] 2) := by
  exact ev_win s fun m hm a c _ _ _ => evBlock_pos s m hs hm

/--
@isnad1 id=allwin.1h1v.s4.876d78f8426c from=translated src=- shape=b934383c vocab=71223f1e
-/
theorem ev_deg (s : ℕ) (hs : 1 ≤ s) : AllWin (DegQ (evDelta s)) (fam [] (evPer s) [] 2) := by
  exact ev_win s fun m hm a c ha hc _ => evBlock_deg s m hs hm a c ha hc

/--
@isnad1 id=somewin.1h1v.s4.7e3393744cee from=translated src=- shape=b934383c vocab=a650c00e
-/
theorem ev_tight (s : ℕ) (hs : 1 ≤ s) : SomeWin (TightQ (evDelta s)) (fam [] (evPer s) [] 2) := by
  rw [ev_fam, someWin_map_range]
  refine ⟨3, by omega, ?_⟩
  have h2 : 2 < 6 * s + 1 := by omega
  have h3 : 3 < 6 * s + 1 := by omega
  have h4 : 4 < 6 * s + 1 := by omega
  simp only [h2, h3, h4, ite_true, show (3 : ℕ) ≠ 0 by omega, ite_false,
    show 3 + 1 < 6 * s + 1 + (6 * s + 1) by omega, show (3 : ℕ) - 1 = 2 by rfl]
  exact evBlock_tight s hs

/--
@isnad1 id=allwin.1h1v.s5.93d15be39754 from=translated src=- shape=221de349 vocab=d4aed19a
-/
theorem ev_cliq (s : ℕ) (hs : 1 ≤ s) : AllWin (CliqQ (2 * (s + 1))) (fam [] (evPer s) [] 2) := by
  exact ev_win s fun m hm a c _ hc hc1 => evBlock_cliq s m hs hm a c hc hc1

end Erdos612All
