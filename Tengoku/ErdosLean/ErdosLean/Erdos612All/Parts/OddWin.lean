import Tengoku.ErdosLean.ErdosLean.Erdos612All.Parts.RangeWin
import Tengoku.ErdosLean.ErdosLean.Erdos612All.Parts.OddDeg
import Tengoku.ErdosLean.ErdosLean.Erdos612All.Parts.OddCliq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős 612 (all `r`), part (ii): the window conditions of the two-period family

`fam (odPre q) (odPer q) (odSuf q) 2 = odPre q ++ odPer q ++ odPer q ++ odSuf q`.  Writing
`odPre q = (List.range 2).map (fun _ => [δ])` and
`odSuf q = (List.range 3).map (fun i => if i = 0 then [1] else [δ])`, `map_range_append`
turns it into `(List.range (2(6q+19) + 5)).map G`.  Windows at the prefix/suffix layers are
checked directly (`δ ≥ x`, clump counts `≤ 2`); windows inside a period use the block lemmas
with left context `[δ]` or `odE q` (sum `x`) and right context `[1]`.
-/

namespace Erdos612All

open Erdos612

/-- The global layer function of the two-period family.-/
def odGlob (q ℓ : ℕ) : List ℕ :=
  if ℓ < 2 then [odDelta q]
  else if ℓ < 2 + (6 * q + 19) then odBlock q (ℓ - 2)
  else if ℓ < 2 + (6 * q + 19) + (6 * q + 19) then odBlock q (ℓ - 2 - (6 * q + 19))
  else if ℓ = 2 + (6 * q + 19) + (6 * q + 19) then [1]
  else [odDelta q]

/--
@isnad1 id=eq.0h1v.s6.96de42d26cb7 from=translated src=- shape=89a6b831 vocab=62a6be77
-/
theorem od_fam (q : ℕ) : fam (odPre q) (odPer q) (odSuf q) 2 =
    (List.range (2 + (6 * q + 19) + (6 * q + 19) + 3)).map (odGlob q) := by
  have hpre : odPre q = (List.range 2).map (fun _ => [odDelta q]) := rfl
  have hsuf : odSuf q = (List.range 3).map (fun i => if i = 0 then [1] else [odDelta q]) := rfl
  simp only [fam, List.replicate_succ, List.replicate_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  rw [hpre, hsuf, odPer, map_range_append, map_range_append, map_range_append]
  rw [show 2 + (6 * q + 19 + (6 * q + 19)) + 3 = 2 + (6 * q + 19) + (6 * q + 19) + 3 by ring]
  congr 1
  funext ℓ
  unfold odGlob
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/--
@isnad1 id=eq.0h1v.s5.fa64208ee0a9 from=translated src=- shape=f1c73fa2 vocab=5e7b800a
-/
theorem odE_ne (q : ℕ) : odBlock q (6 * q + 19 - 1) = odE q := by
  rw [show 6 * q + 19 - 1 = 6 * q + 18 by omega, odBlock_E3]

/--
@isnad1 id=eq.1h2v.s4.560f244ae519 from=translated src=- shape=7311a79c vocab=be7e04c0
-/
theorem odGlob_pre (q ℓ : ℕ) (h : ℓ < 2) : odGlob q ℓ = [odDelta q] := by
  unfold odGlob; rw [ite_eq_left h]

/--
@isnad1 id=eq.2h2v.s6.d4b3dad18478 from=translated src=- shape=0cf36689 vocab=3d66527e
-/
theorem odGlob_blk (q ℓ : ℕ) (h1 : 2 ≤ ℓ) (h2 : ℓ < 2 + (6 * q + 19)) :
    odGlob q ℓ = odBlock q (ℓ - 2) := by
  unfold odGlob; rw [ite_eq_right (by omega), ite_eq_left h2]

/--
@isnad1 id=eq.2h2v.s7.a4d351165ff9 from=translated src=- shape=38e25f3d vocab=3d66527e
-/
theorem odGlob_blk2 (q ℓ : ℕ) (h1 : 2 + (6 * q + 19) ≤ ℓ)
    (h2 : ℓ < 2 + (6 * q + 19) + (6 * q + 19)) :
    odGlob q ℓ = odBlock q (ℓ - 2 - (6 * q + 19)) := by
  unfold odGlob; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]

/--
@isnad1 id=eq.1h2v.s6.4dd6c5400428 from=translated src=- shape=a4aa5105 vocab=e0347313
-/
theorem odGlob_junc (q ℓ : ℕ) (h : ℓ = 2 + (6 * q + 19) + (6 * q + 19)) : odGlob q ℓ = [1] := by
  unfold odGlob; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]

/--
@isnad1 id=eq.1h2v.s6.1ac6bbfd5bb7 from=translated src=- shape=d7aa0e5b vocab=088e70fd
-/
theorem odGlob_suf (q ℓ : ℕ) (h : 2 + (6 * q + 19) + (6 * q + 19) < ℓ) :
    odGlob q ℓ = [odDelta q] := by
  unfold odGlob; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Every window of the two-period family is an end window or a block window.
@isnad1 id=allwin.0h8v.s8.80240af7c46b from=translated src=- shape=a2d24d2a vocab=6a053bb9
-/
theorem od_win (q : ℕ) {Q : List ℕ → List ℕ → List ℕ → Prop}
    (hQ : ∀ m, m < 6 * q + 19 → ∀ a c : List ℕ, (m ≠ 0 → a = odBlock q (m - 1)) →
      (m = 0 → odX q ≤ a.sum) → (m + 1 ≠ 6 * q + 19 → c = odBlock q (m + 1)) →
      (m + 1 = 6 * q + 19 → c = [1]) → Q a (odBlock q m) c)
    (h0 : Q [] [odDelta q] [odDelta q]) (h1 : Q [odDelta q] [odDelta q] [1])
    (h2 : Q (odE q) [1] [odDelta q]) (h3 : Q [1] [odDelta q] [odDelta q])
    (h4 : Q [odDelta q] [odDelta q] []) :
    AllWin Q (fam (odPre q) (odPer q) (odSuf q) 2) := by
  have hB0 : odBlock q 0 = [1] := odBlock_three q 0 (by omega)
  have hxδ : odX q ≤ odDelta q := by unfold odDelta; nlinarith
  have hxE : odX q ≤ (odE q).sum := by rw [odE_sum]; rfl
  rw [od_fam, allWin_map_range]
  intro ℓ hℓ
  by_cases hA : ℓ < 2
  · by_cases hz : ℓ = 0
    · rw [ite_eq_left hz, ite_eq_left (by omega), odGlob_pre q ℓ hA, odGlob_pre q (ℓ + 1) (by omega)]
      exact h0
    · rw [ite_eq_right hz, ite_eq_left (by omega), odGlob_pre q ℓ hA, odGlob_pre q (ℓ - 1) (by omega),
        odGlob_blk q (ℓ + 1) (by omega) (by omega), show ℓ + 1 - 2 = 0 by omega, hB0]
      exact h1
  by_cases hB : ℓ < 2 + (6 * q + 19)
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), odGlob_blk q ℓ (by omega) hB]
    apply hQ (ℓ - 2) (by omega)
    · intro h; rw [odGlob_blk q (ℓ - 1) (by omega) (by omega)]; congr 1 <;> omega
    · intro h; rw [odGlob_pre q (ℓ - 1) (by omega)]; simpa using hxδ
    · intro h; rw [odGlob_blk q (ℓ + 1) (by omega) (by omega)]; congr 1 <;> omega
    · intro h
      rw [odGlob_blk2 q (ℓ + 1) (by omega) (by omega), show ℓ + 1 - 2 - (6 * q + 19) = 0 by omega]
      exact hB0
  by_cases hC : ℓ < 2 + (6 * q + 19) + (6 * q + 19)
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), odGlob_blk2 q ℓ (by omega) hC]
    apply hQ (ℓ - 2 - (6 * q + 19)) (by omega)
    · intro h; rw [odGlob_blk2 q (ℓ - 1) (by omega) (by omega)]; congr 1 <;> omega
    · intro h
      rw [odGlob_blk q (ℓ - 1) (by omega) (by omega), show ℓ - 1 - 2 = 6 * q + 19 - 1 by omega,
        odE_ne]
      exact hxE
    · intro h; rw [odGlob_blk2 q (ℓ + 1) (by omega) (by omega)]; congr 1 <;> omega
    · intro h; exact odGlob_junc q (ℓ + 1) (by omega)
  by_cases hD : ℓ = 2 + (6 * q + 19) + (6 * q + 19)
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), odGlob_junc q ℓ hD,
      odGlob_blk2 q (ℓ - 1) (by omega) (by omega),
      show ℓ - 1 - 2 - (6 * q + 19) = 6 * q + 19 - 1 by omega, odE_ne,
      odGlob_suf q (ℓ + 1) (by omega)]
    exact h2
  by_cases hE : ℓ = 2 + (6 * q + 19) + (6 * q + 19) + 1
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), odGlob_suf q ℓ (by omega),
      odGlob_junc q (ℓ - 1) (by omega), odGlob_suf q (ℓ + 1) (by omega)]
    exact h3
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), odGlob_suf q ℓ (by omega),
      odGlob_suf q (ℓ - 1) (by omega)]
    exact h4

/--
@isnad1 id=allwin.0h1v.s4.902e26d1c6a9 from=translated src=- shape=32574f38 vocab=5fda81f9
-/
theorem od_pos (q : ℕ) : AllWin PosQ (fam (odPre q) (odPer q) (odSuf q) 2) := by
  have hδ : 0 < odDelta q := by unfold odDelta odX odU; positivity
  exact od_win q (fun m hm a c _ _ _ _ => odBlock_pos q m hm)
    ⟨by simp, by simpa using hδ⟩ ⟨by simp, by simpa using hδ⟩ ⟨by simp, by simp⟩
    ⟨by simp, by simpa using hδ⟩ ⟨by simp, by simpa using hδ⟩

/--
@isnad1 id=allwin.0h1v.s4.46541737d14a from=translated src=- shape=7492cdae vocab=eff56658
-/
theorem od_deg (q : ℕ) : AllWin (DegQ (odDelta q)) (fam (odPre q) (odPer q) (odSuf q) 2) := by
  have hE := odE_sum q
  refine od_win q (fun m hm a c ha ha0 hc hc0 => odBlock_deg q m hm a c ha ha0 hc hc0) ?_ ?_ ?_ ?_ ?_ <;>
    · intro w hw; simp at hw; subst hw; simp

/--
@isnad1 id=somewin.0h1v.s4.abf266ddb03d from=translated src=- shape=7492cdae vocab=532ecfdf
-/
theorem od_tight (q : ℕ) : SomeWin (TightQ (odDelta q)) (fam (odPre q) (odPer q) (odSuf q) 2) := by
  rw [od_fam, someWin_map_range]
  refine ⟨5, by omega, ?_⟩
  unfold odGlob
  simp (disch := omega) only [ite_eq_right, ite_eq_left]
  exact odBlock_tight q

/--
@isnad1 id=allwin.0h1v.s5.5dd81f44afcc from=translated src=- shape=68b14e61 vocab=672a0319
-/
theorem od_cliq (q : ℕ) :
    AllWin (CliqQ (2 * (q + 4) + 1)) (fam (odPre q) (odPer q) (odSuf q) 2) := by
  refine od_win q (fun m hm a c _ _ hc hc0 => odBlock_cliq q m hm a c hc
    (fun h => by rw [hc0 h]; simp)) ?_ ?_ ?_ ?_ ?_ <;> (unfold CliqQ; simp)

end Erdos612All
