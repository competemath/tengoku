import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact optimization of the information-dependent graph budget

Algebraic part of 3PREL8 §6.2. `D w` represents the deletion exponent at
cutoff log-height `w`. These lemmas do not assume that a conditioning event
is measurable at a smaller cutoff; the admissible lower endpoint is explicit.
The uniform arithmetic estimates and saddle asymptotics remain separate.
-/
namespace PaperC.Prel8.InformationBudget

noncomputable section

def budget (D : ℝ → ℝ) (I w : ℝ) : ℝ := min (D w-I) ((w-I)/2)

/--
@isnad1 id=eq.1h3v.s6.bd4c7e262ddc from=translated src=- shape=4a806daa vocab=9ea96a66
-/
theorem budget_at_crossing (D : ℝ → ℝ) (I s : ℝ) (h : 2*D s=s+I) :
    budget D I s = (s-I)/2 := by
  unfold budget
  have he : D s-I=(s-I)/2 := by linarith
  rw [he, min_self]

/-- Every admissible cutoff has budget at most that of the crossing.
@isnad1 id=le.4h6v.s6.c455cc97f0ab from=translated src=- shape=723c2b55 vocab=f08fe394
-/
theorem crossing_maximizes {D : ℝ → ℝ} {I lo hi s w : ℝ}
    (hD : AntitoneOn D (Set.Icc lo hi)) (hs : s ∈ Set.Icc lo hi)
    (hw : w ∈ Set.Icc lo hi) (hcross : 2*D s=s+I) :
    budget D I w ≤ budget D I s := by
  rw [budget_at_crossing D I s hcross]
  by_cases h : w ≤ s
  · exact (min_le_right _ _).trans (by linarith)
  · have hd := hD hs hw (le_of_not_ge h)
    exact (min_le_left _ _).trans (by linarith)

/-- The crossing is unique even when deletion is merely nonincreasing.
@isnad1 id=eq.5h6v.s6.82c1ef393d39 from=translated src=- shape=af337c73 vocab=59df8bf1
-/
theorem crossing_unique {D : ℝ → ℝ} {I lo hi s t : ℝ}
    (hD : AntitoneOn D (Set.Icc lo hi)) (hs : s ∈ Set.Icc lo hi)
    (ht : t ∈ Set.Icc lo hi) (hcs : 2*D s=s+I) (hct : 2*D t=t+I) : s=t := by
  rcases le_total s t with h | h
  · have hd := hD hs ht h
    linarith
  · have hd := hD ht hs h
    linarith

/-- If only cutoffs above `floor` are allowed, use `max floor s`.
@isnad1 id=le.6h7v.s6.f9e5b3454bd9 from=translated src=- shape=84d4b3d5 vocab=a3e9c817
-/
theorem admissible_cutoff_maximizes {D : ℝ → ℝ} {I lo hi s floor w : ℝ}
    (hD : AntitoneOn D (Set.Icc lo hi)) (hs : s ∈ Set.Icc lo hi)
    (hf : floor ∈ Set.Icc lo hi) (hw : w ∈ Set.Icc lo hi)
    (hfw : floor ≤ w) (hcross : 2*D s=s+I) :
    budget D I w ≤ budget D I (max floor s) := by
  by_cases h : floor ≤ s
  · rw [max_eq_right h]
    exact crossing_maximizes hD hs hw hcross
  · have hsf : s ≤ floor := le_of_not_ge h
    rw [max_eq_left hsf]
    have hd := hD hs hf hsf
    have hmin : budget D I floor = D floor-I := by
      unfold budget
      rw [min_eq_left (by linarith)]
    rw [hmin]
    have hdw := hD hf hw hfw
    exact (min_le_left _ _).trans (by linarith)

/-- The exact crossing converts one margin into both required exponential margins.
@isnad1 id=and.2h6v.s7.0d01984e9d69 from=translated src=- shape=52beca65 vocab=54041492
-/
theorem two_error_margins {deletion I w ell c nu : ℝ}
    (hcross : 2*deletion=w+I) (hbudget : ell ≤ (w-I)/2-c*nu) :
    I+ell-deletion ≤ -c*nu ∧ I+2*ell-w ≤ -2*c*nu := by
  constructor <;> linarith

/-- A strict smaller margin absorbs a controlled deterministic remainder.
@isnad1 id=le.2h5v.s6.164fcd787cc3 from=translated src=- shape=9c5a59a6 vocab=a87daef5
-/
theorem absorb_remainder {exponent remainder c c' nu : ℝ}
    (hexponent : exponent ≤ -c*nu) (hremainder : remainder ≤ (c-c')*nu) :
    exponent+remainder ≤ -c'*nu := by
  nlinarith

end
end PaperC.Prel8.InformationBudget
