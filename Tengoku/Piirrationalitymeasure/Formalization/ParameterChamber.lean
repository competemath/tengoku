import Tengoku.Piirrationalitymeasure.Formalization.SavingTranslationBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The exact chamber margins and a common one-norm radius in (6.53). -/

namespace PiIrrationality

/--
@isnad1 id=admissib.1h1v.s5.8112fce7a8e9 from=translated src=- shape=0996d82a vocab=eafc6d5a
-/
theorem admissible_candidate_add_of_parameterNormOne_lt {h : ℝ × ℝ}
    (hh : parameterNormOne h < 1 / 5570) : Admissible (candidate + h) := by
  have hx : -parameterNormOne h ≤ h.1 ∧ h.1 ≤ parameterNormOne h := by
    have ha := abs_nonneg h.2
    have hb := abs_le.mp (le_refl |h.1|)
    dsimp [parameterNormOne]
    constructor <;> linarith
  have hy : -parameterNormOne h ≤ h.2 ∧ h.2 ≤ parameterNormOne h := by
    have ha := abs_nonneg h.1
    have hb := abs_le.mp (le_refl |h.2|)
    dsimp [parameterNormOne]
    constructor <;> linarith
  have hsum : -parameterNormOne h ≤ h.1 + h.2 := by
    dsimp [parameterNormOne]
    linarith [neg_abs_le h.1, neg_abs_le h.2]
  obtain ⟨h1, h2, h3, h4⟩ := candidate_chamber_margins
  change 1 < candidate.1 + h.1 + (candidate.2 + h.2) ∧
    1 < 2 * (candidate.2 + h.2) ∧ 7 * (candidate.2 + h.2) < 5 ∧
    1 < 2 * (candidate.1 + h.1) + 4 * (candidate.2 + h.2) - 2
  dsimp only [candidate, Prod.fst, Prod.snd]
  exact ⟨by linarith, by linarith [hy.1], by linarith [hy.2],
    by linarith [hx.1, hy.1]⟩

end PiIrrationality
