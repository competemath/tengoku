import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.MinoriAurei

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
LA BASE AUREA (21 lug 2026) — l'aritmetica del rapporto aureo per i
modelli H₄.  Il 600-cell vive sulle coordinate `{±1, ±1/2, ±φ/2,
±(φ−1)/2, 0}`: qui i fatti fondamentali, i bound numerici derivati da
`sqrt_five_bounds`, la distinzione dei quattro valori assoluti del blocco
aureo e la norma unitaria `(φ/2)² + (1/2)² + ((φ−1)/2)² = 1`.
-/

open Real

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

/-- Il rapporto aureo.-/
noncomputable def aureo : ℝ := (1 + Real.sqrt 5) / 2

theorem aureo_sq : aureo ^ 2 = aureo + 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [aureo]
  nlinarith [h5]

theorem aureo_bounds : 1.615 < aureo ∧ aureo < 1.62 := by
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  rw [aureo]
  constructor <;> nlinarith

theorem aureo_pos : 0 < aureo := by
  have := aureo_bounds
  linarith [this.1]

theorem aureo_sub_one_pos : 0 < aureo - 1 := by
  have := aureo_bounds
  linarith [this.1]

/-- L'inverso dell'aureo è `φ − 1`.-/
theorem aureo_inv : aureo⁻¹ = aureo - 1 := by
  have hne : aureo ≠ 0 := ne_of_gt aureo_pos
  field_simp
  nlinarith [aureo_sq]

/-- **La norma unitaria del blocco aureo**:
`(φ/2)² + (1/2)² + ((φ−1)/2)² = 1`.-/
theorem aureo_norm_sq :
    (aureo / 2) ^ 2 + (1 / 2 : ℝ) ^ 2 + ((aureo - 1) / 2) ^ 2 = 1 := by
  nlinarith [aureo_sq]

/-- I tre valori aurei positivi, in ordine: `(φ−1)/2 < 1/2 < φ/2`.-/
theorem aureo_valori_ordinati :
    0 < (aureo - 1) / 2 ∧ (aureo - 1) / 2 < 1 / 2 ∧
      (1 / 2 : ℝ) < aureo / 2 ∧ aureo / 2 < 1 := by
  have hb := aureo_bounds
  refine ⟨by linarith [hb.1], by linarith [hb.2], by linarith [hb.1],
    by linarith [hb.2]⟩

end LeanEval.Geometry.PlatonicClassification
