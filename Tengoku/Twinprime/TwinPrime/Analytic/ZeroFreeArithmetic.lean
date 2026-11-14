import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Numerical contradiction for the three-four-one zero-free argument

This is only the real-variable parameter calculation. Applying it to an
L-function requires proving the corresponding logarithmic-derivative inequality.
-/

namespace TwinPrime.Analytic

/--
@isnad1 id=not.3h2v.s7.d96d42174c9e from=translated src=- shape=53d7a4ad vocab=70d00927
-/
theorem four_three_pole_contradiction {E δ : ℝ} (hE : 0 < E)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (20 * E)) :
    ¬ 4 / (1 / (4 * E) + δ) ≤ 3 / (1 / (4 * E)) + E := by
  have ha : 0 < 1 / (4 * E) := by positivity
  have hden : 0 < 1 / (4 * E) + δ := by linarith
  have hsum : 1 / (4 * E) + 1 / (20 * E) = 3 / (10 * E) := by field_simp; ring
  have hbound : 1 / (4 * E) + δ ≤ 3 / (10 * E) := by linarith
  have hlo : 40 * E / 3 ≤ 4 / (1 / (4 * E) + δ) := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 40 * E / 3)
    have heq : (40 * E / 3) * (3 / (10 * E)) = 4 := by field_simp; ring
    linarith
  have hr : 3 / (1 / (4 * E)) + E = 13 * E := by field_simp; ring
  rw [hr]
  linarith

/--
@isnad1 id=and.1h1v.s7.b85e21780c86 from=translated src=- shape=e5e20d96 vocab=c96aef97
-/
theorem zero_free_parameters_le {E : ℝ} (hE : 120 ≤ E) :
    0 < 1 / (4 * E) ∧ 1 / (4 * E) ≤ 1 / 8 ∧
      0 < 1 / (20 * E) ∧ 1 / (20 * E) ≤ 1 / 4 := by
  have hE0 : 0 < E := by linarith
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 4 * E)).mpr
    linarith
  · apply (div_le_iff₀ (by positivity : 0 < 20 * E)).mpr
    linarith

end TwinPrime.Analytic
