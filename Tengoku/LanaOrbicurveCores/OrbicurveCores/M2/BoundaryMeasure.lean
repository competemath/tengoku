/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.M2.Setup
import Tengoku.LanaOrbicurveCores.OrbicurveCores.ForMathlib.ProjectiveLine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# M2: measure theory of the boundary action

The boundary `B = OnePoint ℝ` carries the Cauchy measure `cauchy`, a finite measure in the
Lebesgue class (`bdry ≪ cauchy ≪ bdry`). For `g ∈ SL(2, ℝ)`:

* `cauchy_preimage_le`: `ν(g⁻¹E) ≤ ‖g‖² ν(E)` (explicit Radon–Nikodym bound, by the
  one-dimensional change of variables);
* `quasiMeasurePreserving_smul`: `g` preserves the Lebesgue class;
* `tendsto_lintegral_comp_smul`: translation is continuous in `L¹` for bounded measurable
  functions;
* `exists_subseq_ae_tendsto`: if `gₙ → g₀` and `ψ : B → Y` is measurable into a compact
  metrizable space, a subsequence of `ψ ∘ gₙ` converges a.e. to `ψ ∘ g₀`.
-/

open MeasureTheory Matrix Matrix.SpecialLinearGroup OnePoint Set Filter Topology
open scoped MatrixGroups ENNReal

namespace OrbicurveCores.M2

/-- The Möbius function of `g ∈ SL(2, ℝ)` on `ℝ`. -/
noncomputable def mobR (g : SL(2, ℝ)) (x : ℝ) : ℝ := (g 0 0 * x + g 0 1) / (g 1 0 * x + g 1 1)

/-- The squared Frobenius norm. -/
def frob (g : SL(2, ℝ)) : ℝ := g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2

/-- The Cauchy weight. -/
noncomputable def cw (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (1 + x ^ 2)⁻¹

lemma measurable_cw : Measurable cw := by unfold cw; fun_prop

/-- The Cauchy measure on `ℝ`, and on the boundary `OnePoint ℝ` (a finite measure in the
Lebesgue class). -/
noncomputable def cauchyR : Measure ℝ := volume.withDensity cw

noncomputable def cauchy : Measure (OnePoint ℝ) := cauchyR.map ((↑) : ℝ → OnePoint ℝ)

lemma cauchy_apply {E : Set (OnePoint ℝ)} (hE : MeasurableSet E) :
    cauchy E = ∫⁻ x in (↑) ⁻¹' E, cw x := by
  rw [cauchy, Measure.map_apply OnePoint.continuous_coe.measurable hE, cauchyR,
    withDensity_apply _ (OnePoint.continuous_coe.measurable hE)]

lemma cauchy_absolutelyContinuous_bdry : cauchy ≪ bdry :=
  (withDensity_absolutelyContinuous _ _).map OnePoint.continuous_coe.measurable

lemma bdry_absolutelyContinuous_cauchy : bdry ≪ cauchy := by
  refine Measure.AbsolutelyContinuous.map ?_ OnePoint.continuous_coe.measurable
  refine withDensity_absolutelyContinuous' measurable_cw.aemeasurable ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    simp only [cw, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity

end OrbicurveCores.M2
