import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.DummyCoordinate
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.ScalarFinitenessReduction
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.LocalTrivialization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Ordinary critical values become asymptotic critical values after adjoining
one unused torus coordinate. This substitutes for the manuscript's separate
critical-locus stratification argument and introduces no new geometric input. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Filter
open scoped Topology

/-- Every ordinary critical value occurs at infinity for the dummy extension.
The new coordinate tends to infinity, while its inverse remains in the model.
@isnad1 id=le.0h2v.s9.9a826924a902 from=translated src=- shape=acfb6c74 vocab=c3ebe418
-/
theorem ordinaryCriticalValues_subset_dummy_asymptotic {d : ℕ} (p : AmbientPolynomial d) :
    ordinaryCriticalValues (fun x : affineTorus d => ambientEval p x.val)
      (fun x => ambientDifferentialNorm (torusPartial p) x.val) ⊆
    asymptoticCriticalValues (fun x : affineTorus (d + 1) => ambientEval (dummyExtension p) x.val)
      (fun x => ‖x.val‖) (fun x => ambientDifferentialNorm (torusPartial (dummyExtension p)) x.val) := by
  rintro c ⟨x, hx, hc⟩
  let a (n : ℕ) : ℂ := ((n : ℝ) + 1 : ℝ)
  have ha (n : ℕ) : a n ≠ 0 := Complex.ofReal_ne_zero.mpr (by dsimp; positivity)
  let y (n : ℕ) : affineTorus (d + 1) := ⟨dummyPoint (a n) x.val, dummyPoint_mem (ha n) x.property⟩
  refine ⟨y, ?_, ?_, ?_⟩
  · have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_mono (fun n : ℕ => show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
        tendsto_natCast_atTop_atTop
    apply tendsto_atTop_mono _ hn
    intro n
    have h := norm_le_dummyPoint_norm (a n) x.val
    have hn : ‖a n‖ = (n : ℝ) + 1 := by
      change ‖(((n : ℝ) + 1 : ℝ) : ℂ)‖ = (n : ℝ) + 1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hn] at h
    exact h
  · have he (n : ℕ) : ambientEval (dummyExtension p) (y n).val = c := by
      simpa only [y, dummyExtension_eval] using hc
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c))
  · have he (n : ℕ) : ‖(y n).val‖ *
        ambientDifferentialNorm (torusPartial (dummyExtension p)) (y n).val = 0 := by
      rw [show ambientDifferentialNorm (torusPartial (dummyExtension p)) (y n).val = 0 from
        dummyExtension_critical p (a n) x.val hx, mul_zero]
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end
end DuistermaatVanDerKallen
