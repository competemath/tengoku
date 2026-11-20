import Tengoku.PshdLean.PshLines.PSHD.RieszEnergy
import Tengoku.PshdLean.PshLines.PSHD.StarGeometry
import Tengoku.PshdLean.PshLines.PSHD.StarMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # A phase-independent energy bound for star selectors

The remaining parameter integral is independent of the high-value function.
This is the transport inequality of `pshd-vibe`, Lemma 1.3, before the
invariant-measure integrability estimate.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace PshLines.PSHD

/-- Every measurable choice on prescribed affine circles has energy bounded
by the same radial/Hermitian parameter integral.
@isnad1 id=le.3h6v.s11.6bf30732ddca from=translated src=- shape=7fc9196d vocab=d258542e
-/
theorem rieszEnergy_star_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {R : ℝ} (hR : 0 ≤ R) (x : E) (k : ℕ)
    (m : Measure (Icc (R / 2) R × sphere (0 : E) 1)) [SFinite m]
    {Ψ : (Icc (R / 2) R × sphere (0 : E) 1) → E} (hΨ : Measurable Ψ)
    (hcircle : ∀ s, ∃ z : ℂ, ‖z‖ = (s.1 : ℝ) ∧ Ψ s = x + z • (s.2 : E)) :
    rieszEnergy (2 * k : ℕ) (m.map Ψ) ≤
      ∫⁻ p, (ENNReal.ofReal
        (((p.1.1 : ℝ) - (p.2.1 : ℝ)) ^ 2 + (R ^ 2 / 4) *
          (2 - 2 * ‖inner ℂ (p.1.2 : E) (p.2.2 : E)‖)) ^ k)⁻¹ ∂m.prod m := by
  rw [rieszEnergy_map_even k m hΨ]
  apply lintegral_mono
  intro p
  apply ENNReal.inv_le_inv'
  apply pow_le_pow_left'
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨z, hz, heq⟩ := hcircle p.1
  obtain ⟨w, hw, hfeq⟩ := hcircle p.2
  have h := annulus_complex_smul_lower_bound
    (E := E) (e := (p.1.2 : E)) (f := (p.2.2 : E))
    (by simp) (by simp) hR
    (z := z) (w := w) (by rw [hz]; exact p.1.1.property.1)
    (by rw [hw]; exact p.2.1.property.1)
  simpa [heq, hfeq, hz, hw] using h

/-- The high-value annulus probability measure with its phase-independent
energy bound. No finiteness of the parameter integral is assumed or asserted.
@isnad1 id=ex.4h7v.s11.9c231c059fc8 from=translated src=- shape=f6de4f8c vocab=fcc1c804
-/
theorem exists_highValue_annulus_energy_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {u : E → ℝ} (hum : Measurable u) {D : Set E} (x : E)
    {R : ℝ} (hR : 0 < R) (hball : closedBall x R ⊆ D)
    (hu : ∀ v : E, v ≠ 0 → DiscPshOn (fun z => (u (x + z • v) : EReal))
      ((fun z : ℂ => x + z • v) ⁻¹' D))
    (k : ℕ) (m : Measure (Icc (R / 2) R × sphere (0 : E) 1))
    [IsProbabilityMeasure m] :
    ∃ μ : Measure E, IsProbabilityMeasure μ ∧
      μ {y | ‖y - x‖ ∈ Icc (R / 2) R ∧ u x ≤ u y} = 1 ∧
      rieszEnergy (2 * k : ℕ) μ ≤
        ∫⁻ p, (ENNReal.ofReal
          (((p.1.1 : ℝ) - (p.2.1 : ℝ)) ^ 2 + (R ^ 2 / 4) *
            (2 - 2 * ‖inner ℂ (p.1.2 : E) (p.2.2 : E)‖)) ^ k)⁻¹ ∂m.prod m := by
  obtain ⟨Ψ, hΨ, hval, hmass⟩ := exists_highValue_annulus_map hum x hR hball hu m
  refine ⟨m.map Ψ, ?_, hmass, ?_⟩
  · exact Measure.isProbabilityMeasure_map hΨ.aemeasurable
  · exact rieszEnergy_star_le hR.le x k m hΨ (fun s => (hval s).2)

end PshLines.PSHD
