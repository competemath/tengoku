import Tengoku.Seed.MeasureTheory.Measure.Prod
import Tengoku.Seed.MeasureTheory.Measure.WithDensity
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Continuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Riesz energy and measurable transport

The nonnegative energy and pushforward calculation in `pshd-vibe`, Lemma 1.3.
For positive order the kernel is infinite on the diagonal.
-/

open MeasureTheory
open scoped ENNReal

namespace PshLines.PSHD

/-- Riesz energy of order `s`, with the singularity retained in `ℝ≥0∞`.-/
noncomputable def rieszEnergy {E : Type*} [PseudoEMetricSpace E]
    [MeasurableSpace E] (s : ℝ) (μ : Measure E) : ℝ≥0∞ :=
  ∫⁻ p : E × E, (edist p.1 p.2 ^ s)⁻¹ ∂μ.prod μ

/-- Scaling mass scales energy quadratically.
@isnad1 id=eq.0h4v.s6.5ba4e12f269c from=translated src=- shape=9ae214d7 vocab=19b0fa8a
-/
theorem rieszEnergy_smul {E : Type*} [PseudoEMetricSpace E]
    [MeasurableSpace E] (s : ℝ) (μ : Measure E) [SFinite μ] (c : ℝ≥0∞) :
    rieszEnergy s (c • μ) = c ^ 2 * rieszEnergy s μ := by
  simp only [rieszEnergy, Measure.prod_smul_left, Measure.prod_smul_right,
    lintegral_smul_measure, smul_eq_mul, pow_two, mul_assoc]

/-- Energy of a measurable pushforward, expressed on its parameter space.
@isnad1 id=eq.1h5v.s6.c7020d25794e from=translated src=- shape=86c7029f vocab=4ccdd989
-/
theorem rieszEnergy_map {S E : Type*} [MeasurableSpace S]
    [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (s : ℝ) (m : Measure S) [SFinite m]
    {Ψ : S → E} (hΨ : Measurable Ψ) :
    rieszEnergy s (m.map Ψ) =
      ∫⁻ p : S × S, (edist (Ψ p.1) (Ψ p.2) ^ s)⁻¹ ∂m.prod m := by
  unfold rieszEnergy
  rw [Measure.map_prod_map m m hΨ hΨ]
  exact lintegral_map (by fun_prop) (hΨ.prodMap hΨ)

/-- Almost-everywhere separation suffices to control transported energy.
This permits probability laws restricted to bounded parameter regions.
@isnad1 id=le.5h6v.s7.559c38c0cc12 from=translated src=- shape=1a8cacd9 vocab=abb3f170
-/
theorem rieszEnergy_map_le_of_ae_edist_le
    {S E : Type*} [PseudoEMetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [SecondCountableTopology S] [PseudoEMetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {s : ℝ} (hs : 0 ≤ s) (m : Measure S) [SFinite m]
    {Ψ : S → E} (hΨ : Measurable Ψ) {c : ℝ≥0∞}
    (hc₀ : c ≠ 0) (hctop : c ≠ ⊤)
    (hsep : ∀ᵐ p : S × S ∂m.prod m,
      c * edist p.1 p.2 ≤ edist (Ψ p.1) (Ψ p.2)) :
    rieszEnergy s (m.map Ψ) ≤ (c ^ s)⁻¹ * rieszEnergy s m := by
  rw [rieszEnergy_map s m hΨ]
  have hc : c ^ s ≠ 0 := by simp [ENNReal.rpow_eq_zero_iff, hc₀, hctop]
  have hct : c ^ s ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs hctop
  calc
    _ ≤ ∫⁻ p : S × S, (c ^ s)⁻¹ * (edist p.1 p.2 ^ s)⁻¹ ∂m.prod m := by
      apply lintegral_mono_ae
      filter_upwards [hsep] with p hp
      calc
        _ ≤ ((c * edist p.1 p.2) ^ s)⁻¹ :=
          ENNReal.inv_le_inv' (ENNReal.rpow_le_rpow hp hs)
        _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hs,
          ENNReal.mul_inv (Or.inl hc) (Or.inl hct)]
    _ = _ := lintegral_const_mul _ (by fun_prop)

/-- A lower bound on distances gives an upper bound on transported energy.
The coefficient is positive and finite, so the estimate retains diagonal
singularities without any exceptional-set convention.
@isnad1 id=le.5h6v.s7.ff8b9d68cbcb from=translated src=- shape=690a0461 vocab=09d7ef63
-/
theorem rieszEnergy_map_le_of_edist_le
    {S E : Type*} [PseudoEMetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [SecondCountableTopology S] [PseudoEMetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {s : ℝ} (hs : 0 ≤ s) (m : Measure S) [SFinite m]
    {Ψ : S → E} (hΨ : Measurable Ψ) {c : ℝ≥0∞}
    (hc₀ : c ≠ 0) (hctop : c ≠ ⊤)
    (hsep : ∀ x y, c * edist x y ≤ edist (Ψ x) (Ψ y)) :
    rieszEnergy s (m.map Ψ) ≤ (c ^ s)⁻¹ * rieszEnergy s m := by
  rw [rieszEnergy_map s m hΨ]
  have hc : c ^ s ≠ 0 := by simp [ENNReal.rpow_eq_zero_iff, hc₀, hctop]
  have hct : c ^ s ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs hctop
  calc
    _ ≤ ∫⁻ p : S × S, (c ^ s)⁻¹ * (edist p.1 p.2 ^ s)⁻¹ ∂m.prod m := by
      apply lintegral_mono
      intro p
      calc
        _ ≤ ((c * edist p.1 p.2) ^ s)⁻¹ :=
          ENNReal.inv_le_inv' (ENNReal.rpow_le_rpow (hsep p.1 p.2) hs)
        _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hs,
          ENNReal.mul_inv (Or.inl hc) (Or.inl hct)]
    _ = _ := lintegral_const_mul _ (by fun_prop)

/-- At even integral order, the kernel is an inverse power of squared distance.
@isnad1 id=eq.1h5v.s7.0cbb572bccaa from=translated src=- shape=3de08cd7 vocab=cf8c9ccc
-/
theorem rieszEnergy_map_even {S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (k : ℕ) (m : Measure S) [SFinite m]
    {Ψ : S → E} (hΨ : Measurable Ψ) :
    rieszEnergy (2 * k : ℕ) (m.map Ψ) =
      ∫⁻ p : S × S, (ENNReal.ofReal (‖Ψ p.1 - Ψ p.2‖ ^ 2) ^ k)⁻¹ ∂m.prod m := by
  rw [rieszEnergy_map _ m hΨ]
  apply lintegral_congr
  intro p
  rw [ENNReal.rpow_natCast, edist_dist, dist_eq_norm,
    ENNReal.ofReal_pow (norm_nonneg _) 2, pow_mul]

end PshLines.PSHD
