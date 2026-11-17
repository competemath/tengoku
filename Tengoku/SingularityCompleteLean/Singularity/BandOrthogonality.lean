import Tengoku.SingularityCompleteLean.Singularity.FiniteBand

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integrating the frequency-matrix cancellation

This module unfolds the scalar finite-band function into its coordinates. The
matrix identity then gives zero pairing against any bounded periodic modulation
of each frequency profile. Translation covariance of the L² Fourier transform is
a separate step.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Singularity

/-- Translating a band integral back to the base cell.
@isnad1 id=eq.0h5v.s7.b4a13442ed68 from=translated src=- shape=a0a772bf vocab=f98be1dd
-/
theorem integral_mul_bandPiece {d : ℕ} (q : ℝ)
    (v : ℝ → EuclideanSpace ℂ (Fin d)) (a : ℝ → ℂ) (l : Fin d) :
    ∫ t, a t * bandPiece q v l t =
      ∫ ω in Ico 0 q, a (ω + (l : ℕ) * q) * v ω l := by
  rw [← integral_add_right_eq_self (fun t => a t * bandPiece q v l t) ((l : ℕ) * q)]
  rw [← integral_indicator measurableSet_Ico]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    by_cases hω : ω ∈ Ico 0 q <;> simp [bandPiece, hω])

/-- The complete change-of-variables identity, with integrability proved from L².
@isnad1 id=eq.3h4v.s8.b3f092e1a51a from=translated src=- shape=a3e6573d vocab=908c02d9
-/
theorem integral_mul_finiteBand {d : ℕ} (q : ℝ)
    {v : ℝ → EuclideanSpace ℂ (Fin d)} (hv : Measurable v)
    (hnorm : ∀ ω, ‖v ω‖ = 1) {a : ℝ → ℂ} (ha : MemLp a 2 volume) :
    ∫ t, a t * finiteBand q v t =
      ∫ ω in Ico 0 q, ∑ l : Fin d, a (ω + (l : ℕ) * q) * v ω l := by
  have hp : ∀ l : Fin d, Integrable (fun t => a t * bandPiece q v l t) :=
    fun l => ha.integrable_mul (bandPiece_memLp q hv hnorm l)
  have hc : ∀ l : Fin d, IntegrableOn
      (fun ω => a (ω + (l : ℕ) * q) * v ω l) (Ico 0 q) := by
    intro l
    apply (integrable_indicator_iff measurableSet_Ico).mp
    apply ((hp l).comp_add_right ((l : ℕ) * q)).congr
    exact Filter.Eventually.of_forall (fun ω => by
      by_cases hω : ω ∈ Ico 0 q <;> simp [bandPiece, hω])
  calc
    ∫ t, a t * finiteBand q v t = ∫ t, ∑ l, a t * bandPiece q v l t := by
      simp only [finiteBand, Finset.mul_sum]
    _ = ∑ l, ∫ t, a t * bandPiece q v l t := integral_finsetSum _ (fun l _ => hp l)
    _ = ∑ l : Fin d, ∫ ω in Ico 0 q, a (ω + (l : ℕ) * q) * v ω l := by
      simp_rw [integral_mul_bandPiece]
    _ = ∫ ω in Ico 0 q, ∑ l : Fin d, a (ω + (l : ℕ) * q) * v ω l :=
      (integral_finsetSum _ (fun l _ => hc l)).symm

/-- Bounded modulation times the conjugate of an L² profile remains in L².
@isnad1 id=memlp.3h2v.s7.d29aafc4a115 from=translated src=- shape=81b11fdc vocab=e3fcd991
-/
theorem memLp_modulated_conj {h w : ℝ → ℂ} (hh : MemLp h 2 volume)
    (hw : Measurable w) (hwbound : ∀ t, ‖w t‖ ≤ 1) :
    MemLp (fun t => w t * conj (h t)) 2 volume := by
  apply hh.of_le
    (hw.stronglyMeasurable.aestronglyMeasurable.mul
      (Complex.continuous_conj.comp_aestronglyMeasurable hh.aestronglyMeasurable))
  exact Filter.Eventually.of_forall (fun t => by
    change ‖w t * conj (h t)‖ ≤ ‖h t‖
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_right (hwbound t) (norm_nonneg _)).trans_eq (one_mul _))

/-- The pointwise matrix equation implies zero integrated pairing for every
modulation which agrees across the frequency cells.
@isnad1 id=eq.7h5v.s8.317f87166682 from=translated src=- shape=33be7a78 vocab=2909d624
-/
theorem finiteBand_periodic_pairing_zero {d : ℕ} (q : ℝ)
    {v : ℝ → EuclideanSpace ℂ (Fin d)} (hv : Measurable v)
    (hnorm : ∀ ω, ‖v ω‖ = 1) {h w : ℝ → ℂ} (hh : MemLp h 2 volume)
    (hw : Measurable w) (hwbound : ∀ t, ‖w t‖ ≤ 1)
    (hperiod : ∀ ω (l : Fin d), w (ω + (l : ℕ) * q) = w ω)
    (hker : ∀ ω ∈ Ico 0 q, ∑ l : Fin d, conj (h (ω + (l : ℕ) * q)) * v ω l = 0) :
    ∫ t, (w t * conj (h t)) * finiteBand q v t = 0 := by
  rw [integral_mul_finiteBand q hv hnorm (memLp_modulated_conj hh hw hwbound)]
  calc
    ∫ ω in Ico 0 q, ∑ l : Fin d, (w (ω + (l : ℕ) * q) *
        conj (h (ω + (l : ℕ) * q))) * v ω l = ∫ ω in Ico 0 q, (0 : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro ω hω
      simp_rw [hperiod, mul_assoc, ← Finset.mul_sum, hker ω hω, mul_zero]
    _ = 0 := integral_zero _ _

/-- Specialization to the actual Fourier sample matrix.
@isnad1 id=eq.6h6v.s12.174cd80bf11e from=translated src=- shape=55a1088e vocab=f21b542f
-/
theorem frequency_kernel_pairing_zero {N : ℕ} (k : Fin N → RealLineL2) (q : ℝ)
    {v : ℝ → EuclideanSpace ℂ (Fin (N + 1))} (hv : Measurable v)
    (hnorm : ∀ ω, ‖v ω‖ = 1)
    (hker : ∀ ω j, ∑ l : Fin (N + 1), frequencyMatrix k q ω j l * v ω l = 0)
    (j : Fin N) {w : ℝ → ℂ} (hw : Measurable w) (hwbound : ∀ t, ‖w t‖ ≤ 1)
    (hperiod : ∀ ω (l : Fin (N + 1)), w (ω + (l : ℕ) * q) = w ω) :
    ∫ t, (w t * conj ((Lp.fourierTransformₗᵢ ℝ ℂ (k j) : ℝ → ℂ) t)) *
      finiteBand q v t = 0 :=
  finiteBand_periodic_pairing_zero q hv hnorm (Lp.memLp _) hw hwbound hperiod
    (fun ω _ => hker ω j)

end Singularity
