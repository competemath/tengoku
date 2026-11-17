import Tengoku.Seed.Probability.Independence.ZeroOne
import Tengoku.Seed.Probability.Independence.InfinitePi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Zero–one law for almost shift-invariant events

A measurable event in an independent sequence that is unchanged almost surely
by every finite shift has probability zero or one. Taking the limsup of its
shifted copies produces a genuine tail-measurable representative.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace

namespace Singularity

/-- A shifted measurable event uses only coordinates at or beyond the shift.
@isnad1 id=measurab.2h4v.s7.8461f309cffe from=translated src=- shape=60e825ba vocab=30988cee
-/
theorem shifted_event_measurable {S : Type*} [MeasurableSpace S]
    {E : Set (ℕ → S)} (hE : MeasurableSet E) (k n : ℕ) (hkn : k ≤ n) :
    MeasurableSet[⨆ i ≥ k, MeasurableSpace.comap (fun ω : ℕ → S => ω i)
      inferInstance] ((fun (ω : ℕ → S) i => ω (i + n)) ⁻¹' E) := by
  apply hE.preimage
  apply (@measurable_pi_iff (ℕ → S) ℕ (fun _ => S)
    (⨆ i ≥ k, MeasurableSpace.comap (fun ω : ℕ → S => ω i) inferInstance) _).mpr
  intro i
  apply Measurable.of_comap_le
  exact le_iSup_of_le (i + n) (le_iSup_of_le (by omega : k ≤ i + n) le_rfl)

/-- Limsup of shifted copies belongs to the coordinate tail sigma algebra.
@isnad1 id=measurab.1h2v.s6.28a6a0b7b275 from=translated src=- shape=ad370b57 vocab=f2d25e3d
-/
theorem shifted_event_limsup_tail {S : Type*} [MeasurableSpace S]
    {E : Set (ℕ → S)} (hE : MeasurableSet E) :
    MeasurableSet[limsup (fun i => MeasurableSpace.comap
      (fun ω : ℕ → S => ω i) inferInstance) atTop]
      (limsup (fun n => (fun (ω : ℕ → S) i => ω (i + n)) ⁻¹' E) atTop) := by
  rw [limsup_eq_iInf_iSup_of_nat]
  apply measurableSet_iInf.mpr
  intro k
  rw [← limsup_nat_add (fun n => (fun (ω : ℕ → S) i => ω (i + n)) ⁻¹' E) k]
  exact @MeasurableSet.measurableSet_limsup (ℕ → S)
    (⨆ i ≥ k, MeasurableSpace.comap (fun ω : ℕ → S => ω i) inferInstance) _ (fun n => shifted_event_measurable hE k (n+k) (by omega))

end Singularity
