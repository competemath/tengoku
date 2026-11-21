import Tengoku.PshdLean.PshLines.PSHD.ProjectiveTopology
import Tengoku.PshdLean.PshLines.PSHD.HopfHighValue
import Tengoku.PshdLean.PshLines.PSHD.HighValueRelation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Projective high-value sections

The Borel relation and its nonempty compact sections in `pshd-vibe`, Lemma 1.3,
on the actual complex projectivization with its Hopf quotient topology.
-/

open Set Metric

namespace PshLines.PSHD

/-- The article's projective high-value relation is Borel.
@isnad1 id=measurab.1h5v.s9.50a22a4b4c86 from=translated src=- shape=b7618daf vocab=c226870f
-/
theorem measurableSet_projective_highValue_relation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {u : E → ℝ} (hu : Measurable u) (x : E) (R A : ℝ) :
    MeasurableSet {p : (ℝ × Projectivization ℂ E) × sphere (0 : E) 1 |
      p.1.1 ∈ Icc (R / 2) R ∧ hopf p.2 = p.1.2 ∧
        A ≤ u (x + (p.1.1 : ℂ) • (p.2 : E))} :=
  measurableSet_highValue_relation continuous_hopf hu x R A

/-- Every projective direction has a nonempty compact high-value section on an
admissible sphere, assuming the planar disc criterion on affine line pullbacks.
@isnad1 id=and.4h6v.s9.e266353185e9 from=translated src=- shape=dfe9e5ec vocab=b1fbef86
-/
theorem nonempty_isCompact_projective_highValue_section
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → ℝ} {D : Set E} (hD : IsOpen D) {x : E}
    (hu : ∀ v : E, v ≠ 0 →
      DiscPshOn (fun z => (u (x + z • v) : EReal))
        ((fun z : ℂ => x + z • v) ⁻¹' D))
    {r : ℝ} (hr : 0 < r) (hball : closedBall x r ⊆ D)
    (ξ : Projectivization ℂ E) :
    {f : sphere (0 : E) 1 | hopf f = ξ ∧
      u x ≤ u (x + (r : ℂ) • (f : E))}.Nonempty ∧
    IsCompact {f : sphere (0 : E) 1 | hopf f = ξ ∧
      u x ≤ u (x + (r : ℂ) • (f : E))} := by
  obtain ⟨e, rfl⟩ := hopf_surjective ξ
  have hv : (r : ℂ) • (e : E) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    simpa [norm_smul, abs_of_pos hr] using hr.ne'
  apply nonempty_isCompact_highValue_hopf_fiber e (hu _ hv)
  · exact hD.preimage (continuous_const.add (continuous_id.smul continuous_const))
  · intro z hz
    apply hball
    have hz' : ‖z‖ ≤ 1 := by simpa using hz
    have hmul : ‖z‖ * r ≤ r := by nlinarith
    simpa [mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos hr] using hmul

end PshLines.PSHD
