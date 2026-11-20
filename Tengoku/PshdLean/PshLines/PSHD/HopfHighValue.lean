import Tengoku.PshdLean.PshLines.PSHD.Hopf
import Tengoku.PshdLean.PshLines.PSHD.HighValueCircle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Compact high-value fibers of the Hopf map

The nonempty compact sections used in the selection step of `pshd-vibe`,
Lemma 1.3. Only subharmonicity on the specified affine line is assumed.
-/

open Set Metric

namespace PshLines.PSHD

/-- The high-value section of a Hopf fiber is the continuous image of the
high-value part of the parameter circle.
@isnad1 id=eq.0h5v.s9.ed5db506f0bd from=translated src=- shape=6125a8e9 vocab=1f8746a0
-/
theorem highValue_hopf_fiber_eq_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : E → ℝ) (x : E) (r : ℝ) (e : sphere (0 : E) 1) :
    {f : sphere (0 : E) 1 | hopf f = hopf e ∧
      u x ≤ u (x + (r : ℂ) • (f : E))} =
    phaseOrbit e '' {a : sphere (0 : ℂ) 1 |
      u x ≤ u (x + (a : ℂ) • ((r : ℂ) • (e : E)))} := by
  ext f
  constructor
  · rintro ⟨hf, hval⟩
    obtain ⟨a, rfl⟩ := (hopf_fiber_eq_range e ▸ hf : f ∈ range (phaseOrbit e))
    refine ⟨a, ?_, rfl⟩
    simpa only [Set.mem_ofPred_eq, phaseOrbit, smul_smul, mul_comm] using hval
  · rintro ⟨a, hval, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (hopf_eq_iff _ _).mpr ⟨a, by simp, rfl⟩
    · simpa only [Set.mem_ofPred_eq, phaseOrbit, smul_smul, mul_comm] using hval

/-- Every admissible affine line yields a nonempty compact high-value Hopf fiber.
The scalar radius is absorbed into the line direction in the planar hypothesis.
@isnad1 id=and.3h6v.s9.90f8cb52d73c from=translated src=- shape=19f417d4 vocab=ca40d521
-/
theorem nonempty_isCompact_highValue_hopf_fiber
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → ℝ} {x : E} {r : ℝ} (e : sphere (0 : E) 1) {U : Set ℂ}
    (hu : DiscPshOn
      (fun z => (u (x + z • ((r : ℂ) • (e : E))) : EReal)) U)
    (hU : IsOpen U) (hD : closedBall (0 : ℂ) 1 ⊆ U) :
    {f : sphere (0 : E) 1 | hopf f = hopf e ∧
      u x ≤ u (x + (r : ℂ) • (f : E))}.Nonempty ∧
    IsCompact {f : sphere (0 : E) 1 | hopf f = hopf e ∧
      u x ≤ u (x + (r : ℂ) • (f : E))} := by
  obtain ⟨hne, hcomp⟩ :=
    nonempty_isCompact_highValue_sphere hu hU (by norm_num : (0 : ℝ) < 1) hD
  simp only [zero_smul, add_zero] at hne hcomp
  have hpre : IsCompact {a : sphere (0 : ℂ) 1 |
      u x ≤ u (x + (a : ℂ) • ((r : ℂ) • (e : E)))} := by
    simpa only [preimage_ofPred_eq, Subtype.coe_prop, true_and] using
      hcomp.preimage_continuous
        (continuous_subtype_val : Continuous (Subtype.val : sphere (0 : ℂ) 1 → ℂ))
  have hne' : {a : sphere (0 : ℂ) 1 |
      u x ≤ u (x + (a : ℂ) • ((r : ℂ) • (e : E)))}.Nonempty := by
    obtain ⟨a, ha, hval⟩ := hne
    exact ⟨⟨a, ha⟩, hval⟩
  rw [highValue_hopf_fiber_eq_image]
  exact ⟨hne'.image _, hpre.image (continuous_phaseOrbit e)⟩

end PshLines.PSHD
