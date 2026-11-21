import Tengoku.PshdLean.PshLines.FirstPass.PshClosedDiscMaximum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # High values on every circle

The first step of Lemma 1.3 in `pshd-vibe`: a subharmonic function has
a value on each admissible circle at least as large as its central value.
-/

open Set Metric

namespace PshLines.PSHD

/-- Every admissible circle contains a point whose value is at least the
central value of a finite subharmonic function.
@isnad1 id=ex.4h4v.s6.c9a4d77ea08e from=translated src=- shape=1b32e580 vocab=b057d338
-/
theorem exists_highValue_sphere {u : ℂ → ℝ} {U : Set ℂ}
    (hu : DiscPshOn (fun z => (u z : EReal)) U) (hU : IsOpen U)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hD : closedBall c r ⊆ U) :
    ∃ z ∈ sphere c r, u c ≤ u z := by
  have hs : (sphere c r).Nonempty := by
    refine ⟨c + (r : ℂ), ?_⟩
    simp [abs_of_pos hr]
  obtain ⟨z, hz, hmax⟩ :=
    (hu.upperSemicontinuousOn.mono (sphere_subset_closedBall.trans hD)).exists_isMaxOn
      hs (isCompact_sphere c r)
  refine ⟨z, hz, ?_⟩
  exact EReal.coe_le_coe_iff.mp
    ((hu.plurisubharmonicOn hU).le_const_on_closedBall_of_le_on_sphere hr hD
      (fun w hw => hmax hw) c (mem_closedBall_self hr.le))

/-- The high-value portion of an admissible circle is compact.
@isnad1 id=iscompac.2h5v.s6.e0276e54f9ab from=translated src=- shape=25b370de vocab=0871a4a2
-/
theorem isCompact_highValue_sphere {u : ℂ → ℝ} {U : Set ℂ}
    (hu : DiscPshOn (fun z => (u z : EReal)) U)
    {c : ℂ} {r A : ℝ} (hD : sphere c r ⊆ U) :
    IsCompact {z ∈ sphere c r | A ≤ u z} := by
  obtain ⟨F, hF, heq⟩ := upperSemicontinuousOn_iff_preimage_Ici.mp
    (hu.upperSemicontinuousOn.mono hD) (A : EReal)
  have hset : {z ∈ sphere c r | A ≤ u z} = sphere c r ∩ F := by
    simpa only [Set.preimage, Set.mem_Ici, EReal.coe_le_coe_iff,
      Set.inter_ofPred_eq_sep] using heq
  rw [hset]
  exact (isCompact_sphere c r).inter_right hF

/-- The selection fibers in the planar circle parameter are nonempty compact sets.
@isnad1 id=and.4h4v.s7.87485e265b25 from=translated src=- shape=0ebfd241 vocab=198fe090
-/
theorem nonempty_isCompact_highValue_sphere {u : ℂ → ℝ} {U : Set ℂ}
    (hu : DiscPshOn (fun z => (u z : EReal)) U) (hU : IsOpen U)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hD : closedBall c r ⊆ U) :
    {z ∈ sphere c r | u c ≤ u z}.Nonempty ∧
      IsCompact {z ∈ sphere c r | u c ≤ u z} := by
  obtain ⟨z, hz, hval⟩ := exists_highValue_sphere hu hU hr hD
  exact ⟨⟨z, hz, hval⟩,
    isCompact_highValue_sphere hu (sphere_subset_closedBall.trans hD)⟩

/-- High values on an affine circle form a nonempty compact subset of the
ambient complex normed space.
@isnad1 id=and.4h6v.s8.30bd3eb7cbb4 from=translated src=- shape=c18608ab vocab=e839621f
-/
theorem nonempty_isCompact_highValue_affineCircle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → ℝ} {U : Set ℂ} {x v : E}
    (hu : DiscPshOn (fun z => (u (x + z • v) : EReal)) U) (hU : IsOpen U)
    {r : ℝ} (hr : 0 < r) (hD : closedBall (0 : ℂ) r ⊆ U) :
    {y | ∃ z ∈ sphere (0 : ℂ) r, y = x + z • v ∧ u x ≤ u y}.Nonempty ∧
      IsCompact {y | ∃ z ∈ sphere (0 : ℂ) r, y = x + z • v ∧ u x ≤ u y} := by
  obtain ⟨hne, hcomp⟩ := nonempty_isCompact_highValue_sphere hu hU hr hD
  simp only [zero_smul, add_zero] at hne hcomp
  have heq : {y | ∃ z ∈ sphere (0 : ℂ) r, y = x + z • v ∧ u x ≤ u y} =
      (fun z : ℂ => x + z • v) '' {z ∈ sphere (0 : ℂ) r | u x ≤ u (x + z • v)} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl, hval⟩
      exact ⟨z, ⟨hz, hval⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hval⟩, rfl⟩
      exact ⟨z, hz, rfl, hval⟩
  rw [heq]
  exact ⟨hne.image _, hcomp.image (continuous_const.add (continuous_id.smul continuous_const))⟩

end PshLines.PSHD
