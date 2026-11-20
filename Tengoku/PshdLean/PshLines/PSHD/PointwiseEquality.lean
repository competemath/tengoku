import Tengoku.PshdLean.PshLines.PSHD.BallUpperSemicontinuity
import Tengoku.PshdLean.PshLines.LocalPshDiscControl

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Pointwise recovery of a plurisubharmonic representative

Step 4 of Proposition 2.1 of `pshd-vibe`. Let `u` be a Borel function which is
locally bounded above and subharmonic on every affine complex-line section of
an open set, and let `v` be plurisubharmonic there with `u = v` almost
everywhere. Then `u = v` at every point: each function is recovered at a point
from its own means over small balls centered there, and these means agree.
-/

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]

/-- An almost-everywhere upper bound by an upper semicontinuous function is a
pointwise upper bound for a Borel function which is locally bounded above and
subharmonic on line sections.
@isnad1 id=le.7h6v.s7.0b94eeccd278 from=translated src=- shape=39de5c17 vocab=eb733259
-/
theorem LineSubharmonicOn.coe_le_of_ae_le {u : E → ℝ} {v : E → EReal} {D : Set E}
    (hD : IsOpen D) (hl : LineSubharmonicOn u D) (hu : Measurable u)
    (hbdd : ∀ p ∈ D, ∃ r > 0, BddAbove (u '' ball p r))
    (hv : UpperSemicontinuousOn v D) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hae : ∀ᵐ y ∂μ.restrict D, (u y : EReal) ≤ v y) :
    ∀ x ∈ D, (u x : EReal) ≤ v x := by
  intro x hx
  by_contra hle
  have hlt : v x < u x := lt_of_not_ge hle
  obtain ⟨q, hvq, hqu⟩ := EReal.exists_rat_btwn_of_lt hlt
  have hqu' : (q : ℝ) < u x := EReal.coe_lt_coe_iff.mp hqu
  have hvc : ∀ᶠ y in 𝓝 x, v y < ((q : ℝ) : EReal) := by
    have h := hv x hx _ hvq
    rwa [nhdsWithin_eq_nhds.mpr (hD.mem_nhds hx)] at h
  obtain ⟨r₁, hr₁, C, hC⟩ := hbdd x hx
  have hnbhd : {y | y ∈ D ∧ v y < ((q : ℝ) : EReal) ∧ y ∈ ball x r₁} ∈ 𝓝 x := by
    filter_upwards [hD.mem_nhds hx, hvc, ball_mem_nhds x hr₁] with y hyD hyv hyB
    exact ⟨hyD, hyv, hyB⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnbhd
  have hBD : ball x ε ⊆ D := fun y hy => (hεsub hy).1
  have hCb : ∀ y ∈ ball x ε, u y ≤ C := fun y hy => hC ⟨y, (hεsub hy).2.2, rfl⟩
  have huq : ∀ᵐ y ∂μ.restrict (ball x ε), u y ≤ q := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hBD hae,
      ae_restrict_mem measurableSet_ball] with y hy hyB
    exact EReal.coe_le_coe_iff.mp (hy.trans (hεsub hyB).2.1.le)
  have hlower : ENNReal.ofReal (C - q) * μ (ball 0 ε) ≤
      ∫⁻ y in ball x ε, ENNReal.ofReal (C - u y) ∂μ := by
    calc
      _ = ∫⁻ _y in ball x ε, ENNReal.ofReal (C - q) ∂μ := by
        simp [lintegral_const, μ.addHaar_ball_center x ε]
      _ ≤ _ := lintegral_mono_ae (huq.mono fun y hy => ENNReal.ofReal_le_ofReal (by linarith))
  have hupper := hl.ball_deficit_le hu μ x ε C hBD hCb
  rw [mul_comm (μ (ball 0 ε))] at hupper
  have hdeficit : ENNReal.ofReal (C - q) ≤ ENNReal.ofReal (C - u x) :=
    (ENNReal.mul_le_mul_iff_left (ne_of_gt (Metric.measure_ball_pos μ (0 : E) hε))
      measure_ball_ne_top).mp (hlower.trans hupper)
  have hxC : u x ≤ C := hCb x (mem_ball_self hε)
  have hreal := (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hxC)).mp hdeficit
  linarith

/-- An almost-everywhere upper bound by a Borel function which is subharmonic on
line sections is a pointwise upper bound for a plurisubharmonic function.
@isnad1 id=le.7h6v.s7.edc4be427e56 from=translated src=- shape=f2baccae vocab=f19a34bd
-/
theorem LineSubharmonicOn.le_coe_of_plurisubharmonicOn_of_ae_le {u : E → ℝ} {v : E → EReal}
    {D : Set E} (hD : IsOpen D) (hl : LineSubharmonicOn u D) (hu : Measurable u)
    (hbdd : ∀ p ∈ D, ∃ r > 0, BddAbove (u '' ball p r))
    (hv : PlurisubharmonicOn v D) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hae : ∀ᵐ y ∂μ.restrict D, v y ≤ (u y : EReal)) :
    ∀ x ∈ D, v x ≤ (u x : EReal) := by
  intro x hx
  by_contra hle
  have hlt : (u x : EReal) < v x := lt_of_not_ge hle
  obtain ⟨U, hU, hxU, hdisc⟩ := hv x hx
  have hw : ((v x).toReal : EReal) = v x :=
    EReal.coe_toReal (hdisc.ne_top x hxU) (ne_bot_of_gt hlt)
  have huw : u x < (v x).toReal := EReal.coe_lt_coe_iff.mp (hw.symm ▸ hlt)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp (hU.inter hD) x ⟨hxU, hx⟩
  obtain ⟨r₁, hr₁, C₁, hC₁⟩ := hbdd x hx
  set ρ' := min (ρ / 2) r₁ with hρ'
  have hρ'pos : 0 < ρ' := lt_min (half_pos hρ) hr₁
  have hclosed : closedBall x ρ' ⊆ U ∩ D :=
    (closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hρ))).trans hρsub
  obtain ⟨C₂, hC₂⟩ := hdisc.exists_compact_upper_bound (isCompact_closedBall x ρ')
    ⟨x, mem_closedBall_self hρ'pos.le⟩ (fun y hy => (hclosed hy).1)
  set C := max (max C₁ C₂) (v x).toReal with hCdef
  have hwC : (v x).toReal ≤ C := le_max_right _ _
  have ht : ENNReal.ofReal (C - (v x).toReal) < ENNReal.ofReal (C - u x) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  obtain ⟨r, ⟨hr, hrρ⟩, hgt⟩ := hl.exists_ball_deficit_gt hD hu μ hx C ht hρ'pos
  have hBsub : ball x r ⊆ closedBall x ρ' :=
    ball_subset_ball hrρ |>.trans ball_subset_closedBall
  have hmono : ∫⁻ y in ball x r, ENNReal.ofReal (C - u y) ∂μ ≤
      ∫⁻ y in ball x r, ((C : EReal) - v y).toENNReal ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (fun y hy => (hclosed (hBsub hy)).2) hae] with y hy
    rw [← EReal.real_coe_toENNReal, EReal.coe_sub]
    exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hy)
  have hupper := hdisc.ball_deficit_le μ x r C (fun y hy => (hclosed (hBsub hy)).1)
    (fun y hy => (hC₂ y (hBsub hy)).trans
      (EReal.coe_le_coe_iff.mpr ((le_max_right _ _).trans (le_max_left _ _))))
  have hcenter : ((C : EReal) - v x).toENNReal = ENNReal.ofReal (C - (v x).toReal) := by
    rw [← hw, ← EReal.coe_sub, EReal.real_coe_toENNReal, EReal.toReal_coe]
  rw [hcenter] at hupper
  exact lt_irrefl _ (hgt.trans_le (hmono.trans hupper))

/-- **Pointwise recovery of the representative** (Step 4 of Proposition 2.1).
A Borel function which is locally bounded above and subharmonic on every
connected component of every affine complex-line section of an open set agrees
at every point with any plurisubharmonic function equal to it almost
everywhere.
@isnad1 id=eq.7h6v.s7.c44875dde872 from=translated src=- shape=aca94369 vocab=08fbc333
-/
theorem LineSubharmonicOn.eqOn_of_ae_eq {u : E → ℝ} {v : E → EReal} {D : Set E}
    (hD : IsOpen D) (hl : LineSubharmonicOn u D) (hu : Measurable u)
    (hbdd : ∀ p ∈ D, ∃ r > 0, BddAbove (u '' ball p r))
    (hv : PlurisubharmonicOn v D) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hae : ∀ᵐ y ∂μ.restrict D, (u y : EReal) = v y) :
    ∀ x ∈ D, (u x : EReal) = v x := fun x hx =>
  le_antisymm
    (hl.coe_le_of_ae_le hD hu hbdd (PlurisubharmonicOn.upperSemicontinuousOn hv) μ
      (hae.mono fun _ h => h.le) x hx)
    (hl.le_coe_of_plurisubharmonicOn_of_ae_le hD hu hbdd hv μ (hae.mono fun _ h => h.ge) x hx)

end PshLines.PSHD
