import Tengoku.OpenaiMath.OAI.Geometry.QuadricBundles.DualForms

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample
open Matrix Complex Filter Topology BigOperators Set Metric MeasureTheory
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
lemma norm_matrix_pair_le {n : Type u1} [Fintype n]
    (H : Matrix n n ℂ) (v w : n → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ i j, ‖H i j‖ ≤ C) :
    ‖star v ⬝ᵥ H *ᵥ w‖ ≤ (Fintype.card n : ℝ)^2 * C * ‖v‖ * ‖w‖ := by
  change ‖∑ i, star (v i) * ∑ j, H i j * w j‖ ≤ _
  simp_rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i, ∑ j, ‖star (v i) * (H i j * w j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _i : n, ∑ _j : n, ‖v‖ * (C * ‖w‖) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      rw [norm_mul, norm_star, norm_mul]
      exact mul_le_mul (norm_le_pi_norm v i)
        (mul_le_mul (hb i j) (norm_le_pi_norm w j) (norm_nonneg _) hC)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by simp [pow_two]; ring

lemma quadraticValue_sub_bound {n : Type u2} [Fintype n]
    (H : Matrix n n ℂ) (v w : n → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ i j, ‖H i j‖ ≤ C) :
    |quadraticValue H v - quadraticValue H w| ≤
      (Fintype.card n : ℝ)^2 * C * ‖v-w‖ * (‖v‖+‖w‖) := by
  have he : star v ⬝ᵥ H *ᵥ v - star w ⬝ᵥ H *ᵥ w =
      star (v-w) ⬝ᵥ H *ᵥ v + star w ⬝ᵥ H *ᵥ (v-w) := by
    simp only [star_sub, sub_dotProduct, Matrix.mulVec_sub, dotProduct_sub]
    ring
  calc
    _ = |(star v ⬝ᵥ H *ᵥ v - star w ⬝ᵥ H *ᵥ w).re| := by
      simp [quadraticValue]
    _ ≤ ‖star v ⬝ᵥ H *ᵥ v - star w ⬝ᵥ H *ᵥ w‖ := Complex.abs_re_le_norm _
    _ ≤ ‖star (v-w) ⬝ᵥ H *ᵥ v‖ + ‖star w ⬝ᵥ H *ᵥ (v-w)‖ := by
      rw [he]; exact norm_add_le _ _
    _ ≤ (Fintype.card n : ℝ)^2 * C * ‖v-w‖ * ‖v‖ +
        (Fintype.card n : ℝ)^2 * C * ‖w‖ * ‖v-w‖ :=
      add_le_add (norm_matrix_pair_le H _ _ hC hb) (norm_matrix_pair_le H _ _ hC hb)
    _ = _ := by ring

theorem quadraticValue_moving_vector {n : Type u3} [Fintype n]
    (H : ℕ → Matrix n n ℂ) {v : ℕ → n → ℂ} {w : n → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ k i j, ‖H k i j‖ ≤ C)
    (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun k ↦ quadraticValue (H k) (v k) - quadraticValue (H k) w)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun k ↦ (Fintype.card n : ℝ)^2 * C * ‖v k-w‖ * (‖v k‖+‖w‖))
      atTop (𝓝 0) := by
    have hs : Tendsto (fun k ↦ ‖v k-w‖) atTop (𝓝 ‖w-w‖) :=
      (hv.sub tendsto_const_nhds).norm
    have hh : Tendsto (fun k ↦ (Fintype.card n : ℝ)^2 * C * ‖v k-w‖ * (‖v k‖+‖w‖))
        atTop (𝓝 ((Fintype.card n : ℝ)^2 * C * ‖w-w‖ * (‖w‖+‖w‖))) :=
      (tendsto_const_nhds.mul hs).mul (hv.norm.add tendsto_const_nhds)
    simpa using hh
  apply squeeze_zero_norm
    (fun k ↦ by simpa only [Real.norm_eq_abs] using
      quadraticValue_sub_bound (H k) (v k) w hC (hb k)) ht

lemma nonnegative_usc_integrableOn_ball {Ω : Set (ℂ × ℂ)} {q : ℂ × ℂ → ℝ}
    (hq : UpperSemicontinuousOn q Ω) (hpos : ∀ x ∈ Ω, 0 ≤ q x)
    {x : ℂ × ℂ} {r : ℝ} (hb : closedBall x r ⊆ Ω) :
    IntegrableOn q (ball x r) := by
  obtain ⟨C,hC⟩ := (hq.mono hb).bddAbove_of_isCompact (isCompact_closedBall x r)
  have hmeas : AEStronglyMeasurable q (volume.restrict (ball x r)) :=
    (aemeasurable_restrict_of_measurable_subtype measurableSet_ball
      (upperSemicontinuousOn_iff_restrict.mpr
        (hq.mono (ball_subset_closedBall.trans hb))).measurable).aestronglyMeasurable
  exact (integrableOn_const (C := C)
      (measure_ne_top_of_subset ball_subset_closedBall
        (isCompact_closedBall x r).measure_ne_top)).mono' hmeas
    ((ae_restrict_mem measurableSet_ball).mono fun y hy ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos y (hb (ball_subset_closedBall hy)))]
      exact hC (mem_image_of_mem _ (ball_subset_closedBall hy)))

local instance : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)

theorem moving_points_force_nonzero_limit
    {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {u : ℕ → (ℂ × ℂ) → ℝ} {q : (ℂ × ℂ) → ℝ}
    (hu : ∀ k, DiskPshOn Ω (u k)) (hpos : ∀ k x, x ∈ Ω → 0 ≤ u k x)
    {xm : ℕ → ℂ × ℂ} {x : ℂ × ℂ} {r : ℝ} (hr : 0 < r)
    (hb : closedBall x (3*r) ⊆ Ω)
    (hx : Tendsto xm atTop (𝓝 x))
    (hn : Tendsto (fun k ↦ u k (xm k)) atTop (𝓝 1))
    (hl : Tendsto (fun k ↦ ⨍ y in ball x (2*r), u k y) atTop
      (𝓝 (⨍ y in ball x (2*r), q y))) :
    ∃ y ∈ ball x (2*r), q y ≠ 0 := by
  have hb2 : closedBall x (2*r) ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith)).trans hb
  have hv (c : ℂ × ℂ) {s : ℝ} (hs : 0 < s) : 0 < (volume (ball c s)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume c hs))
      (measure_ne_top_of_subset ball_subset_closedBall (isCompact_closedBall c s).measure_ne_top)
  have hV := hv x (show 0 < 2*r by positivity)
  have hW := hv (0 : ℂ × ℂ) hr
  let a : ℝ := (volume (ball x (2*r))).toReal⁻¹ *
    ((volume (ball (0 : ℂ × ℂ) r)).toReal * (1/2))
  apply nonzero_of_average_limit measurableSet_ball (a := a)
    (mul_pos (inv_pos.mpr hV) (mul_pos hW (by norm_num))) hl
  have hxe : ∀ᶠ k in atTop, dist (xm k) x < r :=
    hx.eventually (ball_mem_nhds x hr)
  have hne : ∀ᶠ k in atTop, (1/2 : ℝ) ≤ u k (xm k) :=
    ((tendsto_order.mp hn).1 (1/2) (by norm_num)).mono fun _ h ↦ h.le
  filter_upwards [hxe,hne] with k hk hn'
  have hi := nonnegative_usc_integrableOn_ball (hu k).1 (hpos k) hb2
  have hm := (hu k).moving_base_mass hΩ hr hk hb
    (fun y hy ↦ hpos k y (hb2 (ball_subset_closedBall hy))) hi hn'
  simpa [a, setAverage_eq, smul_eq_mul, measureReal_def] using
    mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hV.le)

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

namespace ExtractedTrace
variable {D : EqualizerData} {ex : ℕ → ℕ} {P : ∀ k, TwistedPshForm D (ex k)}
    (X : ExtractedTrace ex P)

end ExtractedTrace
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

def ExtractedTrace.pshDualForm {D : EqualizerData} {ex : ℕ → ℕ}
    {P : ∀ k, TwistedPshForm D (ex k)} (X : ExtractedTrace ex P)
    (hex : Tendsto ex atTop atTop) : D.PshDualForm where
  value := X.globalValue
  quadratic i z := ⟨X.globalMatrix i z,X.globalMatrix_positive i z,fun _ ↦ rfl⟩
  psh := X.globalValue_psh
  compatible i j _ hz v := X.globalValue_change hex i j hz v

end
end QuadricCounterexample

end

end OAI
