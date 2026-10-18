import Tengoku.OpenaiMath.OAI.Analysis.Fourier.HeightLayers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Deduction of the L log L theorem from a good set estimate -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace OAI

namespace FourierLLogL

def symmetricMaximal (f : Torus → ℂ) (x : Torus) : ℝ≥0∞ :=
  ⨆ N : ℕ, ENNReal.ofReal ‖symmetricPartialSum f N x‖

theorem measurable_symmetricMaximal (f : Torus → ℂ) : Measurable (symmetricMaximal f) :=
  Measurable.iSup (fun N => (measurable_symmetricPartialSum f N).norm.ennreal_ofReal)

theorem symmetricMaximal_mul (f : Torus → ℂ) (c : ℂ) (x : Torus) :
    symmetricMaximal (fun y => c * f y) x = ENNReal.ofReal ‖c‖ * symmetricMaximal f x := by
  simp only [symmetricMaximal, symmetricPartialSum_const_mul, norm_mul,
    ENNReal.ofReal_mul (norm_nonneg c), ENNReal.mul_iSup]

/-- Good-set estimate. We state it at exponential heights exp d with d = 2^j. -/
def GoodBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ j : ℕ in atTop, ∀ (f : Torus → ℂ),
    Integrable f circleMeasure → (∫ x, ‖f x‖ ∂circleMeasure) ≤ 1 →
    (∀ᵐ x ∂circleMeasure, ‖f x‖ ≤ Real.exp ((2 : ℝ)^j)) →
    ∃ G : Set Torus, MeasurableSet G ∧
      circleMeasure Gᶜ ≤ ENNReal.ofReal (C / ((j:ℝ) + 1)^2) ∧
      (∫⁻ x in G, symmetricMaximal f x ∂circleMeasure) ≤ ENNReal.ofReal (C * (2:ℝ)^j)

/-- Trigonometric polynomials, as a subspace of continuous functions. -/
def trigPolys : Submodule ℂ C(Torus, ℂ) := Submodule.span ℂ (Set.range fourier)

lemma integrable_continuous {f : Torus → ℂ} (hf : Continuous f) :
    Integrable f circleMeasure := by
  apply hf.integrable_of_hasCompactSupport
  exact IsClosed.isCompact (isClosed_tsupport f)

lemma exists_bounded_trigPoly_approx (f : Torus → ℂ)
    (hf : Integrable f circleMeasure)
    (B : ℝ) (hB : 0 < B) (hb : ∀ᵐ x ∂circleMeasure, ‖f x‖ ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : C(Torus, ℂ), p ∈ trigPolys ∧
      (∫ x, ‖f x - p x‖ ∂circleMeasure) ≤ ε ∧ ∀ x, ‖p x‖ ≤ B + 1 := by
  obtain ⟨g, hg, hgi⟩ :=
    hf.exists_boundedContinuous_integral_sub_le (show 0 < ε/4 by linarith)
  let k (x : Torus) : ℂ := (B / max B ‖g x‖) • g x
  have hk : Continuous k := by
    have h1 : Continuous fun x => max B ‖g x‖ := continuous_const.max g.continuous.norm
    exact (continuous_const.div h1 (fun x => ne_of_gt (lt_max_of_lt_left hB))).smul g.continuous
  let k' : C(Torus, ℂ) := ⟨k, hk⟩
  have hkB (x : Torus) : ‖k x‖ ≤ B := by
    have hm : 0 < max B ‖g x‖ := lt_max_of_lt_left hB
    simp only [k, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hB hm)]
    exact (mul_le_mul_of_nonneg_left (le_max_right B ‖g x‖) (div_pos hB hm).le).trans
      (div_mul_cancel₀ B hm.ne').le
  have hdk (x : Torus) (hx : ‖f x‖ ≤ B) : ‖f x - k x‖ ≤ 2 * ‖f x - g x‖ := by
    suffices H : ‖g x - k x‖ ≤ ‖f x - g x‖ by
      have hi := dist_triangle (f x) (g x) (k x)
      simp only [dist_eq_norm] at hi
      linarith
    rcases le_total ‖g x‖ B with hxg | hxg
    · simp [k, max_eq_left hxg, hB.ne']
    have hp : 0 < ‖g x‖ := hB.trans_le hxg
    have hxone : (0:ℝ) ≤ 1 - B/‖g x‖ := sub_nonneg.mpr ((div_le_one hp).mpr hxg)
    calc
      ‖g x - k x‖ = ‖((1:ℝ)-B/‖g x‖) • g x‖ := by
        rw [sub_smul, one_smul]; simp only [k, max_eq_right hxg]
      _ = ‖g x‖ - B := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hxone, sub_mul, one_mul,
          div_mul_cancel₀ B hp.ne']
      _ ≤ ‖g x‖ - ‖f x‖ := sub_le_sub_left hx _
      _ ≤ ‖f x - g x‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le _ _
  have hkc : k' ∈ closure (trigPolys : Set _) := by
    change k' ∈ trigPolys.topologicalClosure
    rw [trigPolys, span_fourier_closure_eq_top]; trivial
  obtain ⟨p, hps, hp⟩ := Metric.mem_closure_iff.mp hkc (min 1 (ε / 2)) (by positivity)
  have hp' (x : Torus) : ‖k x - p x‖ < min 1 (ε / 2) := by
    change ‖k' x - p x‖ < _
    rw [← dist_eq_norm]
    exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist _) hp
  refine ⟨p, hps, ?_, fun x => ?_⟩
  · calc
      _ ≤ ∫ x, (2 * ‖f x - g x‖ + (ε / 2)) ∂circleMeasure := by
        apply integral_mono_ae (hf.sub (integrable_continuous p.continuous)).norm
          (((hf.sub hgi).norm.const_mul _).add (integrable_const _))
        filter_upwards [hb] with x hx
        have h1 := dist_triangle (f x) (k x) (p x)
        simp only [dist_eq_norm] at h1
        exact h1.trans (add_le_add (hdk x hx)
          ((hp' x).le.trans (min_le_right _ _)))
      _ = 2 * (∫ x, ‖f x - g x‖ ∂circleMeasure) + (ε/2) := by
        rw [integral_add (show Integrable (fun x => 2 * ‖f x - g x‖) _ from ((hf.sub hgi).norm.const_mul _)) (integrable_const _),
          integral_const_mul]; simp
      _ ≤ ε := by linarith
  · have h1 := norm_sub_norm_le (p x) (k x)
    rw [norm_sub_rev] at h1
    have h2 := ((hp' x).le.trans (min_le_left _ _))
    linarith [hkB x]

private def pad (j : ℕ) : ℝ := ((1/4:ℝ))^j

end FourierLLogL

end OAI
