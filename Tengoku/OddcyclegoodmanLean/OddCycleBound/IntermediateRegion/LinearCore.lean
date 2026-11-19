import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.LinearBranch
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

end AdmissibleParams

/--
@isnad1 id=le.1h1v.s6.1d63f1c199a0 from=translated src=- shape=315c0117 vocab=848325a4
-/
theorem log_lower_bound {v : ℝ} (hv : 0 ≤ v) : 2 * v / (v + 2) ≤ Real.log (1 + v) := by
  have hHD : ∀ x : ℝ, 0 ≤ x →
      HasDerivAt (fun t => Real.log (1 + t) - 2 * t / (t + 2))
        (1 / (1 + x) - (2 * (x + 2) - 2 * x * 1) / (x + 2) ^ 2) x := by
    intro x hx
    have h1x : (1 : ℝ) + x ≠ 0 := by positivity
    have h2x : x + 2 ≠ 0 := by positivity
    have hlog : HasDerivAt (fun t => Real.log (1 + t)) (1 / (1 + x)) x := by
      have := ((hasDerivAt_id x).const_add (1 : ℝ)).log h1x
      simpa [one_div] using this
    have hnum : HasDerivAt (fun t => 2 * t) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    have hden : HasDerivAt (fun t => t + 2) 1 x := (hasDerivAt_id x).add_const 2
    have hfrac : HasDerivAt (fun t => 2 * t / (t + 2))
        ((2 * (x + 2) - 2 * x * 1) / (x + 2) ^ 2) x := hnum.div hden h2x
    exact hlog.sub hfrac
  have hcont : ContinuousOn (fun t => Real.log (1 + t) - 2 * t / (t + 2)) (Set.Ici 0) :=
    fun x hx => (hHD x hx).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (fun t => Real.log (1 + t) - 2 * t / (t + 2)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      exact (hHD x hx.le).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [(hHD x hx.le).deriv]
      have h1x : (0 : ℝ) < 1 + x := by linarith
      have h2x : (0 : ℝ) < x + 2 := by linarith
      have hcombine : 1 / (1 + x) - (2 * (x + 2) - 2 * x * 1) / (x + 2) ^ 2
          = x ^ 2 / ((1 + x) * (x + 2) ^ 2) := by
        field_simp; ring
      rw [hcombine]; positivity
  have h := hmono Set.self_mem_Ici (Set.mem_Ici.mpr hv) hv
  simp only [Real.log_one, add_zero, mul_zero, zero_div, sub_zero] at h
  linarith

namespace AdmissibleParams

variable (P : AdmissibleParams)

/--
@isnad1 id=lt.0h1v.s5.1c028bb81d90 from=translated src=- shape=cfaf030c vocab=bcd5b355
-/
theorem alpha_lower : 1 / (2 + P.chartV) < P.alpha := by
  have hv2 : (0 : ℝ) < 2 + P.chartV := by linarith [P.chartV_pos]
  have hpα : P.p = (1 + P.chartV) * P.alpha := by
    have h1 : P.chartSigma * P.alpha = P.p := by
      have hα := P.alpha_pos.ne'; unfold chartSigma; field_simp
    rw [P.chartSigma_eq_one_add] at h1; linarith [h1]
  have hq : P.q = 1 - P.p := by unfold p; ring
  rw [div_lt_iff₀ hv2]
  nlinarith [P.alpha_gt_q, hpα, hq]

/--
@isnad1 id=lt.0h1v.s5.57f2336b88e0 from=translated src=- shape=dd5046c9 vocab=45435ee7
-/
theorem cxi_crude : 1 / Real.sqrt (2 * (2 + P.chartV)) < P.chartCxi := by
  have hv2 : (0 : ℝ) < 2 + P.chartV := by linarith [P.chartV_pos]
  have hs : 0 < Real.sqrt (2 * (2 + P.chartV)) := Real.sqrt_pos.2 (by positivity)
  have hden2 : (0 : ℝ) < 2 + 4 * P.xi := by linarith [P.xi_pos]
  have hφpos : (0 : ℝ) < (1 + 4 * P.xi) / (2 + 4 * P.xi) :=
    div_pos (by linarith [P.xi_pos]) hden2
  have hφ : 1 / 2 < (1 + 4 * P.xi) / (2 + 4 * P.xi) := by
    rw [lt_div_iff₀ hden2]; linarith [P.xi_pos]
  have hαprod : 1 < P.alpha * (2 + P.chartV) := by
    have := P.alpha_lower; rw [div_lt_iff₀ hv2] at this; linarith [this]
  have hsqrt1 : 1 < Real.sqrt (P.alpha * (2 + P.chartV)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt (by norm_num) hαprod
  rw [div_lt_iff₀ hs]
  have hprod : P.chartCxi * Real.sqrt (2 * (2 + P.chartV))
      = 2 * Real.sqrt (P.alpha * (2 + P.chartV)) * ((1 + 4 * P.xi) / (2 + 4 * P.xi)) := by
    have hcomb : Real.sqrt (2 * P.alpha) * Real.sqrt (2 * (2 + P.chartV))
        = 2 * Real.sqrt (P.alpha * (2 + P.chartV)) := by
      rw [← Real.sqrt_mul (by have := P.alpha_pos; positivity),
        show 2 * P.alpha * (2 * (2 + P.chartV)) = 4 * (P.alpha * (2 + P.chartV)) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
        show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    unfold chartCxi
    rw [show Real.sqrt (2 * P.alpha) * (1 + 4 * P.xi) / (2 + 4 * P.xi) * Real.sqrt (2 * (2 + P.chartV))
        = (Real.sqrt (2 * P.alpha) * Real.sqrt (2 * (2 + P.chartV))) * ((1 + 4 * P.xi) / (2 + 4 * P.xi)) by
      ring, hcomb]
  rw [hprod]
  nlinarith [hsqrt1, hφ, mul_pos (sub_pos.mpr hsqrt1) hφpos]

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
