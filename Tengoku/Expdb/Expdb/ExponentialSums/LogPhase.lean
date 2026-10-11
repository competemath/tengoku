module

public import Tengoku.Expdb.Expdb.ExponentialSums.PhaseFunctions
public import Tengoku

/-!
# The logarithmic phase

Reusable facts about the logarithmic model phase, including its derivatives, separation on
dyadic intervals, and the explicit main term of its oscillatory integral.
-/

@[expose] public section

open Filter Topology
open scoped ContDiff Expdb FourierTransform

noncomputable section

namespace Expdb

/-- The fixed logarithmic phase `u ↦ log u`, regarded as a variable family. -/
def logPhase : VariableFunction (VariableObject.fixed ℝ) ℝ :=
  fun _ ↦ Real.log

/-- The derivatives of `log` on the phase interval agree with the reference derivatives for
model exponent one. -/
theorem iteratedDerivWithin_log_eq_rpow_neg_one
    (p : ℕ) (u : phaseInterval) :
    iteratedDerivWithin (p + 1) Real.log phaseInterval u =
      iteratedDerivWithin p (modelPhase 1) phaseInterval u := by
  have hu_pos : 0 < (u : ℝ) := lt_of_lt_of_le zero_lt_one u.property.1
  rw [show modelPhase 1 = fun v : ℝ ↦ v ^ (-(1 : ℝ)) from rfl]
  have hunique : UniqueDiffOn ℝ phaseInterval :=
    uniqueDiffOn_Icc (by norm_num [phaseInterval])
  rw [iteratedDerivWithin_eq_iteratedDeriv hunique
      (Real.contDiffAt_log.2 hu_pos.ne') u.property,
    iteratedDerivWithin_eq_iteratedDeriv hunique
      (Real.contDiffAt_rpow_const_of_ne hu_pos.ne') u.property,
    iteratedDeriv_succ', Real.deriv_log']
  congr 1
  funext v
  exact (Real.rpow_neg_one v).symm

/-- The fixed logarithmic phase `u ↦ log u` is a model phase function, with model exponent
`σ = 1`. -/
theorem isModelPhaseFunction_log : IsModelPhaseFunction logPhase := by
  refine ⟨?_, 1, zero_lt_one, ?_⟩
  · intro i
    change ContDiffOn ℝ ∞ Real.log phaseInterval
    exact Real.contDiffOn_log.mono fun u hu ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1)
  · intro p u
    rw [VariableObject.IsInfinitesimal]
    simp only [modelPhaseError_apply, modelPhaseErrorAt, logPhase,
      iteratedDerivWithin_log_eq_rpow_neg_one, sub_self, norm_zero]
    exact tendsto_const_nhds

/-- On a dyadic interval, `log (n / N)` is `1 / (2 * N)`-separated. -/
theorem log_div_separated
    {N : ℝ} {a b : ℕ} (hN : 0 < N) (ha : N ≤ a) (hb : (b : ℝ) ≤ 2 * N) :
    IsSeparatedFamily (1 / (2 * N))
      (fun n : ↥(Finset.Icc a b) ↦ Real.log ((n : ℝ) / N)) := by
  have hordered (m n : ↥(Finset.Icc a b)) (hmn : (m : ℕ) < n) :
      1 / (2 * N) ≤ Real.log ((n : ℝ) / N) - Real.log ((m : ℝ) / N) := by
    have hm_mem := Finset.mem_Icc.mp m.property
    have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le hN (ha.trans (by exact_mod_cast hm_mem.1))
    have hnpos : 0 < (n : ℝ) := lt_trans hmpos (by exact_mod_cast hmn)
    have hlog : 1 - (m : ℝ) / n ≤ Real.log ((n : ℝ) / m) := by
      simpa [inv_div] using Real.one_sub_inv_le_log_of_pos (div_pos hnpos hmpos)
    have hdiff : 1 / (2 * N) ≤ 1 - (m : ℝ) / n := by
      have hgapNat : (m : ℕ) + 1 ≤ (n : ℕ) := Nat.add_one_le_iff.mpr hmn
      have hgapCast : ((m : ℕ) : ℝ) + 1 ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hgapNat
      have hgap : (1 : ℝ) ≤ (n : ℝ) - m := by linarith
      have hn_mem := Finset.mem_Icc.mp n.property
      have hnle : (n : ℝ) ≤ 2 * N := le_trans (by exact_mod_cast hn_mem.2) hb
      rw [one_sub_div hnpos.ne']
      calc
        1 / (2 * N) ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hnpos hnle
        _ ≤ ((n : ℝ) - m) / n := (div_le_div_iff_of_pos_right hnpos).2 hgap
    calc
      1 / (2 * N) ≤ Real.log ((n : ℝ) / m) := hdiff.trans hlog
      _ = Real.log ((n : ℝ) / N) - Real.log ((m : ℝ) / N) := by
        rw [Real.log_div (ne_of_gt hnpos) hN.ne', Real.log_div (ne_of_gt hmpos) hN.ne',
          Real.log_div (ne_of_gt hnpos) (ne_of_gt hmpos)]
        ring
  intro m n hmn
  rw [Real.dist_eq]
  rcases lt_or_gt_of_ne (Subtype.coe_ne_coe.mpr hmn) with hmn' | hnm'
  · have hbound := hordered m n hmn'
    have hsign : Real.log ((m : ℝ) / N) - Real.log ((n : ℝ) / N) ≤ 0 := by
      have : 0 < 1 / (2 * N) := by positivity
      linarith
    rw [abs_of_nonpos hsign, neg_sub]
    exact hbound
  · have hbound := hordered n m hnm'
    have hsign : 0 ≤ Real.log ((m : ℝ) / N) - Real.log ((n : ℝ) / N) := by
      have : 0 < 1 / (2 * N) := by positivity
      linarith
    rw [abs_of_nonneg hsign]
    exact hbound

/-- The explicit main term for the logarithmic oscillatory integral, equal to that integral when
`N > 0`. The `2π` factor in the normalization comes from Lean's Fourier character `𝐞`. -/
def logPhaseMainTerm (N T : ℝ) : ℂ :=
  (N : ℂ) * (2 * 𝐞 (T * Real.log 2) - 1) /
    (1 + (2 * Real.pi : ℂ) * Complex.I * T)

/-- The logarithmic oscillatory integral is exactly `logPhaseMainTerm`. -/
theorem logPhase_integral_eq_mainTerm
    {N T : ℝ} (hN : 0 < N) :
    (∫ x in N..2 * N, (𝐞 (T * Real.log (x / N)) : ℂ)) =
      logPhaseMainTerm N T := by
  let r : ℂ := (2 * Real.pi : ℂ) * Complex.I * T
  have hchar (u : ℝ) (hu : 0 < u) :
      (𝐞 (T * Real.log u) : ℂ) = (u : ℂ) ^ r := by
    rw [Real.fourierChar_apply,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne')]
    rw [← Complex.ofReal_log hu.le]
    congr 1
    dsimp [r]
    push_cast
    ring
  have hscale :
      (∫ x in N..2 * N, (𝐞 (T * Real.log (x / N)) : ℂ)) =
        (N : ℂ) * ∫ u in (1 : ℝ)..2, (𝐞 (T * Real.log u) : ℂ) := by
    have h := intervalIntegral.smul_integral_comp_mul_left
      (f := fun x : ℝ ↦ (𝐞 (T * Real.log (x / N)) : ℂ))
      (a := (1 : ℝ)) (b := 2) N
    rw [show N * (1 : ℝ) = N by ring, show N * 2 = 2 * N by ring] at h
    rw [← h, Complex.real_smul]
    refine congrArg (fun z : ℂ ↦ (N : ℂ) * z) ?_
    apply intervalIntegral.integral_congr
    intro u _
    exact congrArg (fun y : ℝ ↦ (𝐞 (T * Real.log y) : ℂ))
      (by field_simp [hN.ne'] : N * u / N = u)
  rw [hscale]
  have hint :
      (∫ u in (1 : ℝ)..2, (𝐞 (T * Real.log u) : ℂ)) =
        ((2 : ℂ) ^ (r + 1) - (1 : ℂ) ^ (r + 1)) / (r + 1) := by
    rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      (fun u hu ↦ hchar u (by linarith [hu.1]))]
    exact integral_cpow (Or.inl (by simp [r]))
  rw [hint, Complex.one_cpow]
  rw [Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
  have htwo : (2 : ℂ) ^ r = (𝐞 (T * Real.log 2) : ℂ) :=
    (hchar 2 (by norm_num)).symm
  simp only [htwo]
  dsimp [logPhaseMainTerm, r]
  ring

end Expdb

end
