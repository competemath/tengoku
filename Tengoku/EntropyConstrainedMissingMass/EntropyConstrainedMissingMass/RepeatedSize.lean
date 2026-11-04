import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.FinitePerturbation
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.Quasiconvexity
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.ScalarLocalMax

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual finite-coordinate perturbations at repeated atom sizes. -/

namespace EntropyConstrainedMissingMass
noncomputable section
open Set Filter
open scoped Topology ENNReal

/--
@isnad1 id=le.1h2v.s5.eae8c6cd9bba from=translated src=- shape=81066cf8 vocab=9755fa41
-/
theorem negMulLog_symmetric_pair_le {a ε : ℝ} (hε : |ε| ≤ a) :
    Real.negMulLog (a + ε) + Real.negMulLog (a - ε) ≤ 2 * Real.negMulLog a := by
  have he := abs_le.mp hε
  have h := Real.concaveOn_negMulLog.2
    (show a + ε ∈ Ici 0 by change 0 ≤ a + ε; linarith)
    (show a - ε ∈ Ici 0 by change 0 ≤ a - ε; linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have heq : (1 / 2 : ℝ) • (a + ε) + (1 / 2 : ℝ) • (a - ε) = a := by
    simp only [smul_eq_mul]
    ring
  rw [heq] at h
  simp only [smul_eq_mul] at h
  linarith

/-- Cauchy's mean-value theorem realizes the logarithmic secant slope as `u f''(u)`.
This gives the same contradiction as the manuscript's weighted-integral average.
@isnad1 id=ex.4h3v.s8.e0b6e0c2ed40 from=translated src=- shape=67e2c2fc vocab=7b04fc78
-/
theorem exists_weighted_second_derivative_eq_log_secant {f : ℝ → ℝ} {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hc : ContinuousOn (deriv f) (Icc x y))
    (hd : DifferentiableOn ℝ (deriv f) (Ioo x y)) :
    ∃ v ∈ Ioo x y, v * deriv (deriv f) v =
      (deriv f y - deriv f x) / (Real.log y - Real.log x) := by
  have hlogc : ContinuousOn Real.log (Icc x y) := by
    intro u hu
    exact (Real.continuousAt_log (ne_of_gt (hx.trans_le hu.1))).continuousWithinAt
  have hlogd : DifferentiableOn ℝ Real.log (Ioo x y) := by
    intro u hu
    exact (Real.differentiableAt_log (ne_of_gt (hx.trans hu.1))).differentiableWithinAt
  obtain ⟨v, hv, heq⟩ := exists_ratio_deriv_eq_ratio_slope (deriv f) hxy hc hd
    Real.log hlogc hlogd
  have hv0 : v ≠ 0 := ne_of_gt (hx.trans hv.1)
  have hL : Real.log y - Real.log x ≠ 0 := ne_of_gt (sub_pos.mpr (Real.log_lt_log hx hxy))
  refine ⟨v, hv, ?_⟩
  rw [Real.deriv_log] at heq
  apply (eq_div_iff hL).2
  have heq' := congrArg (fun r : ℝ => r * v) heq
  simp only [mul_assoc, inv_mul_cancel₀ hv0, mul_one] at heq'
  nlinarith only [heq']

/-- Strict quasiconvexity excludes the two second-variation endpoint inequalities.
@isnad1 id=not.5h3v.s9.5666cbafc9cf from=translated src=- shape=7e44005d vocab=055fd539
-/
theorem not_both_weighted_second_derivative_bounds {f : ℝ → ℝ} {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hc : ContinuousOn (deriv f) (Icc x y))
    (hd : DifferentiableOn ℝ (deriv f) (Ioo x y))
    (hq : ∀ v ∈ Ioo x y, v * deriv (deriv f) v <
      max (x * deriv (deriv f) x) (y * deriv (deriv f) y)) :
    ¬(x * deriv (deriv f) x ≤ (deriv f y - deriv f x) / (Real.log y - Real.log x) ∧
      y * deriv (deriv f) y ≤ (deriv f y - deriv f x) / (Real.log y - Real.log x)) := by
  obtain ⟨v, hv, heq⟩ := exists_weighted_second_derivative_eq_log_secant hx hxy hc hd
  intro hb
  have hstrict := hq v hv
  rw [heq] at hstrict
  exact (not_lt_of_ge (max_le hb.1 hb.2)) hstrict

namespace ProbabilityVector
variable {ι : Type*}
local instance repeatedSizeDecidableEq : DecidableEq ι := Classical.decEq ι

def repeatedPairValues (p : ProbabilityVector ι) (i : ι) (ε : ℝ) (k : ι) : ℝ :=
  if k = i then p.coord i + ε else p.coord i - ε

/--
@isnad1 id=le.2h6v.s6.4d354fb9491c from=translated src=- shape=930ba3b1 vocab=de69b096
-/
theorem repeatedPairValues_nonneg (p : ProbabilityVector ι) {i j : ι} {ε : ℝ}
    (hε : |ε| ≤ p.coord i) (k : ι) (_hk : k ∈ ({i, j} : Finset ι)) :
    0 ≤ repeatedPairValues p i ε k := by
  have hab := abs_le.mp hε
  unfold repeatedPairValues
  split_ifs <;> linarith

/--
@isnad1 id=eq.2h5v.s6.21f48e45d448 from=translated src=- shape=f06561aa vocab=01efcc2f
-/
theorem sum_repeatedPairValues (p : ProbabilityVector ι) {i j : ι} (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (ε : ℝ) :
    ∑ k ∈ ({i, j} : Finset ι), repeatedPairValues p i ε k =
      ∑ k ∈ ({i, j} : Finset ι), p.coord k := by
  simp [Finset.sum_pair hij, repeatedPairValues, hij.symm, heq]

/-- Split a repeated pair symmetrically; outside the nonnegative range leave the vector unchanged.-/
def perturbRepeatedPair (p : ProbabilityVector ι) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (ε : ℝ) : ProbabilityVector ι :=
  if hε : |ε| ≤ p.coord i then
    p.replaceFinite {i, j} (repeatedPairValues p i ε)
      (repeatedPairValues_nonneg p hε) (sum_repeatedPairValues p hij heq ε)
  else p

/--
@isnad1 id=le.2h5v.s6.29e3ef9f2770 from=translated src=- shape=6324d045 vocab=d59f7af1
-/
theorem dist_perturbRepeatedPair_le (p : ProbabilityVector ι) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (ε : ℝ) :
    dist (perturbRepeatedPair p i j hij heq ε) p ≤ 2 * |ε| := by
  unfold perturbRepeatedPair
  split_ifs with hε
  · rw [dist_replaceFinite]
    simp [Finset.sum_pair hij, repeatedPairValues, hij.symm, heq]
    linarith
  · simp

/--
@isnad1 id=tendsto.2h4v.s6.1d9da9ad0690 from=translated src=- shape=5954424a vocab=9421671a
-/
theorem tendsto_perturbRepeatedPair (p : ProbabilityVector ι) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) :
    Tendsto (perturbRepeatedPair p i j hij heq) (𝓝 0) (𝓝 p) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) (dist_perturbRepeatedPair_le p i j hij heq)
  simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul
    ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).abs)

/--
@isnad1 id=le.3h5v.s5.50f6683ae946 from=translated src=- shape=dc1da851 vocab=01f645cb
-/
theorem entropy_perturbRepeatedPair_le (p : ProbabilityVector ι) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (ε : ℝ) (hp : p.entropy ≠ ⊤) :
    (perturbRepeatedPair p i j hij heq ε).entropy ≤ p.entropy := by
  unfold perturbRepeatedPair
  split_ifs with hε
  · apply (ENNReal.toReal_le_toReal (entropy_replaceFinite_ne_top _ _ _ _ _ hp) hp).mp
    rw [entropy_toReal_replaceFinite _ _ _ _ _ hp]
    have hs := negMulLog_symmetric_pair_le hε
    simp [Finset.sum_pair hij, repeatedPairValues, hij.symm, heq]
    linarith
  · exact le_rfl

/--
@isnad1 id=eq.3h6v.s7.f0500cc9cbef from=translated src=- shape=6fee0aad vocab=8c601a11
-/
theorem objective_perturbRepeatedPair (p : ProbabilityVector ι) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (ε : ℝ) (hε : |ε| ≤ p.coord i) (t : ℕ) :
    (perturbRepeatedPair p i j hij heq ε).objective t = p.objective t +
      missingMassTerm t (p.coord i + ε) + missingMassTerm t (p.coord i - ε) -
        2 * missingMassTerm t (p.coord i) := by
  rw [perturbRepeatedPair, dite_eq_left hε, objective_replaceFinite]
  simp [Finset.sum_pair hij, repeatedPairValues, hij.symm, heq]
  ring

/-- Local maximality in the actual ℓ¹ space passes to the symmetric pair variation.
@isnad1 id=islocalm.4h6v.s6.58fca6e16763 from=translated src=- shape=208ecb8a vocab=cf16e07f
-/
theorem localMax_symmetric_pair_of_repeated (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (hp : LocalMaximizer t h p) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (hi : 0 < p.coord i) :
    IsLocalMax (fun ε : ℝ => missingMassTerm t (p.coord i + ε) +
      missingMassTerm t (p.coord i - ε)) 0 := by
  have hfin := finite_entropy_of_feasible hp.1
  have hlocal : {q : ProbabilityVector ι | q.objective t ≤ p.objective t} ∈ 𝓝[Feasible h] p := hp.2
  obtain ⟨u, hu, hule⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hlocal
  have hq := (tendsto_perturbRepeatedPair p i j hij heq).eventually hu
  have habs : ∀ᶠ ε : ℝ in 𝓝 0, |ε| < p.coord i := by
    exact (continuous_abs.tendsto (0 : ℝ)).eventually (by simpa using eventually_lt_nhds hi)
  filter_upwards [hq, habs] with ε hεu hε
  have hfeas : perturbRepeatedPair p i j hij heq ε ∈ Feasible h :=
    (entropy_perturbRepeatedPair_le p i j hij heq ε hfin).trans hp.1
  have hobj : (perturbRepeatedPair p i j hij heq ε).objective t ≤ p.objective t :=
    hule ⟨hεu, hfeas⟩
  rw [objective_perturbRepeatedPair p i j hij heq ε hε.le t] at hobj
  simp only [add_zero, sub_zero]
  linarith

/--
@isnad1 id=le.2h4v.s5.3566fe651811 from=translated src=- shape=38fbbdaf vocab=29351807
-/
theorem repeated_size_le_half (p : ProbabilityVector ι) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) : p.coord i ≤ 1 / 2 := by
  have hs := p.summable_coord.sum_le_tsum ({i, j} : Finset ι) (fun k _ => p.coord_nonneg k)
  rw [p.tsum_coord] at hs
  simp only [Finset.sum_pair hij, heq] at hs
  linarith

end ProbabilityVector
end
end EntropyConstrainedMissingMass
