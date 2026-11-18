import Tengoku.WasowAsymptoticsLean.WasowFuchsianFundamental
import Tengoku.WasowAsymptoticsLean.WasowFuchsianBounds
import Tengoku.WasowAsymptoticsLean.WasowTruncatedGauge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms truncation_inverse_tendsto` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms regularCoefficient_continuousOn` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_regular_tail_bound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_truncated_fundamental` (it only prints; the queue checks the axioms of every declaration). -/

/-! The actual regular-singular coefficient of an arbitrary finite formal
truncation has a polynomially bounded true fundamental matrix. The exponent
is independent of truncation order; the starting radius may depend on it.
No convergence of the infinite formal series is assumed. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Matrix.Norms.Operator
namespace WasowFuchsianTruncation
open WasowMatrixPolynomial WasowTruncatedGauge
variable {m : ℕ}

def regularCoefficient (B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (N : ℕ)
    (r : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  (r : ℂ)⁻¹ • gauge B N ((r : ℂ)⁻¹)

/-- Only the finite polynomial is evaluated. Its constant term is the residue.
@isnad1 id=tendsto.1h3v.s7.0a6280e15ce7 from=translated src=- shape=5153fede vocab=75f1333e
-/
theorem truncation_inverse_tendsto
    (B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) {N : ℕ} (hN : 0 < N) :
    Tendsto (fun r : ℝ => gauge B N ((r : ℂ)⁻¹)) atTop
      (𝓝 (PowerSeries.constantCoeff B)) := by
  have hh := (continuous_eval (PowerSeries.trunc N B)).continuousAt.tendsto.comp
    WasowAnalyticRemainder.inverse_real_tendsto_zero
  change Tendsto (fun r : ℝ => gauge B N ((r : ℂ)⁻¹)) atTop (𝓝 (gauge B N 0)) at hh
  rwa [gauge_zero B hN] at hh

/-- The full finite truncated coefficient is continuous away from the origin.
@isnad1 id=continuo.0h3v.s5.eafed1b2b5d6 from=translated src=- shape=623a3fc6 vocab=3f5683e1
-/
theorem regularCoefficient_continuousOn
    (B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) (N : ℕ) :
    ContinuousOn (regularCoefficient B N) (Ici 1) := by
  have hi : ContinuousOn (fun r : ℝ => (r : ℂ)⁻¹) (Ici 1) :=
    Complex.continuous_ofReal.continuousOn.inv₀ (fun r hr =>
      Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le hr)))
  exact hi.smul ((continuous_eval (PowerSeries.trunc N B)).comp_continuousOn hi)

/-- The Fuchsian exponent bound is independent of the truncation order.
@isnad1 id=ex.1h3v.s8.d5ab8762194e from=translated src=- shape=1b10ac99 vocab=f49b2831
-/
theorem exists_regular_tail_bound
    (B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) {N : ℕ} (hN : 0 < N) :
    ∃ a : ℝ, 1 ≤ a ∧ ContinuousOn (regularCoefficient B N) (Ici a) ∧
      ∀ r ≥ a, ‖regularCoefficient B N r‖ ≤
        (‖PowerSeries.constantCoeff B‖ + 1) / r := by
  have he := (truncation_inverse_tendsto B hN).norm.eventually
    (gt_mem_nhds (lt_add_one ‖PowerSeries.constantCoeff B‖))
  obtain ⟨b, hb⟩ := eventually_atTop.mp he
  let a := max 1 b
  have ha : 1 ≤ a := le_max_left _ _
  refine ⟨a, ha, (regularCoefficient_continuousOn B N).mono
    (fun r hr => ha.trans hr), fun r hr => ?_⟩
  have hrp : 0 < r := zero_lt_one.trans_le (ha.trans hr)
  have hn := (hb r ((le_max_right 1 b).trans hr)).le
  rw [regularCoefficient, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hrp.le]
  calc
    r⁻¹ * ‖gauge B N (r : ℂ)⁻¹‖ ≤ r⁻¹ * (‖PowerSeries.constantCoeff B‖ + 1) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hrp.le)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- A genuinely constructed fundamental matrix and true inverse for the
entire finite regular truncation, including every nonconstant matrix term.
@isnad1 id=ex.1h3v.s10.f56859a498e4 from=translated src=- shape=b6a379a7 vocab=6f729bd4
-/
theorem exists_truncated_fundamental
    (B : PowerSeries (Matrix (Fin m) (Fin m) ℂ)) {N : ℕ} (hN : 0 < N) :
    ∃ R C : ℝ, 1 ≤ R ∧ 0 < C ∧
      ∃ T S : ℝ → Matrix (Fin m) (Fin m) ℂ,
        ContinuousOn T (Ici R) ∧ ContinuousOn S (Ici R) ∧
        (∀ r > R, HasDerivAt T (regularCoefficient B N r * T r) r) ∧
        (∀ r > R, HasDerivAt S (-(S r * regularCoefficient B N r)) r) ∧
        (∀ r ≥ R, S r * T r = 1 ∧ T r * S r = 1) ∧
        (∀ r ≥ R,
          ‖T r‖ ≤ C * r ^ (‖PowerSeries.constantCoeff B‖ + 1) ∧
          ‖S r‖ ≤ C * r ^ (‖PowerSeries.constantCoeff B‖ + 1)) := by
  obtain ⟨a, ha, hc, hb⟩ := exists_regular_tail_bound B hN
  obtain ⟨T, S, hT0, hS0, hTc, hSc, hTd, hSd⟩ :=
    WasowFuchsianFundamental.exists_matrix_solutions (regularCoefficient B N) hc
  obtain ⟨C, hC, hbound⟩ := WasowFuchsianBounds.matrix_solutions_bounds a (a + 1)
    (‖PowerSeries.constantCoeff B‖ + 1) (regularCoefficient B N) T S
    (by linarith) (by linarith) (by positivity) hTd hSd (fun r hr => hb r hr.le)
  have hinv := WasowFuchsianBounds.matrix_solutions_inverse a
    (regularCoefficient B N) T S hT0 hS0 hTc hSc hTd hSd
  refine ⟨a + 1, C, by linarith, hC, T, S,
    hTc.mono (Ici_subset_Ici.mpr (by linarith)), hSc.mono (Ici_subset_Ici.mpr (by linarith)),
    fun r hr => hTd r (by linarith), fun r hr => hSd r (by linarith),
    fun r hr => hinv r (by linarith), hbound⟩

end WasowFuchsianTruncation
