import Tengoku.OpenaiMath.OAI.Analysis.DirectCrouzeix.PoissonBoundary

namespace OAI

universe u_132

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

open InnerProductSpace Real

theorem circleAverage_conj {E : Type u_132} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (R : ℝ) :
    Real.circleAverage (fun ζ => f (conj ζ)) 0 R = Real.circleAverage f 0 R := by
  conv_lhs => rw [Real.circleAverage_eq_circleAverage_zero_one]
  conv_rhs => rw [Real.circleAverage_eq_circleAverage_zero_one]
  calc
    Real.circleAverage (fun z => f (conj ((R : ℂ) * z + 0))) 0 1 =
        Real.circleAverage (fun z => f ((R : ℂ) * z⁻¹ + 0)) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hn : ‖z‖ = 1 := by simpa using hz
      simp [Complex.inv_eq_conj hn]
    _ = Real.circleAverage (fun z => f ((R : ℂ) * z + 0)) 0 1 :=
      Real.circleAverage_zero_one_congr_inv (f := fun z => f ((R : ℂ) * z + 0))

theorem poisson_conj (z ζ : ℂ) :
    poissonKernel 0 (conj z) (conj ζ) = poissonKernel 0 z ζ := by
  simp only [poissonKernel, sub_zero, Complex.norm_conj, ← map_sub]

theorem poisson_odd {R : ℝ} {u : ℂ → ℝ}
    (hu : ∀ ζ, u (conj ζ) = -u ζ) (z : ℂ) :
    poissonExtension R u (conj z) = -poissonExtension R u z := by
  dsimp [poissonExtension]
  rw [← circleAverage_conj (fun ζ => poissonKernel 0 (conj z) ζ * u ζ) R]
  simp_rw [poisson_conj, hu, mul_neg]
  have he (ζ : ℂ) : -(poissonKernel 0 z ζ * u ζ) = (-1 : ℝ) • (poissonKernel 0 z ζ * u ζ) := by simp
  simp_rw [he]
  rw [Real.circleAverage_fun_smul, neg_one_smul]

theorem poisson_real_zero {R : ℝ} {u : ℂ → ℝ}
    (hu : ∀ ζ, u (conj ζ) = -u ζ) {z : ℂ} (hz : z.im = 0) :
    poissonExtension R u z = 0 := by
  have hc : conj z = z := Complex.conj_eq_iff_im.mpr hz
  have hh := poisson_odd (R := R) hu z
  rw [hc] at hh
  linarith

def poissonClosed (R : ℝ) (u : ℂ → ℝ) (z : ℂ) : ℝ := by
  classical
  exact if z ∈ ball 0 R then poissonExtension R u z else u z

def upperBall (R : ℝ) : Set ℂ := ball 0 R ∩ {z | 0 < z.im}

def upperClosedBall (R : ℝ) : Set ℂ := closedBall 0 R ∩ {z | 0 ≤ z.im}

theorem upperBall_open (R : ℝ) : IsOpen (upperBall R) :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

theorem upperClosedBall_closed (R : ℝ) : IsClosed (upperClosedBall R) :=
  isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)

theorem closure_upperBall_subset (R : ℝ) : closure (upperBall R) ⊆ upperClosedBall R := by
  apply closure_minimal _ (upperClosedBall_closed R)
  intro z hz
  exact ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩

def oddUpper (u : ℂ → ℝ) (z : ℂ) : ℝ := if 0 ≤ z.im then u z else -u (conj z)

theorem oddUpper_conj {u : ℂ → ℝ} (hzero : ∀ z, z.im = 0 → u z = 0)
    (z : ℂ) : oddUpper u (conj z) = -oddUpper u z := by
  dsimp [oddUpper]
  rw [Complex.conj_conj]
  change (if 0 ≤ -z.im then u (conj z) else -u z) = -(if 0 ≤ z.im then u z else -u (conj z))
  by_cases hz : z.im = 0
  · have hc : conj z = z := Complex.conj_eq_iff_im.mpr hz
    simp [hz, hc, hzero z hz]
  · by_cases hh : 0 ≤ z.im
    · have hn : ¬ 0 ≤ -z.im := fun he => hz (by linarith)
      rw [ite_eq_right hn, ite_eq_left hh]
    · rw [ite_eq_left (show 0 ≤ -z.im by linarith), ite_eq_right hh, neg_neg]

theorem oddUpper_continuous_circle {R : ℝ} {u : ℂ → ℝ}
    (hu : ContinuousOn u (upperClosedBall R))
    (hzero : ∀ z, z.im = 0 → u z = 0) :
    ContinuousOn (oddUpper u) (sphere 0 R) := by
  classical
  apply ContinuousOn.if
  · intro z hz
    have hfr := Complex.continuous_im.frontier_preimage_subset (Ici (0 : ℝ)) hz.2
    have hz0 : z.im = 0 := by simpa only [frontier_Ici, mem_preimage, mem_singleton_iff] using hfr
    have hc : conj z = z := Complex.conj_eq_iff_im.mpr hz0
    simp [hc, hzero z hz0]
  · apply hu.mono
    intro z hz
    have hi : 0 ≤ z.im := by
      exact (closure_minimal (by intro w hw; exact hw)
        (isClosed_le continuous_const Complex.continuous_im)) hz.2
    exact ⟨sphere_subset_closedBall hz.1, hi⟩
  · apply ContinuousOn.neg
    apply hu.comp Complex.continuous_conj.continuousOn
    intro z hz
    have hi : z.im ≤ 0 := by
      exact (closure_minimal (by intro w hw; exact (le_of_not_ge hw))
        (isClosed_le Complex.continuous_im continuous_const)) hz.2
    exact ⟨by simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using
      sphere_subset_closedBall hz.1, by simpa only [mem_ofPred_eq, Complex.conj_im, neg_nonneg] using hi⟩

end Conformal

end DirectCrouzeix

end

end

end

end OAI
