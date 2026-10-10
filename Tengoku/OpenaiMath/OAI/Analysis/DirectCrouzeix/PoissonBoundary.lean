import Tengoku.OpenaiMath.OAI.Analysis.DirectCrouzeix.DiskMapping

namespace OAI

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

def poissonExtension (R : ℝ) (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  Real.circleAverage (fun ζ => poissonKernel 0 z ζ * u ζ) 0 R

theorem poisson_nonnegative_circle {R : ℝ} {z ζ : ℂ}
    (hz : z ∈ ball 0 R) (hζ : ζ ∈ sphere 0 R) : 0 ≤ poissonKernel 0 z ζ := by
  have hz' := mem_ball_zero_iff.mp hz
  have hζ' : ‖ζ‖ = R := by simpa using hζ
  dsimp [poissonKernel]
  simp only [sub_zero]
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg z]

theorem poisson_average_one {R : ℝ} {z : ℂ} (hz : z ∈ ball 0 R) :
    Real.circleAverage (poissonKernel 0 z) 0 R = 1 := by
  simpa only [Pi.smul_def, Pi.mul_def, smul_eq_mul, mul_one] using (harmonicContOnCl_const (c := (1 : ℝ))
    (s := ball 0 R)).circleAverage_poissonKernel_smul hz

theorem harmonic_eventually_eq_of_isLocalMax {u : ℂ → ℝ} {a : ℂ}
    (hu : HarmonicAt u a) (hm : IsLocalMax u a) :
    u =ᶠ[𝓝 a] (fun _ => u a) := by
  obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp (isOpen_setOfPred_harmonicAt u) a hu
  obtain ⟨F, hF, hRe⟩ := (show HarmonicOnNhd u (ball a r) from hB).exists_analyticOnNhd_ball_re_eq
  have hd : ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ (fun z => Complex.exp (F z)) z := by
    filter_upwards [ball_mem_nhds a hr] with z hz
    exact (hF z hz).differentiableAt.cexp
  have hmax : IsLocalMax (norm ∘ (fun z => Complex.exp (F z))) a := by
    filter_upwards [hm, ball_mem_nhds a hr] with z hz hzB
    simpa only [Function.comp_apply, Complex.norm_exp, hRe hzB,
      hRe (mem_ball_self hr), Real.exp_le_exp] using hz
  have he := Complex.norm_eventually_eq_of_isLocalMax hd hmax
  filter_upwards [he, ball_mem_nhds a hr] with z hz hzB
  simpa only [Complex.norm_exp, hRe hzB, hRe (mem_ball_self hr), Real.exp_eq_exp] using hz

theorem harmonic_le_boundary {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) {u : ℂ → ℝ}
    (hu : HarmonicContOnCl u U) {M : ℝ}
    (hM : ∀ z ∈ frontier U, u z ≤ M) :
    ∀ z ∈ closure U, u z ≤ M := by
  intro z hz
  by_contra hle
  obtain ⟨a, ha, hmax⟩ := hb.isCompact_closure.exists_isMaxOn ⟨z, hz⟩ hu.2
  have hhigh : M < u a := (lt_of_not_ge hle).trans_le (hmax hz)
  let S := {x ∈ closure U | u x = u a}
  have hSc : IsCompact S := by
    exact hb.isCompact_closure.of_isClosed_subset
      (hu.2.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton) (by intro x hx; exact hx.1)
  have hSo : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hxU : x ∈ U := by
      by_contra hn
      have hf : x ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hx.1, hn⟩
      exact (not_le_of_gt hhigh) (hx.2 ▸ hM x hf)
    have hxmax : IsLocalMax u x := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact hx.2 ▸ hmax (subset_closure hy)
    have he := harmonic_eventually_eq_of_isLocalMax (hu.1 x hxU) hxmax
    filter_upwards [he, hU.mem_nhds hxU] with y hy hyU
    exact ⟨subset_closure hyU, hy.trans hx.2⟩
  have hSne : S.Nonempty := ⟨a, ha, rfl⟩
  have hSun : S = univ := (show IsClopen S from ⟨hSc.isClosed, hSo⟩).eq_univ hSne
  exact hSc.ne_univ hSun

def herglotzExtension (R : ℝ) (u : ℂ → ℝ) (z : ℂ) : ℂ :=
  Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ * (u ζ : ℂ)) 0 R

end Conformal

end DirectCrouzeix

end

end

end

end OAI
