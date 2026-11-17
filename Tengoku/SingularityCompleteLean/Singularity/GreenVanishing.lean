import Tengoku.SingularityCompleteLean.Singularity.WeightedOccupation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Green rows and columns vanish at infinity

Square summability supplies vanishing along the cofinite filter. In particular,
escaping pole sequences have Green mass tending to zero; this is independent
of a boundary-limit theorem or visual-density comparison.
-/

noncomputable section
open Filter
open scoped Topology
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ]

/-- Every Green column is square summable.
@isnad1 id=summable.1h4v.s12.c2754386ab22 from=translated src=- shape=d566bd18 vocab=a5f45623
-/
theorem walkGreen_column_square_summable (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (y : Γ) :
    Summable (fun x => walkGreen s μ x y ^ 2) := by
  have hh := counting_square_summable (green (rightMarkov s μ) (countingDelta y))
  simpa only [← walkGreen_eq_coefficient s μ hgap, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hh

/-- Each nonnegative Green row tends to zero outside finite sets.
@isnad1 id=tendsto.2h4v.s12.689950b59164 from=translated src=- shape=753205e6 vocab=1c0ec117
-/
theorem walkGreen_row_tendsto_zero (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x : Γ) :
    Tendsto (walkGreen s μ x) cofinite (𝓝 0) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
    (walkGreen_row_square_summable s μ hgap x).tendsto_cofinite_zero
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (walkGreen_nonneg s μ hμ _ _),
    Real.sqrt_zero] using hh

/-- Each nonnegative Green column tends to zero outside finite sets.
@isnad1 id=tendsto.2h4v.s12.51125920f28c from=translated src=- shape=df50df75 vocab=1c0ec117
-/
theorem walkGreen_column_tendsto_zero (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (y : Γ) :
    Tendsto (fun x => walkGreen s μ x y) cofinite (𝓝 0) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
    (walkGreen_column_square_summable s μ hgap y).tendsto_cofinite_zero
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (walkGreen_nonneg s μ hμ _ _),
    Real.sqrt_zero] using hh

/-- Eventual avoidance of every state is sufficient for row decay.
@isnad1 id=tendsto.3h7v.s12.c8f96d8b8f14 from=translated src=- shape=d99ee85c vocab=f1f7cf05
-/
theorem walkGreen_row_escape_tendsto_zero (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
    {α : Type*} {l : Filter α} (x : Γ) (y : α → Γ)
    (hy : ∀ g, ∀ᶠ n in l, y n ≠ g) :
    Tendsto (fun n => walkGreen s μ x (y n)) l (𝓝 0) := by
  have ht : Tendsto y l cofinite := le_cofinite_iff_eventually_ne.mpr hy
  exact (walkGreen_row_tendsto_zero s μ hμ hgap x).comp ht

/-- A positive lower bound on a vanishing factor times f forces f to infinity.
@isnad1 id=tendsto.4h5v.s6.2ed1c71b0d1d from=translated src=- shape=7ce04185 vocab=f5725af0
-/
theorem tendsto_atTop_of_positive_product_lower {α : Type*} {l : Filter α}
    (f a : α → ℝ) (c : ℝ) (hc : 0 < c) (ha : ∀ n, 0 < a n)
    (ha0 : Tendsto a l (𝓝 0)) (hprod : ∀ n, c ≤ a n * f n) :
    Tendsto f l atTop := by
  apply tendsto_atTop.mpr
  intro B
  have hε : 0 < c / (max B 0 + 1) := div_pos hc (by positivity)
  filter_upwards [ha0.eventually (gt_mem_nhds hε)] with n hn
  have hmul : a n * (max B 0 + 1) < c := (lt_div_iff₀ (by positivity)).mp hn
  have hh : max B 0 + 1 < f n := (mul_lt_mul_iff_right₀ (ha n)).mp (hmul.trans_le (hprod n))
  linarith [le_max_left B 0]

end Singularity
