import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Topology.Order.OrderClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!+# Variational limits of vanishing and diverging penalties

A convergent family of minimizers of `f + βg` selects the smallest penalty
among minimizers of `f` as `β ↓ 0`; as `β → ∞`, a nonnegative penalty
forces its zero set and selects the smallest `f` there.
-/
noncomputable section
open Filter Topology
namespace NLAlib
variable {E : Type*} [TopologicalSpace E]

/-- A convergent positive vanishing-penalty family minimizes the primary
objective and, among all its minimizers, the secondary objective.
@isnad1 id=and.4h5v.s7.b911d0d59d62 from=translated src=- shape=7a5263a3 vocab=fb0749cf
-/
theorem vanishing_penalty_limit_minimizes {f g : E → ℝ}
    (hf : Continuous f) (hg : Continuous g) (x : ℝ → E) (x₀ : E)
    (hx : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 x₀))
    (hmin : ∀ β : ℝ, 0 < β → ∀ z, f (x β) + β * g (x β) ≤ f z + β * g z) :
    (∀ z, f x₀ ≤ f z) ∧
      ∀ z, (∀ y, f z ≤ f y) → g x₀ ≤ g z := by
  have hβ : Tendsto (fun β : ℝ => β) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hfx := hf.continuousAt.tendsto.comp hx
  have hgx := hg.continuousAt.tendsto.comp hx
  have hfirst : ∀ z, f x₀ ≤ f z := by
    intro z
    have hl : Tendsto (fun β => f (x β) + β * g (x β)) (𝓝[>] (0 : ℝ)) (𝓝 (f x₀)) := by
      simpa using hfx.add (hβ.mul hgx)
    have hr : Tendsto (fun β : ℝ => f z + β * g z) (𝓝[>] (0 : ℝ)) (𝓝 (f z)) := by
      simpa using tendsto_const_nhds.add (hβ.mul tendsto_const_nhds)
    apply le_of_tendsto_of_tendsto hl hr
    filter_upwards [self_mem_nhdsWithin] with β hβ
    exact hmin β hβ z
  refine ⟨hfirst, ?_⟩
  intro z hz
  apply le_of_tendsto hgx
  filter_upwards [self_mem_nhdsWithin] with β hβ
  change g (x β) ≤ g z
  have hh := hmin β hβ z
  have hm : β * g (x β) ≤ β * g z := by linarith [hz (x β)]
  exact (mul_le_mul_iff_right₀ hβ).mp hm

/-- A convergent family with diverging nonnegative penalty lies in the
penalty's zero set and minimizes the primary objective on that set.
@isnad1 id=and.7h6v.s7.f2a2491e8906 from=translated src=- shape=112b0a3a vocab=f39437e0
-/
theorem diverging_penalty_limit_minimizes {f g : E → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfn : ∀ z, 0 ≤ f z) (hgn : ∀ z, 0 ≤ g z)
    (x : ℝ → E) (xInf : E) (hx : Tendsto x atTop (𝓝 xInf))
    (z₀ : E) (hz₀ : g z₀ = 0)
    (hmin : ∀ β : ℝ, 0 < β → ∀ z, f (x β) + β * g (x β) ≤ f z + β * g z) :
    g xInf = 0 ∧ ∀ z, g z = 0 → f xInf ≤ f z := by
  have hfx := hf.continuousAt.tendsto.comp hx
  have hgx := hg.continuousAt.tendsto.comp hx
  have hpositive : ∀ᶠ β : ℝ in atTop, 0 < β := eventually_gt_atTop 0
  have hbound : ∀ᶠ β : ℝ in atTop, g (x β) ≤ f z₀ / β := by
    filter_upwards [hpositive] with β hβ
    apply (le_div_iff₀ hβ).mpr
    have hh := hmin β hβ z₀
    rw [hz₀, mul_zero, add_zero] at hh
    nlinarith [hfn (x β)]
  have hzero : g xInf ≤ 0 :=
    le_of_tendsto_of_tendsto hgx (tendsto_id.const_div_atTop (f z₀)) hbound
  refine ⟨le_antisymm hzero (hgn xInf), ?_⟩
  intro z hz
  apply le_of_tendsto hfx
  filter_upwards [hpositive] with β hβ
  change f (x β) ≤ f z
  have hh := hmin β hβ z
  rw [hz, mul_zero, add_zero] at hh
  linarith [mul_nonneg hβ.le (hgn (x β))]

end NLAlib
