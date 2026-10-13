/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.Rado.Surface.Barriers
import Tengoku.LeanPool.LeanPool.Rado.Surface.Germs
import Tengoku.LeanPool.LeanPool.Rado.Topology.PoincareVolterra
import Tengoku.LeanPool.LeanPool.Rado.Topology.SecondCountable
public import Tengoku

/-!
# Assembly: Radó's theorem

Step 8 of `Rado/PLAN.md`: normalize a chart to contain the standard
configuration (`exists_config_chart`), run Perron + barriers to get a
nonconstant harmonic function on the connected open `configY e`, apply the
Poincaré–Volterra lemma to the evaluation map on a connected component of the
étale space of conjugate germs, descend along the open covering projection
(`secondCountable_configY`), and cover `X` by that set together with a chart
ball (`secondCountableTopology_of_riemannSurface`).
-/

@[expose] public section

open Set Topology Metric MeasureTheory InnerProductSpace Complex Filter

namespace Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Assembly -/

section Assembly

variable [T2Space X] [ConnectedSpace X]

omit [T2Space X] [ConnectedSpace X] in
/-- Some maximal-atlas chart has target containing the standard configuration
ball (affine renormalization of any chart,
`Rado.affine_trans_mem_riemannAtlas`). -/
theorem exists_config_chart [Nonempty X] :
    ∃ e ∈ riemannAtlas X, ball (0 : ℂ) 8 ⊆ e.target := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have he₀ := chartAt_mem_riemannAtlas x₀
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (chartAt ℂ x₀).open_target _
    ((chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀))
  have hρC : ((ρ : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have ha : (8 / (ρ:ℂ)) ≠ 0 := div_ne_zero (by norm_num) hρC
  obtain ⟨e', he', hsrc, hval⟩ := affine_trans_mem_riemannAtlas he₀ (a := 8/(ρ:ℂ))
    (b := -(8/(ρ:ℂ)) * (chartAt ℂ x₀ x₀)) ha
  refine ⟨e', he', ?_⟩
  intro w hw
  set z := chartAt ℂ x₀ x₀ + ((ρ:ℂ)/8) * w with hz
  have hzball : z ∈ ball (chartAt ℂ x₀ x₀) ρ := by
    rw [mem_ball, dist_eq_norm]
    have hzz : z - chartAt ℂ x₀ x₀ = ((ρ:ℂ)/8) * w := by rw [hz]; ring
    rw [hzz, norm_mul]
    have h1 : ‖((ρ:ℂ)/8)‖ = ρ/8 := by
      rw [norm_div]
      simp [abs_of_pos hρ]
    rw [h1]
    have hw8 : ‖w‖ < 8 := by rwa [mem_ball, dist_zero_right] at hw
    calc ρ/8 * ‖w‖ < ρ/8 * 8 := by
          exact mul_lt_mul_of_pos_left hw8 (by positivity)
      _ = ρ := by field_simp
  have hzt : z ∈ (chartAt ℂ x₀).target := hball hzball
  have hxs : (chartAt ℂ x₀).symm z ∈ (chartAt ℂ x₀).source := (chartAt ℂ x₀).map_target hzt
  have hval' := hval _ hxs
  rw [(chartAt ℂ x₀).right_inv hzt] at hval'
  have hwz : e' ((chartAt ℂ x₀).symm z) = w := by
    rw [hval', hz]
    field_simp
    ring
  have hmem : (chartAt ℂ x₀).symm z ∈ e'.source := by rw [hsrc]; exact hxs
  rw [← hwz]
  exact e'.map_source hmem

/-- Transfer of local second countability to an open subspace. -/
theorem locally_secondCountable_subtype {Z : Type*} [TopologicalSpace Z] {C : Set Z}
    (h : ∀ z ∈ C, ∃ U : Set Z, z ∈ U ∧ IsOpen U ∧ SecondCountableTopology U)
    (q : C) : ∃ W : Set C, q ∈ W ∧ IsOpen W ∧ SecondCountableTopology W := by
  obtain ⟨U, hqU, hUo, hUsc⟩ := h q.1 q.2
  refine ⟨Subtype.val ⁻¹' U, hqU, hUo.preimage continuous_subtype_val, ?_⟩
  have := hUsc
  exact (Topology.IsEmbedding.subtypeVal.restrictPreimage U).secondCountableTopology

end Assembly

end Rado
