import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.AffineTorus
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.UniformGradient
import Tengoku.Seed.Analysis.ODE.Gronwall

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Quantitative and compactness inputs for transport. These results control an
existing differentiable trajectory; existence, parameter dependence, and global
continuation for the manuscript vector field remain separate obligations. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen

/-- Properness in the topology of the affine torus itself.-/
theorem affineTorus_sublevel_isCompact (d : ℕ) (R : ℝ) :
    IsCompact {x : affineTorus d | ‖x.val‖ ≤ R} := by
  simpa [Metric.closedBall, dist_zero_right] using
    (affineTorus_isClosed d).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_closedBall (0 : TorusAmbient d) R)

/-- The manuscript lower-bound lemma specialized to its proper affine geometry.
The identification of `lam` with the restricted differential remains explicit.-/
theorem affineTorus_uniform_gradient {d : ℕ}
    (F : affineTorus d → ℂ) (lam : affineTorus d → ℝ)
    (hF : Continuous F) (hlam : Continuous lam) (hlam0 : ∀ x, 0 ≤ lam x)
    (Q : Set ℂ) (hQ : IsCompact Q)
    (hgood : ∀ c ∈ Q, c ∉ ordinaryCriticalValues F lam ∪
      asymptoticCriticalValues F (fun x => ‖x.val‖) lam) :
    ∃ c > (0 : ℝ), ∀ x, F x ∈ Q → c ≤ (1 + ‖x.val‖) * lam x :=
  uniform_gradient_lower_bound F (fun x => ‖x.val‖) lam hF hlam
    (fun _ => norm_nonneg _) hlam0 (affineTorus_sublevel_isCompact d) Q hQ hgood

/-- The controlled region is compact and lies entirely in the regular domain.
This is stronger than just bounding the radius.-/
theorem compact_regular_controlled_region {d : ℕ}
    (F : affineTorus d → ℂ) (lam : affineTorus d → ℝ)
    (hF : Continuous F) (hlam0 : ∀ x, 0 ≤ lam x)
    (Q : Set ℂ) (hQ : IsCompact Q) {c R : ℝ} (hc : 0 < c)
    (hbound : ∀ x, F x ∈ Q → c ≤ (1 + ‖x.val‖) * lam x) :
    IsCompact {x : affineTorus d | ‖x.val‖ ≤ R ∧ F x ∈ Q} ∧
      ∀ x : affineTorus d, ‖x.val‖ ≤ R → F x ∈ Q →
        0 < c / (1 + R) ∧ c / (1 + R) ≤ lam x := by
  refine ⟨(affineTorus_sublevel_isCompact d R).inter_right
    (hQ.isClosed.preimage hF), ?_⟩
  intro x hx hFx
  exact regular_lower_bound_on_radius_sublevel hc (norm_nonneg _) hx
    (hlam0 x) (hbound x hFx)

/-- Grönwall's precise radius bound for a trajectory with linear growth.-/
theorem trajectory_radius_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x v : ℝ → E} {a b C : ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hv : ∀ t ∈ Ico a b, HasDerivWithinAt x (v t) (Ici t) t)
    (hgrowth : ∀ t ∈ Ico a b, ‖v t‖ ≤ C * (1 + ‖x t‖)) :
    ∀ t ∈ Icc a b, 1 + ‖x t‖ ≤ (1 + ‖x a‖) * Real.exp (C * (t - a)) := by
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le hx hv (le_refl ‖x a‖)
    (fun t ht => by nlinarith [hgrowth t ht])
  intro t ht
  have h := hb t ht
  by_cases hC : C = 0
  · simpa [hC, gronwallBound] using h
  · rw [gronwallBound_of_K_ne_0 hC, div_self hC] at h
    nlinarith

end DuistermaatVanDerKallen
