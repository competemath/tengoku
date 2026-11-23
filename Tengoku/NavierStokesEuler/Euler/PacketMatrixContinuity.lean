import Tengoku.NavierStokesEuler.Euler.PacketPhysicalCoefficients

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Continuity of the actual rescaled moving-frame matrices. -/

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay InnerProductSpace

/--
@isnad1 id=continuo.7h11v.s14.ffa98987ff6d from=translated src=- shape=7d55de0e vocab=0fe92196
-/
theorem rescaledFrame_continuousOn (B D : ℝ → Space →L[ℝ] Space)
    {m v : ℝ → Space} {S U : Set ℝ} {t₀ a ε : ℝ}
    (hmap : MapsTo (physicalTime t₀ a ε) U S)
    (hDc : ContinuousOn D S)
    (hm : ∀ t ∈ S, HasDerivWithinAt m (-(B t).adjoint (m t)) S t)
    (hv : ∀ t ∈ S, HasDerivWithinAt v (-(B t) (v t)+
      (2*⟪m t,(B t) (v t)⟫_ℝ/‖m t‖^2) • m t) S t)
    (hm0 : ∀ t ∈ S, m t ≠ 0) (hv0 : ∀ t ∈ S, v t ≠ 0)
    (hmv : ∀ t ∈ S, ⟪m t,v t⟫_ℝ = 0) :
    ∀ i j, ContinuousOn (fun τ => rescaledFrame D m v t₀ a ε τ i j) U := by
  have ht : ContinuousOn (physicalTime t₀ a ε) U := by unfold physicalTime; fun_prop
  have hf : ∀ i, ContinuousOn (fun t => normalizedFrame m v t i) S := by
    intro i t hts
    exact (normalizedFrame_hasDerivWithinAt (B t) (hm t hts) (hv t hts)
      (hm0 t hts) (hv0 t hts) (hmv t hts) i).continuousWithinAt
  intro i j
  exact ((hf i).comp ht hmap).inner ((hDc.comp ht hmap).clm_apply ((hf j).comp ht hmap))

/--
@isnad1 id=continuo.1h4v.s6.fcfe7cdb86e9 from=translated src=- shape=d8fbbe14 vocab=72376b51
-/
theorem frameSkew_continuousOn {B : ℝ → Fin 3 → Fin 3 → ℝ} {U : Set ℝ}
    (hB : ∀ i j, ContinuousOn (fun τ => B τ i j) U) :
    ∀ i j, ContinuousOn (fun τ => frameSkew (B τ) i j) U := by
  intro i j
  unfold frameSkew
  split_ifs <;> fun_prop

/--
@isnad1 id=continuo.2h7v.s7.655f578029a8 from=translated src=- shape=5e0507d1 vocab=9afe3511
-/
theorem scaledRayEntry_continuousOn {M S : ℝ → Fin 3 → Fin 3 → ℝ} {U : Set ℝ}
    (a ε : ℝ) (hM : ∀ i j, ContinuousOn (fun τ => M τ i j) U)
    (hS : ∀ i j, ContinuousOn (fun τ => S τ i j) U) :
    ∀ i j, ContinuousOn (fun τ => scaledRayEntry a ε (M τ) (S τ) i j) U := by
  intro i j
  unfold scaledRayEntry
  fun_prop

/--
@isnad1 id=continuo.1h6v.s6.ab92ea23f13a from=translated src=- shape=e875fd4b vocab=ca37a541
-/
theorem scaledVelocityEntry_continuousOn {M : ℝ → Fin 3 → Fin 3 → ℝ} {U : Set ℝ}
    (a ε : ℝ) (hM : ∀ i j, ContinuousOn (fun τ => M τ i j) U) :
    ∀ i j, ContinuousOn (fun τ => scaledVelocityEntry a ε (M τ) i j) U := by
  intro i j
  unfold scaledVelocityEntry
  fun_prop

end EulerPacketMovingFrame
