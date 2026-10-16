import Tengoku.NavierStokesEuler.Euler.PacketPhysicalNormBounds
import Tengoku.NavierStokesEuler.Euler.PacketPhysicalFamily

/-!
Early physical amplitudes are exponentially small relative to the center
target amplitude.  The initial scalar slope cancels, including for
neighboring initial data controlled by the common reference.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set Real EulerSmoothLimit EulerPacketRay EulerPacketStage InnerProductSpace

theorem early_neighbor_state_bound {α : Type*} (center : α) (U V : α → ℝ → ℝ)
    {σ Θ T lam δ : ℝ} {F F₁ Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4) (hΘ : 1 ≤ Θ) (hT : T ≤ Θ)
    (hTtarget : 1/σ ≤ T) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (hδsmall : 4*exp 6*δ ≤ 1)
    (hF : ∀ t, HasDerivAt F (F₁ t) t) (hZ : ∀ t, HasDerivAt Z (Z₁ t) t)
    (hfluxF : ∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*F₁ s)
      (2*(1-σ^2*(σ^2*t^2))*F t) t)
    (hfluxZ : ∀ t, HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
      (2*(1-σ^2*(σ^2*t^2))*Z t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : ∀ ξ t, t ∈ Icc 0 T → |V ξ t-Z t|+|U ξ t+Z₁ t| ≤ δ*(1+lam)*F t) :
    0 < V center T ∧ ∀ ξ s, s ∈ Icc 0 1 →
      (|U ξ s|+|V ξ s|)/V center T ≤ 84*exp 9*Θ*exp (-(1/(4*σ))) := by
  have hcenter := early_forward_exponential_suppression hσ hσsmall hΘ hT hTtarget hlam hδ hδsmall
    hF hZ hfluxF hfluxZ hF0 hF₁0 hZ0 hZ₁0 (herror center)
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity : 0 < 1/σ) hTtarget
  have hTnot : ¬T ≤ 1 := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh, hσ, hσsmall, hTpos]
  refine ⟨hcenter.1, ?_⟩
  intro ξ s hs
  let U' : ℝ → ℝ := fun t => if t ≤ 1 then U ξ t else U center t
  let V' : ℝ → ℝ := fun t => if t ≤ 1 then V ξ t else V center t
  have he : ∀ t ∈ Icc 0 T, |V' t-Z t|+|U' t+Z₁ t| ≤ δ*(1+lam)*F t := by
    intro t ht
    by_cases h : t ≤ 1
    · simpa only [U', V', ite_eq_left h] using herror ξ t ht
    · simpa only [U', V', ite_eq_right h] using herror center t ht
  have hh := early_forward_exponential_suppression hσ hσsmall hΘ hT hTtarget hlam hδ hδsmall
    hF hZ hfluxF hfluxZ hF0 hF₁0 hZ0 hZ₁0 he
  simpa only [U', V', ite_eq_left hs.2, ite_eq_right hTnot] using hh.2 s hs

end EulerPacketMovingFrame
