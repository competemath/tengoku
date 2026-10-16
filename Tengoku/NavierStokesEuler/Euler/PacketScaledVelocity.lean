import Tengoku.NavierStokesEuler.Euler.PacketScaledRay
import Tengoku.NavierStokesEuler.Euler.PacketMovingVelocity
import Tengoku.NavierStokesEuler.Euler.PacketScaledVelocityAlgebra

/-!
The actual projected velocity equation after the source scaling, with its
pressure numerator and denominator identified exactly.  The first two rows
therefore feed the existing scalar-amplification estimates.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay InnerProductSpace

def scaledVelocity (m v w : ℝ → Space) (t₀ a ε τ : ℝ) (i : Fin 3) : ℝ :=
  movingVelocity m v w (physicalTime t₀ a ε τ) i / velocityScale ε i

theorem scaledRay_restore (m v r : ℝ → Space) {s₀ t₀ a ε τ : ℝ}
    (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0) (i : Fin 3) :
    s₀*rayScale ε i*scaledRay m v r s₀ t₀ a ε τ i = movingRay m v r (physicalTime t₀ a ε τ) i := by
  unfold scaledRay
  field_simp [hs₀, rayScale_ne_zero hε i]

theorem scaledVelocity_restore (m v w : ℝ → Space) {t₀ a ε τ : ℝ}
    (hε : ε ≠ 0) (i : Fin 3) :
    velocityScale ε i*scaledVelocity m v w t₀ a ε τ i = movingVelocity m v w (physicalTime t₀ a ε τ) i := by
  unfold scaledVelocity
  field_simp [velocityScale_ne_zero hε i]

def scaledAction (M : Space →L[ℝ] Space) (m v : ℝ → Space) (a ε t : ℝ) : Fin 3 → Fin 3 → ℝ :=
  scaledVelocityEntry a ε (frameMatrix M (unit (m t)) (unit (v t)))

def scaledTransport (B M : Space →L[ℝ] Space) (m v : ℝ → Space) (a ε t : ℝ) : Fin 3 → Fin 3 → ℝ :=
  scaledVelocityEntry a ε (fun i j => frameMatrix M (unit (m t)) (unit (v t)) i j +
    frameSkew (frameMatrix B (unit (m t)) (unit (v t))) i j)

theorem movingDenominator_scaling (m v r : ℝ → Space) {s₀ t₀ a ε τ : ℝ}
    (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0) :
    movingDenominator m v r (physicalTime t₀ a ε τ) = s₀^2 *
      rayDenominator ε (scaledRay m v r s₀ t₀ a ε τ 0)
        (scaledRay m v r s₀ t₀ a ε τ 1) (scaledRay m v r s₀ t₀ a ε τ 2) := by
  unfold movingDenominator
  simp_rw [← scaledRay_restore m v r hs₀ hε]
  exact scaling_denominator s₀ ε (scaledRay m v r s₀ t₀ a ε τ)

theorem movingFlux_scaling (M : Space →L[ℝ] Space) (m v r w : ℝ → Space) {s₀ t₀ a ε τ : ℝ}
    (ha : a ≠ 0) (hs₀ : s₀ ≠ 0) (hε : ε ≠ 0) :
    movingFlux M m v r w (physicalTime t₀ a ε τ) = s₀*a*
      velocityNumerator (scaledAction M m v a ε (physicalTime t₀ a ε τ))
        (scaledRay m v r s₀ t₀ a ε τ 0) (scaledRay m v r s₀ t₀ a ε τ 1)
        (scaledRay m v r s₀ t₀ a ε τ 2)
        (scaledVelocity m v w t₀ a ε τ 0) (scaledVelocity m v w t₀ a ε τ 1)
        (scaledVelocity m v w t₀ a ε τ 2) := by
  unfold movingFlux
  simp_rw [← scaledRay_restore m v r hs₀ hε, ← scaledVelocity_restore m v w hε]
  exact scaling_flux ha s₀ ε _ _ _

end EulerPacketMovingFrame
