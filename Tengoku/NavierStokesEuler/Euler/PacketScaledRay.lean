import Tengoku.NavierStokesEuler.Euler.PacketMovingRay

/-! The actual ray in the source time and coordinate scaling. -/

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay InnerProductSpace

def physicalTime (t₀ a ε τ : ℝ) : ℝ := t₀ + (ε/a)*τ

theorem physicalTime_hasDerivAt (t₀ a ε τ : ℝ) :
    HasDerivAt (physicalTime t₀ a ε) (ε/a) τ := by
  convert! ((hasDerivAt_id τ).const_mul (ε/a)).const_add t₀ using 1
  simp

theorem rayScale_ne_zero {ε : ℝ} (hε : ε ≠ 0) (i : Fin 3) : rayScale ε i ≠ 0 := by
  unfold rayScale
  split_ifs
  · exact hε
  · exact one_ne_zero

theorem scaledRayRate_algebra {a ε s₀ : ℝ} (ha : a ≠ 0) (hε : ε ≠ 0) (hs₀ : s₀ ≠ 0)
    (M S : Fin 3 → Fin 3 → ℝ) (R : Fin 3 → ℝ) (i : Fin 3) :
    ((-(∑ j : Fin 3, (M j i-S j i)*R j))*(ε/a))/(s₀*rayScale ε i) =
      ∑ j : Fin 3, scaledRayEntry a ε M S i j*(R j/(s₀*rayScale ε j)) := by
  rw [← Finset.sum_neg_distrib, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  unfold scaledRayEntry
  field_simp [ha, hs₀, rayScale_ne_zero hε i, rayScale_ne_zero hε j]

def scaledRay (m v r : ℝ → Space) (s₀ t₀ a ε τ : ℝ) (i : Fin 3) : ℝ :=
  movingRay m v r (physicalTime t₀ a ε τ) i / (s₀*rayScale ε i)

end EulerPacketMovingFrame
