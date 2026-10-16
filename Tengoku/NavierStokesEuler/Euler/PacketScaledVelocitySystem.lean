import Tengoku.NavierStokesEuler.Euler.PacketScaledVelocity

/-!
The actual scaled velocity supplies the first two equations and the scalar
flux equation used in amplification.  Only the first two transport rows are
relevant; the auxiliary third row in the scalar estimate is filled explicitly.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  EulerPacketBridge InnerProductSpace

/-- A harmless third-row extension of a two-row transport matrix. -/
def firstTwoRows (C : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 then C 0 j else C 1 j

theorem velocityFirstRhs_firstTwoRows (A C : Fin 3 → Fin 3 → ℝ)
    (ε P Q N U V : ℝ) :
    velocityFirstRhs A (firstTwoRows C) ε P Q N U V =
      velocityFirstRhs A C ε P Q N U V := by
  simp [velocityFirstRhs, firstTwoRows]

theorem velocitySecondRhs_firstTwoRows (A C : Fin 3 → Fin 3 → ℝ)
    (ε P Q N U V : ℝ) :
    velocitySecondRhs A (firstTwoRows C) ε P Q N U V =
      velocitySecondRhs A C ε P Q N U V := by
  simp [velocitySecondRhs, firstTwoRows]

/-- The scalar error estimate needs no assumption on the physical third
transport row. -/
theorem velocity_rhs_error_firstTwo
    {A C : Fin 3 → Fin 3 → ℝ} {Θ e ε β P Q N P₀ Q₀ U V : ℝ}
    (hΘ : 1 ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hsmall : 10000 * e * Θ ^ 5 ≤ 1) (hβ : |β| ≤ 1)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ 3 * e)
    (hC : ∀ j, |C 0 j - idealUnprojectedEntry 0 j| ≤ 5 * e ∧
      |C 1 j - idealUnprojectedEntry 1 j| ≤ 5 * e)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q - Q₀| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5) :
    |velocityFirstRhs A C ε P Q N U V -
        (-2 * V + 2 * P₀ * ((P₀ + β) * V + Q₀ * U) / (1 + P₀ ^ 2))| +
      |velocitySecondRhs A C ε P Q N U V + U| ≤
        200000 * e * Θ ^ 12 * (|U| + |V|) := by
  have hC' : ∀ i j, |firstTwoRows C i j - idealUnprojectedEntry i j| ≤ 5 * e := by
    intro i j
    fin_cases i
    · simpa [firstTwoRows] using (hC j).1
    · simpa [firstTwoRows] using (hC j).2
    · simpa [firstTwoRows, idealUnprojectedEntry] using (hC j).2
  simpa only [velocityFirstRhs_firstTwoRows, velocitySecondRhs_firstTwoRows] using
    velocity_rhs_error hΘ he hε hεe hsmall hβ hA hC' hP₀ hQ₀ hP hQ hN

/-- The flux identity is valid with the actual one-sided endpoint derivatives
of packet paths, as well as in the interior. -/
theorem velocity_scalar_flux_within
    {β t u₁ v₁ : ℝ} {U V : ℝ → ℝ} {S : Set ℝ}
    (hU : HasDerivWithinAt U u₁ S t) (hV : HasDerivWithinAt V v₁ S t) :
    HasDerivWithinAt V (-U t + (v₁ + U t)) S t ∧
    HasDerivWithinAt (fun s => (1 + (β * s ^ 2) ^ 2) * (-U s))
      (2 * (1 - β * (β * t ^ 2)) * V t + (1 + (β * t ^ 2) ^ 2) *
        (-u₁ + idealVelocityFirst β t (U t) (V t))) S t := by
  refine ⟨hV.congr_deriv (by ring), ?_⟩
  have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2) (4 * β ^ 2 * t ^ 3) t := by
    convert! ((((hasDerivAt_id t).pow 2).const_mul β).pow 2).const_add 1 using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  apply (hD.hasDerivWithinAt.mul hU.neg).congr_deriv
  have hden : 1 + (β * t ^ 2) ^ 2 ≠ 0 := by positivity
  dsimp [idealVelocityFirst]
  field_simp
  ring

end EulerPacketMovingFrame
