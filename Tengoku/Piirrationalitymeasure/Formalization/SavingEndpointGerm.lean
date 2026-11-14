import Tengoku.Piirrationalitymeasure.Formalization.FloorGerm
import Tengoku.Piirrationalitymeasure.Formalization.SavingEndpoints
import Tengoku.Piirrationalitymeasure.Formalization.SavingFloor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual one-sided indicator values at a moving endpoint. -/

namespace PiIrrationality

open Filter Set
open scoped Topology

noncomputable def savingEndpointGradient (v : ℝ × ℝ) (T : SavingEndpointType) : ℝ :=
  savingEndpointShift v T - savingEndpointShift 0 T

noncomputable def savingEndpointVelocity (a b c : ℝ) (v : ℝ × ℝ)
    (T : SavingEndpointType) : ℝ :=
  -savingEndpointGradient v T / savingEndpointSlope a b c T

noncomputable def savingEndpointArgument (a b c : ℝ) (z : ℝ × ℝ)
    (T : SavingEndpointType) (u : ℝ) : ℝ :=
  savingEndpointSlope a b c T * u + savingEndpointShift z T

noncomputable def savingEndpointFloorGerm (a b c : ℝ) (v : ℝ × ℝ)
    (T : SavingEndpointType) (j : ℤ) (side : ℝ) (S : SavingEndpointType) : ℤ :=
  quadraticFloorGerm (savingEndpointArgument a b c 0 S (savingEndpoint a b c 0 T j))
    (savingEndpointSlope a b c S * savingEndpointVelocity a b c v T + savingEndpointGradient v S)
    (savingEndpointSlope a b c S * side)

noncomputable def savingEndpointChiGerm (a b c : ℝ) (v : ℝ × ℝ)
    (T : SavingEndpointType) (j : ℤ) (side : ℝ) : ℝ :=
  if savingEndpointFloorGerm a b c v T j side .Q <
    savingEndpointFloorGerm a b c v T j side .A +
      2 * savingEndpointFloorGerm a b c v T j side .B -
        savingEndpointFloorGerm a b c v T j side .C then 1 else 0

theorem translatedSavingChi_floor_arguments (a b c : ℝ) (z : ℝ × ℝ) (u : ℝ) :
    translatedSavingChi a b c z u =
      if ⌊savingEndpointArgument a b c z .Q u⌋ <
        ⌊savingEndpointArgument a b c z .A u⌋ +
          2 * ⌊savingEndpointArgument a b c z .B u⌋ -
            ⌊savingEndpointArgument a b c z .C u⌋ then 1 else 0 := by
  unfold translatedSavingChi
  rw [savingChi_floor_formula]
  have hA : a * u + z.1 + 1 / 2 = a * u + (1 / 2 + z.1) := by ring
  have hQ : a * u + z.1 + 2 * (b * u + z.2) - c * u + 1 / 2 =
      (a + 2 * b - c) * u + (1 / 2 + z.1 + 2 * z.2) := by ring
  simp only [savingEndpointArgument, savingEndpointSlope, savingEndpointShift, hA, hQ, add_zero]

theorem savingEndpointShift_smul (v : ℝ × ℝ) (s : ℝ) (T : SavingEndpointType) :
    savingEndpointShift (s • v) T = savingEndpointShift 0 T + s * savingEndpointGradient v T := by
  cases T <;> dsimp [savingEndpointShift, savingEndpointGradient] <;> ring

theorem savingEndpoint_eq_base_add_velocity (a b c : ℝ) (v : ℝ × ℝ)
    (T : SavingEndpointType) (j : ℤ) (s : ℝ) :
    savingEndpoint a b c (s • v) T j =
      savingEndpoint a b c 0 T j + s * savingEndpointVelocity a b c v T := by
  have h := savingEndpoint_affine a b c T j 0 v s
  simp only [zero_add] at h
  rw [h]
  unfold savingEndpointVelocity savingEndpointGradient
  ring

theorem savingEndpointArgument_perturbation (a b c : ℝ) (v : ℝ × ℝ)
    (T S : SavingEndpointType) (j : ℤ) (side s : ℝ) :
    savingEndpointArgument a b c (s • v) S
      (savingEndpoint a b c (s • v) T j + side * s ^ 2) =
    savingEndpointArgument a b c 0 S (savingEndpoint a b c 0 T j) +
      s * (savingEndpointSlope a b c S * savingEndpointVelocity a b c v T +
        savingEndpointGradient v S) + s ^ 2 * (savingEndpointSlope a b c S * side) := by
  rw [savingEndpoint_eq_base_add_velocity]
  unfold savingEndpointArgument
  rw [savingEndpointShift_smul]
  ring

theorem savingEndpoint_floor_eventually (a b c : ℝ) (v : ℝ × ℝ)
    (T S : SavingEndpointType) (j : ℤ) (side : ℝ) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      ⌊savingEndpointArgument a b c (s • v) S
        (savingEndpoint a b c (s • v) T j + side * s ^ 2)⌋ =
      savingEndpointFloorGerm a b c v T j side S := by
  simp_rw [savingEndpointArgument_perturbation]
  exact floor_quadratic_eventually _ _ _

theorem savingEndpoint_chi_eventually (a b c : ℝ) (v : ℝ × ℝ)
    (T : SavingEndpointType) (j : ℤ) (side : ℝ) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      translatedSavingChi a b c (s • v) (savingEndpoint a b c (s • v) T j + side * s ^ 2) =
        savingEndpointChiGerm a b c v T j side := by
  filter_upwards [savingEndpoint_floor_eventually a b c v T .A j side,
    savingEndpoint_floor_eventually a b c v T .B j side,
    savingEndpoint_floor_eventually a b c v T .C j side,
    savingEndpoint_floor_eventually a b c v T .Q j side] with s hA hB hC hQ
  rw [translatedSavingChi_floor_arguments, hA, hB, hC, hQ]
  rfl

end PiIrrationality
