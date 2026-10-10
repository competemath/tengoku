import Tengoku.Degiorgi.DeGiorgi.Oscillation.BMO

/-!
# Chapter 02: Campanato and Holder Theory

This module packages the Campanato seminorm machinery and the equivalence with
Holder regularity.
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal NNReal Topology

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Campanato Characterization of Hölder Spaces -/

/-- Admissible sub-balls of `Metric.ball x₀ R` for the Campanato seminorm. -/
def CampanatoBall (x₀ : E) (R : ℝ) :=
  {p : E × ℝ // 0 < p.2 ∧ p.2 ≤ R ∧ Metric.ball p.1 p.2 ⊆ Metric.ball x₀ R}

namespace CampanatoBall

def center {x₀ : E} {R : ℝ} (b : CampanatoBall x₀ R) : E := b.1.1

def radius {x₀ : E} {R : ℝ} (b : CampanatoBall x₀ R) : ℝ := b.1.2

end CampanatoBall

/-- The Campanato seminorm on a ball B_R(x₀):
sup_{B ⊆ B_R} ⨍_B |u - (u)_B|. -/
noncomputable def campanatoBallValue
    (u : E → ℝ) (α : ℝ) {x₀ : E} {R : ℝ} (b : CampanatoBall x₀ R) : ℝ :=
  (CampanatoBall.radius b)⁻¹ ^ α *
    ⨍ x in Metric.ball (CampanatoBall.center b) (CampanatoBall.radius b),
      |u x - ⨍ z in Metric.ball (CampanatoBall.center b) (CampanatoBall.radius b), u z| ∂volume

noncomputable def campanatoSeminorm (u : E → ℝ) (x₀ : E) (R : ℝ) (α : ℝ) : ℝ :=
  sSup (Set.range (campanatoBallValue u α (x₀ := x₀) (R := R)))

/-- Expanded local form of a Campanato bound on `Metric.ball x₀ R`. -/
def HasCampanatoBound (u : E → ℝ) (x₀ : E) (R α C : ℝ) : Prop :=
  ∀ b : CampanatoBall x₀ R,
    IntegrableOn u (Metric.ball (CampanatoBall.center b) (CampanatoBall.radius b)) volume ∧
      campanatoBallValue u α b ≤ C

noncomputable def dyadicBallAverage (u : E → ℝ) (x : E) (ρ : ℝ) (n : ℕ) : ℝ :=
  ⨍ z in Metric.ball x (ρ / (2 : ℝ) ^ n), u z ∂volume

/-- A conservative Hölder constant extracted from a Campanato bound. -/
noncomputable def C_campanato_holder (d : ℕ) (α : ℝ) : ℝ :=
  (2 : ℝ) ^ (d + 3) / (1 - (2 : ℝ) ^ (-α))

lemma le_mul_rpow_of_inv_rpow_mul_le
    {a C r α : ℝ} (hr : 0 < r)
    (h : r⁻¹ ^ α * a ≤ C) :
    a ≤ C * r ^ α := by
  have hrpow_nonneg : 0 ≤ r ^ α := Real.rpow_nonneg hr.le _
  have hrpow_ne : r ^ α ≠ 0 := (Real.rpow_pos_of_pos hr α).ne'
  have h' := mul_le_mul_of_nonneg_left h hrpow_nonneg
  calc
    a = (r ^ α * (r⁻¹ ^ α)) * a := by
      rw [Real.inv_rpow hr.le, mul_inv_cancel₀ hrpow_ne, one_mul]
    _ = r ^ α * (r⁻¹ ^ α * a) := by ring
    _ ≤ r ^ α * C := h'
    _ = C * r ^ α := by ring

noncomputable def dyadicBallAverageLimit
    (u : E → ℝ) (x : E) (ρ : ℝ) : ℝ :=
  limUnder atTop (dyadicBallAverage u x ρ)

end DeGiorgi
