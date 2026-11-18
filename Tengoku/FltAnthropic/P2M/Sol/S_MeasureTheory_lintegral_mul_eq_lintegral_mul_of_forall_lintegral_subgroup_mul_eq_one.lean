import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_lintegral_subgroup_mul_eq_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_lintegral_subgroup_mul_eq_one

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Admissible

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
variable (H : Subgroup G)

private theorem measurable_coe_mul : Measurable (fun p : H × G => (p.1 : G) * p.2) :=
  (measurable_subtype_coe.comp measurable_fst).mul measurable_snd

variable {H}

section Lintegral

variable [MeasurableInv G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]

private theorem lintegral_mul_eq_of_invariant (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ ρ' : G → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρ'1 : ∀ g, ∫⁻ n : H, ρ' ((n : G) * g) ∂μH = 1)
    {φ : G → ℝ≥0∞} (hφ : AEMeasurable φ μ) (hφinv : ∀ (n : H) (g : G), φ ((n : G) * g) = φ g) :
    ∫⁻ g, φ g * ρ g ∂μ = ∫⁻ g, φ g * ρ' g ∂μ := by

  have hmeas : AEMeasurable (fun p : H × G => φ p.2 * ρ p.2 * ρ' ((p.1 : G) * p.2)) (μH.prod μ) :=
    (hφ.comp_snd.mul (hρ.comp measurable_snd).aemeasurable).mul (hρ'.comp (measurable_coe_mul H)).aemeasurable
  calc ∫⁻ g, φ g * ρ g ∂μ
      = ∫⁻ g, ∫⁻ n : H, φ g * ρ g * ρ' ((n : G) * g) ∂μH ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul (φ g * ρ g) (f := fun n : H => ρ' ((n : G) * g))
          (hρ'.comp (measurable_subtype_coe.mul_const g)), hρ'1 g, mul_one]
    _ = ∫⁻ n : H, ∫⁻ g, φ g * ρ g * ρ' ((n : G) * g) ∂μ ∂μH :=
        lintegral_lintegral_swap hmeas.prod_swap
    _ = ∫⁻ n : H, ∫⁻ g, φ g * ρ ((n : G)⁻¹ * g) * ρ' g ∂μ ∂μH := by
        refine lintegral_congr fun n => ?_

        rw [← lintegral_mul_left_eq_self (fun g => φ g * ρ ((n : G)⁻¹ * g) * ρ' g) (n : G)]
        refine lintegral_congr fun g => ?_
        simp only [inv_mul_cancel_left, hφinv n g]
    _ = ∫⁻ g, ∫⁻ n : H, φ g * ρ ((n : G)⁻¹ * g) * ρ' g ∂μH ∂μ := by
        refine (lintegral_lintegral_swap ?_).symm
        exact ((hφ.comp_snd.mul
          (hρ.comp ((measurable_subtype_coe.comp measurable_fst).inv.mul measurable_snd)).aemeasurable).mul
            (hρ'.comp measurable_snd).aemeasurable).prod_swap
    _ = ∫⁻ g, φ g * ρ' g ∂μ := by
        refine lintegral_congr fun g => ?_
        have h1 : ∫⁻ n : H, ρ ((n : G)⁻¹ * g) ∂μH = 1 := by
          rw [← hρ1 g, ← hinv (fun n : H => ρ ((n : G) * g))]
          simp only [Subgroup.coe_inv]
        calc ∫⁻ n : H, φ g * ρ ((n : G)⁻¹ * g) * ρ' g ∂μH
            = ∫⁻ n : H, (φ g * ρ' g) * ρ ((n : G)⁻¹ * g) ∂μH := by
              refine lintegral_congr fun n => ?_; ring
          _ = φ g * ρ' g := by
              rw [lintegral_const_mul (φ g * ρ' g) (f := fun n : H => ρ ((n : G)⁻¹ * g))
                (hρ.comp (measurable_subtype_coe.inv.mul_const g)), h1, mul_one]

end Lintegral

section Descent

variable (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end Descent

section Bochner

variable [MeasurableInv G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end Bochner

end Admissible

end

theorem solution
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (H : Subgroup G) (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ] (μH : Measure H) [SFinite μH]
    (hinv : ∀ f : H → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂μH = ∫⁻ n, f n ∂μH)
    {ρ ρ' : G → ℝ≥0∞} (hρ : Measurable ρ) (hρ' : Measurable ρ')
    (hρ1 : ∀ g, ∫⁻ n : H, ρ ((n : G) * g) ∂μH = 1) (hρ'1 : ∀ g, ∫⁻ n : H, ρ' ((n : G) * g) ∂μH = 1)
    {φ : G → ℝ≥0∞} (hφ : AEMeasurable φ μ) (hφinv : ∀ (n : H) (g : G), φ ((n : G) * g) = φ g) :
    ∫⁻ g, φ g * ρ g ∂μ = ∫⁻ g, φ g * ρ' g ∂μ :=
  Admissible.lintegral_mul_eq_of_invariant μ μH hinv hρ hρ' hρ1 hρ'1 hφ hφinv

