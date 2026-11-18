import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_integral_integral_integral_comm_of_integrable_prod_prod.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeasureTheory_integral_integral_integral_comm_of_integrable_prod_prod

set_option autoImplicit false

open MeasureTheory Set

/--
@isnad1 id=eq.1h8v.s7.073a80006fa3 from=translated src=- shape=bba93661 vocab=1b1c9397
-/
theorem solution
    {X Y Z E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure Z) [SFinite μ] [SFinite ν] [SFinite ρ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : X × Y × Z → E) (hf : Integrable f (μ.prod (ν.prod ρ))) :
    ∫ x, ∫ y, ∫ z, f (x, y, z) ∂ρ ∂ν ∂μ = ∫ z, ∫ y, ∫ x, f (x, y, z) ∂μ ∂ν ∂ρ := by
  have h1 : ∀ᵐ x ∂μ, Integrable (fun p : Y × Z => f (x, p)) (ν.prod ρ) := hf.prod_right_ae
  have e1 : ∫ x, ∫ y, ∫ z, f (x, y, z) ∂ρ ∂ν ∂μ = ∫ x, ∫ p, f (x, p) ∂(ν.prod ρ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [h1] with x hx
    exact (integral_prod _ hx).symm
  have hf' : Integrable (Function.uncurry fun (x : X) (p : Y × Z) => f (x, p)) (μ.prod (ν.prod ρ)) := hf
  have e2 : ∫ x, ∫ p, f (x, p) ∂(ν.prod ρ) ∂μ = ∫ p, ∫ x, f (x, p) ∂μ ∂(ν.prod ρ) :=
    integral_integral_swap hf'
  have hG : Integrable (fun p : Y × Z => ∫ x, f (x, p) ∂μ) (ν.prod ρ) := hf.integral_prod_right
  rw [e1, e2]
  exact integral_prod_symm _ hG
