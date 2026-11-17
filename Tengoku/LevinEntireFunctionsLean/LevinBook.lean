import Tengoku.LevinEntireFunctionsLean.LevinC0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms dense_rays_constant_order` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms radial_iff_c0` (it only prints; the queue checks the axioms of every declaration). -/

/-! Book-facing entry points. These are the constant-positive-order, entire-function
specialization of Levin's dense-ray criterion and the proved C0 bridge.
They do not claim the general proximate-order or sector version of the book. -/
set_option autoImplicit false
noncomputable section
namespace LevinBook
open LevinGrowth

/-- Levin, Chapter III, section 1, p. 142: dense rays imply CRG,
specialized to an entire function of positive constant order and normal type.-/
theorem dense_rays_constant_order {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ)
    (htype : FinitePositiveType f ρ)
    (hdense : Dense {ζ : Direction | ∃ h : ℝ, RayRegular f ρ ζ h}) :
    ∃ h : Direction → ℝ, DiskRegular f ρ h ∧ IsIndicator f ρ h :=
  LevinC0.constantOrderLevin f ρ hf hρ htype hdense

/-- The constant-order radial/C0 equivalence, with all analytic hypotheses
explicit. The construction of the exceptional disks is part of the proof.-/
theorem radial_iff_c0 {f : ℂ → ℂ} {ρ : ℝ} {h : Direction → ℝ}
    (hf : Differentiable ℂ f) (hρ : 0 < ρ)
    (htype : FinitePositiveType f ρ) :
    RadialRegular f ρ h ↔ DiskRegular f ρ h :=
  ⟨LevinC0.diskRegular_of_radialRegular hf hρ htype,
    LevinGrowth.diskRegular_radialRegular⟩

end LevinBook
