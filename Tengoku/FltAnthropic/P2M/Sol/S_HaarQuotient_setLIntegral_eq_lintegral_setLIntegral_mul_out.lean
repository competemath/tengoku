import Tengoku.Seed.MeasureTheory.Group.FundamentalDomain
import Tengoku.FltAnthropic.Definitions.Def_HaarQuotient
import Tengoku.Seed.MeasureTheory.Measure.Haar.Unique
import Tengoku.Seed.Topology.Algebra.Group.ClosedSubgroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

open scoped ENNReal NNReal Pointwise Topology

noncomputable section

namespace HaarDisM65

open HaarQuotient

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private noncomputable def orb (H : Subgroup G) (μH : Measure H) (φ : G → ℝ≥0∞) (g : G) : ℝ≥0∞ :=
  ∫⁻ x : H, φ ((x : G) * g) ∂μH

section Orbit

variable (H : Subgroup G) (μH : Measure H)

end Orbit

section Weight

variable (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

private noncomputable def E : CompactExhaustion G := CompactExhaustion.choice G

private noncomputable def M (n : ℕ) : ℝ≥0∞ :=
  μH (((↑) : H → G) ⁻¹' ((E (G := G) (n + 1) : Set G) * (E (G := G) (n + 1) : Set G)⁻¹))

private noncomputable def coef (n : ℕ) : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ n * (1 + M H μH n)⁻¹

private def V (n : ℕ) : Set G := interior (E (G := G) (n + 1) : Set G)

private def slice (n : ℕ) (g : G) : Set H := {x : H | (x : G) * g ∈ V (G := G) n}

end Weight

section Inv

variable (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

end Inv

section Symmetry

variable (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
  (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

end Symmetry

section Core

variable (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
  (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

end Core

section FDae

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G]

variable {α : Type*} [MeasurableSpace α] {Γ : Type*} [Group Γ] [MulAction Γ α] [Countable Γ]
  [MeasurableConstSMul Γ α]

end FDae

section D2

variable (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
  (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
  (Γ : Subgroup G) (hΓ : Γ ≤ H) [Countable Γ]

private def fibre (S : Set G) (g : G) : Set H := {x : H | (x : G) * g ∈ S}

private def bad (S : Set G) : Set G :=
  {g : G | ∀ γ : Γ, (γ : G) * g ∉ S} ∪ ⋃ γ₁ : Γ, ⋃ γ₂ : Γ, ⋃ (_ : γ₁ ≠ γ₂),
    {g : G | (γ₁ : G) * g ∈ S ∧ (γ₂ : G) * g ∈ S}

end D2

section OuterMeasurability

variable (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

end OuterMeasurability

end HaarDisM65

end
