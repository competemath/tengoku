import Tengoku.SingularityCompleteLean.Singularity.StripMartinVectors
import Tengoku.SingularityCompleteLean.Singularity.NaimAnconaBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A positive Naïm kernel on opposite finite boundary sides

The normalized restricted Green vectors have unique strong limits determined by
their Martin coordinates. Their compressed-inverse pairing defines a real kernel.
Every pair of approaches to a negative and a positive endpoint converges to it.
No visual-density, Green-distance-comparison, or current hypothesis is used.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical Topology MatrixGroups UpperHalfPlane
namespace Singularity

/-- Supported counting-L² vectors are determined by their coordinates on the support.
@isnad1 id=eq.1h4v.s13.d52892390dca from=translated src=- shape=e5a9c4d2 vocab=5a718caa
-/
theorem supportedL2_ext_on {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (A : Set X) (u v : supportedL2 A)
    (h : ∀ g ∈ A, (u : GroupL2 X) g = (v : GroupL2 X) g) : u = v := by
  apply Subtype.ext
  apply Lp.ext
  apply Filter.Eventually.of_forall
  intro g
  by_cases hg : g ∈ A
  · exact h g hg
  · rw [u.property g hg, v.property g hg]

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

local notation "A" => finiteJumpStrip Γ UpperHalfPlane.I s
local notation "Km" => rayMartinPoint Γ (s.map (Function.Embedding.mk Inv.inv inv_injective))
  (fun g => μ g⁻¹) (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
  (reflectedMarkov_spectral_gap s μ hgap)
local notation "Kp" => rayMartinPoint Γ s μ hpos hgen hgap
local notation "M" => ContinuousLinearEquiv.symm
  (walkGreenCompression s μ (fun g hg => le_of_lt (hpos g hg)) hmass hgap A)

/-- The unique reflected Martin vector on the actual strip.-/
def stripMartinRow (ξ : ℝ) (hξ : ξ ≠ 0) : supportedL2 A :=
  (stripMartinVectors_limit Γ s μ hpos hmass hgen hgap ξ hξ
    (cocompactRaySequence Γ ξ) (cocompactRaySequence_tendsto Γ ξ)).choose

/-- The unique forward Martin vector on the actual strip.-/
def stripMartinColumn (ξ : ℝ) (hξ : ξ ≠ 0) : supportedL2 A :=
  (stripMartinVectors_limit Γ s μ hpos hmass hgen hgap ξ hξ
    (cocompactRaySequence Γ ξ) (cocompactRaySequence_tendsto Γ ξ)).choose_spec.choose

/-- The real compressed-inverse pairing of the actual limiting Martin vectors.-/
def stripNaimKernel (ξ η : ℝ) (hξ : ξ ≠ 0) (hη : η ≠ 0) : ℝ :=
  (inner ℂ (stripMartinRow Γ s μ hpos hmass hgen hgap ξ hξ)
    (M (stripMartinColumn Γ s μ hpos hmass hgen hgap η hη))).re

end Singularity
