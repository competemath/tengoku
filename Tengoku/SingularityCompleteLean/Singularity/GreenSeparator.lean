import Tengoku.SingularityCompleteLean.Singularity.KilledWalk
import Tengoku.SingularityCompleteLean.Singularity.EntranceOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Green separator identity from finite paths

We identify the killed-path Green kernel with G-F i* G by ℓ² Dirichlet uniqueness.
If A meets every permitted finite jump path from x to y, the killed term is zero,
yielding the genuine separator factorization through G_A⁻¹.

The geometric construction of such a separator is not assumed proved here.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- A meets every finite word of permitted jumps from x to y, including its endpoints.-/
def SeparatesJumpPaths (s : Finset Γ) (A : Set Γ) (x y : Γ) : Prop :=
  ∀ (n : ℕ) (w : WalkWord s n),
    ¬(avoidsBefore s A n x w ∧ walkEndpoint s n x w = y ∧ y ∉ A)

/-- No path surviving killing at A can connect separated endpoints.
@isnad1 id=eq.1h6v.s5.85d8f6cda80e from=translated src=- shape=bff23363 vocab=a442a68e
-/
theorem killedGreen_eq_zero_of_separator (s : Finset Γ) (μ : Γ → ℝ)
    (A : Set Γ) (x y : Γ) (hsep : SeparatesJumpPaths s A x y) :
    killedGreen s μ A x y = 0 := by
  have hz (n : ℕ) : killedWeight s μ A n x y = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    exact ite_eq_right_iff.mpr (fun h => (hsep n w h).elim)
  simp only [killedGreen, hz, tsum_zero]

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ)

/-- The bounded operator whose kernel counts the paths avoiding A.-/
def killedGreenOperator : GroupL2 Γ →L[ℂ] GroupL2 Γ :=
  green (rightMarkov s μ) - (entranceOperator s μ hμ hmass hgap A).comp
    ((supportedRestriction A).comp (green (rightMarkov s μ)))

/-- The operator vanishes on the boundary.
@isnad1 id=eq.3h5v.s15.106ff580fbcc from=translated src=- shape=f60210e1 vocab=3afba02b
-/
theorem killedGreenOperator_boundary (f : GroupL2 Γ) :
    supportedRestriction A (killedGreenOperator s μ hμ hmass hgap A f) = 0 := by
  change supportedRestriction A (green (rightMarkov s μ) f -
    entranceOperator s μ hμ hmass hgap A (supportedRestriction A (green (rightMarkov s μ) f))) = 0
  rw [map_sub, entranceOperator_boundary, sub_self]

/-- Outside A its defect under I-P is the original source.
@isnad1 id=eq.4h6v.s14.a0a0ada57461 from=translated src=- shape=32b8ab78 vocab=7fda5625
-/
theorem killedGreenOperator_defect (f : GroupL2 Γ) {x : Γ} (hx : x ∉ A) :
    (killedGreenOperator s μ hμ hmass hgap A f -
      rightMarkov s μ (killedGreenOperator s μ hμ hmass hgap A f)) x = f x := by
  have h := congrArg (countingEvaluation x) (green_right_inverse (rightMarkov s μ) hgap f)
  simp only [map_sub, countingEvaluation_apply] at h
  change ((green (rightMarkov s μ) f -
      entranceOperator s μ hμ hmass hgap A (supportedRestriction A (green (rightMarkov s μ) f))) -
    rightMarkov s μ (green (rightMarkov s μ) f -
      entranceOperator s μ hμ hmass hgap A (supportedRestriction A (green (rightMarkov s μ) f)))) x = _
  simp only [map_sub, counting_sub_apply]
  rw [entranceOperator_harmonic s μ hμ hmass hgap A _ hx]
  linear_combination h

variable [Countable Γ]

/-- Dirichlet uniqueness identifies the operator with the actual killed path columns.
@isnad1 id=eq.3h5v.s13.3731cc8d3810 from=translated src=- shape=1d18fa70 vocab=ee83687a
-/
theorem killedGreenOperator_delta (y : Γ) :
    killedGreenOperator s μ hμ hmass hgap A (countingDelta y) =
      killedGreenColumn s μ hμ hgap A y := by
  apply dirichlet_eq_of_defect_eq (rightMarkov s μ)
    (rightMarkov_contraction s μ hμ hmass) hgap A
  · intro x hx
    rw [killedGreenColumn_boundary s μ hμ hgap A y hx]
    have h := supportedRestriction_apply A
      (killedGreenOperator s μ hμ hmass hgap A (countingDelta y)) ⟨x, hx⟩
    rw [killedGreenOperator_boundary] at h
    have hz : (0 : GroupL2 Γ) x = 0 := by
      simpa only [countingEvaluation_apply] using (countingEvaluation x).map_zero
    exact h.symm.trans hz
  · intro x hx
    rw [killedGreenOperator_defect s μ hμ hmass hgap A _ hx,
      killedGreenColumn_defect s μ hμ hgap A y hx]

/-- The killed operator has the expected path-counting coefficients.
@isnad1 id=eq.3h6v.s13.4b49fabb03d1 from=translated src=- shape=287d0cde vocab=6c9b7e16
-/
theorem killedGreenOperator_coefficient (x y : Γ) :
    killedGreenOperator s μ hμ hmass hgap A (countingDelta y) x =
      (killedGreen s μ A x y : ℂ) := by
  rw [killedGreenOperator_delta, killedGreenColumn_apply]

/-- Green paths decompose into the killed part and the entrance contribution.
@isnad1 id=eq.3h6v.s15.096adee67ec7 from=translated src=- shape=bf12b7d8 vocab=cc788dcd
-/
theorem walkGreen_entrance_decomposition (x y : Γ) :
    (walkGreen s μ x y : ℂ) = (killedGreen s μ A x y : ℂ) +
      entranceOperator s μ hμ hmass hgap A
        (supportedRestriction A (green (rightMarkov s μ) (countingDelta y))) x := by
  have h := killedGreenOperator_coefficient s μ hμ hmass hgap A x y
  change (green (rightMarkov s μ) (countingDelta y) -
    entranceOperator s μ hμ hmass hgap A
      (supportedRestriction A (green (rightMarkov s μ) (countingDelta y)))) x = _ at h
  rw [counting_sub_apply, ← walkGreen_eq_coefficient s μ hgap] at h
  exact sub_eq_iff_eq_add.mp h

/-- The separator identity in bounded-operator form, without an unjustified matrix double sum.
@isnad1 id=eq.4h6v.s16.4c35e48e1dc0 from=translated src=- shape=764ec7ba vocab=2e4d2d34
-/
theorem walkGreen_separator_factorization (x y : Γ) (hsep : SeparatesJumpPaths s A x y) :
    (walkGreen s μ x y : ℂ) =
      green (rightMarkov s μ) (supportedInclusion A
        ((walkGreenCompression s μ hμ hmass hgap A).symm
          (supportedRestriction A (green (rightMarkov s μ) (countingDelta y))))) x := by
  have h := walkGreen_entrance_decomposition s μ hμ hmass hgap A x y
  rw [killedGreen_eq_zero_of_separator s μ A x y hsep, Complex.ofReal_zero, zero_add] at h
  exact h

/-- The separator formula as an ℓ² pairing of the Green row, M_A, and Green column.
This is the form to which the already proved strong-limit theorem applies.
@isnad1 id=eq.4h6v.s17.fe67820aba25 from=translated src=- shape=3b107c4b vocab=4c77bd2a
-/
theorem walkGreen_separator_pairing (x y : Γ) (hsep : SeparatesJumpPaths s A x y) :
    (walkGreen s μ x y : ℂ) = inner ℂ
      (supportedRestriction A ((green (rightMarkov s μ)).adjoint (countingDelta x)))
      ((walkGreenCompression s μ hμ hmass hgap A).symm
        (supportedRestriction A (green (rightMarkov s μ) (countingDelta y)))) := by
  rw [walkGreen_separator_factorization s μ hμ hmass hgap A x y hsep]
  rw [← countingDelta_inner x]
  change inner ℂ (countingDelta x) (green (rightMarkov s μ) (supportedInclusion A _)) =
    inner ℂ ((supportedInclusion A).toContinuousLinearMap.adjoint
      ((green (rightMarkov s μ)).adjoint (countingDelta x))) _
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  rfl

end Singularity
