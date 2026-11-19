import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyFiniteBlockHighReduction
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyHighSuffixDilationResolved
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.LacunaryFrozenBlockCommonError
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.LacunaryMiddleSparseAdapter
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.LacunaryOscillatoryScaling

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual lacunary frozen-block estimate from the direct quadratic proof

The finite family contains only the paper's modulations. Each block is
compared with a positive dilation of the proved high full-odd suffix maximum.
The two endpoint errors stay outside this family as one common maximal term.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson.LacunaryFrozenBlockDirectResolved

open KrauseLaceyFiniteBlockHighReduction KrauseLaceyHighSuffixDilationResolved
open KrauseLaceySparseDilation KrauseLaceyFullDyadicSparseTransfer
open KrauseLaceyHighFullSuffixResolved LacunaryFrozenBlockCommonError
open LacunaryMiddleRange LacunaryMiddleOperator LacunaryMiddleSparseAdapter
open LacunaryFrozenInputL0 LacunaryMiddleKalton PositiveEndpointOptimization

set_option autoImplicit false

noncomputable section

/-- Exactly the positive normalization parameters of the paper modulation block.-/
def blockDilation (B : ℕ) (τ : ℤ) (i : Fin (Q B τ).card) : ℝ :=
  Real.sqrt (dyadicModulation (modulationBlockIndex B τ i))

/--
@isnad1 id=lt.0h3v.s4.8b5aa9973ca3 from=translated src=- shape=e9092cf1 vocab=10b097f2
-/
theorem blockDilation_pos (B : ℕ) (τ : ℤ) (i : Fin (Q B τ).card) :
    0 < blockDilation B τ i :=
  Real.sqrt_pos.mpr (dyadicModulation_pos _)

def frozenHighSuffixFamily (B : ℕ) (τ : ℤ) : Fin (Q B τ).card → TestOperator :=
  dilatedHighSuffixFamily B (blockDilation B τ) (blockDilation_pos B τ)

/-- The comparison uses the actual frozen input, with no extra cardinality loss.
@isnad1 id=le.0h6v.s6.bf086dd29cf4 from=translated src=- shape=58d97ad6 vocab=ce07ec78
-/
theorem frozenBlockMaxEnorm_le_highSuffixFamily_add_maximal
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) (x : ℝ) :
    frozenBlockMaxEnorm lacunaryAmplitude f k B c τ x ≤
      ENNReal.ofReal (finiteMax (frozenHighSuffixFamily B τ)
        (frozenBlockInputL0 f k B c τ) x) +
      48 * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖frozenBlockInputL0 f k B c τ y‖ₑ) x := by
  classical
  unfold frozenBlockMaxEnorm
  apply Finset.sup_le
  intro m hm
  let i : Fin (Q B τ).card := (Q B τ).equivFin ⟨m, hm⟩
  have hi : modulationBlockIndex B τ i = m := by
    dsimp only [i, modulationBlockIndex]
    simp
  change ‖paperLowDyadicOperator (dyadicModulation m) (dyadicModulation_pos m).ne'
    B (frozenBlockInputL0 f k B c τ) x‖ₑ ≤ _
  have hpoint := enorm_paperLowDyadicOperator_le_dilatedHighSuffix_add_maximal
    (dyadicModulation m) (dyadicModulation_pos m) B
    (frozenBlockInputL0 f k B c τ) x
  apply hpoint.trans
  refine add_le_add ?_ le_rfl
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [frozenHighSuffixFamily, dilatedHighSuffixFamily, blockDilation, hi] using
    le_finiteMax (frozenHighSuffixFamily B τ) (frozenBlockInputL0 f k B c τ) x i

/-- Universal high-family coefficient, independent of input, height, and modulation.-/
def directFrozenHighWeakConstant : ℝ :=
  finiteSparseMaximalUniversalConstant * highFullSuffixSparseConstant

/--
@isnad1 id=le.0h0v.s3.190dc0e50fdc from=translated src=- shape=ff3a10fc vocab=12ca7dac
-/
theorem directFrozenHighWeakConstant_nonneg : 0 ≤ directFrozenHighWeakConstant :=
  mul_nonneg finiteSparseMaximalUniversalConstant_pos.le highFullSuffixSparseConstant_nonneg

/--
@isnad1 id=hasweako.0h2v.s5.e5b998957442 from=translated src=- shape=d3ee3b3f vocab=2dbf07a9
-/
theorem hasWeakOneOneBound_frozenHighSuffixFamily (B : ℕ) (τ : ℤ) :
    HasWeakOneOneBound (directFrozenHighWeakConstant * paperLog 1 (B : ℝ) ^ 2)
      (finiteMax (frozenHighSuffixFamily B τ)) := by
  simpa only [directFrozenHighWeakConstant, frozenHighSuffixFamily, card_Q] using
    hasWeakOneOneBound_dilatedHighSuffixFamily B (blockDilation B τ)
      (blockDilation_pos B τ)

/-- The actual frozen-block weak estimate, now with no outstanding analytic premise.
@isnad1 id=haslogsq.0h3v.s5.0eb85b3d103f from=translated src=- shape=652c73d5 vocab=a0bf71bb
-/
theorem hasLogSquaredFrozenBlockWeakBounds (f : L0Infinity) (B : ℕ → ℕ) (c : ℕ) :
    HasLogSquaredFrozenBlockWeakBounds (f : ℝ → ℂ) B c
      (2 * directFrozenHighWeakConstant + 384) :=
  hasLogSquaredFrozenBlockWeakBounds_of_common_error f B c
    directFrozenHighWeakConstant_nonneg
    (fun k τ ↦ frozenHighSuffixFamily (B k) τ)
    (fun k τ ↦ hasWeakOneOneBound_frozenHighSuffixFamily (B k) τ)
    (fun k τ x ↦ frozenBlockMaxEnorm_le_highSuffixFamily_add_maximal f k (B k) c τ x)

/-- Discharges exactly the remaining input of the paper-facing lacunary endpoint.
@isnad1 id=hasunifo.0h0v.s5.cb558cc1eea5 from=translated src=- shape=edf2ae49 vocab=4c7d888a
-/
theorem hasUniformL0LogSquaredFrozenBlockWeakBounds :
    LacunaryOscillatoryScaling.HasUniformL0LogSquaredFrozenBlockWeakBounds
      (2 * directFrozenHighWeakConstant + 384) :=
  fun f ↦ hasLogSquaredFrozenBlockWeakBounds f PositiveHighHeightEstimate.lacunaryHighCutoff 0

end
end QuadraticCarleson.LacunaryFrozenBlockDirectResolved
