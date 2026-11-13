import Tengoku.Nlalib.NLAlib.Matrix.Norms.Core
import Tengoku.Nlalib.NLAlib.ForMathlib.MeasureTheory.CompactSupportDifferentiation
import Tengoku.Seed.Analysis.Calculus.FDeriv.Mul
import Tengoku.Seed.Analysis.Matrix.Order
import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Complex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Actual matrix K-transform Fréchet calculus -/
noncomputable section
open MeasureTheory Set Filter
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Hermitian matrices carry their canonical Borel sigma algebra.-/
instance selfAdjointMatrixMeasurableSpace : MeasurableSpace (selfAdjoint (Matrix n n ℂ)) := borel _

/--
@isnad1 id=borelspa.0h1v.s7.3552f8a3cb72 from=translated src=- shape=69b08264 vocab=bd2b49a2
-/
instance selfAdjointMatrixBorelSpace : BorelSpace (selfAdjoint (Matrix n n ℂ)) := ⟨rfl⟩

/-- The genuine matrix resolvent kernel, defined with the ordinary total
matrix inverse. Analytic hypotheses are needed only on the support.-/
def matrixKResolvent (S T : Matrix n n ℂ) : Matrix n n ℂ := T * (1 + S * T)⁻¹

/-- The real continuous linear derivative of a resolvent kernel.-/
def matrixKResolventDeriv (S T : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  -ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (matrixKResolvent S T) (matrixKResolvent S T)

/-- The actual matrix K-transform with a measure on Hermitian matrices.-/
def matrixKTransform (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ)
    (S : Matrix n n ℂ) : Matrix n n ℂ :=
  (∫ T, matrixKResolvent S T.val ∂ν) - α⁻¹ • S⁻¹

/-- The candidate derivative, as an actual Bochner integral of real CLMs.-/
def matrixKTransformDeriv (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ)
    (S : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  (∫ T, matrixKResolventDeriv S T.val ∂ν) +
    α⁻¹ • ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) S⁻¹ S⁻¹

/-- Ordinary nonsingular matrix inversion has the actual real Fréchet
inverse derivative.
@isnad1 id=hasfderi.1h2v.s14.022c35ed1f35 from=translated src=- shape=cffda28a vocab=e6047961
-/
theorem hasFDerivAt_matrixInverse (S : Matrix n n ℂ) (hS : IsUnit S) :
    HasFDerivAt (fun X : Matrix n n ℂ => X⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) S⁻¹ S⁻¹) S := by
  obtain ⟨u,hu⟩ := hS
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at h
  convert! h using 1
  · funext X
    exact Matrix.nonsing_inv_eq_ringInverse X
  · rw [← hu, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]

/-- The resolvent kernel's genuine Fréchet derivative requires only its
actual solved denominator to be invertible.
@isnad1 id=hasfderi.1h3v.s7.c6ceb9cc9be1 from=translated src=- shape=54c3bcfc vocab=5382ccc7
-/
theorem hasFDerivAt_matrixKResolvent (S T : Matrix n n ℂ)
    (h : IsUnit (1 + S * T)) :
    HasFDerivAt (fun X => matrixKResolvent X T) (matrixKResolventDeriv S T) S := by
  have hlin := ((hasFDerivAt_id (𝕜 := ℝ) S).mul_const' T).const_add 1
  have hi := (hasFDerivAt_matrixInverse (1 + S * T) h).comp S hlin
  have hk := hi.const_mul T
  convert! hk using 1
  apply ContinuousLinearMap.ext
  intro X
  simp only [matrixKResolventDeriv, neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, matrixKResolvent, Matrix.mul_assoc, Matrix.mul_neg]

/-- Joint continuity of the kernel holds at every genuinely admissible pair.
@isnad1 id=continuo.1h3v.s7.cc317fb64d3e from=translated src=- shape=f3b62f5b vocab=2eb254da
-/
theorem continuousAt_matrixKResolvent (S T : Matrix n n ℂ)
    (h : IsUnit (1 + S * T)) :
    ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ => matrixKResolvent p.1 p.2) (S,T) := by
  have hi := (hasFDerivAt_matrixInverse (1 + S * T) h).continuousAt
  have harg : ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ => 1 + p.1 * p.2) (S,T) := by fun_prop
  have hi' : ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ => (1 + p.1 * p.2)⁻¹) (S,T) := hi.comp (f := fun p : Matrix n n ℂ × Matrix n n ℂ => 1 + p.1 * p.2) harg
  have hmul : ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ => p.2 * (1 + p.1 * p.2)⁻¹) (S,T) :=
    continuous_snd.continuousAt.mul hi'
  simpa only [matrixKResolvent] using hmul

/-- The actual derivative kernel is jointly continuous wherever the solved
resolvent denominator is invertible.
@isnad1 id=continuo.1h3v.s8.c506e69a2f52 from=translated src=- shape=0b7c6226 vocab=830d65c3
-/
theorem continuousAt_matrixKResolventDeriv (S T : Matrix n n ℂ)
    (h : IsUnit (1 + S * T)) :
    ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ => matrixKResolventDeriv p.1 p.2) (S,T) := by
  have hr := continuousAt_matrixKResolvent S T h
  have hleft := (ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ)).continuous.continuousAt.comp hr
  exact (hleft.clm_apply hr).neg

/-- Compact support and actual solved denominators give the genuine Fréchet
derivative under the integral. All inverse assumptions are on the support
only. Source: user derivations, equation (F20).
atlas: matrix-k-transform-stability (partial)
@isnad1 id=hasfderi.3h4v.s10.bafb67352068 from=translated src=- shape=e6c2288c vocab=ef076d42
-/
theorem hasFDerivAt_matrixKTransform (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    [IsFiniteMeasure ν] (hν : IsCompact ν.support) (α : ℝ) (S : Matrix n n ℂ)
    (hS : IsUnit S) (hden : ∀ T ∈ ν.support, IsUnit (1 + S * T.val)) :
    HasFDerivAt (matrixKTransform ν α) (matrixKTransformDeriv ν α S) S := by
  let U : Set (Matrix n n ℂ × selfAdjoint (Matrix n n ℂ)) := {p | IsUnit (1 + p.1 * p.2.val)}
  have hproj : Continuous (fun p : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => (p.1,p.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hU : IsOpen U := Units.isOpen.preimage
    (continuous_const.add (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
  have hF : ContinuousOn (fun p : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => matrixKResolvent p.1 p.2.val) U := by
    intro p hp
    have hc : ContinuousAt (fun q : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => matrixKResolvent q.1 q.2.val) p :=
      (continuousAt_matrixKResolvent p.1 p.2.val hp).comp (f := fun q : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => (q.1,q.2.val)) hproj.continuousAt
    exact hc.continuousWithinAt
  have hD : ContinuousOn (fun p : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => matrixKResolventDeriv p.1 p.2.val) U := by
    intro p hp
    have hc : ContinuousAt (fun q : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => matrixKResolventDeriv q.1 q.2.val) p :=
      (continuousAt_matrixKResolventDeriv p.1 p.2.val hp).comp (f := fun q : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => (q.1,q.2.val)) hproj.continuousAt
    exact hc.continuousWithinAt
  have hI := hasFDerivAt_integral_of_compact_support ν hν
    (fun X T => matrixKResolvent X T.val) (fun X T => matrixKResolventDeriv X T.val)
    U hU hF hD (fun p hp => hasFDerivAt_matrixKResolvent p.1 p.2.val hp) S hden
  have hInv := (hasFDerivAt_matrixInverse S hS).const_smul α⁻¹
  convert! hI.sub hInv using 1
  simp only [matrixKTransformDeriv, smul_neg, sub_neg_eq_add]

end NLAlib
