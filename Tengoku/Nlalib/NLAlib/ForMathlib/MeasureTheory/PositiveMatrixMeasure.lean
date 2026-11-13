import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Matrix.QuadraticForm
import Tengoku.Seed.MeasureTheory.VectorMeasure.Integral
import Tengoku.Seed.MeasureTheory.Measure.Complex
import Tengoku.Seed.Analysis.Matrix.PosDef

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive matrix-valued measures

A positive matrix measure is a native countably additive vector measure
whose value on every measurable set is positive semidefinite. Entry
complex measures and real quadratic-form signed measures are native
pushforwards along continuous real-linear maps.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace MeasureTheory

variable {α n : Type*} [MeasurableSpace α] [Fintype n] [DecidableEq n]

/-- A countably additive finite-dimensional positive matrix-valued measure.-/
structure PositiveMatrixMeasure (α n : Type*) [MeasurableSpace α] [Fintype n] [DecidableEq n]
    extends VectorMeasure α (Matrix n n ℂ) where
  /-- Values on measurable sets are positive semidefinite.-/
  posSemidef' (s : Set α) (hs : MeasurableSet s) : Matrix.PosSemidef (toVectorMeasure s)

namespace PositiveMatrixMeasure

instance : CoeFun (PositiveMatrixMeasure α n) (fun _ => Set α → Matrix n n ℂ) :=
  ⟨fun μ => μ.toVectorMeasure⟩

/-- Every measurable value of a positive matrix measure is positive semidefinite.
@isnad1 id=possemid.1h4v.s6.f429ac4f3f4d from=translated src=- shape=3a6351d1 vocab=ce343152
-/
theorem posSemidef (μ : PositiveMatrixMeasure α n) (s : Set α) (hs : MeasurableSet s) :
    Matrix.PosSemidef (μ s) := μ.posSemidef' s hs

/-- Every measurable value of a positive matrix measure is Hermitian.
@isnad1 id=ishermit.1h4v.s7.24655fd5b900 from=translated src=- shape=ead13d4c vocab=3d7c9d12
-/
theorem isHermitian (μ : PositiveMatrixMeasure α n) (s : Set α) (hs : MeasurableSet s) :
    Matrix.IsHermitian (μ s) := (μ.posSemidef s hs).isHermitian

/-- A matrix-measure entry is a native complex measure.-/
def entry (μ : PositiveMatrixMeasure α n) (i j : n) : ComplexMeasure α :=
  let L : Matrix n n ℂ →L[ℝ] ℂ :=
    (show Matrix n n ℂ →ₗ[ℝ] ℂ from
      { toFun := fun A => A i j
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }).toContinuousLinearMap
  μ.toVectorMeasure.mapRange L.toAddMonoidHom L.continuous

/--
@isnad1 id=eq.0h6v.s7.86016200825a from=translated src=- shape=70f3f641 vocab=c887594f
-/
@[simp] theorem entry_apply (μ : PositiveMatrixMeasure α n) (i j : n) (s : Set α) :
    μ.entry i j s = μ s i j := rfl

/-- A fixed-vector real quadratic form of a positive matrix measure is
an actual native signed measure, subsequently shown nonnegative.-/
def quadraticForm (μ : PositiveMatrixMeasure α n) (v : n → ℂ) : SignedMeasure α :=
  μ.toVectorMeasure.mapRange (matrixRealQuadraticFormCLM v).toAddMonoidHom
    (matrixRealQuadraticFormCLM v).continuous

/--
@isnad1 id=eq.0h5v.s7.081e480dc743 from=translated src=- shape=4ea2ab66 vocab=4bbb460d
-/
@[simp] theorem quadraticForm_apply (μ : PositiveMatrixMeasure α n) (v : n → ℂ) (s : Set α) :
    μ.quadraticForm v s = (star v ⬝ᵥ (μ s *ᵥ v)).re := rfl

/-- Scalar quadratic-form measures have nonnegative measurable values.
@isnad1 id=le.1h5v.s6.2fd5c27afd59 from=translated src=- shape=d4e8b0e6 vocab=148af369
-/
theorem quadraticForm_nonneg (μ : PositiveMatrixMeasure α n) (v : n → ℂ)
    (s : Set α) (hs : MeasurableSet s) : 0 ≤ μ.quadraticForm v s :=
  (μ.posSemidef s hs).re_dotProduct_nonneg v

end PositiveMatrixMeasure

/-- The continuous real-linear line through a fixed complex matrix.-/
def realMatrixLine (H : Matrix n n ℂ) : ℝ →L[ℝ] Matrix n n ℂ :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight H

omit [Fintype n] [DecidableEq n] in
/--
@isnad1 id=eq.0h3v.s7.822afdb85bda from=translated src=- shape=ef28fc11 vocab=cd6c570a
-/
@[simp] theorem realMatrixLine_apply (H : Matrix n n ℂ) (r : ℝ) :
    realMatrixLine H r = r • H := rfl

/-- A finite real-linear combination of matrix-valued native measures.-/
def matrixMeasureCombination {κ : Type*} [Fintype κ]
    (H : κ → Matrix n n ℂ) (s : κ → SignedMeasure α) :
    VectorMeasure α (Matrix n n ℂ) :=
  ∑ k, (s k).mapRange (realMatrixLine (H k)).toAddMonoidHom (realMatrixLine (H k)).continuous

omit [Fintype n] [DecidableEq n] in
/--
@isnad1 id=eq.0h6v.s7.da38437c75b1 from=translated src=- shape=75e58873 vocab=f2c9b3a9
-/
@[simp] theorem matrixMeasureCombination_apply {κ : Type*} [Fintype κ]
    (H : κ → Matrix n n ℂ) (s : κ → SignedMeasure α) (E : Set α) :
    matrixMeasureCombination H s E = ∑ k, (s k E) • H k := by
  simp [matrixMeasureCombination]
  rfl

/-- The real quadratic-form signed measure of a finite Hermitian combination.-/
def quadraticMeasureCombination {κ : Type*} [Fintype κ]
    (H : κ → Matrix n n ℂ) (s : κ → SignedMeasure α) (v : n → ℂ) : SignedMeasure α :=
  ∑ k, (matrixRealQuadraticFormCLM v (H k)) • s k

omit [DecidableEq n] in
/--
@isnad1 id=eq.0h7v.s7.641f3ed5dd28 from=translated src=- shape=2cc48681 vocab=14d08252
-/
@[simp] theorem quadraticMeasureCombination_apply {κ : Type*} [Fintype κ]
    (H : κ → Matrix n n ℂ) (s : κ → SignedMeasure α) (v : n → ℂ) (E : Set α) :
    quadraticMeasureCombination H s v E =
      (star v ⬝ᵥ (matrixMeasureCombination H s E *ᵥ v)).re := by
  rw [← matrixRealQuadraticFormCLM_apply]
  simp only [matrixMeasureCombination_apply, map_sum, map_smul, smul_eq_mul]
  simp [quadraticMeasureCombination, mul_comm]

omit [Fintype n] [DecidableEq n] in
/-- A real signed combination of Hermitian matrices remains Hermitian
on every set, including nonmeasurable sets.
@isnad1 id=ishermit.1h6v.s7.474f2c681b90 from=translated src=- shape=ca0fac2c vocab=bbd53bf0
-/
theorem isHermitian_matrixMeasureCombination {κ : Type*} [Fintype κ]
    (H : κ → Matrix n n ℂ) (hH : ∀ k, (H k).IsHermitian)
    (s : κ → SignedMeasure α) (E : Set α) :
    Matrix.IsHermitian (matrixMeasureCombination H s E) := by
  rw [matrixMeasureCombination_apply]
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [(hH k).smul (show IsSelfAdjoint (s k E) by simp [isSelfAdjoint_iff]) |>.eq]

/-- Finite Hermitian measure combinations are positive whenever every
real quadratic-form signed measure has nonnegative measurable values.-/
def positiveMatrixMeasureOfCombination {κ : Type*} [Fintype κ]
    (H : κ → Matrix n n ℂ) (hH : ∀ k, (H k).IsHermitian)
    (s : κ → SignedMeasure α)
    (hpos : ∀ v : n → ℂ, ∀ E : Set α, MeasurableSet E →
      0 ≤ quadraticMeasureCombination H s v E) : PositiveMatrixMeasure α n where
  toVectorMeasure := matrixMeasureCombination H s
  posSemidef' E hE := by
    have hHerm := isHermitian_matrixMeasureCombination H hH s E
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
    intro v
    refine RCLike.nonneg_iff.mpr ⟨?_, hHerm.im_star_dotProduct_mulVec_self v⟩
    change 0 ≤ (star v ⬝ᵥ (matrixMeasureCombination H s E *ᵥ v)).re
    rw [← quadraticMeasureCombination_apply]
    exact hpos v E hE

end MeasureTheory
