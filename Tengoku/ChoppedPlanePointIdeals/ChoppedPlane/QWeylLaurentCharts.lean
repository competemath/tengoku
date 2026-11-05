module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylModule
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.FiniteCechDuality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Concrete cubic coefficient modules on binary coefficient charts

Every chart uses the actual cyclic cubic quotient and the literal transposed
cyclic action.  The unit-chart cross exactness statements are specialized to
these modules; the cubic relation and unit identities are verified here.
-/

noncomputable section
namespace ChoppedPlane.QWeyl
set_option maxHeartbeats 1000000

open MvPolynomial SymmetricDerivative FiniteCech

variable {K : Type*} [Field K]
variable {A : Type*} [CommRing A] [Algebra K A]

/-- The dual cyclic operator after a binary coefficient change.-/
def chartDualZ (φ : BinaryRing K →ₐ[K] A) (q : K) (s : CubicProfile) :
    Module.End A (Fin 3 → A) :=
  cyclicZDual (fun i => φ (profileFactors q s i))

/--
@isnad1 id=eq.1h5v.s10.c029e13acfca from=translated src=- shape=0a7f8fb1 vocab=eb57401e
-/
theorem chartDualZ_cube (φ : BinaryRing K →ₐ[K] A) (q : K)
    (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    chartDualZ φ q s ^ 3 = φ (binaryCubic K) • 1 := by
  rw [chartDualZ, cyclicZDual_cube]
  congr 1
  rw [← map_mul, ← map_mul, profileFactors_product q hq s]

abbrev ChartCubicRing (φ : BinaryRing K →ₐ[K] A) :=
  CyclicCubicRing A (φ (binaryCubic K))

/-- The concrete coefficient module, with its quotient-ring action.-/
abbrev chartDualModuleStructure (φ : BinaryRing K →ₐ[K] A) (q : K)
    (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :=
  cyclicModuleStructure (φ (binaryCubic K)) (chartDualZ φ q s)
    (chartDualZ_cube φ q hq s)

def chartU (φ : BinaryRing K →ₐ[K] A) : ChartCubicRing φ :=
  cyclicCoefficientHom (φ (binaryCubic K)) (φ (binaryU K))

def chartV (φ : BinaryRing K →ₐ[K] A) : ChartCubicRing φ :=
  cyclicCoefficientHom (φ (binaryCubic K)) (φ (binaryV K))

def chartZ (φ : BinaryRing K →ₐ[K] A) : ChartCubicRing φ :=
  cyclicRoot (φ (binaryCubic K))

def chartCoefficient (φ : BinaryRing K →ₐ[K] A) (a : A) : ChartCubicRing φ :=
  cyclicCoefficientHom (φ (binaryCubic K)) a

/--
@isnad1 id=eq.1h4v.s9.342a84905cbd from=translated src=- shape=18bda5cb vocab=1a0b49bf
-/
theorem chartU_unit (φ : BinaryRing K →ₐ[K] A) (a : A)
    (hu : φ (binaryU K) * a = 1) : chartU φ * chartCoefficient φ a = 1 := by
  change cyclicCoefficientHom _ _ * cyclicCoefficientHom _ _ = 1
  rw [← map_mul, hu, map_one]

/--
@isnad1 id=eq.1h4v.s9.3a23ab10585a from=translated src=- shape=18bda5cb vocab=5ef66d35
-/
theorem chartV_unit (φ : BinaryRing K →ₐ[K] A) (a : A)
    (hv : φ (binaryV K) * a = 1) : chartV φ * chartCoefficient φ a = 1 := by
  change cyclicCoefficientHom _ _ * cyclicCoefficientHom _ _ = 1
  rw [← map_mul, hv, map_one]

/-- Actual coordinates for the `u` chart's cyclic quotient.-/
def chartCrossPresentationU (φ : BinaryRing K →ₐ[K] A) (a : A)
    (hu : φ (binaryU K) * a = 1) :
    CrossPresentation (chartU φ) (chartV φ) (chartZ φ) :=
  crossPresentationU (chartU φ) (chartV φ) (chartZ φ)
    (chartCoefficient φ a) (chartU_unit φ a hu)

/-- Actual coordinates for the `v` chart's cyclic quotient.-/
def chartCrossPresentationV (φ : BinaryRing K →ₐ[K] A) (a : A)
    (hv : φ (binaryV K) * a = 1) :
    CrossPresentation (chartU φ) (chartV φ) (chartZ φ) :=
  crossPresentationV (chartU φ) (chartV φ) (chartZ φ)
    (chartCoefficient φ a) (chartV_unit φ a hv)

def chartLinearForm (φ : BinaryRing K →ₐ[K] A) : Fin 3 → ChartCubicRing φ :=
  ![chartU φ, chartV φ, chartZ φ]

def chartCrossMatrix (φ : BinaryRing K →ₐ[K] A) :
    Matrix (Fin 3) (Fin 3) (ChartCubicRing φ) :=
  crossMatrix (chartU φ) (chartV φ) (chartZ φ)

/-- The local cross quotient for the actual dual cyclic module, on `u`.
@isnad1 id=iff.2h7v.s15.f926bbd42a75 from=translated src=- shape=01aa7576 vocab=0daa4e9e
-/
theorem chart_dual_cross_kernel_u
    (φ : BinaryRing K →ₐ[K] A) (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (a : A) (hu : φ (binaryU K) * a = 1) :
    letI := chartDualModuleStructure φ q hq s
    ∀ P : AuxTensor (R := ChartCubicRing φ) (M := Fin 3 → A),
      tensorChange (chartCrossMatrix φ) P = 0 ↔
        P ∈ LinearMap.range (tensorMultiplyLinear (chartLinearForm φ)) := by
  let _ := chartDualModuleStructure φ q hq s
  exact (chartCrossPresentationU φ a hu).cross_kernel

/-- The same local exactness calculation on `v`.
@isnad1 id=iff.2h7v.s15.885001b4b42f from=translated src=- shape=01aa7576 vocab=dfe93dba
-/
theorem chart_dual_cross_kernel_v
    (φ : BinaryRing K →ₐ[K] A) (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (a : A) (hv : φ (binaryV K) * a = 1) :
    letI := chartDualModuleStructure φ q hq s
    ∀ P : AuxTensor (R := ChartCubicRing φ) (M := Fin 3 → A),
      tensorChange (chartCrossMatrix φ) P = 0 ↔
        P ∈ LinearMap.range (tensorMultiplyLinear (chartLinearForm φ)) := by
  let _ := chartDualModuleStructure φ q hq s
  exact (chartCrossPresentationV φ a hv).cross_kernel

/-- Homogeneous local exactness for the actual cyclic module on `u`.
@isnad1 id=ex.4h8v.s15.7538aed59de8 from=translated src=- shape=f146d0fc vocab=7b924c4d
-/
theorem chart_dual_cross_kernel_homogeneous_u
    (φ : BinaryRing K →ₐ[K] A) (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (a : A) (hu : φ (binaryU K) * a = 1) (n : ℕ) :
    letI := chartDualModuleStructure φ q hq s
    ∀ P : AuxTensor (R := ChartCubicRing φ) (M := Fin 3 → A),
      TensorHomogeneous (n + 1) P → tensorChange (chartCrossMatrix φ) P = 0 →
      ∃ Q, TensorHomogeneous n Q ∧ tensorMultiplyLinear (chartLinearForm φ) Q = P := by
  let _ := chartDualModuleStructure φ q hq s
  intro P hP hcross
  exact (chartCrossPresentationU φ a hu).cross_kernel_homogeneous hP hcross

/-- Homogeneous local exactness for the actual cyclic module on `v`.
@isnad1 id=ex.4h8v.s15.2530209c45d3 from=translated src=- shape=f146d0fc vocab=393f8b9f
-/
theorem chart_dual_cross_kernel_homogeneous_v
    (φ : BinaryRing K →ₐ[K] A) (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (a : A) (hv : φ (binaryV K) * a = 1) (n : ℕ) :
    letI := chartDualModuleStructure φ q hq s
    ∀ P : AuxTensor (R := ChartCubicRing φ) (M := Fin 3 → A),
      TensorHomogeneous (n + 1) P → tensorChange (chartCrossMatrix φ) P = 0 →
      ∃ Q, TensorHomogeneous n Q ∧ tensorMultiplyLinear (chartLinearForm φ) Q = P := by
  let _ := chartDualModuleStructure φ q hq s
  intro P hP hcross
  exact (chartCrossPresentationV φ a hv).cross_kernel_homogeneous hP hcross

variable [CharZero K]

/-- Every homogeneous local derivative kernel has a cross representative.
@isnad1 id=ex.4h8v.s15.21c1446721e2 from=translated src=- shape=fc3c2fda vocab=3eeb0848
-/
theorem chart_dual_cross_range_homogeneous_u
    (φ : BinaryRing K →ₐ[K] A) (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (a : A) (hu : φ (binaryU K) * a = 1) (n : ℕ) :
    letI := chartDualModuleStructure φ q hq s
    ∀ P : AuxTensor (R := ChartCubicRing φ) (M := Fin 3 → A),
      TensorHomogeneous n P → tensorDirectional (chartLinearForm φ) P = 0 →
      ∃ Q, TensorHomogeneous n Q ∧ tensorChange (chartCrossMatrix φ) Q = P := by
  let _ := chartDualModuleStructure φ q hq s
  intro P hP hdP
  exact (chartCrossPresentationU φ a hu).cross_range_homogeneous (K := K) hP hdP

/--
@isnad1 id=ex.4h8v.s15.f0cd9e81f84a from=translated src=- shape=fc3c2fda vocab=a5eb6ac1
-/
theorem chart_dual_cross_range_homogeneous_v
    (φ : BinaryRing K →ₐ[K] A) (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (a : A) (hv : φ (binaryV K) * a = 1) (n : ℕ) :
    letI := chartDualModuleStructure φ q hq s
    ∀ P : AuxTensor (R := ChartCubicRing φ) (M := Fin 3 → A),
      TensorHomogeneous n P → tensorDirectional (chartLinearForm φ) P = 0 →
      ∃ Q, TensorHomogeneous n Q ∧ tensorChange (chartCrossMatrix φ) Q = P := by
  let _ := chartDualModuleStructure φ q hq s
  intro P hP hdP
  exact (chartCrossPresentationV φ a hv).cross_range_homogeneous (K := K) hP hdP

end ChoppedPlane.QWeyl
