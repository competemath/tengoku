import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.StructuredAdjoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms sourceCross_one_left` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceProduct_one_left` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceProductLinear` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceAdjoint_eq_product_square` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms StructuredSourceProductTheorem` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Canonical product recovered from the structured source cubic

The definitions in this file depend only on the locked source cubic and its
trace-dual adjoint.  They do not import generated F0 tensors or comparison
proofs, and the product is not defined by pullback.
-/

namespace AlbertLean.Triality.StructuredProduct

open AlbertLean.CubicNorm
open CoordinateTensor StructuredCubic StructuredAdjoint

variable {K : Type*} [Field K] [CharZero K]

/-- The source cross product, obtained by polarizing the source adjoint.-/
noncomputable def sourceCross (x y : JCoord K) : JCoord K :=
  (sourceRecoveryData (K := K)).cross x y

/-- The source spur bilinear form used in cubic product recovery.-/
def sourceSpurBilinear (x y : JCoord K) : K :=
  sourceTrace x * sourceTrace y - sourceTraceForm x y

/-- The source-defined product, recovered from cubic data without F0 input.-/
noncomputable def sourceProduct (x y : JCoord K) : JCoord K :=
  (sourceRecoveryData (K := K)).product x y

/--
@isnad1 id=eq.0h4v.s6.a5bffbc8f52b from=translated src=- shape=5b7c17ad vocab=cdfdd84a
-/
theorem sourceCross_characterization (x y z : JCoord K) :
    sourceTraceForm (sourceCross x y) z =
      (sourcePolar x y z + sourcePolar y x z) / 2 := by
  simpa [sourceCross, sourceRecoveryData] using
    (sourceRecoveryData (K := K)).cross_characterization x y z

/--
@isnad1 id=eq.0h3v.s5.024f0eb7c4d9 from=translated src=- shape=2bf8e938 vocab=86f34c0c
-/
theorem sourceCross_comm (x y : JCoord K) : sourceCross x y = sourceCross y x :=
  (sourceRecoveryData (K := K)).cross_comm x y

/-- The source unit cross identity, proved by trace-form uniqueness.
@isnad1 id=eq.0h2v.s7.57393a644b5b from=translated src=- shape=cae43e96 vocab=28b94136
-/
theorem sourceCross_one_left (x : JCoord K) :
    sourceCross sourceOne x = sourceTrace x • sourceOne - x := by
  apply sub_eq_zero.mp
  apply sourceTraceForm_nondegenerate
  intro y
  change sourceTraceFormLinear
    (sourceCross sourceOne x - (sourceTrace x • sourceOne - x)) y = 0
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  change sourceTraceForm (sourceCross sourceOne x) y -
      (sourceTrace x * sourceTraceForm sourceOne y - sourceTraceForm x y) = 0
  rw [sourceCross_characterization, sourcePolar_swap_left x sourceOne y,
    sourcePolar_one, sourceTraceForm_one_left]
  rw [sourceTraceForm]
  ring

/--
@isnad1 id=eq.0h2v.s7.28d0111c643a from=translated src=- shape=8d2f2283 vocab=28b94136
-/
theorem sourceCross_one_right (x : JCoord K) :
    sourceCross x sourceOne = sourceTrace x • sourceOne - x := by
  rw [sourceCross_comm]
  exact sourceCross_one_left x

/--
@isnad1 id=eq.0h3v.s9.f948d0fb1cb8 from=translated src=- shape=000b7257 vocab=81f02164
-/
theorem sourceProduct_formula (x y : JCoord K) :
    sourceProduct x y = (2 : K)⁻¹ •
      (sourceCross x y + sourceTrace x • y + sourceTrace y • x -
        sourceSpurBilinear x y • sourceOne) := rfl

/--
@isnad1 id=eq.0h3v.s5.0e65b4bbe35b from=translated src=- shape=2bf8e938 vocab=3cafcf91
-/
theorem sourceProduct_comm (x y : JCoord K) : sourceProduct x y = sourceProduct y x := by
  apply (sourceRecoveryData (K := K)).product_comm
  exact sourceTraceForm_symmetric

/--
@isnad1 id=eq.0h4v.s6.ccafeccaabca from=translated src=- shape=5b155e13 vocab=2bf7b7db
-/
theorem sourceProduct_add_left (x₁ x₂ y : JCoord K) :
    sourceProduct (x₁ + x₂) y = sourceProduct x₁ y + sourceProduct x₂ y :=
  (sourceRecoveryData (K := K)).product_add_left x₁ x₂ y

/--
@isnad1 id=eq.0h4v.s8.7eb46bac8cf8 from=translated src=- shape=018d7bdd vocab=069e7af4
-/
theorem sourceProduct_smul_left (a : K) (x y : JCoord K) :
    sourceProduct (a • x) y = a • sourceProduct x y :=
  (sourceRecoveryData (K := K)).product_smul_left a x y

/--
@isnad1 id=eq.0h4v.s6.821e60d6df93 from=translated src=- shape=b399cc4f vocab=2bf7b7db
-/
theorem sourceProduct_add_right (x y₁ y₂ : JCoord K) :
    sourceProduct x (y₁ + y₂) = sourceProduct x y₁ + sourceProduct x y₂ :=
  (sourceRecoveryData (K := K)).product_add_right sourceTraceForm_symmetric x y₁ y₂

/--
@isnad1 id=eq.0h4v.s8.e54f0fa651c0 from=translated src=- shape=3002dacc vocab=069e7af4
-/
theorem sourceProduct_smul_right (a : K) (x y : JCoord K) :
    sourceProduct x (a • y) = a • sourceProduct x y :=
  (sourceRecoveryData (K := K)).product_smul_right sourceTraceForm_symmetric a x y

/-- The source product as a curried bilinear map.-/
noncomputable def sourceProductLinear :
    JCoord K →ₗ[K] JCoord K →ₗ[K] JCoord K where
  toFun x :=
    { toFun := sourceProduct x
      map_add' := sourceProduct_add_right x
      map_smul' := by intro a y; exact sourceProduct_smul_right a x y }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    exact sourceProduct_add_left x y z
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    exact sourceProduct_smul_left a x y

/--
@isnad1 id=eq.0h3v.s10.39e1880fe4ea from=translated src=- shape=229a5892 vocab=642b3bc2
-/
@[simp] theorem sourceProductLinear_apply (x y : JCoord K) :
    sourceProductLinear x y = sourceProduct x y := rfl

/--
@isnad1 id=eq.0h2v.s5.d8b949c386e2 from=translated src=- shape=6d305448 vocab=4776bc77
-/
@[simp] theorem sourceProduct_one_left (x : JCoord K) :
    sourceProduct sourceOne x = x := by
  rw [sourceProduct_formula, sourceCross_one_left]
  have hS : sourceSpurBilinear (sourceOne : JCoord K) x = 2 * sourceTrace x := by
    simp [sourceSpurBilinear, sourceTraceForm_one_left]
    ring
  rw [hS]
  simp
  module

/--
@isnad1 id=eq.0h2v.s5.e09dcaf97d87 from=translated src=- shape=8e2b6c00 vocab=4776bc77
-/
@[simp] theorem sourceProduct_one_right (x : JCoord K) :
    sourceProduct x sourceOne = x := by
  rw [sourceProduct_comm]
  exact sourceProduct_one_left x

/--
@isnad1 id=eq.0h2v.s7.85f80242f755 from=translated src=- shape=d32fba1d vocab=11d303b2
-/
theorem sourceCross_self_eq_two_adjoint (x : JCoord K) :
    sourceCross x x = (2 : K) • sourceAdjoint x := by
  apply sub_eq_zero.mp
  apply sourceTraceForm_nondegenerate
  intro y
  change sourceTraceFormLinear
    (sourceCross x x - (2 : K) • sourceAdjoint x) y = 0
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  change sourceTraceForm (sourceCross x x) y -
      2 * sourceTraceForm (sourceAdjoint x) y = 0
  rw [sourceCross_characterization, sourceAdjoint_characterization]
  ring

/-- Quadratic adjoint identity recovered from the source product definition.
@isnad1 id=eq.0h2v.s8.1a09d0b7e8cb from=translated src=- shape=a5cc0cbb vocab=6a8c76f7
-/
theorem sourceAdjoint_eq_product_square (x : JCoord K) :
    sourceAdjoint x = sourceProduct x x - sourceTrace x • x + sourceSpur x • sourceOne := by
  have hS : sourceSpurBilinear x x = 2 * sourceSpur x := by
    rw [sourceSpurBilinear, sourceTraceForm, sourceSpurPolar_diagonal]
    ring
  rw [sourceProduct_formula, sourceCross_self_eq_two_adjoint, hS]
  module

/-- Source-only product capstone: unit, commutativity, and bilinearity.
@isnad1 id=and.0h1v.s8.9e4490d19e64 from=translated src=- shape=4a486605 vocab=23601010
-/
theorem StructuredSourceProductTheorem :
    (∀ x : JCoord K, sourceProduct sourceOne x = x) ∧
    (∀ x : JCoord K, sourceProduct x sourceOne = x) ∧
    (∀ x y : JCoord K, sourceProduct x y = sourceProduct y x) ∧
    (∀ x₁ x₂ y : JCoord K,
      sourceProduct (x₁ + x₂) y = sourceProduct x₁ y + sourceProduct x₂ y) ∧
    (∀ (a : K) (x y : JCoord K),
      sourceProduct (a • x) y = a • sourceProduct x y) := by
  exact ⟨sourceProduct_one_left, sourceProduct_one_right, sourceProduct_comm,
    sourceProduct_add_left, sourceProduct_smul_left⟩

end AlbertLean.Triality.StructuredProduct
