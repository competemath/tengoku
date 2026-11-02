import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Solution
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.StructuredCubic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms structuredEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceNorm_agrees_with_f0` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourcePolar_agrees_with_f0` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceSpur_agrees_with_f0` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceTraceForm_agrees_with_f0` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms SourceCubicAgreesWithF0` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Two rational coordinate descriptions of the cubic norm

The adapted coordinate order is specific to this formalization; it is not
asserted to be a verbatim source coordinate map.

The explicit map `structuredEquiv` relates the structured coordinates to the
27-coordinate presentation over `ℚ`. The theorems compare trace, quadratic
coefficient, cubic norm, cubic polarization, and trace pairing. Product
comparison is stated separately for a supplied multiplication.
-/

namespace AlbertLean.Comparison.StructuredF0

open AlbertLean
open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic

set_option maxHeartbeats 50000000
set_option maxRecDepth 100000

/-- The exact project-authored structured-to-F0 flattening order.-/
def structuredToF0 (x : JCoord ℚ) : Coord := fun i ↦
  match i.val with
  | 0 => x.d1
  | 1 => x.d2
  | 2 => x.d3
  | 3 => x.v.r
  | 4 => x.v.z
  | 5 => x.v.omega .i12
  | 6 => x.v.omega .i13
  | 7 => x.v.omega .i14
  | 8 => x.v.omega .i23
  | 9 => x.v.omega .i24
  | 10 => x.v.omega .i34
  | 11 => x.s.p 0
  | 12 => x.s.p 1
  | 13 => x.s.p 2
  | 14 => x.s.p 3
  | 15 => x.s.phi 0
  | 16 => x.s.phi 1
  | 17 => x.s.phi 2
  | 18 => x.s.phi 3
  | 19 => x.c.q 0
  | 20 => x.c.q 1
  | 21 => x.c.q 2
  | 22 => x.c.q 3
  | 23 => x.c.psi 0
  | 24 => x.c.psi 1
  | 25 => x.c.psi 2
  | 26 => x.c.psi 3
  | _ => 0

/-- The inverse unflattening in the same locked order.-/
def f0ToStructured (x : Coord) : JCoord ℚ :=
  { d1 := x 0
    d2 := x 1
    d3 := x 2
    v :=
      { r := x 3
        z := x 4
        omega := fun
          | .i12 => x 5
          | .i13 => x 6
          | .i14 => x 7
          | .i23 => x 8
          | .i24 => x 9
          | .i34 => x 10 }
    s :=
      { p := ![x 11, x 12, x 13, x 14]
        phi := ![x 15, x 16, x 17, x 18] }
    c :=
      { q := ![x 19, x 20, x 21, x 22]
        psi := ![x 23, x 24, x 25, x 26] } }

theorem f0ToStructured_structuredToF0 (x : JCoord ℚ) :
    f0ToStructured (structuredToF0 x) = x := by
  apply JCoord.ext
  · rfl
  · rfl
  · rfl
  · apply VCoord.ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> rfl
  · apply SCoord.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  · apply CCoord.ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl

theorem structuredToF0_f0ToStructured (x : Coord) :
    structuredToF0 (f0ToStructured x) = x := by
  funext i
  fin_cases i <;> rfl

/-- The explicit adapted coordinate linear equivalence, specialized to `ℚ`.-/
def structuredEquiv : JCoord ℚ ≃ₗ[ℚ] Coord where
  toFun := structuredToF0
  invFun := f0ToStructured
  left_inv := f0ToStructured_structuredToF0
  right_inv := structuredToF0_f0ToStructured
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' a x := by
    funext i
    fin_cases i <;> rfl

@[simp] theorem structuredEquiv_apply (x : JCoord ℚ) :
    structuredEquiv x = structuredToF0 x := rfl

@[simp] theorem structuredEquiv_symm_apply (x : Coord) :
    structuredEquiv.symm x = f0ToStructured x := rfl

/-- The frozen structured unit maps to the accepted F0 unit.-/
theorem structuredEquiv_sourceOne :
    structuredEquiv (sourceOne : JCoord ℚ) = one := by
  funext i
  fin_cases i <;> norm_num [structuredEquiv, structuredToF0, sourceOne, one, q]

/-- The source norm includes no hidden constant term.-/
theorem sourceNorm_zero : sourceNorm (0 : JCoord ℚ) = 0 := by
  simp [sourceNorm]

/-- The accepted F0 norm has the matching zero normalization.-/
theorem f0_cubicNorm_zero : cubicNorm (0 : Coord) = 0 := by
  norm_num [cubicNorm, v, q]

/-- Universal equality of the independently frozen source cubic and F0 norm.-/
theorem sourceNorm_agrees_with_f0 (x : JCoord ℚ) :
    sourceNorm x = cubicNorm (structuredEquiv x) := by
  simp [sourceNorm, cubicNorm, structuredEquiv, structuredToF0, v, q,
    nV, nS, nC, triality, Pf, BW, evalU, pairW, wedge2, dualWedge2]
  ring

/-- Universal equality of the source trace and the accepted F0 trace.-/
theorem sourceTrace_agrees_with_f0 (x : JCoord ℚ) :
    sourceTrace x = traceN (structuredEquiv x) := by
  rw [traceN_eq_coords]
  rfl

/--
The source finite difference is exactly the canonical F0 polarization.  The
proof uses both zero-normalization theorems explicitly; no constant term is
silently discarded.-/
theorem sourcePolar_agrees_with_f0 (x y z : JCoord ℚ) :
    sourcePolar x y z =
      cubicPolar (structuredEquiv x) (structuredEquiv y) (structuredEquiv z) := by
  simp only [sourcePolar, cubicPolar, sourceNorm_agrees_with_f0,
    map_add, f0_cubicNorm_zero, sub_zero]

/-- The quadratic source spur agrees with the F0 spur derived from polarization.-/
theorem sourceSpur_agrees_with_f0 (x : JCoord ℚ) :
    sourceSpur x = spurN (structuredEquiv x) := by
  calc
    sourceSpur x = sourcePolar (sourceOne : JCoord ℚ) x x / 2 := by
      rw [sourcePolar_one, sourceSpurPolar_diagonal]
      ring
    _ = cubicPolar (structuredEquiv (sourceOne : JCoord ℚ))
          (structuredEquiv x) (structuredEquiv x) / 2 := by
      rw [sourcePolar_agrees_with_f0]
    _ = cubicPolar one (structuredEquiv x) (structuredEquiv x) / 2 := by
      rw [structuredEquiv_sourceOne]
    _ = spurN (structuredEquiv x) := rfl

/-- Bilinear spur polarization also agrees universally.-/
theorem sourceSpurPolar_agrees_with_f0 (x y : JCoord ℚ) :
    sourceSpurPolar x y = spurBilinear (structuredEquiv x) (structuredEquiv y) := by
  rw [← sourcePolar_one, sourcePolar_agrees_with_f0, structuredEquiv_sourceOne]
  rfl

/-- The nondegenerate source trace form agrees with the accepted F0 trace form.-/
theorem sourceTraceForm_agrees_with_f0 (x y : JCoord ℚ) :
    sourceTraceForm x y = traceForm (structuredEquiv x) (structuredEquiv y) := by
  rw [sourceTraceForm, traceForm, sourceTrace_agrees_with_f0,
    sourceTrace_agrees_with_f0, sourceSpurPolar_agrees_with_f0]

/--
The exact residual product-comparison target.  This is only a proposition
parameterized by a candidate source multiplication: no independently defined
source multiplication is supplied here, and this declaration neither
assumes nor proves the desired equality.  In particular, this file does not
fill the gap by transporting `structuredProduct` through `structuredEquiv`.-/
def StructuredProductAgreesWithF0Statement
    (sourceProduct : JCoord ℚ → JCoord ℚ → JCoord ℚ) : Prop :=
  ∀ x y,
    structuredEquiv (sourceProduct x y) =
      structuredProduct (structuredEquiv x) (structuredEquiv y)

/--
Cubic comparison over `ℚ`: the exact adapted equivalence carries
`T`, `S`, `N`, the complete cubic polarization, and the trace form to F0.-/
theorem SourceCubicAgreesWithF0 :
    sourceNorm (0 : JCoord ℚ) = 0 ∧
    structuredEquiv (sourceOne : JCoord ℚ) = one ∧
    (∀ x : JCoord ℚ,
      sourceTrace x = traceN (structuredEquiv x) ∧
      sourceSpur x = spurN (structuredEquiv x) ∧
      sourceNorm x = cubicNorm (structuredEquiv x)) ∧
    (∀ x y z : JCoord ℚ,
      sourcePolar x y z =
        cubicPolar (structuredEquiv x) (structuredEquiv y) (structuredEquiv z)) ∧
    (∀ x y : JCoord ℚ,
      sourceTraceForm x y = traceForm (structuredEquiv x) (structuredEquiv y)) := by
  exact ⟨sourceNorm_zero, structuredEquiv_sourceOne,
    fun x ↦ ⟨sourceTrace_agrees_with_f0 x, sourceSpur_agrees_with_f0 x,
      sourceNorm_agrees_with_f0 x⟩,
    sourcePolar_agrees_with_f0, sourceTraceForm_agrees_with_f0⟩

end AlbertLean.Comparison.StructuredF0
