import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.CubicAutomorphism
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Compact.Automorphisms
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.TraceFormLaws
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cubic-and-unit automorphisms of the literal compact source model

This module instantiates the generic recovery theorem for the existing
rational 27-coordinate source definitions.  The only coordinate calculation
is the representation of the already defined `adjoint` by the nondegenerate
trace pairing.  Product preservation then follows abstractly from cubic and
unit preservation.
-/

noncomputable section

namespace CompactOneBit

open scoped BigOperators
open AlbertLean.Generic.CubicAutomorphism

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

theorem pairing_add_right (x y z : Coord) :
    pairing x (y + z) = pairing x y + pairing x z := by
  rw [pairing_eq, pairing_eq, pairing_eq,
    AlbertLean.traceForm_eq_gram, AlbertLean.traceForm_eq_gram,
    AlbertLean.traceForm_eq_gram]
  simp [AlbertLean.traceFormGram, AlbertLean.v]
  ring

theorem pairing_smul_right (a : ℚ) (x y : Coord) :
    pairing x (a • y) = a * pairing x y := by
  rw [pairing_eq, pairing_eq, AlbertLean.traceForm_eq_gram,
    AlbertLean.traceForm_eq_gram]
  simp [AlbertLean.traceFormGram, AlbertLean.v]
  ring

theorem pairing_add_left (x y z : Coord) :
    pairing (x + y) z = pairing x z + pairing y z := by
  rw [pairing_eq, pairing_eq, pairing_eq,
    AlbertLean.traceForm_eq_gram, AlbertLean.traceForm_eq_gram,
    AlbertLean.traceForm_eq_gram]
  simp [AlbertLean.traceFormGram, AlbertLean.v]
  ring

theorem pairing_smul_left (a : ℚ) (x y : Coord) :
    pairing (a • x) y = a * pairing x y := by
  rw [pairing_eq, pairing_eq, AlbertLean.traceForm_eq_gram,
    AlbertLean.traceForm_eq_gram]
  simp [AlbertLean.traceFormGram, AlbertLean.v]
  ring

/-- The literal source trace pairing as a bilinear map.-/
def pairingLinear : Coord →ₗ[ℚ] Coord →ₗ[ℚ] ℚ where
  toFun x :=
    { toFun := pairing x
      map_add' := pairing_add_right x
      map_smul' := by
        intro a y
        simpa [smul_eq_mul] using pairing_smul_right a x y }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    exact pairing_add_left x y z
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    simpa [smul_eq_mul] using pairing_smul_left a x y

@[simp] theorem pairingLinear_apply (x y : Coord) :
    pairingLinear x y = pairing x y := rfl

/-- The explicit signed dual permutation represents coordinate evaluation
against the trace pairing.-/
theorem pairing_dual (f y : Coord) :
    pairing (dual f) y = ∑ j : Fin 27, f j * y j := by
  rw [pairing_eq, AlbertLean.traceForm_eq_gram]
  simp [dual, AlbertLean.traceFormGram, AlbertLean.v,
    Fin.sum_univ_succ]
  ring

/-- Expansion of the cubic differential in the literal ordered basis.-/
theorem polar_add_right (x y z w : Coord) :
    polar x y (z + w) = polar x y z + polar x y w := by
  rw [polar_eq, polar_eq, polar_eq,
    AlbertLean.Generated.cubicPolar_eq_polarForm,
    AlbertLean.Generated.cubicPolar_eq_polarForm,
    AlbertLean.Generated.cubicPolar_eq_polarForm]
  simp [AlbertLean.Generated.polarForm, AlbertLean.v, AlbertLean.q]
  ring

theorem polar_smul_right (a : ℚ) (x y z : Coord) :
    polar x y (a • z) = a * polar x y z := by
  rw [polar_eq, polar_eq,
    AlbertLean.Generated.cubicPolar_eq_polarForm,
    AlbertLean.Generated.cubicPolar_eq_polarForm]
  simp [AlbertLean.Generated.polarForm, AlbertLean.v, AlbertLean.q]
  ring

/-- The cubic polarization, linear in its third argument.-/
def polarRightLinear (x y : Coord) : Coord →ₗ[ℚ] ℚ where
  toFun := polar x y
  map_add' := polar_add_right x y
  map_smul' := by
    intro a z
    simpa [smul_eq_mul] using polar_smul_right a x y z

@[simp] theorem polarRightLinear_apply (x y z : Coord) :
    polarRightLinear x y z = polar x y z := rfl

theorem polar_basis_sum (x y : Coord) :
    (∑ j : Fin 27, (polar x x (Pi.single j 1) / 2) * y j) =
      polar x x y / 2 := by
  calc
    (∑ j : Fin 27, (polar x x (Pi.single j 1) / 2) * y j) =
        ∑ j : Fin 27,
          y j * polarRightLinear x x ((Pi.basisFun ℚ (Fin 27)) j) / 2 := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.basisFun_apply, polarRightLinear_apply]
      ring
    _ = polarRightLinear x x
          (∑ j : Fin 27, y j • (Pi.basisFun ℚ (Fin 27)) j) / 2 := by
      simp only [map_sum, map_smul, smul_eq_mul, div_eq_mul_inv,
        Finset.sum_mul]
    _ = polar x x y / 2 := by
      have hy : (∑ j : Fin 27, y j • (Pi.basisFun ℚ (Fin 27)) j) = y := by
        simpa only [Pi.basisFun_repr] using
          (Pi.basisFun ℚ (Fin 27)).sum_repr y
      rw [hy]
      rfl

/-- The source adjoint is exactly the trace-dual cubic gradient.-/
theorem adjoint_characterization (x y : Coord) :
    pairing (adjoint x) y = polar x x y / 2 := by
  rw [adjoint, pairing_dual]
  exact polar_basis_sum x y

/-- The existing literal cubic, unit, pairing, and adjoint packaged for the
generic recovery theorem.-/
def cubicData : AlbertLean.Generic.CubicAutomorphism.Data ℚ Coord where
  cubic := cubic
  one := unit
  traceForm := pairingLinear
  adjoint := adjoint
  traceForm_nondegenerate := by
    intro x hx
    apply AlbertLean.traceForm_nondegenerate x
    intro y
    simpa only [pairingLinear_apply, pairing_eq] using hx y
  traceForm_formula := by
    intro x y
    rfl
  adjoint_characterization := by
    intro x y
    exact adjoint_characterization x y

@[simp] theorem cubicData_trace (x : Coord) : cubicData.trace x = trace x := rfl

@[simp] theorem cubicData_spurBilinear (x y : Coord) :
    cubicData.spurBilinear x y = polar unit x y := rfl

@[simp] theorem cubicData_cross (x y : Coord) :
    cubicData.cross x y = adjoint (x + y) - adjoint x - adjoint y := rfl

@[simp] theorem cubicData_product (x y : Coord) :
    cubicData.product x y = product x y := rfl

/-- Cubic-and-unit preservation implies source-trace preservation.-/
theorem trace_invariant_of_cubic_unit (g : Coord ≃ₗ[ℚ] Coord)
    (hUnit : g unit = unit) (hCubic : ∀ x, cubic (g x) = cubic x)
    (x : Coord) : trace (g x) = trace x := by
  simpa only [cubicData_trace] using cubicData.map_trace g hUnit hCubic x

/-- Cubic-and-unit preservation implies source-pairing preservation.-/
theorem pairing_invariant_of_cubic_unit (g : Coord ≃ₗ[ℚ] Coord)
    (hUnit : g unit = unit) (hCubic : ∀ x, cubic (g x) = cubic x)
    (x y : Coord) : pairing (g x) (g y) = pairing x y := by
  simpa only [cubicData, pairingLinear_apply] using
    cubicData.map_traceForm g hUnit hCubic x y

/-- Cubic-and-unit preservation implies source-adjoint preservation.-/
theorem adjoint_invariant_of_cubic_unit (g : Coord ≃ₗ[ℚ] Coord)
    (hUnit : g unit = unit) (hCubic : ∀ x, cubic (g x) = cubic x)
    (x : Coord) : g (adjoint x) = adjoint (g x) := by
  exact cubicData.map_adjoint g hUnit hCubic x

/-- Cubic-and-unit preservation implies preservation of the literal source
Springer product.-/
theorem product_invariant_of_cubic_unit (g : Coord ≃ₗ[ℚ] Coord)
    (hUnit : g unit = unit) (hCubic : ∀ x, cubic (g x) = cubic x)
    (x y : Coord) : g (product x y) = product (g x) (g y) := by
  simpa only [cubicData_product] using
    cubicData.map_product g hUnit hCubic x y

/-- A rational-linear bijection preserving the literal source cubic and unit
is an actual compact unital product automorphism.-/
def autOfCubicUnit (g : Coord ≃ₗ[ℚ] Coord)
    (hUnit : g unit = unit) (hCubic : ∀ x, cubic (g x) = cubic x) : Aut where
  linear := g
  unit := hUnit
  product := product_invariant_of_cubic_unit g hUnit hCubic

/-- Detector invariance is inherited from the existing product-automorphism
theorem once the compressed hypotheses have produced an `Aut`.-/
theorem detector_invariant_of_cubic_unit
    (g : Coord ≃ₗ[ℚ] Coord)
    (hUnit : g unit = unit) (hCubic : ∀ x, cubic (g x) = cubic x)
    (X Y : Triple)
    (h : Transports (autOfCubicUnit g hUnit hCubic) X Y) :
    detector Y = detector X :=
  detector_invariant (autOfCubicUnit g hUnit hCubic) X Y h

end CompactOneBit
