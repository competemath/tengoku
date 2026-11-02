import Tengoku.AlbertFrameTripleInvariants.AlbertLean.DetectorIdentities

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Trace geometry of multiplication commutators

An associative symmetric pairing makes every multiplication operator
self-adjoint. Its operator commutators are therefore skew-adjoint. This
general linear-algebra argument gives trace and orthogonality identities
for the accepted public product, without expanding its coordinates.

These are general identities, not assertions of exceptional specificity.
The final theorem removes the trace-zero premise from the existing detector
factor-three identity for every public triple, with no frame hypotheses.
-/

namespace AlbertLean.Generic.CommutatorGeometry

section LinearAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The commutator of operators self-adjoint for a bilinear pairing is
skew-adjoint. No field, nondegeneracy, or Jordan identity is needed.-/
theorem commutator_skewAdjoint
    (B : V →ₗ[R] V →ₗ[R] R) (A C : V →ₗ[R] V)
    (hA : ∀ u v, B (A u) v = B u (A v))
    (hC : ∀ u v, B (C u) v = B u (C v)) (u v : V) :
    B ((A.comp C - C.comp A) u) v =
      -B u ((A.comp C - C.comp A) v) := by
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [hA (C u) v, hC u (A v), hC (A u) v, hA u (C v)]
  ring

end LinearAlgebra

/-- The accepted trace pairing, linear in its second argument.-/
def tracePairingRight (x : Coord) : Coord →ₗ[ℚ] ℚ where
  toFun := traceForm x
  map_add' y z := by
    rw [← traceN_structuredProduct_eq_traceForm,
      productQBilinear.2.2.1, traceN_add,
      traceN_structuredProduct_eq_traceForm,
      traceN_structuredProduct_eq_traceForm]
  map_smul' a y := by
    change traceForm x (a • y) = a * traceForm x y
    rw [← traceN_structuredProduct_eq_traceForm,
      productQBilinear.2.2.2, traceN_smul,
      traceN_structuredProduct_eq_traceForm]

/-- The accepted trace pairing packaged as a bilinear map.-/
def tracePairing : Coord →ₗ[ℚ] Coord →ₗ[ℚ] ℚ where
  toFun := tracePairingRight
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change traceForm (x + y) z = traceForm x z + traceForm y z
    rw [traceForm_symmetric (x + y) z, traceForm_symmetric x z,
      traceForm_symmetric y z]
    exact (tracePairingRight z).map_add x y
  map_smul' a x := by
    apply LinearMap.ext
    intro z
    change traceForm (a • x) z = a * traceForm x z
    rw [traceForm_symmetric (a • x) z, traceForm_symmetric x z]
    exact (tracePairingRight z).map_smul a x

@[simp] theorem tracePairing_apply (x y : Coord) :
    tracePairing x y = traceForm x y := rfl

/-- Associativity of the trace pairing makes left multiplication self-adjoint.-/
theorem leftMultiplication_selfAdjoint (x z w : Coord) :
    traceForm (structuredProduct x z) w =
      traceForm z (structuredProduct x w) := by
  rw [productCommutative x z, traceFormAssociative]

/-- The commutator `[L_x,L_y]` as an actual linear operator on public coordinates.-/
def innerCommutator (x y : Coord) : Coord →ₗ[ℚ] Coord :=
  (leftMulLinear productQBilinear x).comp (leftMulLinear productQBilinear y) -
    (leftMulLinear productQBilinear y).comp (leftMulLinear productQBilinear x)

@[simp] theorem innerCommutator_apply (x y z : Coord) :
    innerCommutator x y z =
      structuredProduct x (structuredProduct y z) -
        structuredProduct y (structuredProduct x z) := rfl

/-- Multiplication commutators are skew-adjoint for the accepted trace pairing.-/
theorem innerCommutator_skewAdjoint (x y z w : Coord) :
    traceForm (innerCommutator x y z) w =
      -traceForm z (innerCommutator x y w) := by
  exact commutator_skewAdjoint tracePairing
    (leftMulLinear productQBilinear x) (leftMulLinear productQBilinear y)
    (leftMultiplication_selfAdjoint x) (leftMultiplication_selfAdjoint y) z w

@[simp] theorem innerCommutator_one (x y : Coord) :
    innerCommutator x y one = 0 := by
  rw [innerCommutator_apply, (unitLaw y).2, (unitLaw x).2,
    productCommutative x y, sub_self]

/-- A skew-adjoint multiplication commutator annihilates the scalar trace.-/
theorem traceN_innerCommutator (x y z : Coord) :
    traceN (innerCommutator x y z) = 0 := by
  have h := innerCommutator_skewAdjoint x y z one
  rw [innerCommutator_one, traceForm_symmetric _ one,
    traceForm_one_eq_traceN] at h
  have hz : traceForm z 0 = 0 := (tracePairingRight z).map_zero
  rw [hz, neg_zero] at h
  exact h

/-- Every value is orthogonal to its multiplication-commutator image.-/
theorem traceForm_self_innerCommutator (x y z : Coord) :
    traceForm z (innerCommutator x y z) = 0 := by
  have h := innerCommutator_skewAdjoint x y z z
  rw [traceForm_symmetric (innerCommutator x y z) z] at h
  linarith

/-- The framed word is an evaluation of the same linear commutator operator.-/
theorem W0_eq_innerCommutator (X : WitnessTriple) :
    W0 X = innerCommutator X.cE X.cF X.cK := rfl

/-- Factor three holds for every public triple; no separate trace-zero or
frame premise needs to be carried by downstream results.-/
theorem detectorFactorThree_unconditional (X : WitnessTriple) :
    traceCubeDetector X = 3 * cubicNormDetector X := by
  apply detectorFactorThree X
  rw [W0_eq_innerCommutator]
  exact traceN_innerCommutator X.cE X.cF X.cK

end AlbertLean.Generic.CommutatorGeometry
