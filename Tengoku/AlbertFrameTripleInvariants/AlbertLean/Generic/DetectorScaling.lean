import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.CommutatorGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Multihomogeneity of the public detector

The framed word is linear in each of its three encoder inputs.  Consequently
the trace-cube detector is homogeneous of degree three in their product.  The
proof uses only the already established bilinearity of the public product and
linearity of its trace; it does not expand any coordinate.
-/

namespace AlbertLean.Generic.DetectorScaling

/-- Independently rescale all three encoders of a public witness triple.-/
def scaleWitnessTriple (a b c : ℚ) (X : WitnessTriple) : WitnessTriple :=
  ⟨a • X.cE, b • X.cF, c • X.cK⟩

@[simp] theorem scaleWitnessTriple_cE (a b c : ℚ) (X : WitnessTriple) :
    (scaleWitnessTriple a b c X).cE = a • X.cE := rfl

@[simp] theorem scaleWitnessTriple_cF (a b c : ℚ) (X : WitnessTriple) :
    (scaleWitnessTriple a b c X).cF = b • X.cF := rfl

@[simp] theorem scaleWitnessTriple_cK (a b c : ℚ) (X : WitnessTriple) :
    (scaleWitnessTriple a b c X).cK = c • X.cK := rfl

/-- The framed word is trilinear in the three public encoders.-/
theorem W0_scaleWitnessTriple (a b c : ℚ) (X : WitnessTriple) :
    W0 (scaleWitnessTriple a b c X) = (a * b * c) • W0 X := by
  have h₁ :
      structuredProduct (a • X.cE)
          (structuredProduct (b • X.cF) (c • X.cK)) =
        (a * b * c) •
          structuredProduct X.cE (structuredProduct X.cF X.cK) := by
    simp only [productQBilinear.2.1, productQBilinear.2.2.2, smul_smul]
    congr 1
    ring
  have h₂ :
      structuredProduct (b • X.cF)
          (structuredProduct (a • X.cE) (c • X.cK)) =
        (a * b * c) •
          structuredProduct X.cF (structuredProduct X.cE X.cK) := by
    simp only [productQBilinear.2.1, productQBilinear.2.2.2, smul_smul]
    congr 1
    ring
  change
    structuredProduct (a • X.cE)
          (structuredProduct (b • X.cF) (c • X.cK)) -
        structuredProduct (b • X.cF)
          (structuredProduct (a • X.cE) (c • X.cK)) =
      (a * b * c) •
        (structuredProduct X.cE (structuredProduct X.cF X.cK) -
          structuredProduct X.cF (structuredProduct X.cE X.cK))
  rw [h₁, h₂, smul_sub]

/-- The accepted trace pairing is bilinear under independent scalar rescaling.-/
theorem traceForm_smul_smul (a b : ℚ) (x y : Coord) :
    traceForm (a • x) (b • y) = a * b * traceForm x y := by
  calc
    traceForm (a • x) (b • y) =
        traceN (structuredProduct (a • x) (b • y)) :=
      (traceN_structuredProduct_eq_traceForm (a • x) (b • y)).symm
    _ = traceN ((a * b) • structuredProduct x y) := by
      rw [productQBilinear.2.1, productQBilinear.2.2.2, smul_smul]
    _ = a * b * traceForm x y := by
      rw [traceN_smul, traceN_structuredProduct_eq_traceForm]

/-- Rescaling all three encoders multiplies the detector by the cube of the
product of the three scalars.-/
theorem traceCubeDetector_scaleWitnessTriple (a b c : ℚ)
    (X : WitnessTriple) :
    traceCubeDetector (scaleWitnessTriple a b c X) =
      (a * b * c) ^ 3 * traceCubeDetector X := by
  calc
    traceCubeDetector (scaleWitnessTriple a b c X) =
        traceForm ((a * b * c) • W0 X)
          (structuredProduct ((a * b * c) • W0 X)
            ((a * b * c) • W0 X)) := by
      simp only [traceCubeDetector, W0_scaleWitnessTriple]
    _ = traceForm ((a * b * c) • W0 X)
          (((a * b * c) * (a * b * c)) •
            structuredProduct (W0 X) (W0 X)) := by
      rw [productQBilinear.2.1, productQBilinear.2.2.2, smul_smul]
    _ = (a * b * c) ^ 3 * traceCubeDetector X := by
      rw [traceForm_smul_smul]
      simp only [traceCubeDetector]
      ring

/-- The form used by the reconstruction family: keep the first encoder fixed
and rescale the second and third independently.-/
theorem traceCubeDetector_scaleFK (a b : ℚ) (E F K : Coord) :
    traceCubeDetector ⟨E, a • F, b • K⟩ =
      (a * b) ^ 3 * traceCubeDetector ⟨E, F, K⟩ := by
  simpa [scaleWitnessTriple] using
    traceCubeDetector_scaleWitnessTriple 1 a b (⟨E, F, K⟩ : WitnessTriple)

end AlbertLean.Generic.DetectorScaling
