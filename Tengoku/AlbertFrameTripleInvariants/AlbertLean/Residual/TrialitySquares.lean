import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.StructuredProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms sourceSquare_formula` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exteriorQ_transpose` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms uV_parameterized_expansion` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms uV_of_mul_eq_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalizedUV_exterior_identity` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TrialitySquaresAndExteriorTheorem` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Triality square blocks and the residual exterior identity

This module records two canonically derived coordinate consequences of the
frozen source data.

First, the square for the source-defined product is obtained from the accepted
trace-dual adjoint.  Its diagonal and `V/S/C` blocks are therefore consequences
of `sourceProduct`, not a new product convention.

Second, the residual `4 x 4` evaluation matrix is used to state the exact
six-term exterior polynomial.  The parameterized identity retains separate
coefficients `alpha` and `beta` and assumes only `alpha * beta = 1`.  The row
with `alpha = beta = 1` is a declared normalization specialization; it is not
derived from the composition identity.

All conclusions are statements about the explicit coordinate chart.  Nothing
here identifies that chart with a global quotient or invariant field.
-/

namespace AlbertLean.Residual.TrialitySquares

open Matrix
open AlbertLean.Triality
open ExteriorSix CoordinateTensor StructuredCubic StructuredAdjoint
  StructuredProduct

variable {K : Type*} [Field K] [CharZero K]

/-! ## Source-product square blocks -/

/-- Square for the canonical product reconstructed from the source cubic.-/
noncomputable def sourceSquare (x : JCoord K) : JCoord K :=
  sourceProduct x x

/-- Solving the accepted adjoint identity for the source-product square.-/
theorem sourceSquare_eq_adjoint_trace_spur (x : JCoord K) :
    sourceSquare x =
      sourceAdjoint x + sourceTrace x • x - sourceSpur x • sourceOne := by
  rw [sourceSquare, sourceAdjoint_eq_product_square]
  module

/-- The complete explicit block formula for a square in source coordinates.-/
theorem sourceSquare_formula (x : JCoord K) :
    sourceSquare x =
      { d1 := x.d1 ^ 2 + nS x.s + nC x.c
        d2 := x.d2 ^ 2 + nC x.c + nV x.v
        d3 := x.d3 ^ 2 + nV x.v + nS x.s
        v := (x.d2 + x.d3) • x.v + normalizedMuV x.s x.c
        s := (x.d1 + x.d3) • x.s + sourceMuS x.c x.v
        c := (x.d1 + x.d2) • x.c + sourceMuC x.v x.s } := by
  rw [sourceSquare_eq_adjoint_trace_spur, sourceAdjoint_eq_explicit]
  apply JCoord.ext
  · change
      (x.d2 * x.d3 - nV x.v) + sourceTrace x * x.d1 - sourceSpur x * 1 =
        x.d1 ^ 2 + nS x.s + nC x.c
    simp [sourceTrace, sourceSpur]
    ring
  · change
      (x.d1 * x.d3 - nS x.s) + sourceTrace x * x.d2 - sourceSpur x * 1 =
        x.d2 ^ 2 + nC x.c + nV x.v
    simp [sourceTrace, sourceSpur]
    ring
  · change
      (x.d1 * x.d2 - nC x.c) + sourceTrace x * x.d3 - sourceSpur x * 1 =
        x.d3 ^ 2 + nV x.v + nS x.s
    simp [sourceTrace, sourceSpur]
    ring
  · change
      (normalizedMuV x.s x.c - x.d1 • x.v) + sourceTrace x • x.v -
          sourceSpur x • (0 : VCoord K) =
        (x.d2 + x.d3) • x.v + normalizedMuV x.s x.c
    simp [sourceTrace]
    module
  · change
      (sourceMuS x.c x.v - x.d2 • x.s) + sourceTrace x • x.s -
          sourceSpur x • (0 : SCoord K) =
        (x.d1 + x.d3) • x.s + sourceMuS x.c x.v
    simp [sourceTrace]
    module
  · change
      (sourceMuC x.v x.s - x.d3 • x.c) + sourceTrace x • x.c -
          sourceSpur x • (0 : CCoord K) =
        (x.d1 + x.d2) • x.c + sourceMuC x.v x.s
    simp [sourceTrace]
    module

@[simp] theorem sourceSquare_d1 (x : JCoord K) :
    (sourceSquare x).d1 = x.d1 ^ 2 + nS x.s + nC x.c := by
  rw [sourceSquare_formula]

@[simp] theorem sourceSquare_d2 (x : JCoord K) :
    (sourceSquare x).d2 = x.d2 ^ 2 + nC x.c + nV x.v := by
  rw [sourceSquare_formula]

@[simp] theorem sourceSquare_d3 (x : JCoord K) :
    (sourceSquare x).d3 = x.d3 ^ 2 + nV x.v + nS x.s := by
  rw [sourceSquare_formula]

@[simp] theorem sourceSquare_v (x : JCoord K) :
    (sourceSquare x).v =
      (x.d2 + x.d3) • x.v + normalizedMuV x.s x.c := by
  rw [sourceSquare_formula]

@[simp] theorem sourceSquare_s (x : JCoord K) :
    (sourceSquare x).s =
      (x.d1 + x.d3) • x.s + sourceMuS x.c x.v := by
  rw [sourceSquare_formula]

@[simp] theorem sourceSquare_c (x : JCoord K) :
    (sourceSquare x).c =
      (x.d1 + x.d2) • x.c + sourceMuC x.v x.s := by
  rw [sourceSquare_formula]

/-! ## Residual evaluation matrix and six-term exterior polynomial -/

/-- The `4 x 4` matrix `M = A X` in row order
`phi₁, phi₂, psi₁, psi₂` and column order `p₁, p₂, q₁, q₂`.-/
def momentMatrix (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    Matrix (Fin 4) (Fin 4) K :=
  ![![evalU s1.phi s1.p, evalU s1.phi s2.p,
      evalU s1.phi c1.q, evalU s1.phi c2.q],
    ![evalU s2.phi s1.p, evalU s2.phi s2.p,
      evalU s2.phi c1.q, evalU s2.phi c2.q],
    ![evalU c1.psi s1.p, evalU c1.psi s2.p,
      evalU c1.psi c1.q, evalU c1.psi c2.q],
    ![evalU c2.psi s1.p, evalU c2.psi s2.p,
      evalU c2.psi c1.q, evalU c2.psi c2.q]]

/-- The exact six-term polynomial `Q(M)` from the residual chart.-/
def exteriorQ (M : Matrix (Fin 4) (Fin 4) K) : K :=
  M 2 0 * M 1 3 + M 3 1 * M 0 2
    + M 1 0 * M 3 2 - M 1 2 * M 3 0
    + M 0 1 * M 2 3 - M 0 3 * M 2 1

/-- Transposition permutes the six monomials of `Q` in pairs.-/
theorem exteriorQ_transpose (M : Matrix (Fin 4) (Fin 4) K) :
    exteriorQ Mᵀ = exteriorQ M := by
  simp [exteriorQ, Matrix.transpose_apply]
  ring

/-- The oriented vector four-bracket in the frozen column order
`p₁, p₂, q₁, q₂`.-/
def deltaX (s1 s2 : SCoord K) (c1 c2 : CCoord K) : K :=
  -BW (wedge2 s1.p c1.q) (wedge2 s2.p c2.q)

/-- The oriented covector four-bracket in the frozen row order
`phi₁, phi₂, psi₁, psi₂`.-/
def deltaStarA (s1 s2 : SCoord K) (c1 c2 : CCoord K) : K :=
  -BW (hodgeStar (dualWedge2 s1.phi c1.psi))
    (hodgeStar (dualWedge2 s2.phi c2.psi))

/-- The parameterized `V`-moment before choosing the relative normalization.-/
def uV (alpha beta : K) (s1 s2 : SCoord K) (c1 c2 : CCoord K) : K :=
  BV (muV alpha beta s1 c1) (muV alpha beta s2 c2)

/-- Direct expansion with both exterior coefficients still visible.-/
theorem uV_parameterized_expansion (alpha beta : K)
    (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    uV alpha beta s1 s2 c1 c2 =
      (momentMatrix s1 s2 c1 c2) 2 0 *
          (momentMatrix s1 s2 c1 c2) 1 3
        + (momentMatrix s1 s2 c1 c2) 3 1 *
          (momentMatrix s1 s2 c1 c2) 0 2
        + alpha * beta *
          ((momentMatrix s1 s2 c1 c2) 1 0 *
              (momentMatrix s1 s2 c1 c2) 3 2
            - (momentMatrix s1 s2 c1 c2) 1 2 *
              (momentMatrix s1 s2 c1 c2) 3 0
            + (momentMatrix s1 s2 c1 c2) 0 1 *
              (momentMatrix s1 s2 c1 c2) 2 3
            - (momentMatrix s1 s2 c1 c2) 0 3 *
              (momentMatrix s1 s2 c1 c2) 2 1)
        - alpha ^ 2 * deltaX s1 s2 c1 c2
        - beta ^ 2 * deltaStarA s1 s2 c1 c2 := by
  simp only [uV, BV, muV, BW_add_left, BW_add_right, BW_smul_left,
    BW_smul_right]
  rw [BW_wedge_hodge_dual, BW_hodgeStar, wedge_dual_pairing]
  simp [momentMatrix, deltaX, deltaStarA]
  ring

/-- Under the composition condition `alpha * beta = 1`, only the two pure
four-bracket coefficients retain the separate normalization parameters.-/
theorem uV_of_mul_eq_one {alpha beta : K} (h : alpha * beta = 1)
    (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    uV alpha beta s1 s2 c1 c2 =
      exteriorQ (momentMatrix s1 s2 c1 c2)
        - alpha ^ 2 * deltaX s1 s2 c1 c2
        - beta ^ 2 * deltaStarA s1 s2 c1 c2 := by
  rw [uV_parameterized_expansion, h]
  simp [exteriorQ]
  ring

/-- The separately declared relative normalization `alpha = beta = 1`.-/
def normalizedUV (s1 s2 : SCoord K) (c1 c2 : CCoord K) : K :=
  BV (normalizedMuV s1 c1) (normalizedMuV s2 c2)

/-- The normalized six-term exterior identity
`U_V = Q(M) - Delta - DeltaStar`.-/
theorem normalizedUV_exterior_identity
    (s1 s2 : SCoord K) (c1 c2 : CCoord K) :
    normalizedUV s1 s2 c1 c2 =
      exteriorQ (momentMatrix s1 s2 c1 c2)
        - deltaX s1 s2 c1 c2 - deltaStarA s1 s2 c1 c2 := by
  simpa [normalizedUV, normalizedMuV, uV] using
    (uV_of_mul_eq_one (alpha := (1 : K)) (beta := (1 : K)) (by simp)
      s1 s2 c1 c2)

/-- Chart-level comparison: the source-product square blocks, transpose
symmetry of `Q`, the parameterized identity, and its declared normalized row.-/
theorem TrialitySquaresAndExteriorTheorem :
    (∀ x : JCoord K,
      sourceSquare x =
        { d1 := x.d1 ^ 2 + nS x.s + nC x.c
          d2 := x.d2 ^ 2 + nC x.c + nV x.v
          d3 := x.d3 ^ 2 + nV x.v + nS x.s
          v := (x.d2 + x.d3) • x.v + normalizedMuV x.s x.c
          s := (x.d1 + x.d3) • x.s + sourceMuS x.c x.v
          c := (x.d1 + x.d2) • x.c + sourceMuC x.v x.s }) ∧
    (∀ M : Matrix (Fin 4) (Fin 4) K, exteriorQ Mᵀ = exteriorQ M) ∧
    (∀ (alpha beta : K), alpha * beta = 1 →
      ∀ (s1 s2 : SCoord K) (c1 c2 : CCoord K),
        uV alpha beta s1 s2 c1 c2 =
          exteriorQ (momentMatrix s1 s2 c1 c2)
            - alpha ^ 2 * deltaX s1 s2 c1 c2
            - beta ^ 2 * deltaStarA s1 s2 c1 c2) ∧
    (∀ (s1 s2 : SCoord K) (c1 c2 : CCoord K),
      normalizedUV s1 s2 c1 c2 =
        exteriorQ (momentMatrix s1 s2 c1 c2)
          - deltaX s1 s2 c1 c2 - deltaStarA s1 s2 c1 c2) := by
  exact ⟨sourceSquare_formula, exteriorQ_transpose,
    fun _ _ h => uV_of_mul_eq_one h, normalizedUV_exterior_identity⟩

end AlbertLean.Residual.TrialitySquares
