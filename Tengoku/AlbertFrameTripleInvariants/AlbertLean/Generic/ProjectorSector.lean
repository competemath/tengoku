import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.FrameIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar sector formulas for source spectral projectors

A spectral projector is a scalar combination of the unit, an encoder and its
square. On the explicit hyperbolic chart, all spinor-sector pairings of these
combinations are matrix contractions. The vector-sector pairing has exactly
one additional term, the already proved exterior root sum. No public tensor
or complete coordinate multiplication is expanded here.
-/

noncomputable section

namespace AlbertLean.Generic.ProjectorSector

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Residual.TrialitySquares

/-- The three-term expression used by every spectral projector.-/
def sourceCombo (z : JCoord ℚ) (a b c : ℚ) : JCoord ℚ :=
  c • sourceOne + b • z + a • sourceSquare z

def sWeight (z : JCoord ℚ) (a b : ℚ) : ℚ := b + a * (z.d1 + z.d3)
def cWeight (z : JCoord ℚ) (a b : ℚ) : ℚ := b + a * (z.d1 + z.d2)
def vWeight (z : JCoord ℚ) (a b : ℚ) : ℚ := b + a * (z.d2 + z.d3)

/-- The S block of a source polynomial on the hyperbolic plane.-/
def mixedS (s : SCoord ℚ) (c : CCoord ℚ) (u a r z : ℚ) : SCoord ℚ where
  p := u • s.p + (a * r) • c.q
  phi := u • s.phi + (a * z) • c.psi

/-- The C block of the same polynomial.-/
def mixedC (s : SCoord ℚ) (c : CCoord ℚ) (u a r z : ℚ) : CCoord ℚ where
  q := u • c.q + (a * z) • s.p
  psi := u • c.psi + (a * r) • s.phi

/-- The V block retains one normalized triality square.-/
def mixedV (v : VCoord ℚ) (s : SCoord ℚ) (c : CCoord ℚ)
    (u a : ℚ) : VCoord ℚ :=
  u • v + a • normalizedMuV s c

theorem sourceCombo_d1 (z : JCoord ℚ) (a b c : ℚ) :
    (sourceCombo z a b c).d1 =
      c + b * z.d1 + a * (z.d1 ^ 2 + nS z.s + nC z.c) := by
  simp [sourceCombo, sourceOne, sourceSquare_formula]

theorem sourceCombo_d2 (z : JCoord ℚ) (a b c : ℚ) :
    (sourceCombo z a b c).d2 =
      c + b * z.d2 + a * (z.d2 ^ 2 + nC z.c + nV z.v) := by
  simp [sourceCombo, sourceOne, sourceSquare_formula]

theorem sourceCombo_d3 (z : JCoord ℚ) (a b c : ℚ) :
    (sourceCombo z a b c).d3 =
      c + b * z.d3 + a * (z.d3 ^ 2 + nV z.v + nS z.s) := by
  simp [sourceCombo, sourceOne, sourceSquare_formula]

/-- The source square formula reduces the S block to two linear combinations.-/
theorem sourceCombo_s_of_plane (x : JCoord ℚ) (a b c : ℚ)
    (hx : x.v.omega = 0) :
    (sourceCombo x a b c).s =
      mixedS x.s x.c (sWeight x a b) a x.v.r x.v.z := by
  apply SCoord.ext
  · funext i
    fin_cases i <;>
      simp [sourceCombo, sourceSquare_formula, sourceOne, mixedS, sWeight,
        sourceMuS, hx, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply] <;> ring
  · funext i
    fin_cases i <;>
      simp [sourceCombo, sourceSquare_formula, sourceOne, mixedS, sWeight,
        sourceMuS, hx, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply] <;> ring

/-- The source square formula reduces the C block to two linear combinations.-/
theorem sourceCombo_c_of_plane (x : JCoord ℚ) (a b c : ℚ)
    (hx : x.v.omega = 0) :
    (sourceCombo x a b c).c =
      mixedC x.s x.c (cWeight x a b) a x.v.r x.v.z := by
  apply CCoord.ext
  · funext i
    fin_cases i <;>
      simp [sourceCombo, sourceSquare_formula, sourceOne, mixedC, cWeight,
        sourceMuC, hx, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply] <;> ring
  · funext i
    fin_cases i <;>
      simp [sourceCombo, sourceSquare_formula, sourceOne, mixedC, cWeight,
        sourceMuC, hx, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply] <;> ring

theorem sourceCombo_v (x : JCoord ℚ) (a b c : ℚ) :
    (sourceCombo x a b c).v =
      mixedV x.v x.s x.c (vWeight x a b) a := by
  simp only [sourceCombo, add_v, smul_v, sourceSquare_v]
  change c • (0 : VCoord ℚ) + b • x.v +
      a • ((x.d2 + x.d3) • x.v + normalizedMuV x.s x.c) = _
  simp only [smul_zero, zero_add, mixedV, vWeight]
  module

/-- Seven matrix contractions give every S-sector projector pairing.-/
theorem mixedS_pair (s1 s2 : SCoord ℚ) (c1 c2 : CCoord ℚ)
    (u u' a a' r1 z1 r2 z2 : ℚ) :
    BS (mixedS s1 c1 u a r1 z1) (mixedS s2 c2 u' a' r2 z2) =
      u * u' * (momentMatrix s1 s2 c1 c2 0 1 + momentMatrix s1 s2 c1 c2 1 0) +
      u * a' * r2 * momentMatrix s1 s2 c1 c2 0 3 +
      a * z1 * u' * momentMatrix s1 s2 c1 c2 2 1 +
      a * a' * z1 * r2 * momentMatrix s1 s2 c1 c2 2 3 +
      u' * a * r1 * momentMatrix s1 s2 c1 c2 1 2 +
      a' * z2 * u * momentMatrix s1 s2 c1 c2 3 0 +
      a * a' * z2 * r1 * momentMatrix s1 s2 c1 c2 3 2 := by
  simp [BS, mixedS, momentMatrix, evalU]
  ring

/-- Seven matrix contractions give every C-sector projector pairing.-/
theorem mixedC_pair (s1 s2 : SCoord ℚ) (c1 c2 : CCoord ℚ)
    (u u' a a' r1 z1 r2 z2 : ℚ) :
    BC (mixedC s1 c1 u a r1 z1) (mixedC s2 c2 u' a' r2 z2) =
      u * u' * (momentMatrix s1 s2 c1 c2 2 3 + momentMatrix s1 s2 c1 c2 3 2) +
      u * a' * z2 * momentMatrix s1 s2 c1 c2 2 1 +
      a * r1 * u' * momentMatrix s1 s2 c1 c2 0 3 +
      a * a' * r1 * z2 * momentMatrix s1 s2 c1 c2 0 1 +
      u' * a * z1 * momentMatrix s1 s2 c1 c2 3 0 +
      a' * r2 * u * momentMatrix s1 s2 c1 c2 1 2 +
      a * a' * r2 * z1 * momentMatrix s1 s2 c1 c2 1 0 := by
  simp [BC, mixedC, momentMatrix, evalU]
  ring

private theorem BV_add_left (x y z : VCoord ℚ) :
    BV (x + y) z = BV x z + BV y z := by
  simp [BV, BW]
  ring

private theorem BV_add_right (x y z : VCoord ℚ) :
    BV x (y + z) = BV x y + BV x z := by
  simp [BV, BW]
  ring

private theorem BV_smul_left (a : ℚ) (x y : VCoord ℚ) :
    BV (a • x) y = a * BV x y := by
  simp [BV, BW]
  ring

private theorem BV_smul_right (a : ℚ) (x y : VCoord ℚ) :
    BV x (a • y) = a * BV x y := by
  simp [BV, BW]
  ring

private theorem BV_plane_plane (v1 v2 : VCoord ℚ)
    (h1 : v1.omega = 0) (h2 : v2.omega = 0) :
    BV v1 v2 = v1.r * v2.z + v1.z * v2.r := by
  simp [BV, h1, h2, BW]

private theorem BV_plane_mu (v : VCoord ℚ) (hv : v.omega = 0)
    (s : SCoord ℚ) (c : CCoord ℚ) :
    BV v (normalizedMuV s c) =
      v.r * evalU s.phi c.q + v.z * evalU c.psi s.p := by
  simp [BV, hv, normalizedMuV, muV, BW]

private theorem BV_mu_plane (v : VCoord ℚ) (hv : v.omega = 0)
    (s : SCoord ℚ) (c : CCoord ℚ) :
    BV (normalizedMuV s c) v =
      v.r * evalU s.phi c.q + v.z * evalU c.psi s.p := by
  rw [BV_symmetric]
  exact BV_plane_mu v hv s c

/-- Only the V-sector pairing contains determinant-root data, and it contains
exactly their sum with coefficient minus the product of square coefficients.-/
theorem mixedV_pair (v1 v2 : VCoord ℚ)
    (h1 : v1.omega = 0) (h2 : v2.omega = 0)
    (s1 s2 : SCoord ℚ) (c1 c2 : CCoord ℚ) (u u' a a' : ℚ) :
    BV (mixedV v1 s1 c1 u a) (mixedV v2 s2 c2 u' a') =
      u * u' * (v1.r * v2.z + v1.z * v2.r) +
      u * a' * (v1.r * momentMatrix s1 s2 c1 c2 1 3 +
        v1.z * momentMatrix s1 s2 c1 c2 3 1) +
      a * u' * (v2.r * momentMatrix s1 s2 c1 c2 0 2 +
        v2.z * momentMatrix s1 s2 c1 c2 2 0) +
      a * a' * (exteriorQ (momentMatrix s1 s2 c1 c2) -
        deltaX s1 s2 c1 c2 - deltaStarA s1 s2 c1 c2) := by
  simp only [mixedV, BV_add_left, BV_add_right, BV_smul_left, BV_smul_right]
  rw [BV_plane_plane v1 v2 h1 h2,
    BV_plane_mu v1 h1 s2 c2, BV_mu_plane v2 h2 s1 c1]
  have hUV := normalizedUV_exterior_identity s1 s2 c1 c2
  change BV (normalizedMuV s1 c1) (normalizedMuV s2 c2) = _ at hUV
  rw [hUV]
  simp [momentMatrix]
  ring

end AlbertLean.Generic.ProjectorSector
