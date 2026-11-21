import Tengoku.RainichKaluzaReconstruction.RainichKaluza.CanonicalMaxwellTwoForm
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
import Tengoku.Seed.Tactic.NoncommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lorentz-frame transport of the Maxwell seed

The canonical two-form is useful geometrically only if it transports correctly
between Lorentz frames.  This file proves the relevant matrix covariance
identities.  A frame matrix `L` and its inverse `K` are supplied with the
explicit Lorentz identities needed by the proof; bundle smoothness and the
existence of such frames are separate geometric hypotheses.
-/

namespace RainichKaluza

open scoped Matrix
open Matrix

abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℝ

/-- Diagonal Minkowski metric in the selected frame.-/
def minkowskiMetric : Matrix4 :=
  !![-1, 0, 0, 0;
      0, 1, 0, 0;
      0, 0, 1, 0;
      0, 0, 0, 1]

/-- Determinant of the canonical Lorentz metric.-/
theorem minkowskiMetric_det : Matrix.det minkowskiMetric = -1 := by
  rw [show minkowskiMetric = Matrix.diagonal minkowskiSign by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [minkowskiMetric, minkowskiSign]]
  rw [Matrix.det_diagonal]
  simp [minkowskiSign, Fin.prod_univ_succ]

/-- **Dual-coframe metric identity.** If the columns of `E` are
pseudo-orthonormal for the coordinate metric `G`, then the true dual coframe
`E⁻¹` reconstructs `G` by congruence from the Minkowski metric.-/
theorem inverseFrame_metric_of_frame_metric
    (E G : Matrix4) (hframe : Eᵀ * G * E = minkowskiMetric) :
    E⁻¹ᵀ * minkowskiMetric * E⁻¹ = G := by
  have hdet : Matrix.det E ≠ 0 := by
    intro hzero
    have hd := congrArg Matrix.det hframe
    simp [Matrix.det_mul, hzero, minkowskiMetric_det] at hd
  have hunit : IsUnit (Matrix.det E) := isUnit_iff_ne_zero.mpr hdet
  have hleft : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E hunit
  have hright : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E hunit
  have hleftT : E⁻¹ᵀ * Eᵀ = 1 := by
    rw [← Matrix.transpose_mul, hright, Matrix.transpose_one]
  calc
    E⁻¹ᵀ * minkowskiMetric * E⁻¹ =
        E⁻¹ᵀ * (Eᵀ * G * E) * E⁻¹ := by rw [hframe]
    _ = (E⁻¹ᵀ * Eᵀ) * G * (E * E⁻¹) := by noncomm_ring
    _ = G := by rw [hleftT, hright, Matrix.one_mul, Matrix.mul_one]

/-- Matrix form of the ordinary (unhalved) mixed Maxwell stress for an
antisymmetric covariant two-tensor. For an antisymmetric `F`, `-tr(GFGF)` is
its quadratic invariant. The curvature seed represents
`H = exp(a phi / 2) F_physical / sqrt(2)`, so this stress equals the EMD Ricci
residual.-/
noncomputable def matrixMaxwellStress (G F : Matrix4) : Matrix4 :=
  let core := G * F * G * F
  (-core) + (1 / 4 * Matrix.trace core) • (1 : Matrix4)

/-- Covariant two-form transport by a frame matrix.-/
def transportTwoForm (L F : Matrix4) : Matrix4 :=
  Lᵀ * F * L

/-- Mixed-endomorphism transport by a frame and supplied inverse.-/
def transportMixed (K X L : Matrix4) : Matrix4 :=
  K * X * L

set_option maxHeartbeats 800000 in
/-- The trace formula agrees with the component Maxwell stress on the
canonical two-form.-/
theorem matrixMaxwellStress_canonical (E B : ℝ) :
    matrixMaxwellStress minkowskiMetric (canonicalMaxwellTwoForm E B) =
      canonicalMaxwellStress E B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixMaxwellStress, minkowskiMetric, canonicalMaxwellTwoForm,
      canonicalMaxwellStress, canonicalStressMagnitude,
      Matrix.trace, Fin.sum_univ_succ] <;> ring

/-- Coordinate normal form of an arbitrary real two-form in a Lorentz
orthonormal frame.  The first three entries are its electric components and
the last three its magnetic components.-/
def lorentzSkewTwoForm4
    (e1 e2 e3 b1 b2 b3 : ℝ) : Matrix4 :=
  !![ 0,  e1,  e2,  e3;
     -e1,  0,  b3, -b2;
     -e2, -b3,  0,  b1;
     -e3,  b2, -b1,   0]

/-- Every skew four-by-four matrix has the displayed six-component normal
form.-/
theorem eq_lorentzSkewTwoForm4_of_transpose_eq_neg
    (F : Matrix4) (hF : Fᵀ = -F) :
    F = lorentzSkewTwoForm4
      (F 0 1) (F 0 2) (F 0 3) (F 2 3) (F 3 1) (F 1 2) := by
  have hcomp (i j : Fin 4) : F j i = -F i j := by
    have h := congrArg (fun M : Matrix4 => M i j) hF
    simpa [Matrix.transpose_apply] using h
  have h00 : F 0 0 = 0 := by nlinarith [hcomp 0 0]
  have h11 : F 1 1 = 0 := by nlinarith [hcomp 1 1]
  have h22 : F 2 2 = 0 := by nlinarith [hcomp 2 2]
  have h33 : F 3 3 = 0 := by nlinarith [hcomp 3 3]
  have h10 : F 1 0 = -F 0 1 := hcomp 0 1
  have h20 : F 2 0 = -F 0 2 := hcomp 0 2
  have h30 : F 3 0 = -F 0 3 := hcomp 0 3
  have h21 : F 2 1 = -F 1 2 := hcomp 1 2
  have h13 : F 1 3 = -F 3 1 := hcomp 3 1
  have h32 : F 3 2 = -F 2 3 := hcomp 2 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzSkewTwoForm4, h00, h11, h22, h33,
      h10, h20, h30, h21, h13, h32]

/-- **Canonical Maxwell stress-fibre theorem.** A real two-form whose
positive non-null Maxwell stress is the canonical residual has no components
outside the two canonical principal-plane area forms. Its remaining electric
and magnetic amplitudes lie on the circle `E²+B²=2q`.

This is the converse algebraic Rainich statement missing from mere forward
duality invariance.-/
theorem matrixMaxwellStress_eq_canonicalResidual_iff_amplitudeCircle
    (F : Matrix4) (q : ℝ) (hF : Fᵀ = -F) :
    matrixMaxwellStress minkowskiMetric F = canonicalMaxwellResidual q ↔
      ∃ E B : ℝ,
        E ^ 2 + B ^ 2 = 2 * q ∧
        F = canonicalMaxwellTwoForm E B := by
  constructor
  · intro hstress
    let e1 := F 0 1
    let e2 := F 0 2
    let e3 := F 0 3
    let b1 := F 2 3
    let b2 := F 3 1
    let b3 := F 1 2
    have hnormal : F = lorentzSkewTwoForm4 e1 e2 e3 b1 b2 b3 := by
      simpa [e1, e2, e3, b1, b2, b3] using
        eq_lorentzSkewTwoForm4_of_transpose_eq_neg F hF
    have h00 := congrArg (fun M : Matrix4 => M 0 0) hstress
    have h11 := congrArg (fun M : Matrix4 => M 1 1) hstress
    rw [hnormal] at h00 h11
    simp [matrixMaxwellStress, minkowskiMetric, lorentzSkewTwoForm4,
      canonicalMaxwellResidual, Matrix.trace, Fin.sum_univ_succ] at h00 h11
    have hzero : e2 ^ 2 + e3 ^ 2 + b2 ^ 2 + b3 ^ 2 = 0 := by
      nlinarith
    have he2 : e2 = 0 := by
      nlinarith [sq_nonneg e2, sq_nonneg e3, sq_nonneg b2, sq_nonneg b3]
    have he3 : e3 = 0 := by
      nlinarith [sq_nonneg e2, sq_nonneg e3, sq_nonneg b2, sq_nonneg b3]
    have hb2 : b2 = 0 := by
      nlinarith [sq_nonneg e2, sq_nonneg e3, sq_nonneg b2, sq_nonneg b3]
    have hb3 : b3 = 0 := by
      nlinarith [sq_nonneg e2, sq_nonneg e3, sq_nonneg b2, sq_nonneg b3]
    have hcircle : e1 ^ 2 + b1 ^ 2 = 2 * q := by
      nlinarith
    refine ⟨e1, b1, hcircle, ?_⟩
    rw [hnormal, he2, he3, hb2, hb3]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lorentzSkewTwoForm4, canonicalMaxwellTwoForm]
  · rintro ⟨E, B, hcircle, rfl⟩
    rw [matrixMaxwellStress_canonical]
    unfold canonicalMaxwellStress canonicalStressMagnitude
    rw [show (E ^ 2 + B ^ 2) / 2 = q by nlinarith]
    rfl

/-- Equivalently, the complete canonical stress fibre is one unit duality
orbit of the purely electric positive-`q` seed.-/
theorem exists_dualityParameter_of_matrixMaxwellStress_eq_canonicalResidual
    (F : Matrix4) (q : ℝ) (hq : 0 < q) (hF : Fᵀ = -F)
    (hstress : matrixMaxwellStress minkowskiMetric F =
      canonicalMaxwellResidual q) :
    ∃ p : DualityParameter,
      F = p.c • canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 +
        p.s • canonicalHodgeStar (Real.sqrt (2 * q)) 0 := by
  obtain ⟨E, B, hcircle, rfl⟩ :=
    (matrixMaxwellStress_eq_canonicalResidual_iff_amplitudeCircle
      F q hF).mp hstress
  have hsqrtSq : (Real.sqrt (2 * q)) ^ 2 = 2 * q := by
    rw [Real.sq_sqrt]
    positivity
  have hmag : canonicalMaxwellMagnitude (Real.sqrt (2 * q)) 0 ≠ 0 := by
    unfold canonicalMaxwellMagnitude
    rw [hsqrtSq]
    positivity
  have heq : canonicalMaxwellMagnitude E B =
      canonicalMaxwellMagnitude (Real.sqrt (2 * q)) 0 := by
    unfold canonicalMaxwellMagnitude
    rw [hsqrtSq]
    simpa using hcircle
  obtain ⟨p, hpE, hpB⟩ :=
    (exists_dualityParameter_iff_same_magnitude
      (Real.sqrt (2 * q)) 0 E B hmag).mpr heq
  refine ⟨p, ?_⟩
  rw [← canonicalTwoForm_duality p (Real.sqrt (2 * q)) 0, hpE, hpB]

/-- Constructive cosine coordinate on the positive canonical Maxwell
stress fibre.-/
noncomputable def canonicalStressFiberCosine (q : ℝ) (F : Matrix4) : ℝ :=
  F 0 1 / Real.sqrt (2 * q)

/-- Constructive sine coordinate on the positive canonical Maxwell stress
fibre.-/
noncomputable def canonicalStressFiberSine (q : ℝ) (F : Matrix4) : ℝ :=
  F 2 3 / Real.sqrt (2 * q)

/-- **Constructive non-null Maxwell duality-orbit theorem.** The stress
itself recovers smooth algebraic duality coordinates: the `01` and `23`
components, normalized by the positive canonical amplitude, lie on the unit
circle and reconstruct the entire two-form.-/
theorem canonicalStressFiber_coordinates
    (F : Matrix4) (q : ℝ) (hq : 0 < q) (hF : Fᵀ = -F)
    (hstress : matrixMaxwellStress minkowskiMetric F =
      canonicalMaxwellResidual q) :
    canonicalStressFiberCosine q F ^ 2 +
          canonicalStressFiberSine q F ^ 2 = 1 ∧
      F = canonicalStressFiberCosine q F •
            canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 +
          canonicalStressFiberSine q F •
            canonicalHodgeStar (Real.sqrt (2 * q)) 0 := by
  obtain ⟨E, B, hcircle, hcanonical⟩ :=
    (matrixMaxwellStress_eq_canonicalResidual_iff_amplitudeCircle
      F q hF).mp hstress
  have hsqrtSq : (Real.sqrt (2 * q)) ^ 2 = 2 * q := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt : Real.sqrt (2 * q) ≠ 0 := by positivity
  subst F
  constructor
  · unfold canonicalStressFiberCosine canonicalStressFiberSine
    change (E / Real.sqrt (2 * q)) ^ 2 +
      (B / Real.sqrt (2 * q)) ^ 2 = 1
    field_simp [hsqrt]
    nlinarith
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [canonicalStressFiberCosine, canonicalStressFiberSine,
        canonicalMaxwellTwoForm, canonicalHodgeStar] <;>
      field_simp [hsqrt]

/-- The normalized stress-fibre coordinates form the unique duality
parameter carrying the positive electric seed to the supplied two-form.-/
noncomputable def canonicalStressFiberDualityParameter
    (q : ℝ) (F : Matrix4)
    (hunit : canonicalStressFiberCosine q F ^ 2 +
      canonicalStressFiberSine q F ^ 2 = 1) : DualityParameter where
  c := canonicalStressFiberCosine q F
  s := canonicalStressFiberSine q F
  unit := hunit

/-- Congruence transport preserves antisymmetry of a two-form.-/
theorem transportTwoForm_transpose
    (L F : Matrix4) (hF : Fᵀ = -F) :
    (transportTwoForm L F)ᵀ = -transportTwoForm L F := by
  unfold transportTwoForm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    hF]
  simp [Matrix.mul_assoc]

/-- Lorentz identities transport the quadratic stress core by similarity.-/
theorem lorentzTransport_core
    (G L K F : Matrix4)
    (hGLt : G * Lᵀ = K * G)
    (hLGLt : L * G * Lᵀ = G) :
    G * transportTwoForm L F * G * transportTwoForm L F =
      transportMixed K (G * F * G * F) L := by
  unfold transportTwoForm transportMixed
  calc
    G * (Lᵀ * F * L) * G * (Lᵀ * F * L) =
        (G * Lᵀ) * F * (L * G * Lᵀ) * F * L := by noncomm_ring
    _ = (K * G) * F * G * F * L := by rw [hGLt, hLGLt]
    _ = K * (G * F * G * F) * L := by noncomm_ring

/-- Similarity by mutually inverse frame matrices preserves the core trace.-/
theorem lorentzTransport_core_trace
    (G L K F : Matrix4)
    (hLK : L * K = 1)
    (hGLt : G * Lᵀ = K * G)
    (hLGLt : L * G * Lᵀ = G) :
    Matrix.trace
        (G * transportTwoForm L F * G * transportTwoForm L F) =
      Matrix.trace (G * F * G * F) := by
  rw [lorentzTransport_core G L K F hGLt hLGLt]
  unfold transportMixed
  calc
    Matrix.trace (K * (G * F * G * F) * L) =
        Matrix.trace (L * (K * (G * F * G * F))) := by
      rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((L * K) * (G * F * G * F)) := by
      congr 1
      exact (Matrix.mul_assoc L K (G * F * G * F)).symm
    _ = Matrix.trace (G * F * G * F) := by rw [hLK, one_mul]

/-- **Lorentz covariance of Maxwell stress.**-/
theorem matrixMaxwellStress_lorentzTransport
    (G L K F : Matrix4)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hGLt : G * Lᵀ = K * G)
    (hLGLt : L * G * Lᵀ = G) :
    matrixMaxwellStress G (transportTwoForm L F) =
      transportMixed K (matrixMaxwellStress G F) L := by
  have hcore := lorentzTransport_core G L K F hGLt hLGLt
  have htrace := lorentzTransport_core_trace G L K F hLK hGLt hLGLt
  have htrace' : Matrix.trace (transportMixed K (G * F * G * F) L) =
      Matrix.trace (G * F * G * F) := by
    rw [← hcore]
    exact htrace
  unfold matrixMaxwellStress transportMixed
  dsimp only
  rw [hcore, htrace']
  simp only [mul_add, add_mul, mul_neg, neg_mul, mul_assoc,
    smul_mul_assoc, mul_smul_comm, mul_one, hKL]
  unfold transportMixed
  noncomm_ring

/-- **General basis covariance of Maxwell stress.** Unlike the Lorentz-frame
specialization above, this theorem transforms the contravariant metric and
covariant two-form together under an arbitrary invertible basis change.-/
theorem matrixMaxwellStress_changeBasis
    (G L K F : Matrix4)
    (hKL : K * L = 1) (hLK : L * K = 1) :
    matrixMaxwellStress (L * G * Lᵀ) (transportTwoForm K F) =
      transportMixed L (matrixMaxwellStress G F) K := by
  have htrans : Lᵀ * Kᵀ = (1 : Matrix4) := by
    rw [← Matrix.transpose_mul, hKL, Matrix.transpose_one]
  have hcore :
      (L * G * Lᵀ) * transportTwoForm K F *
          (L * G * Lᵀ) * transportTwoForm K F =
        L * (G * F * G * F) * K := by
    unfold transportTwoForm
    calc
      (L * G * Lᵀ) * (Kᵀ * F * K) *
          (L * G * Lᵀ) * (Kᵀ * F * K) =
        L * G * (Lᵀ * Kᵀ) * F * (K * L) * G *
          (Lᵀ * Kᵀ) * F * K := by noncomm_ring
      _ = L * (G * F * G * F) * K := by
        rw [htrans, hKL]
        simp
        noncomm_ring
  have htrace :
      Matrix.trace (L * (G * F * G * F) * K) =
        Matrix.trace (G * F * G * F) := by
    calc
      Matrix.trace (L * (G * F * G * F) * K) =
          Matrix.trace (K * (L * (G * F * G * F))) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace ((K * L) * (G * F * G * F)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace (G * F * G * F) := by rw [hKL, one_mul]
  unfold matrixMaxwellStress transportMixed
  dsimp only
  rw [hcore, htrace]
  simp only [mul_add, add_mul, mul_neg, neg_mul, mul_assoc,
    smul_mul_assoc, mul_smul_comm, mul_one, hLK]

/-- **Arbitrary adapted-frame Maxwell duality-orbit theorem.** If an
invertible coframe sends the inverse metric and physical Maxwell stress to
their canonical Lorentz forms, then the pulled physical two-form is exactly
a unit duality rotation of the positive curvature seed.-/
theorem exists_dualityParameter_of_adaptedMaxwellStress
    (GInv L K F : Matrix4) (q : ℝ) (hq : 0 < q)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hmetric : L * GInv * Lᵀ = minkowskiMetric)
    (hF : Fᵀ = -F)
    (hstress : transportMixed L (matrixMaxwellStress GInv F) K =
      canonicalMaxwellResidual q) :
    ∃ p : DualityParameter,
      transportTwoForm K F =
        p.c • canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 +
          p.s • canonicalHodgeStar (Real.sqrt (2 * q)) 0 := by
  have hskew : (transportTwoForm K F)ᵀ = -transportTwoForm K F :=
    transportTwoForm_transpose K F hF
  have hcanonical :
      matrixMaxwellStress minkowskiMetric (transportTwoForm K F) =
        canonicalMaxwellResidual q := by
    rw [← hmetric]
    exact (matrixMaxwellStress_changeBasis GInv L K F hKL hLK).trans hstress
  exact exists_dualityParameter_of_matrixMaxwellStress_eq_canonicalResidual
    (transportTwoForm K F) q hq hskew hcanonical

/-- Constructive version of the arbitrary adapted-frame orbit theorem. The
normalized `01/23` components of the pulled physical form are the smooth
duality coordinates used by the differential splice.-/
theorem adaptedMaxwellStressFiber_coordinates
    (GInv L K F : Matrix4) (q : ℝ) (hq : 0 < q)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hmetric : L * GInv * Lᵀ = minkowskiMetric)
    (hF : Fᵀ = -F)
    (hstress : transportMixed L (matrixMaxwellStress GInv F) K =
      canonicalMaxwellResidual q) :
    canonicalStressFiberCosine q (transportTwoForm K F) ^ 2 +
          canonicalStressFiberSine q (transportTwoForm K F) ^ 2 = 1 ∧
      transportTwoForm K F =
        canonicalStressFiberCosine q (transportTwoForm K F) •
            canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 +
          canonicalStressFiberSine q (transportTwoForm K F) •
            canonicalHodgeStar (Real.sqrt (2 * q)) 0 := by
  have hskew : (transportTwoForm K F)ᵀ = -transportTwoForm K F :=
    transportTwoForm_transpose K F hF
  have hcanonical :
      matrixMaxwellStress minkowskiMetric (transportTwoForm K F) =
        canonicalMaxwellResidual q := by
    rw [← hmetric]
    exact (matrixMaxwellStress_changeBasis GInv L K F hKL hLK).trans hstress
  exact canonicalStressFiber_coordinates
    (transportTwoForm K F) q hq hskew hcanonical

/-- Similarity transport preserves a scalar square law.-/
theorem transportMixed_sq
    (L K X : Matrix4) (qSq : ℝ)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hX : X * X = qSq • (1 : Matrix4)) :
    transportMixed K X L * transportMixed K X L =
      qSq • (1 : Matrix4) := by
  unfold transportMixed
  calc
    (K * X * L) * (K * X * L) = K * X * (L * K) * X * L := by
      noncomm_ring
    _ = K * (X * X) * L := by rw [hLK]; noncomm_ring
    _ = K * (qSq • (1 : Matrix4)) * L := by rw [hX]
    _ = qSq • (1 : Matrix4) := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, hKL]

/-- Similarity transport preserves idempotence.-/
theorem transportMixed_idempotent
    (L K P : Matrix4)
    (hLK : L * K = 1)
    (hP : P * P = P) :
    transportMixed K P L * transportMixed K P L =
      transportMixed K P L := by
  unfold transportMixed
  calc
    (K * P * L) * (K * P * L) = K * P * (L * K) * P * L := by
      noncomm_ring
    _ = K * (P * P) * L := by rw [hLK]; noncomm_ring
    _ = K * P * L := by rw [hP]

/-- A transported complementary projector pair still resolves the identity.-/
theorem transportMixed_projectors_sum
    (L K P Q : Matrix4)
    (hKL : K * L = 1)
    (hsum : P + Q = 1) :
    transportMixed K P L + transportMixed K Q L = 1 := by
  unfold transportMixed
  calc
    K * P * L + K * Q * L = K * (P + Q) * L := by noncomm_ring
    _ = K * 1 * L := by rw [hsum]
    _ = 1 := by rw [mul_one, hKL]

/-- **Transported local Maxwell seed.** Every positive canonical residual has
an explicit real two-form square root in any supplied Lorentz frame, and its
stress is the similarity transport of the canonical residual.-/
theorem matrixMaxwellStress_transported_seed
    (L K : Matrix4) (q : ℝ) (hq : 0 < q)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hGLt : minkowskiMetric * Lᵀ = K * minkowskiMetric)
    (hLGLt : L * minkowskiMetric * Lᵀ = minkowskiMetric) :
    matrixMaxwellStress minkowskiMetric
        (transportTwoForm L
          (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0)) =
      transportMixed K (canonicalMaxwellResidual q) L := by
  rw [matrixMaxwellStress_lorentzTransport minkowskiMetric L K
    (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0)
    hKL hLK hGLt hLGLt]
  rw [matrixMaxwellStress_canonical]
  have harg : 0 ≤ 2 * q := by positivity
  have hsqrt : (Real.sqrt (2 * q)) ^ 2 = 2 * q := Real.sq_sqrt harg
  have hrho : canonicalStressMagnitude (Real.sqrt (2 * q)) 0 = q := by
    unfold canonicalStressMagnitude
    rw [hsqrt]
    ring
  congr 1
  unfold canonicalMaxwellStress
  rw [hrho]
  rfl

/-- The transported positive-`q` seed remains an antisymmetric two-form.-/
theorem transported_seed_transpose
    (L : Matrix4) (q : ℝ) :
    (transportTwoForm L
      (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0))ᵀ =
      -transportTwoForm L
        (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0) :=
  transportTwoForm_transpose L _
    (canonicalMaxwellTwoForm_transpose (Real.sqrt (2 * q)) 0)

/-- Block-diagonal transition between two tetrads adapted to the negative and
positive Maxwell principal planes.-/
def principalPlaneTransition
    (a00 a01 a10 a11 b00 b01 b10 b11 : ℝ) : Matrix4 :=
  !![a00, a01,   0,   0;
     a10, a11,   0,   0;
       0,   0, b00, b01;
       0,   0, b10, b11]

/-- Oriented area scale of the Lorentzian principal-plane transition.-/
def negativePlaneAreaScale (a00 a01 a10 a11 : ℝ) : ℝ :=
  a00 * a11 - a01 * a10

/-- Oriented area scale of the spacelike principal-plane transition.-/
def positivePlaneAreaScale (b00 b01 b10 b11 : ℝ) : ℝ :=
  b00 * b11 - b01 * b10

/-- A principal-plane transition acts on the canonical electric seed by the
oriented area scale of the negative principal plane.-/
theorem transportTwoForm_principalPlaneTransition_electric
    (a00 a01 a10 a11 b00 b01 b10 b11 E : ℝ) :
    transportTwoForm
        (principalPlaneTransition a00 a01 a10 a11 b00 b01 b10 b11)
        (canonicalMaxwellTwoForm E 0) =
      negativePlaneAreaScale a00 a01 a10 a11 •
        canonicalMaxwellTwoForm E 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transportTwoForm, principalPlaneTransition,
      negativePlaneAreaScale, canonicalMaxwellTwoForm, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

/-- The same transition acts on the canonical Hodge seed by the oriented area
scale of the positive principal plane.-/
theorem transportTwoForm_principalPlaneTransition_hodge
    (a00 a01 a10 a11 b00 b01 b10 b11 E : ℝ) :
    transportTwoForm
        (principalPlaneTransition a00 a01 a10 a11 b00 b01 b10 b11)
        (canonicalHodgeStar E 0) =
      positivePlaneAreaScale b00 b01 b10 b11 •
        canonicalHodgeStar E 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transportTwoForm, principalPlaneTransition,
      positivePlaneAreaScale, canonicalHodgeStar, canonicalMaxwellTwoForm,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- **Adapted-frame seed-line theorem.** If an adapted transition preserves
the relative orientation of the two principal planes, it multiplies the
electric seed and its Hodge partner by one common factor.  For orthonormal
orientation-matched tetrads that factor is necessarily one of `±1`; the
separate determinant statement is left explicit here.-/
theorem transportTwoForm_principalPlaneTransition_seed_pair
    (a00 a01 a10 a11 b00 b01 b10 b11 E epsilon : ℝ)
    (hnegative : negativePlaneAreaScale a00 a01 a10 a11 = epsilon)
    (hpositive : positivePlaneAreaScale b00 b01 b10 b11 = epsilon) :
    transportTwoForm
        (principalPlaneTransition a00 a01 a10 a11 b00 b01 b10 b11)
        (canonicalMaxwellTwoForm E 0) =
          epsilon • canonicalMaxwellTwoForm E 0 ∧
      transportTwoForm
        (principalPlaneTransition a00 a01 a10 a11 b00 b01 b10 b11)
        (canonicalHodgeStar E 0) =
          epsilon • canonicalHodgeStar E 0 := by
  constructor
  · rw [transportTwoForm_principalPlaneTransition_electric, hnegative]
  · rw [transportTwoForm_principalPlaneTransition_hodge, hpositive]

/-- Congruence transport composes contravariantly in the frame matrices.-/
theorem transportTwoForm_mul (L H F : Matrix4) :
    transportTwoForm (H * L) F =
      transportTwoForm L (transportTwoForm H F) := by
  unfold transportTwoForm
  rw [Matrix.transpose_mul]
  noncomm_ring

/-- Transport is linear in the two-form representative.-/
theorem transportTwoForm_smul (L F : Matrix4) (c : ℝ) :
    transportTwoForm L (c • F) = c • transportTwoForm L F := by
  unfold transportTwoForm
  simp only [Matrix.smul_mul, Matrix.mul_smul]

/-- **Principal-frame overlap theorem.** If a second adapted frame is obtained
from the first by an orientation-matched principal-plane transition, then the
two transported Maxwell seed pairs differ by one common factor.  This is the
finite-dimensional probe/frame-independence statement consumed by the channel
detector's common-scale invariance theorem.-/
theorem transportedSeedPair_principalFrameOverlap
    (L : Matrix4)
    (a00 a01 a10 a11 b00 b01 b10 b11 E epsilon : ℝ)
    (hnegative : negativePlaneAreaScale a00 a01 a10 a11 = epsilon)
    (hpositive : positivePlaneAreaScale b00 b01 b10 b11 = epsilon) :
    let H := principalPlaneTransition
      a00 a01 a10 a11 b00 b01 b10 b11
    transportTwoForm (H * L) (canonicalMaxwellTwoForm E 0) =
        epsilon • transportTwoForm L (canonicalMaxwellTwoForm E 0) ∧
      transportTwoForm (H * L) (canonicalHodgeStar E 0) =
        epsilon • transportTwoForm L (canonicalHodgeStar E 0) := by
  dsimp only
  obtain ⟨helectric, hhodge⟩ :=
    transportTwoForm_principalPlaneTransition_seed_pair
      a00 a01 a10 a11 b00 b01 b10 b11 E epsilon
      hnegative hpositive
  constructor
  · rw [transportTwoForm_mul, helectric, transportTwoForm_smul]
  · rw [transportTwoForm_mul, hhodge, transportTwoForm_smul]

end RainichKaluza
