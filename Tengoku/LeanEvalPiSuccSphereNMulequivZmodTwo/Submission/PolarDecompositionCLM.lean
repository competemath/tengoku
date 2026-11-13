import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.GramSchmidtTriangular
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SOFrameGauge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Splitting an invertible codomain gauge into an `SO` factor and an unobstructed factor

`Submission.PositiveDistortion.bijective_one_sub_smul_of_inner_pos`
(`BridgeEntryPositiveDistortion.lean`) accepts a distortion `A` with no norm
bound at all: all it asks is that the straight-line path `s ↦ 1 - s • (1 - A)`
from the identity to `A` consists of bijections, which it derives from
positive definiteness of the quadratic form of `A`.

This module supplies the *existence* half of that interface: given an
invertible `Φ : F →L[ℝ] F` on `F = EuclideanSpace ℝ (Fin k)`, it factors
`Φ = R ∘ A` with `R` special orthogonal and `A` an unobstructed distortion.

Two factorizations are provided, and they are genuinely different in what they
cost.

* **Gram--Schmidt (`QR`).**  `qrSO Φ` and `qrUpper Φ` factor `Φ = R ∘ A` with
  `R ∈ SO(k)` and `A` **upper triangular with positive diagonal**.  The
  straight-line path from the identity to such an `A` stays bijective
  (`bijective_one_sub_smul_of_upperTriangular`), because the path matrix is
  again upper triangular with positive diagonal.  Both factors depend
  **smoothly** on a smooth parameter (`contDiff_qrUpper`,
  `contDiff_qrSOMatrix_apply`), because Gram--Schmidt does
  (`Submission.contDiff_matrixGramSchmidtSO_apply`).  No square roots occur, so
  there is no functional calculus to differentiate.

* **Polar.**  `polarPos Φ` and `polarSO Φ` factor `Φ = R ∘ P` with `R`
  orthogonal and `P` positive definite in the strong sense
  `∀ v ≠ 0, 0 < ⟪P v, v⟫`, i.e. exactly the hypothesis
  `PositiveFrameJetRealization.A_positive` /
  `BridgeEntryStandardTarget.StandardEntryDatum.A_positive` demand.  `P` is the
  Hermitian square root of `Φᵀ Φ`, built from the spectral theorem
  (`hermSqrt`).  This factorization is canonical but its parameter dependence
  is *not* supplied here: smoothness of `hermSqrt` is not available from
  Mathlib's spectral theorem and is the one analytic input the polar route
  needs (see the module comment at `SmoothPositiveFactor`).

Main results:

* `bijective_one_sub_smul_of_upperTriangular` — the triangular analogue of
  `bijective_one_sub_smul_of_inner_pos`, with no norm bound and no positive
  definiteness;
* `qr_factorization` : `Φ = SOFrameGauge.toCLM (qrSO Φ h) ∘L qrUpper Φ h`;
* `contDiff_qrUpper` / `contDiff_qrSOMatrix_apply` — smooth dependence of both
  `QR` factors on a smooth parameter;
* `hermSqrt_mul_self`, `hermSqrt_posDef` — the Hermitian square root;
* `polar_factorization`, `polarPos_inner_pos`, `polarSO_mem_specialOrthogonalGroup`
  — the polar decomposition and its positive-definiteness statement;
* `SmoothPositiveFactor` — the parametrized polar statement, isolated as a
  named obligation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Submission
namespace PolarDecompositionCLM

open Matrix InnerProductSpace
open scoped RealInnerProductSpace ContDiff Matrix

variable {k : ℕ}

/-! ## The matrix of a continuous linear endomorphism of Euclidean space -/

/-- The matrix of a continuous linear endomorphism of `EuclideanSpace ℝ (Fin k)`.-/
def clmMatrix (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    Matrix (Fin k) (Fin k) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)).symm Φ

/--
@isnad1 id=eq.0h2v.s12.aae0e78e5a17 from=translated src=- shape=05123477 vocab=056e5298
-/
@[simp] theorem toEuclideanCLM_clmMatrix
    (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)) (clmMatrix Φ) = Φ :=
  (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)).apply_symm_apply Φ

/--
@isnad1 id=eq.0h2v.s12.f5c8f24ba82f from=translated src=- shape=da6d64c5 vocab=056e5298
-/
@[simp] theorem clmMatrix_toEuclideanCLM (M : Matrix (Fin k) (Fin k) ℝ) :
    clmMatrix ((Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)) M) = M :=
  (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)).symm_apply_apply M

/--
@isnad1 id=eq.0h1v.s9.875a355dee9a from=translated src=- shape=76276535 vocab=7365c877
-/
@[simp] theorem clmMatrix_one :
    clmMatrix (1 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) = 1 :=
  map_one _

/--
@isnad1 id=eq.0h3v.s10.45fb083e8f21 from=translated src=- shape=00603466 vocab=b5417cc6
-/
theorem clmMatrix_sub
    (Φ Ψ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    clmMatrix (Φ - Ψ) = clmMatrix Φ - clmMatrix Ψ :=
  map_sub _ _ _

/--
@isnad1 id=eq.0h3v.s10.254d7e2aeb6a from=translated src=- shape=5aa0a18f vocab=ec0e2f3a
-/
theorem clmMatrix_smul (c : ℝ)
    (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    clmMatrix (c • Φ) = c • clmMatrix Φ :=
  map_smul _ _ _

/--
@isnad1 id=eq.0h3v.s13.8560d700deb9 from=translated src=- shape=e2ac8c4f vocab=6b4d101c
-/
theorem toEuclideanCLM_mul (M N : Matrix (Fin k) (Fin k) ℝ) :
    (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)) (M * N) =
      ((Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)) M).comp
        ((Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)) N) := by
  rw [map_mul]
  rfl

/-- Coordinates of the value of a gauge, through its matrix.
@isnad1 id=eq.0h4v.s9.ce7b4a05d807 from=translated src=- shape=7383b13b vocab=f2354a20
-/
theorem clm_apply_coord (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (u : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    Φ u i = ∑ j : Fin k, clmMatrix Φ i j * u j := by
  conv_lhs => rw [← toEuclideanCLM_clmMatrix Φ]
  rfl

/-- An invertible matrix acts bijectively.
@isnad1 id=bijectiv.1h2v.s12.21a04b064f42 from=translated src=- shape=46cf40c1 vocab=a16b70e0
-/
theorem bijective_toEuclideanCLM_of_det_ne_zero
    {M : Matrix (Fin k) (Fin k) ℝ} (h : M.det ≠ 0) :
    Function.Bijective (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) M) := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr h
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun x => (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) M⁻¹) x, ?_, ?_⟩
  · intro x
    have := congrArg (fun N => (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) N) x) h2
    simpa [toEuclideanCLM_mul] using this
  · intro x
    have := congrArg (fun N => (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) N) x) h1
    simpa [toEuclideanCLM_mul] using this

/--
@isnad1 id=bijectiv.1h2v.s9.d378acc169c6 from=translated src=- shape=1fccb638 vocab=0eec854e
-/
theorem bijective_of_det_clmMatrix_ne_zero
    {Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)}
    (h : (clmMatrix Φ).det ≠ 0) : Function.Bijective Φ := by
  have := bijective_toEuclideanCLM_of_det_ne_zero h
  rwa [toEuclideanCLM_clmMatrix] at this

/-! ## Triangular distortions: the straight-line path stays bijective -/

/-- **Upper-triangularity with positive diagonal is an admissibility condition
for a distortion.**  No norm bound and no symmetry are used: this is the
Gram--Schmidt analogue of
`Submission.PositiveDistortion.bijective_one_sub_smul_of_inner_pos`.
@isnad1 id=bijectiv.4h3v.s12.dec6feaab7ec from=translated src=- shape=f42494cd vocab=458055d1
-/
theorem bijective_one_sub_smul_of_upperTriangular
    {A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)}
    (hupper : ∀ i j : Fin k, j < i → clmMatrix A i j = 0)
    (hdiag : ∀ i : Fin k, 0 < clmMatrix A i i)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Function.Bijective
      ((1 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) -
        s • ((1 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) - A)) := by
  set M := clmMatrix A with hM
  have hpath : clmMatrix
      ((1 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) -
        s • ((1 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) - A))
      = (1 : Matrix (Fin k) (Fin k) ℝ) -
        s • ((1 : Matrix (Fin k) (Fin k) ℝ) - M) := by
    rw [clmMatrix_sub, clmMatrix_smul, clmMatrix_sub, clmMatrix_one]
  apply bijective_of_det_clmMatrix_ne_zero
  rw [hpath]
  have hup : ∀ i j : Fin k, j < i →
      ((1 : Matrix (Fin k) (Fin k) ℝ) -
        s • ((1 : Matrix (Fin k) (Fin k) ℝ) - M)) i j = 0 := by
    intro i j hij
    have hne : i ≠ j := ne_of_gt hij
    have hone : (1 : Matrix (Fin k) (Fin k) ℝ) i j = 0 := Matrix.one_apply_ne hne
    simp [hone, hupper i j hij]
  have hdiagpath : ∀ i : Fin k,
      ((1 : Matrix (Fin k) (Fin k) ℝ) -
        s • ((1 : Matrix (Fin k) (Fin k) ℝ) - M)) i i = 1 - s + s * M i i := by
    intro i
    simp [Matrix.one_apply_eq]
    ring
  have hdetpos : 0 < ((1 : Matrix (Fin k) (Fin k) ℝ) -
      s • ((1 : Matrix (Fin k) (Fin k) ℝ) - M)).det := by
    rw [Matrix.det_of_isUpperTriangular hup]
    apply Finset.prod_pos
    intro i _
    rw [hdiagpath i]
    have hMi : 0 < M i i := hdiag i
    rcases eq_or_lt_of_le hs1 with heq | hlt
    · subst heq
      simpa using hMi
    · have h1 : 0 < 1 - s := by linarith
      have h2 : 0 ≤ s * M i i := mul_nonneg hs0 hMi.le
      linarith
  exact ne_of_gt hdetpos

/-! ## The Gram--Schmidt (`QR`) factorization of an invertible gauge -/

/--
@isnad1 id=mem.1h2v.s8.41a3a1f9245d from=translated src=- shape=57fa1209 vocab=c9b67d60
-/
theorem mem_specialOrthogonalGroup_transpose {Q : Matrix (Fin k) (Fin k) ℝ}
    (hQ : Q ∈ Matrix.specialOrthogonalGroup (Fin k) ℝ) :
    Qᵀ ∈ Matrix.specialOrthogonalGroup (Fin k) ℝ := by
  obtain ⟨horth, hdet⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hQ
  have hmul : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin k) ℝ).mp horth
  refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
  · exact (Matrix.mem_orthogonalGroup_iff (Fin k) ℝ).mpr
      (by simpa using mul_eq_one_comm.mp hmul)
  · rwa [Matrix.det_transpose]

variable {Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)}

/--
@isnad1 id=lt.1h2v.s8.f41165ded652 from=translated src=- shape=f324e6b8 vocab=c91e9ceb
-/
theorem det_transpose_clmMatrix_pos (h : 0 < (clmMatrix Φ).det) :
    0 < ((clmMatrix Φ)ᵀ).det := by
  rwa [Matrix.det_transpose]

/-- The special-orthogonal factor of the Gram--Schmidt factorization.-/
def qrSO (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (h : 0 < (clmMatrix Φ).det) : SOGroup k :=
  ⟨((matrixGramSchmidtSO ((clmMatrix Φ)ᵀ) (det_transpose_clmMatrix_pos h) :
      SOGroup k) : Matrix (Fin k) (Fin k) ℝ)ᵀ,
    mem_specialOrthogonalGroup_transpose
      (matrixGramSchmidtSO ((clmMatrix Φ)ᵀ)
        (det_transpose_clmMatrix_pos h)).property⟩

/--
@isnad1 id=eq.1h2v.s8.05f0422623ad from=translated src=- shape=637ec6c1 vocab=53a1424b
-/
theorem qrSO_coe (h : 0 < (clmMatrix Φ).det) :
    ((qrSO Φ h : SOGroup k) : Matrix (Fin k) (Fin k) ℝ)
      = (rowsMatrix (gramSchmidtNormed ℝ (matrixRows ((clmMatrix Φ)ᵀ))))ᵀ :=
  rfl

/-- The triangular factor of the Gram--Schmidt factorization, as a matrix.-/
def qrUpperMatrix (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    Matrix (Fin k) (Fin k) ℝ :=
  (GramSchmidtTriangular.gsLower (matrixRows ((clmMatrix Φ)ᵀ)))ᵀ

/-- The triangular factor of the Gram--Schmidt factorization.-/
def qrUpper (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)) (qrUpperMatrix Φ)

/--
@isnad1 id=eq.0h2v.s8.7f6f8eeb9472 from=translated src=- shape=a571f2f3 vocab=6c1fbfa8
-/
@[simp] theorem clmMatrix_qrUpper :
    clmMatrix (qrUpper Φ) = qrUpperMatrix Φ :=
  clmMatrix_toEuclideanCLM _

/--
@isnad1 id=linearin.1h2v.s8.5ca4a6a60e43 from=translated src=- shape=1b3dc9d3 vocab=36eadbe9
-/
theorem linearIndependent_matrixRows_transpose (h : 0 < (clmMatrix Φ).det) :
    LinearIndependent ℝ (matrixRows ((clmMatrix Φ)ᵀ)) :=
  linearIndependent_matrixRows_of_det_ne_zero
    (ne_of_gt (det_transpose_clmMatrix_pos h))

/-- **The triangular factor is upper triangular.**
@isnad1 id=eq.1h4v.s8.f4e41368f1c5 from=translated src=- shape=42253eb6 vocab=45a81077
-/
theorem qrUpperMatrix_eq_zero_of_lt (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ]
      EuclideanSpace ℝ (Fin k)) {i j : Fin k} (hij : j < i) :
    qrUpperMatrix Φ i j = 0 :=
  GramSchmidtTriangular.gsLower_eq_zero_of_lt _ hij

/-- **The triangular factor has positive diagonal.**
@isnad1 id=lt.1h3v.s8.1f7ed09d6151 from=translated src=- shape=f611b18c vocab=f44f97ed
-/
theorem qrUpperMatrix_diag_pos (h : 0 < (clmMatrix Φ).det) (i : Fin k) :
    0 < qrUpperMatrix Φ i i :=
  GramSchmidtTriangular.gsLower_diag_pos
    (linearIndependent_matrixRows_transpose h) i

/-- **The Gram--Schmidt factorization of an orientation-preserving gauge.**
@isnad1 id=eq.1h2v.s9.0b6f8f3cbcac from=translated src=- shape=270cd4f8 vocab=15aa80f6
-/
theorem qr_factorization (h : 0 < (clmMatrix Φ).det) :
    Φ = (SOFrameGauge.toCLM (qrSO Φ h)).comp (qrUpper Φ) := by
  have hfac : (clmMatrix Φ)ᵀ
      = GramSchmidtTriangular.gsLower (matrixRows ((clmMatrix Φ)ᵀ)) *
          rowsMatrix (gramSchmidtNormed ℝ (matrixRows ((clmMatrix Φ)ᵀ))) := by
    have := GramSchmidtTriangular.rowsMatrix_eq_gsLower_mul
      (linearIndependent_matrixRows_transpose h)
    rwa [rowsMatrix_matrixRows] at this
  have hmat : clmMatrix Φ
      = ((qrSO Φ h : SOGroup k) : Matrix (Fin k) (Fin k) ℝ) * qrUpperMatrix Φ := by
    have := congrArg Matrix.transpose hfac
    rw [Matrix.transpose_transpose, Matrix.transpose_mul] at this
    rw [this, qrSO_coe, qrUpperMatrix]
  calc Φ = (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)) (clmMatrix Φ) :=
        (toEuclideanCLM_clmMatrix Φ).symm
    _ = (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ))
          (((qrSO Φ h : SOGroup k) : Matrix (Fin k) (Fin k) ℝ) *
            qrUpperMatrix Φ) := by rw [hmat]
    _ = (SOFrameGauge.toCLM (qrSO Φ h)).comp (qrUpper Φ) := toEuclideanCLM_mul _ _

/-- **The triangular factor is an admissible distortion**: the straight-line
path from the identity to it consists of bijections.
@isnad1 id=bijectiv.3h3v.s12.e37b6a4ebc68 from=translated src=- shape=b25dcda5 vocab=be795cf4
-/
theorem bijective_one_sub_smul_qrUpper (h : 0 < (clmMatrix Φ).det)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Function.Bijective
      ((1 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) -
        s • ((1 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) -
          qrUpper Φ)) := by
  apply bijective_one_sub_smul_of_upperTriangular
  · intro i j hij
    rw [clmMatrix_qrUpper]
    exact qrUpperMatrix_eq_zero_of_lt Φ hij
  · intro i
    rw [clmMatrix_qrUpper]
    exact qrUpperMatrix_diag_pos h i
  · exact hs0
  · exact hs1

/-! ## Smooth dependence of the Gram--Schmidt factorization -/

section Smooth

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]

/--
@isnad1 id=eq.0h4v.s9.cc211bfca379 from=translated src=- shape=8b75d990 vocab=4c8fdb89
-/
theorem clmMatrix_apply
    (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (i j : Fin k) :
    clmMatrix Φ i j = Φ (EuclideanSpace.single j (1 : ℝ)) i := by
  conv_rhs => rw [← toEuclideanCLM_clmMatrix Φ]
  change clmMatrix Φ i j =
    (WithLp.toLp 2 (clmMatrix Φ *ᵥ
      WithLp.ofLp (EuclideanSpace.single j (1 : ℝ)))) i
  simp [Matrix.mulVec, dotProduct, EuclideanSpace.single]

/-- Entrywise smoothness of the matrix of a smooth family of gauges.
@isnad1 id=contdiff.1h5v.s10.1cbd5f8c140d from=translated src=- shape=304fa6fe vocab=e169c704
-/
theorem contDiff_clmMatrix_apply {Ψ : T → EuclideanSpace ℝ (Fin k) →L[ℝ]
      EuclideanSpace ℝ (Fin k)} (hΨ : ContDiff ℝ ∞ Ψ) (i j : Fin k) :
    ContDiff ℝ ∞ fun t => clmMatrix (Ψ t) i j := by
  have hrw : (fun t => clmMatrix (Ψ t) i j)
      = fun t => (EuclideanSpace.proj i) (Ψ t (EuclideanSpace.single j (1 : ℝ))) := by
    funext t
    exact clmMatrix_apply (Ψ t) i j
  rw [hrw]
  exact (EuclideanSpace.proj i).contDiff.comp
    ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin k))
      (EuclideanSpace.single j (1 : ℝ))).contDiff.comp hΨ)

/-- A family of matrices with smooth entries induces a smooth family of
gauges.
@isnad1 id=contdiff.1h3v.s12.097e57b8248b from=translated src=- shape=5591a1c2 vocab=127f4658
-/
theorem contDiff_toEuclideanCLM_of_entries
    {M : T → Matrix (Fin k) (Fin k) ℝ}
    (hM : ∀ i j, ContDiff ℝ ∞ fun t => M t i j) :
    ContDiff ℝ ∞ fun t => (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)) (M t) := by
  rw [contDiff_clm_apply_iff]
  intro y
  rw [contDiff_euclidean]
  intro i
  have hrw : (fun t => ((Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)) (M t)) y i)
      = fun t => ∑ l : Fin k, M t i l * (WithLp.ofLp y) l := by
    funext t
    rfl
  rw [hrw]
  exact ContDiff.sum fun l _ => (hM i l).mul contDiff_const

/-- Smooth dependence of the special-orthogonal `QR` factor.
@isnad1 id=contdiff.2h5v.s10.ad9520b80497 from=translated src=- shape=315c9937 vocab=134ce7c6
-/
theorem contDiff_qrSOMatrix_apply
    {Ψ : T → EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)}
    (hΨ : ContDiff ℝ ∞ Ψ) (h : ∀ t, 0 < (clmMatrix (Ψ t)).det) (i j : Fin k) :
    ContDiff ℝ ∞ fun t =>
      ((qrSO (Ψ t) (h t) : SOGroup k) : Matrix (Fin k) (Fin k) ℝ) i j := by
  have hrw : (fun t => ((qrSO (Ψ t) (h t) : SOGroup k) :
        Matrix (Fin k) (Fin k) ℝ) i j)
      = fun t => ((matrixGramSchmidtSO ((clmMatrix (Ψ t))ᵀ)
        (det_transpose_clmMatrix_pos (h t)) : SOGroup k) :
          Matrix (Fin k) (Fin k) ℝ) j i := by
    funext t
    rfl
  rw [hrw]
  exact contDiff_matrixGramSchmidtSO_apply (fun t => (clmMatrix (Ψ t))ᵀ)
    (fun a b => contDiff_clmMatrix_apply hΨ b a)
    (fun t => det_transpose_clmMatrix_pos (h t)) j i

/-- Smooth dependence of the triangular `QR` factor.
@isnad1 id=contdiff.2h5v.s10.33b880422dda from=translated src=- shape=ec4c08c9 vocab=a9c0c545
-/
theorem contDiff_qrUpperMatrix_apply
    {Ψ : T → EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)}
    (hΨ : ContDiff ℝ ∞ Ψ) (h : ∀ t, 0 < (clmMatrix (Ψ t)).det) (i j : Fin k) :
    ContDiff ℝ ∞ fun t => qrUpperMatrix (Ψ t) i j := by
  have hrw : (fun t => qrUpperMatrix (Ψ t) i j)
      = fun t => ∑ l : Fin k, clmMatrix (Ψ t) l j *
          ((matrixGramSchmidtSO ((clmMatrix (Ψ t))ᵀ)
            (det_transpose_clmMatrix_pos (h t)) : SOGroup k) :
              Matrix (Fin k) (Fin k) ℝ) i l := by
    funext t
    show (GramSchmidtTriangular.gsLower
      (matrixRows ((clmMatrix (Ψ t))ᵀ))) j i = _
    rw [GramSchmidtTriangular.gsLower, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rfl
  rw [hrw]
  refine ContDiff.sum fun l _ => ?_
  exact (contDiff_clmMatrix_apply hΨ l j).mul
    (contDiff_matrixGramSchmidtSO_apply (fun t => (clmMatrix (Ψ t))ᵀ)
      (fun a b => contDiff_clmMatrix_apply hΨ b a)
      (fun t => det_transpose_clmMatrix_pos (h t)) i l)

/-- **The triangular `QR` distortion of a smooth family is smooth.**
@isnad1 id=contdiff.2h3v.s10.2fba6b07b621 from=translated src=- shape=03a6d637 vocab=261dfe29
-/
theorem contDiff_qrUpper
    {Ψ : T → EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)}
    (hΨ : ContDiff ℝ ∞ Ψ) (h : ∀ t, 0 < (clmMatrix (Ψ t)).det) :
    ContDiff ℝ ∞ fun t => qrUpper (Ψ t) :=
  contDiff_toEuclideanCLM_of_entries
    (fun i j => contDiff_qrUpperMatrix_apply hΨ h i j)

end Smooth

/-! ## The Hermitian square root and the polar decomposition -/

/--
@isnad1 id=injectiv.1h3v.s6.8aac428a1ad8 from=translated src=- shape=90a327b6 vocab=976623f6
-/
theorem mulVec_injective_of_mul_eq_one {A B : Matrix (Fin k) (Fin k) ℝ}
    (h : B * A = 1) : Function.Injective A.mulVec := by
  intro x y hxy
  have h1 := congrArg (fun z => B *ᵥ z) hxy
  simp only [Matrix.mulVec_mulVec, h, Matrix.one_mulVec] at h1
  exact h1

/-- **The positive-definite square root of a positive-definite matrix**, built
from the spectral theorem.-/
def posDefSqrt {M : Matrix (Fin k) (Fin k) ℝ} (hM : M.PosDef) :
    Matrix (Fin k) (Fin k) ℝ :=
  (Unitary.conjStarAlgAut ℝ (Matrix (Fin k) (Fin k) ℝ)
      hM.isHermitian.eigenvectorUnitary)
    (Matrix.diagonal fun i => Real.sqrt (hM.isHermitian.eigenvalues i))

/--
@isnad1 id=eq.1h2v.s6.d17b8e3d0d67 from=translated src=- shape=4c27d60c vocab=d8a29545
-/
theorem posDefSqrt_mul_self {M : Matrix (Fin k) (Fin k) ℝ} (hM : M.PosDef) :
    posDefSqrt hM * posDefSqrt hM = M := by
  have hmul := map_mul (Unitary.conjStarAlgAut ℝ (Matrix (Fin k) (Fin k) ℝ)
      hM.isHermitian.eigenvectorUnitary)
    (Matrix.diagonal fun i => Real.sqrt (hM.isHermitian.eigenvalues i))
    (Matrix.diagonal fun i => Real.sqrt (hM.isHermitian.eigenvalues i))
  rw [posDefSqrt, ← hmul, Matrix.diagonal_mul_diagonal]
  have hd : (fun i => Real.sqrt (hM.isHermitian.eigenvalues i) *
      Real.sqrt (hM.isHermitian.eigenvalues i))
      = (RCLike.ofReal ∘ hM.isHermitian.eigenvalues) := by
    funext i
    exact Real.mul_self_sqrt (hM.eigenvalues_pos i).le
  rw [hd]
  exact hM.isHermitian.spectral_theorem.symm

/--
@isnad1 id=posdef.1h2v.s4.6d65f2d8bcce from=translated src=- shape=ae4aeae8 vocab=33058a62
-/
theorem posDefSqrt_posDef {M : Matrix (Fin k) (Fin k) ℝ} (hM : M.PosDef) :
    (posDefSqrt hM).PosDef := by
  set U : Matrix (Fin k) (Fin k) ℝ :=
    (hM.isHermitian.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) with hU
  have hUU : U * star U = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hM.isHermitian.eigenvectorUnitary.property
  have hdiag : (Matrix.diagonal fun i =>
      Real.sqrt (hM.isHermitian.eigenvalues i)).PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro i
    exact Real.sqrt_pos.mpr (hM.eigenvalues_pos i)
  have hinj : Function.Injective (star U : Matrix (Fin k) (Fin k) ℝ).mulVec :=
    mulVec_injective_of_mul_eq_one hUU
  have hconj := hdiag.conjTranspose_mul_mul_same hinj
  have hstar : (star U : Matrix (Fin k) (Fin k) ℝ)ᴴ = U := star_star U
  rw [hstar] at hconj
  have hrw : posDefSqrt hM = U *
      (Matrix.diagonal fun i => Real.sqrt (hM.isHermitian.eigenvalues i)) *
      star U := by
    rw [posDefSqrt, Unitary.conjStarAlgAut_apply]
  rw [hrw]
  exact hconj

/-! ### The polar factors -/

/--
@isnad1 id=posdef.1h2v.s8.924031d696df from=translated src=- shape=5994afee vocab=2f7bd928
-/
theorem posDef_conjTranspose_mul_self (h : (clmMatrix Φ).det ≠ 0) :
    ((clmMatrix Φ)ᴴ * clmMatrix Φ).PosDef := by
  have hinj : Function.Injective (clmMatrix Φ).mulVec :=
    mulVec_injective_of_mul_eq_one
      (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h))
  have := (Matrix.PosDef.one (n := Fin k) (R := ℝ)).conjTranspose_mul_mul_same hinj
  simpa using this

/-- The positive factor of the polar decomposition.-/
def polarPosMatrix (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (h : (clmMatrix Φ).det ≠ 0) : Matrix (Fin k) (Fin k) ℝ :=
  posDefSqrt (posDef_conjTranspose_mul_self h)

/--
@isnad1 id=posdef.1h2v.s8.9b70d4e2d664 from=translated src=- shape=be2ce75e vocab=67aaa425
-/
theorem polarPosMatrix_posDef (h : (clmMatrix Φ).det ≠ 0) :
    (polarPosMatrix Φ h).PosDef :=
  posDefSqrt_posDef _

/--
@isnad1 id=eq.1h2v.s8.311ce71ad893 from=translated src=- shape=7b664ebc vocab=dd685aa7
-/
theorem polarPosMatrix_mul_self (h : (clmMatrix Φ).det ≠ 0) :
    polarPosMatrix Φ h * polarPosMatrix Φ h = (clmMatrix Φ)ᴴ * clmMatrix Φ :=
  posDefSqrt_mul_self _

/--
@isnad1 id=lt.1h2v.s8.352c8ba68096 from=translated src=- shape=0dcf4747 vocab=24a20d49
-/
theorem polarPosMatrix_det_pos (h : (clmMatrix Φ).det ≠ 0) :
    0 < (polarPosMatrix Φ h).det :=
  (polarPosMatrix_posDef h).det_pos

/-- The orthogonal factor of the polar decomposition.-/
def polarOrthMatrix (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (h : (clmMatrix Φ).det ≠ 0) : Matrix (Fin k) (Fin k) ℝ :=
  clmMatrix Φ * (polarPosMatrix Φ h)⁻¹

/--
@isnad1 id=eq.1h2v.s8.c31d65a9248e from=translated src=- shape=bd8824fe vocab=5f9b56ee
-/
theorem polarOrthMatrix_mul_polarPosMatrix (h : (clmMatrix Φ).det ≠ 0) :
    polarOrthMatrix Φ h * polarPosMatrix Φ h = clmMatrix Φ := by
  have hunit : IsUnit (polarPosMatrix Φ h).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (polarPosMatrix_det_pos h))
  rw [polarOrthMatrix, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]

/--
@isnad1 id=eq.1h2v.s8.0a89f7e1c8f8 from=translated src=- shape=61f061bb vocab=2bcd4dbd
-/
theorem polarOrthMatrix_conjTranspose_mul_self (h : (clmMatrix Φ).det ≠ 0) :
    (polarOrthMatrix Φ h)ᴴ * polarOrthMatrix Φ h = 1 := by
  have hunit : IsUnit (polarPosMatrix Φ h).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (polarPosMatrix_det_pos h))
  have hherm : (polarPosMatrix Φ h)ᴴ = polarPosMatrix Φ h :=
    (polarPosMatrix_posDef h).isHermitian
  have hinvherm : ((polarPosMatrix Φ h)⁻¹)ᴴ = (polarPosMatrix Φ h)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hherm]
  rw [polarOrthMatrix, Matrix.conjTranspose_mul, hinvherm, Matrix.mul_assoc,
    ← Matrix.mul_assoc (clmMatrix Φ)ᴴ, ← polarPosMatrix_mul_self h,
    Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one,
    Matrix.nonsing_inv_mul _ hunit]

/--
@isnad1 id=mem.1h2v.s8.1b32aa4ca2e0 from=translated src=- shape=e272b37a vocab=24b3ee76
-/
theorem polarOrthMatrix_mem_orthogonalGroup (h : (clmMatrix Φ).det ≠ 0) :
    polarOrthMatrix Φ h ∈ Matrix.orthogonalGroup (Fin k) ℝ := by
  refine (Matrix.mem_orthogonalGroup_iff (Fin k) ℝ).mpr ?_
  exact mul_eq_one_comm.mp (polarOrthMatrix_conjTranspose_mul_self h)

/--
@isnad1 id=lt.1h2v.s8.7b1bc8d888e1 from=translated src=- shape=6534b3ab vocab=a6d1c6f7
-/
theorem polarOrthMatrix_det_pos (h : 0 < (clmMatrix Φ).det) :
    0 < (polarOrthMatrix Φ (ne_of_gt h)).det := by
  have hP := polarPosMatrix_det_pos (ne_of_gt h)
  have hmul := congrArg Matrix.det
    (polarOrthMatrix_mul_polarPosMatrix (ne_of_gt h))
  rw [Matrix.det_mul] at hmul
  nlinarith [hmul, hP, h]

/--
@isnad1 id=mem.1h2v.s8.77e4b4b7a022 from=translated src=- shape=5c74d196 vocab=2ae4fc45
-/
theorem polarOrthMatrix_mem_specialOrthogonalGroup (h : 0 < (clmMatrix Φ).det) :
    polarOrthMatrix Φ (ne_of_gt h) ∈
      Matrix.specialOrthogonalGroup (Fin k) ℝ := by
  refine Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨polarOrthMatrix_mem_orthogonalGroup (ne_of_gt h), ?_⟩
  have hdetsq : (polarOrthMatrix Φ (ne_of_gt h)).det *
      (polarOrthMatrix Φ (ne_of_gt h)).det = 1 := by
    have hmul := congrArg Matrix.det
      ((Matrix.mem_orthogonalGroup_iff (Fin k) ℝ).mp
        (polarOrthMatrix_mem_orthogonalGroup (ne_of_gt h)))
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hmul
    exact hmul
  rcases mul_self_eq_one_iff.mp hdetsq with hone | hneg
  · exact hone
  · have := polarOrthMatrix_det_pos h
    rw [hneg] at this
    linarith

/-- **The polar decomposition of an orientation-preserving gauge.**-/
def polarSO (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (h : 0 < (clmMatrix Φ).det) : SOGroup k :=
  ⟨polarOrthMatrix Φ (ne_of_gt h),
    polarOrthMatrix_mem_specialOrthogonalGroup h⟩

/-- The positive factor of the polar decomposition, as a gauge.-/
def polarPos (Φ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (h : (clmMatrix Φ).det ≠ 0) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)) (polarPosMatrix Φ h)

/-- **`Φ = R ∘ P` with `R` special orthogonal and `P` positive definite.**
@isnad1 id=eq.1h2v.s9.d9eb74c5732d from=translated src=- shape=62f9b4f6 vocab=56ddafc5
-/
theorem polar_factorization (h : 0 < (clmMatrix Φ).det) :
    Φ = (SOFrameGauge.toCLM (polarSO Φ h)).comp (polarPos Φ (ne_of_gt h)) := by
  calc Φ = (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)) (clmMatrix Φ) :=
        (toEuclideanCLM_clmMatrix Φ).symm
    _ = (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ))
          (polarOrthMatrix Φ (ne_of_gt h) * polarPosMatrix Φ (ne_of_gt h)) := by
        rw [polarOrthMatrix_mul_polarPosMatrix]
    _ = (SOFrameGauge.toCLM (polarSO Φ h)).comp (polarPos Φ (ne_of_gt h)) :=
        toEuclideanCLM_mul _ _

/-- **The positive factor has positive-definite quadratic form**, which is
exactly the admissibility hypothesis of
`Submission.PositiveDistortion.bijective_one_sub_smul_of_inner_pos` and of
`BridgeEntryStandardTarget.StandardEntryDatum.A_positive`.
@isnad1 id=lt.2h3v.s9.ed00412360ff from=translated src=- shape=2e63fdb9 vocab=c847f269
-/
theorem polarPos_inner_pos (h : (clmMatrix Φ).det ≠ 0)
    (v : EuclideanSpace ℝ (Fin k)) (hv : v ≠ 0) :
    0 < ⟪polarPos Φ h v, v⟫ := by
  have hx : (WithLp.ofLp v : Fin k → ℝ) ≠ 0 := by
    intro hzero
    apply hv
    exact (WithLp.ofLp_eq_zero (p := 2)).mp hzero
  have hpos := (polarPosMatrix_posDef h).dotProduct_mulVec_pos hx
  rw [GramSchmidtTriangular.inner_eq_dotProduct]
  have hrw : WithLp.ofLp (polarPos Φ h v)
      = polarPosMatrix Φ h *ᵥ (WithLp.ofLp v) := rfl
  rw [hrw, dotProduct_comm]
  simpa using hpos

/-! ## The parametrized polar statement -/

/-- **The parametrized polar decomposition, isolated as a named obligation.**

The `QR` factorization above is smooth in the parameter with no extra input,
but its positive factor is only triangular.  If a *positive definite* smooth
factor is wanted — the literal shape of
`BridgeEntryStandardTarget.StandardEntryDatum.A` — the missing analytic input
is smoothness of the positive-definite square root `posDefSqrt`, equivalently
of the polar factor.  This is the standard fact that
`S ↦ S * S` is a local diffeomorphism at every positive definite `S` (its
derivative `X ↦ S * X + X * S` is invertible because the spectrum of `S` is
positive), together with uniqueness of positive definite square roots; neither
is currently available in Mathlib.  `SmoothPositiveFactor k` names exactly what
is needed.-/
structure SmoothPositiveFactor (d : ℕ) : Prop where
  smooth : ∀ {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (Ψ : T → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (_hΨ : ContDiff ℝ ∞ Ψ) (hdet : ∀ t, (clmMatrix (Ψ t)).det ≠ 0),
    ContDiff ℝ ∞ fun t => polarPos (Ψ t) (hdet t)

end PolarDecompositionCLM
end Submission
