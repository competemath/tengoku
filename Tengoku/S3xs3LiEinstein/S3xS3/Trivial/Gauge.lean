import Tengoku.S3xs3LiEinstein.S3xS3.Trivial.PositiveEinstein

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.Gauge

open S3xS3.Naturality
open S3xS3.Trivial.Graph
open S3xS3.Trivial.EinsteinBridge
open S3xS3.Trivial.PositiveEinstein
open S3xS3.Trivial.Euler

def complementJ : I3 → I3 := ![1, 0, 0]
def complementK : I3 → I3 := ![2, 2, 1]

noncomputable def diagonalRoot (p : I3 → ℝ) : I3 → ℝ :=
  fun i ↦ Real.sqrt (p (complementJ i) * p (complementK i))

/--
@isnad1 id=lt.1h2v.s5.e73995620a77 from=translated src=- shape=fc3c31a9 vocab=e09f7316
-/
lemma diagonalRoot_pos {p : I3 → ℝ} (hp : ∀ i, 0 < p i) (i : I3) :
    0 < diagonalRoot p i := by
  exact Real.sqrt_pos.2 (mul_pos (hp _) (hp _))

/--
@isnad1 id=eq.1h2v.s5.d15588eb7f9f from=translated src=- shape=348f68d2 vocab=be13d4b4
-/
lemma diagonalRoot_sq {p : I3 → ℝ} (hp : ∀ i, 0 < p i) (i : I3) :
    diagonalRoot p i ^ 2 = p (complementJ i) * p (complementK i) := by
  exact Real.sq_sqrt (mul_pos (hp _) (hp _)).le

/--
@isnad1 id=eq.1h2v.s5.29c14cf1a453 from=translated src=- shape=feb7039a vocab=937fbad0
-/
lemma diagonalRoot_product {p : I3 → ℝ} (hp : ∀ i, 0 < p i)
    (i : I3) :
    diagonalRoot p (complementJ i) * diagonalRoot p (complementK i) =
      p i * diagonalRoot p i := by
  have h0 := diagonalRoot_sq hp 0
  have h1 := diagonalRoot_sq hp 1
  have h2 := diagonalRoot_sq hp 2
  have hd0 := diagonalRoot_pos hp 0
  have hd1 := diagonalRoot_pos hp 1
  have hd2 := diagonalRoot_pos hp 2
  simp [complementJ, complementK] at h0 h1 h2
  fin_cases i
  · simp [complementJ, complementK]
    have hsquare :
        (diagonalRoot p 1 * diagonalRoot p 2) ^ 2 =
          (p 0 * diagonalRoot p 0) ^ 2 := by
      rw [mul_pow, h1, h2, mul_pow, h0]
      ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with heq | heq
    · exact heq
    · have hl : 0 < diagonalRoot p 1 * diagonalRoot p 2 :=
        mul_pos hd1 hd2
      have hr : 0 < p 0 * diagonalRoot p 0 := mul_pos (hp 0) hd0
      nlinarith
  · simp [complementJ, complementK]
    have hsquare :
        (diagonalRoot p 0 * diagonalRoot p 2) ^ 2 =
          (p 1 * diagonalRoot p 1) ^ 2 := by
      rw [mul_pow, h0, h2, mul_pow, h1]
      ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with heq | heq
    · exact heq
    · have hl : 0 < diagonalRoot p 0 * diagonalRoot p 2 :=
        mul_pos hd0 hd2
      have hr : 0 < p 1 * diagonalRoot p 1 := mul_pos (hp 1) hd1
      nlinarith
  · simp [complementJ, complementK]
    have hsquare :
        (diagonalRoot p 0 * diagonalRoot p 1) ^ 2 =
          (p 2 * diagonalRoot p 2) ^ 2 := by
      rw [mul_pow, h0, h1, mul_pow, h2]
      ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with heq | heq
    · exact heq
    · have hl : 0 < diagonalRoot p 0 * diagonalRoot p 1 :=
        mul_pos hd0 hd1
      have hr : 0 < p 2 * diagonalRoot p 2 := mul_pos (hp 2) hd2
      nlinarith

noncomputable def rawOfDiagonalGraph {g : LeftInvariantMetric}
    (d : GraphData g) (p q : I3 → ℝ) : RawGraph where
  d := diagonalRoot p
  e := diagonalRoot q
  M := d.M

/--
@isnad1 id=rawposit.2h4v.s5.09abd856f728 from=translated src=- shape=d9107963 vocab=cdd5ea61
-/
lemma rawOfDiagonalGraph_positive {g : LeftInvariantMetric}
    (d : GraphData g) (p q : I3 → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    RawPositive (rawOfDiagonalGraph d p q) where
  d_pos := diagonalRoot_pos hp
  e_pos := diagonalRoot_pos hq

/--
@isnad1 id=eq.1h5v.s5.155430674d70 from=translated src=- shape=8635fb6a vocab=dbe8cdca
-/
lemma rawOfDiagonalGraph_p {g : LeftInvariantMetric}
    (d : GraphData g) (p q : I3 → ℝ)
    (hp : ∀ i, 0 < p i) (i : I3) :
    (rawOfDiagonalGraph d p q).p i = p i := by
  have hprod := diagonalRoot_product hp i
  have hden := ne_of_gt (diagonalRoot_pos hp i)
  fin_cases i
  · simp [rawOfDiagonalGraph, RawGraph.p] at hprod ⊢
    exact (div_eq_iff hden).2 hprod
  · simp [rawOfDiagonalGraph, RawGraph.p] at hprod ⊢
    exact (div_eq_iff hden).2 hprod
  · simp [rawOfDiagonalGraph, RawGraph.p] at hprod ⊢
    exact (div_eq_iff hden).2 hprod

/--
@isnad1 id=eq.1h5v.s5.1c7a5488ec6a from=translated src=- shape=d36405d0 vocab=8d734a14
-/
lemma rawOfDiagonalGraph_q {g : LeftInvariantMetric}
    (d : GraphData g) (p q : I3 → ℝ)
    (hq : ∀ i, 0 < q i) (i : I3) :
    (rawOfDiagonalGraph d p q).q i = q i := by
  have hprod := diagonalRoot_product hq i
  have hden := ne_of_gt (diagonalRoot_pos hq i)
  fin_cases i
  · simp [rawOfDiagonalGraph, RawGraph.q] at hprod ⊢
    exact (div_eq_iff hden).2 hprod
  · simp [rawOfDiagonalGraph, RawGraph.q] at hprod ⊢
    exact (div_eq_iff hden).2 hprod
  · simp [rawOfDiagonalGraph, RawGraph.q] at hprod ⊢
    exact (div_eq_iff hden).2 hprod

/--
@isnad1 id=eq.1h4v.s5.67749b6b5e30 from=translated src=- shape=6a826b9f vocab=8d9f1bb4
-/
lemma rawOfDiagonalGraph_P {g : LeftInvariantMetric}
    (d : GraphData g) (p q : I3 → ℝ) (hp : ∀ i, 0 < p i) :
    (rawOfDiagonalGraph d p q).P = Matrix.diagonal p := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [RawGraph.P, rawOfDiagonalGraph_p d p q hp]
  · simp [RawGraph.P, Matrix.diagonal, hij]

/--
@isnad1 id=eq.1h4v.s5.ebc63291aca4 from=translated src=- shape=3a89cb27 vocab=36090c4f
-/
lemma rawOfDiagonalGraph_Q {g : LeftInvariantMetric}
    (d : GraphData g) (p q : I3 → ℝ) (hq : ∀ i, 0 < q i) :
    (rawOfDiagonalGraph d p q).Q = Matrix.diagonal q := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [RawGraph.Q, rawOfDiagonalGraph_q d p q hq]
  · simp [RawGraph.Q, Matrix.diagonal, hij]

/--
@isnad1 id=eq.3h4v.s6.e4e1afa3ae10 from=translated src=- shape=38d6f339 vocab=f8464e66
-/
lemma rawOfDiagonalGraph_D_eq {g : LeftInvariantMetric}
    (d : GraphData g) (p q : I3 → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hP : d.P = Matrix.diagonal p) :
    (rawOfDiagonalGraph d p q).D = d.D := by
  let r := rawOfDiagonalGraph d p q
  let hr := rawOfDiagonalGraph_positive d p q hp hq
  apply posDef_sqrt_unique hr.D_posDef d.D_pos
  rw [r.D_sq_cofactor_P hr, rawOfDiagonalGraph_P d p q hp, ← hP,
    ← d.D_sq]

/--
@isnad1 id=eq.3h4v.s6.1a974ba435bc from=translated src=- shape=cf97ee7b vocab=c12ad86d
-/
lemma rawOfDiagonalGraph_E_eq {g : LeftInvariantMetric}
    (d : GraphData g) (p q : I3 → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hQ : d.Q = Matrix.diagonal q) :
    (rawOfDiagonalGraph d p q).E = d.E := by
  let r := rawOfDiagonalGraph d p q
  let hr := rawOfDiagonalGraph_positive d p q hp hq
  apply posDef_sqrt_unique hr.E_posDef d.E_pos
  rw [r.E_sq_cofactor_Q hr, rawOfDiagonalGraph_Q d p q hq, ← hQ,
    ← d.E_sq]

/--
@isnad1 id=eq.4h4v.s6.fa539f88e296 from=translated src=- shape=93c485c4 vocab=a08c73c1
-/
lemma rawOfDiagonalGraph_metric_eq {g : LeftInvariantMetric}
    (d : GraphData g) (p q : I3 → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hP : d.P = Matrix.diagonal p) (hQ : d.Q = Matrix.diagonal q) :
    (rawOfDiagonalGraph d p q).metric
      (rawOfDiagonalGraph_positive d p q hp hq) = g := by
  have hD := rawOfDiagonalGraph_D_eq d p q hp hq hP
  have hE := rawOfDiagonalGraph_E_eq d p q hp hq hQ
  have hframe : (rawOfDiagonalGraph d p q).frame =
      graphFrame d.D d.E d.M := by
    rw [RawGraph.frame, hD, hE]
    rfl
  let r := rawOfDiagonalGraph d p q
  let hr := rawOfDiagonalGraph_positive d p q hp hq
  calc
    r.metric hr = metricOfFrame r.frame (r.frame_det_ne_zero hr) := rfl
    _ = metricOfFrame (graphFrame d.D d.E d.M)
        (graphFrame_det_ne_zero d.D_pos d.E_pos) := by
      apply LeftInvariantMetric.ext
      simp only [metricOfFrame_gram]
      rw [show r.frame = graphFrame d.D d.E d.M by exact hframe]
    _ = g := d.metric_eq.symm

/--
@isnad1 id=eq.0h3v.s9.c39b23a2e83d from=translated src=- shape=05162f7b vocab=291c0e8c
-/
lemma cofactor3_two_sided_so3 (A : Mat3) (U V : SO3) :
    cofactor3 ((V : Mat3)ᵀ * A * U) =
      (V : Mat3)ᵀ * cofactor3 A * U := by
  rw [cofactor3_mul, cofactor3_mul, cofactor3_transpose,
    cofactor3_eq_of_mem_SO3, cofactor3_eq_of_mem_SO3]

/--
@isnad1 id=eq.0h2v.s5.4b1f2446ef5f from=translated src=- shape=869775bd vocab=f2694d52
-/
lemma cofactor3_add_polarization (A H : Mat3) :
    cofactor3 (A + H) = cofactor3 A + cofactor3 H + dcof A H := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cofactor3, dcof] <;> ring

/--
@isnad1 id=eq.0h4v.s10.891cd7f2850e from=translated src=- shape=a2739b1f vocab=59628170
-/
lemma dcof_two_sided_so3 (A H : Mat3) (U V : SO3) :
    dcof ((V : Mat3)ᵀ * A * U) ((V : Mat3)ᵀ * H * U) =
      (V : Mat3)ᵀ * dcof A H * U := by
  have hadd :
      (V : Mat3)ᵀ * A * U + (V : Mat3)ᵀ * H * U =
        (V : Mat3)ᵀ * (A + H) * U := by noncomm_ring
  calc
    dcof ((V : Mat3)ᵀ * A * U) ((V : Mat3)ᵀ * H * U) =
        cofactor3 ((V : Mat3)ᵀ * A * U + (V : Mat3)ᵀ * H * U) -
          cofactor3 ((V : Mat3)ᵀ * A * U) -
          cofactor3 ((V : Mat3)ᵀ * H * U) := by
            rw [cofactor3_add_polarization]
            abel
    _ = cofactor3 ((V : Mat3)ᵀ * (A + H) * U) -
          cofactor3 ((V : Mat3)ᵀ * A * U) -
          cofactor3 ((V : Mat3)ᵀ * H * U) := by rw [hadd]
    _ = (V : Mat3)ᵀ * cofactor3 (A + H) * U -
          (V : Mat3)ᵀ * cofactor3 A * U -
          (V : Mat3)ᵀ * cofactor3 H * U := by
            rw [cofactor3_two_sided_so3, cofactor3_two_sided_so3,
              cofactor3_two_sided_so3]
    _ = (V : Mat3)ᵀ * dcof A H * U := by
      rw [cofactor3_add_polarization]
      noncomm_ring

/--
@isnad1 id=eq.0h2v.s8.dfe0058623e0 from=translated src=- shape=1f6cdce3 vocab=db79214a
-/
lemma trace_so3_conjugate (A : Mat3) (U : SO3) :
    ((U : Mat3)ᵀ * A * U).trace = A.trace := by
  calc
    ((U : Mat3)ᵀ * A * U).trace =
        ((U : Mat3) * (U : Mat3)ᵀ * A).trace :=
      Matrix.trace_mul_cycle (U : Mat3)ᵀ A U
    _ = A.trace := by rw [so3_mul_transpose]; simp

/--
@isnad1 id=eq.0h1v.s8.aa171201021d from=translated src=- shape=0545f59d vocab=83cb85ff
-/
lemma so3_nonsing_inv (U : SO3) : (U : Mat3)⁻¹ = (U : Mat3)ᵀ := by
  have hU : IsUnit (U : Mat3) :=
    (Matrix.isUnit_iff_isUnit_det (U : Mat3)).mpr
      (isUnit_iff_ne_zero.mpr (by
        rw [(Matrix.mem_specialOrthogonalGroup_iff.mp U.property).2]
        exact one_ne_zero))
  apply hU.mul_right_cancel
  rw [(U : Mat3).nonsing_inv_mul
    ((Matrix.isUnit_iff_isUnit_det (U : Mat3)).mp hU),
    so3_transpose_mul]

/--
@isnad1 id=eq.0h1v.s8.162e0544b546 from=translated src=- shape=d03658bd vocab=83cb85ff
-/
lemma so3_transpose_nonsing_inv (U : SO3) :
    ((U : Mat3)ᵀ)⁻¹ = (U : Mat3) := by
  have hUt : IsUnit (U : Mat3)ᵀ :=
    (Matrix.isUnit_transpose (U : Mat3)).2
      ((Matrix.isUnit_iff_isUnit_det (U : Mat3)).mpr
        (isUnit_iff_ne_zero.mpr (by
          rw [(Matrix.mem_specialOrthogonalGroup_iff.mp U.property).2]
          exact one_ne_zero)))
  apply hUt.mul_right_cancel
  rw [(U : Mat3)ᵀ.nonsing_inv_mul
    ((Matrix.isUnit_iff_isUnit_det (U : Mat3)ᵀ).mp hUt),
    so3_mul_transpose]

/--
@isnad1 id=eq.0h5v.s10.45a7792186c4 from=translated src=- shape=241b0d66 vocab=247000f5
-/
lemma so3_two_sided_mul_ll (L O R : SO3) (A B : Mat3) :
    (((L : Mat3)ᵀ * A) * O) * (((O : Mat3)ᵀ * B) * R) =
      (L : Mat3)ᵀ * ((A * B) * R) := by
  calc
    (((L : Mat3)ᵀ * A) * O) * (((O : Mat3)ᵀ * B) * R) =
        (L : Mat3)ᵀ * A * ((O : Mat3) * (O : Mat3)ᵀ) * B * R := by
          noncomm_ring
    _ = (L : Mat3)ᵀ * ((A * B) * R) := by
      rw [so3_mul_transpose]
      simp
      noncomm_ring

/--
@isnad1 id=eq.0h5v.s10.3df2f9c23fd3 from=translated src=- shape=b47b7044 vocab=247000f5
-/
lemma so3_two_sided_mul_rl (L O R : SO3) (A B : Mat3) :
    ((L : Mat3)ᵀ * (A * O)) * (((O : Mat3)ᵀ * B) * R) =
      (L : Mat3)ᵀ * ((A * B) * R) := by
  calc
    ((L : Mat3)ᵀ * (A * O)) * (((O : Mat3)ᵀ * B) * R) =
        (L : Mat3)ᵀ * A * ((O : Mat3) * (O : Mat3)ᵀ) * B * R := by
          noncomm_ring
    _ = (L : Mat3)ᵀ * ((A * B) * R) := by
      rw [so3_mul_transpose]
      simp
      noncomm_ring

/--
@isnad1 id=eq.0h5v.s10.91d2cc63c8c3 from=translated src=- shape=c042c3a3 vocab=247000f5
-/
lemma so3_two_sided_mul_lr (L O R : SO3) (A B : Mat3) :
    (((L : Mat3)ᵀ * A) * O) * ((O : Mat3)ᵀ * (B * R)) =
      (L : Mat3)ᵀ * ((A * B) * R) := by
  calc
    (((L : Mat3)ᵀ * A) * O) * ((O : Mat3)ᵀ * (B * R)) =
        (L : Mat3)ᵀ * A * ((O : Mat3) * (O : Mat3)ᵀ) * B * R := by
          noncomm_ring
    _ = (L : Mat3)ᵀ * ((A * B) * R) := by
      rw [so3_mul_transpose]
      simp
      noncomm_ring

/--
@isnad1 id=eq.0h2v.s8.84f343a86808 from=translated src=- shape=eababfb8 vocab=597969d4
-/
lemma smul_one_so3_conjugate (c : ℝ) (U : SO3) :
    c • (1 : Mat3) = (U : Mat3)ᵀ * (c • (1 : Mat3)) * U := by
  rw [Matrix.mul_smul, Matrix.smul_mul]
  change c • (1 : Mat3) = c • ((U : Mat3)ᵀ * (1 : Mat3) * U)
  rw [Matrix.mul_one, so3_transpose_mul]

/--
@isnad1 id=eq.0h2v.s9.a650a0def301 from=translated src=- shape=ee6e82f4 vocab=c6fe85cf
-/
lemma inv_so3_conjugate (A : Mat3) (U : SO3) :
    ((U : Mat3)ᵀ * A * U)⁻¹ = (U : Mat3)ᵀ * A⁻¹ * U := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, so3_nonsing_inv,
    so3_transpose_nonsing_inv]
  noncomm_ring

def rotateP (P : Mat3) (U : SO3) : Mat3 := (U : Mat3)ᵀ * P * U
def rotateQ (Q : Mat3) (V : SO3) : Mat3 := (V : Mat3)ᵀ * Q * V
def rotateM (M : Mat3) (U V : SO3) : Mat3 := (V : Mat3)ᵀ * M * U

/--
@isnad1 id=eq.0h3v.s9.5640733f5a98 from=translated src=- shape=e2c46294 vocab=9f018d3d
-/
lemma rotateM_transpose_mul (M : Mat3) (U V : SO3) :
    (rotateM M U V)ᵀ * rotateM M U V =
      (U : Mat3)ᵀ * (Mᵀ * M) * U := by
  simp only [rotateM, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    (U : Mat3)ᵀ * (Mᵀ * V) * ((V : Mat3)ᵀ * M * U) =
        (U : Mat3)ᵀ * Mᵀ * ((V : Mat3) * (V : Mat3)ᵀ) * M * U := by
          noncomm_ring
    _ = (U : Mat3)ᵀ * (Mᵀ * M) * U := by
      rw [so3_mul_transpose]
      simp
      noncomm_ring

/--
@isnad1 id=eq.0h5v.s9.d6b410156fac from=translated src=- shape=26fbc432 vocab=d5034f8a
-/
lemma residual_rotate (P Q M : Mat3) (U V : SO3) :
    Euler.residual (rotateP P U) (rotateQ Q V) (rotateM M U V) =
      (V : Mat3)ᵀ * Euler.residual P Q M * U := by
  rw [Euler.residual, Euler.residual]
  simp only [rotateP, rotateQ, rotateM]
  rw [cofactor3_two_sided_so3]
  rw [show ((V : Mat3)ᵀ * cofactor3 M * U) *
          ((U : Mat3)ᵀ * P * U) =
        (V : Mat3)ᵀ * cofactor3 M *
          ((U : Mat3) * (U : Mat3)ᵀ) * P * U by noncomm_ring,
    show ((V : Mat3)ᵀ * Q * V) * ((V : Mat3)ᵀ * M * U) =
        (V : Mat3)ᵀ * Q * ((V : Mat3) * (V : Mat3)ᵀ) * M * U by
          noncomm_ring,
    so3_mul_transpose, so3_mul_transpose]
  simp
  noncomm_ring

noncomputable def gradPFormula (P Q M : Mat3) : Mat3 :=
  P.trace • (1 : Mat3) - (2 : ℝ) • P -
      (Mᵀ * M).trace • P +
      (1 / 2 : ℝ) • (Mᵀ * M * P + P * (Mᵀ * M)) +
      dcof P (Mᵀ * M) -
      (1 / 2 : ℝ) •
        ((cofactor3 M)ᵀ * Euler.residual P Q M +
          ((cofactor3 M)ᵀ * Euler.residual P Q M)ᵀ)

noncomputable def gradQFormula (P Q M : Mat3) : Mat3 :=
  Q.trace • (1 : Mat3) - (2 : ℝ) • Q +
    (1 / 2 : ℝ) •
      (Euler.residual P Q M * Mᵀ +
        M * (Euler.residual P Q M)ᵀ)

def gradMFormula (P Q M : Mat3) : Mat3 :=
  -(M * lop' P) - dcof M (Euler.residual P Q M * P) +
    Q * Euler.residual P Q M

/--
@isnad1 id=eq.0h5v.s9.30797c1437ff from=translated src=- shape=7b61b86f vocab=408c53bc
-/
lemma gradPFormula_rotate (P Q M : Mat3) (U V : SO3) :
    gradPFormula (rotateP P U) (rotateQ Q V) (rotateM M U V) =
      (U : Mat3)ᵀ * gradPFormula P Q M * U := by
  have hUU : (U : Mat3) * (U : Mat3)ᵀ = 1 := so3_mul_transpose U
  have hUtU : (U : Mat3)ᵀ * (U : Mat3) = 1 := so3_transpose_mul U
  have hVV : (V : Mat3) * (V : Mat3)ᵀ = 1 := so3_mul_transpose V
  rw [gradPFormula, gradPFormula, residual_rotate,
    rotateM_transpose_mul]
  simp only [rotateP, rotateM]
  rw [trace_so3_conjugate, trace_so3_conjugate,
    cofactor3_two_sided_so3, dcof_two_sided_so3]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [so3_two_sided_mul_ll U U U (Mᵀ * M) P,
    so3_two_sided_mul_ll U U U P (Mᵀ * M),
    so3_two_sided_mul_rl U V U (cofactor3 M)ᵀ
      (Euler.residual P Q M),
    so3_two_sided_mul_rl U V U (Euler.residual P Q M)ᵀ
      (cofactor3 M)]
  conv_lhs =>
    rw [smul_one_so3_conjugate P.trace U]
  noncomm_ring

/--
@isnad1 id=eq.0h5v.s9.e101f28586f3 from=translated src=- shape=ac11f4b7 vocab=3d9628d2
-/
lemma gradQFormula_rotate (P Q M : Mat3) (U V : SO3) :
    gradQFormula (rotateP P U) (rotateQ Q V) (rotateM M U V) =
      (V : Mat3)ᵀ * gradQFormula P Q M * V := by
  have hUU : (U : Mat3) * (U : Mat3)ᵀ = 1 := so3_mul_transpose U
  have hVV : (V : Mat3) * (V : Mat3)ᵀ = 1 := so3_mul_transpose V
  have hVtV : (V : Mat3)ᵀ * (V : Mat3) = 1 := so3_transpose_mul V
  rw [gradQFormula, gradQFormula, residual_rotate]
  simp only [rotateQ, rotateM]
  rw [trace_so3_conjugate]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [so3_two_sided_mul_lr V U V (Euler.residual P Q M) Mᵀ,
    so3_two_sided_mul_lr V U V M (Euler.residual P Q M)ᵀ]
  conv_lhs =>
    rw [smul_one_so3_conjugate Q.trace V]
  noncomm_ring

/--
@isnad1 id=eq.0h5v.s9.21ec616b0640 from=translated src=- shape=26fbc432 vocab=54655b91
-/
lemma gradMFormula_rotate (P Q M : Mat3) (U V : SO3) :
    gradMFormula (rotateP P U) (rotateQ Q V) (rotateM M U V) =
      (V : Mat3)ᵀ * gradMFormula P Q M * U := by
  rw [gradMFormula, gradMFormula, residual_rotate]
  simp only [rotateP, rotateQ, rotateM]
  rw [lop'_conjugate_so3]
  have hRP :
      ((V : Mat3)ᵀ * Euler.residual P Q M * U) *
          ((U : Mat3)ᵀ * P * U) =
        (V : Mat3)ᵀ * (Euler.residual P Q M * P) * U := by
    rw [show ((V : Mat3)ᵀ * Euler.residual P Q M * U) *
          ((U : Mat3)ᵀ * P * U) =
        (V : Mat3)ᵀ * Euler.residual P Q M *
          ((U : Mat3) * (U : Mat3)ᵀ) * P * U by noncomm_ring,
      so3_mul_transpose]
    simp
    noncomm_ring
  rw [hRP, dcof_two_sided_so3]
  rw [show ((V : Mat3)ᵀ * M * U) *
          ((U : Mat3)ᵀ * lop' P * U) =
        (V : Mat3)ᵀ * M * ((U : Mat3) * (U : Mat3)ᵀ) *
          lop' P * U by noncomm_ring,
    show ((V : Mat3)ᵀ * Q * V) *
          ((V : Mat3)ᵀ * Euler.residual P Q M * U) =
        (V : Mat3)ᵀ * Q * ((V : Mat3) * (V : Mat3)ᵀ) *
          Euler.residual P Q M * U by noncomm_ring,
    so3_mul_transpose, so3_mul_transpose]
  simp
  noncomm_ring

noncomputable def EulerData.rotate (d : EulerData) (U V : SO3) : EulerData where
  P := rotateP d.P U
  Q := rotateQ d.Q V
  M := rotateM d.M U V
  kappa := d.kappa
  P_pos := posDef_conjugate_so3 d.P_pos U
  Q_pos := posDef_conjugate_so3 d.Q_pos V
  kappa_pos := d.kappa_pos
  gradP := by
    change gradPFormula (rotateP d.P U) (rotateQ d.Q V)
        (rotateM d.M U V) = d.kappa • (rotateP d.P U)⁻¹
    rw [gradPFormula_rotate]
    simp only [rotateP]
    rw [inv_so3_conjugate]
    change (U : Mat3)ᵀ * gradPFormula d.P d.Q d.M * U = _
    have hd : gradPFormula d.P d.Q d.M = d.kappa • d.P⁻¹ := d.gradP
    rw [hd]
    simp
  gradQ := by
    change gradQFormula (rotateP d.P U) (rotateQ d.Q V)
        (rotateM d.M U V) = d.kappa • (rotateQ d.Q V)⁻¹
    rw [gradQFormula_rotate]
    simp only [rotateQ]
    rw [inv_so3_conjugate]
    change (V : Mat3)ᵀ * gradQFormula d.P d.Q d.M * V = _
    have hd : gradQFormula d.P d.Q d.M = d.kappa • d.Q⁻¹ := d.gradQ
    rw [hd]
    simp
  gradM := by
    change gradMFormula (rotateP d.P U) (rotateQ d.Q V)
        (rotateM d.M U V) = 0
    rw [gradMFormula_rotate]
    change (V : Mat3)ᵀ * gradMFormula d.P d.Q d.M * U = 0
    have hd : gradMFormula d.P d.Q d.M = 0 := d.gradM
    rw [hd]
    simp

end S3xS3.Trivial.Gauge
