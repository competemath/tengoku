import Tengoku.S3xs3LiEinstein.S3xS3.Naturality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.Graph

/--
@isnad1 id=eq.0h1v.s4.02f8d22af0e1 from=translated src=- shape=fb668585 vocab=9593c58a
-/
lemma cofactor3_transpose (A : Mat3) :
    cofactor3 Aᵀ = (cofactor3 A)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cofactor3] <;> ring

set_option maxHeartbeats 800000 in
/--
@isnad1 id=eq.0h2v.s5.0c79b0b8f0c0 from=translated src=- shape=95a13ccd vocab=12ac03c1
-/
lemma cofactor3_mul (A B : Mat3) :
    cofactor3 (A * B) = cofactor3 A * cofactor3 B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactor3, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/--
@isnad1 id=eq.0h2v.s9.d308cab41b7c from=translated src=- shape=260ecbf4 vocab=291c0e8c
-/
lemma cofactor3_so3_conjugate (U : SO3) (A : Mat3) :
    cofactor3 ((U : Mat3)ᵀ * A * U) =
      (U : Mat3)ᵀ * cofactor3 A * U := by
  rw [cofactor3_mul, cofactor3_mul, cofactor3_transpose,
    cofactor3_eq_of_mem_SO3]

noncomputable def invCof (C : Mat3) : Mat3 :=
  Real.sqrt C.det • C⁻¹

/--
@isnad1 id=posdef.1h1v.s4.d19c95e9b920 from=translated src=- shape=01966e3f vocab=a1b88ff0
-/
lemma invCof_posDef {C : Mat3} (hC : C.PosDef) : (invCof C).PosDef := by
  apply hC.inv.smul
  exact Real.sqrt_pos.2 hC.det_pos

/--
@isnad1 id=eq.1h1v.s5.f1edc8bcc0d9 from=translated src=- shape=0be51d28 vocab=62958088
-/
lemma det_invCof {C : Mat3} (hC : C.PosDef) :
    (invCof C).det = Real.sqrt C.det := by
  have hdet : 0 < C.det := hC.det_pos
  have hs : 0 < Real.sqrt C.det := Real.sqrt_pos.2 hdet
  have hs2 : (Real.sqrt C.det) ^ 2 = C.det := Real.sq_sqrt hdet.le
  rw [invCof, Matrix.det_smul, Matrix.det_nonsing_inv]
  simp only [Fintype.card_fin]
  rw [Ring.inverse_eq_inv]
  field_simp [ne_of_gt hdet]
  nlinarith [hs2]

/--
@isnad1 id=eq.1h1v.s4.9604ada674fc from=translated src=- shape=7e2fb2cb vocab=82879961
-/
lemma cofactor3_invCof {C : Mat3} (hC : C.PosDef) :
    cofactor3 (invCof C) = C := by
  let P := invCof C
  have hP : P.PosDef := invCof_posDef hC
  have hdetP : P.det = Real.sqrt C.det := det_invCof hC
  have hs : Real.sqrt C.det ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hC.det_pos)
  have hCunit : IsUnit C.det := isUnit_iff_ne_zero.mpr (ne_of_gt hC.det_pos)
  have hPinv : IsUnit P := hP.isUnit
  have hPtinv : IsUnit Pᵀ := (Matrix.isUnit_transpose P).2 hPinv
  apply hPtinv.mul_right_cancel
  rw [cofactor3_mul_transpose]
  change P.det • (1 : Mat3) = C * Pᵀ
  rw [hdetP]
  change Real.sqrt C.det • (1 : Mat3) =
    C * (Real.sqrt C.det • C⁻¹)ᵀ
  have hCt : Cᵀ = C := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hC.isHermitian.eq
  rw [Matrix.transpose_smul, Matrix.transpose_nonsing_inv, hCt]
  rw [Matrix.mul_smul, C.mul_nonsing_inv hCunit]

noncomputable def pdSqrt (A : Mat3) : Mat3 := CFC.sqrt A

/--
@isnad1 id=posdef.1h1v.s4.822c0bace4ef from=translated src=- shape=01966e3f vocab=e6584517
-/
lemma pdSqrt_posDef {A : Mat3} (hA : A.PosDef) : (pdSqrt A).PosDef := by
  have hspsd : (CFC.sqrt A).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  apply hspsd.posDef_iff_isUnit.mpr
  exact (CStarAlgebra.isStrictlyPositive_iff_isUnit_sqrt_and_eq_sqrt_mul_sqrt
    (a := A)).mp hA.isStrictlyPositive |>.1

/--
@isnad1 id=eq.1h1v.s5.f0c6beb53eb7 from=translated src=- shape=a57e7892 vocab=ea474255
-/
lemma pdSqrt_sq {A : Mat3} (hA : A.PosDef) :
    pdSqrt A * pdSqrt A = A := by
  exact CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg

/--
@isnad1 id=eq.1h1v.s4.5039c7265429 from=translated src=- shape=0af1b380 vocab=6df4f602
-/
lemma pdSqrt_transpose {A : Mat3} (hA : A.PosDef) :
    (pdSqrt A)ᵀ = pdSqrt A := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (pdSqrt_posDef hA).isHermitian.eq

/--
@isnad1 id=posdef.1h1v.s4.33e5f1327b73 from=translated src=- shape=6bf5a6ff vocab=1be9e7de
-/
lemma block22_posDef {K : Mat6} (hK : K.PosDef) : K.toBlocks₂₂.PosDef := by
  exact hK.submatrix Sum.inr_injective

/--
@isnad1 id=posdef.1h1v.s4.9b86fae396db from=translated src=- shape=6bf5a6ff vocab=2e7dc4e2
-/
lemma block11_posDef {K : Mat6} (hK : K.PosDef) : K.toBlocks₁₁.PosDef := by
  exact hK.submatrix Sum.inl_injective

/--
@isnad1 id=eq.1h1v.s5.c012b7d259e9 from=translated src=- shape=20d56cbe vocab=cc4b6443
-/
lemma block21_eq_transpose_block12 {K : Mat6} (hK : K.IsHermitian) :
    K.toBlocks₂₁ = K.toBlocks₁₂ᵀ := by
  ext i j
  have hij := congrFun (congrFun hK.eq (Sum.inl j)) (Sum.inr i)
  simpa [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hij

/--
@isnad1 id=posdef.1h1v.s7.7803633d03ec from=translated src=- shape=b6937f43 vocab=3c4cdbbf
-/
theorem schur_posDef {K : Mat6} (hK : K.PosDef) :
    (K.toBlocks₁₁ - K.toBlocks₁₂ * K.toBlocks₂₂⁻¹ *
      K.toBlocks₁₂ᵀ).PosDef := by
  let A : Mat3 := K.toBlocks₁₁
  let B : Mat3 := K.toBlocks₁₂
  let D : Mat3 := K.toBlocks₂₂
  have hD : D.PosDef := block22_posDef hK
  letI : Invertible D := hD.isUnit.invertible
  have hform : K = Matrix.fromBlocks A B Bᴴ D := by
    rw [← Matrix.fromBlocks_toBlocks K]
    congr 1
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      block21_eq_transpose_block12 hK.isHermitian
  have hA : A.PosDef := block11_posDef hK
  have hterm : (B * D⁻¹ * Bᴴ).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose B hD.isHermitian.inv
  have hSsym : (A - B * D⁻¹ * Bᴴ).IsHermitian :=
    hA.isHermitian.sub hterm
  have hS : (A - B * D⁻¹ * Bᴴ).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hSsym
    intro x hx
    let y : I3 → ℝ := -((D⁻¹ * Bᴴ) *ᵥ x)
    have hxy : Sum.elim x y ≠ 0 := by
      intro hz
      apply hx
      funext i
      have hi := congrFun hz (Sum.inl i)
      exact hi
    have hp := hK.dotProduct_mulVec_pos hxy
    rw [hform] at hp
    rw [Matrix.dotProduct_mulVec,
      Matrix.schur_complement_eq₂₂ A B x y hD.isHermitian] at hp
    rw [Matrix.dotProduct_mulVec]
    simpa [y, Matrix.conjTranspose_eq_transpose_of_trivial] using hp
  simpa [A, B, D, Matrix.conjTranspose_eq_transpose_of_trivial] using hS

def graphFrame (D E M : Mat3) : Mat6 :=
  Matrix.fromBlocks D 0 (M * D) E

structure GraphData (g : LeftInvariantMetric) where
  P : Mat3
  Q : Mat3
  M : Mat3
  D : Mat3
  E : Mat3
  P_pos : P.PosDef
  Q_pos : Q.PosDef
  D_pos : D.PosDef
  E_pos : E.PosDef
  D_sq : D * D = cofactor3 P
  E_sq : E * E = cofactor3 Q
  cometric_eq : g.gram⁻¹ = (graphFrame D E M)ᵀ * graphFrame D E M

/--
@isnad1 id=ne.2h3v.s6.ae6807935ecd from=translated src=- shape=6ba08bd0 vocab=bca57da1
-/
lemma graphFrame_det_ne_zero {D E M : Mat3}
    (hD : D.PosDef) (hE : E.PosDef) : (graphFrame D E M).det ≠ 0 := by
  rw [graphFrame, Matrix.det_fromBlocks_zero₁₂]
  exact mul_ne_zero (ne_of_gt hD.det_pos) (ne_of_gt hE.det_pos)

/--
@isnad1 id=eq.0h2v.s4.7ce84a25dbe5 from=translated src=- shape=7b49b693 vocab=646a65a5
-/
lemma GraphData.metric_eq (d : GraphData g) :
    g = metricOfFrame (graphFrame d.D d.E d.M)
      (graphFrame_det_ne_zero d.D_pos d.E_pos) := by
  apply LeftInvariantMetric.ext_of_inv_eq
  rw [metricOfFrame_gram_inv]
  exact d.cometric_eq

noncomputable def canonicalGraphData (g : LeftInvariantMetric) : GraphData g := by
  let K : Mat6 := g.gram⁻¹
  have hK : K.PosDef := g.posDef.inv
  let K11 : Mat3 := K.toBlocks₁₁
  let K12 : Mat3 := K.toBlocks₁₂
  let K21 : Mat3 := K.toBlocks₂₁
  let K22 : Mat3 := K.toBlocks₂₂
  have hK22 : K22.PosDef := block22_posDef hK
  let S : Mat3 := K11 - K12 * K22⁻¹ * K12ᵀ
  have hS : S.PosDef := by simpa [S, K11, K12, K22] using schur_posDef hK
  let E : Mat3 := pdSqrt K22
  let D : Mat3 := pdSqrt S
  have hE : E.PosDef := pdSqrt_posDef hK22
  have hD : D.PosDef := pdSqrt_posDef hS
  let W : Mat3 := E⁻¹ * K21
  let M : Mat3 := W * D⁻¹
  let CP : Mat3 := D * D
  let CQ : Mat3 := E * E
  have hCP : CP.PosDef := by
    change (D * D).PosDef
    rw [show D * D = S by simpa [D] using pdSqrt_sq hS]
    exact hS
  have hCQ : CQ.PosDef := by
    change (E * E).PosDef
    rw [show E * E = K22 by simpa [E] using pdSqrt_sq hK22]
    exact hK22
  let P : Mat3 := invCof CP
  let Q : Mat3 := invCof CQ
  have hP : P.PosDef := invCof_posDef hCP
  have hQ : Q.PosDef := invCof_posDef hCQ
  refine
    { P := P, Q := Q, M := M, D := D, E := E
      P_pos := hP, Q_pos := hQ, D_pos := hD, E_pos := hE
      D_sq := ?_, E_sq := ?_, cometric_eq := ?_ }
  · exact (cofactor3_invCof hCP).symm
  · exact (cofactor3_invCof hCQ).symm
  · change K = (graphFrame D E M)ᵀ * graphFrame D E M
    have hKsym : K21 = K12ᵀ := by
      simpa [K21, K12] using block21_eq_transpose_block12 hK.isHermitian
    have hEsq : E * E = K22 := pdSqrt_sq hK22
    have hDsq : D * D = S := pdSqrt_sq hS
    have hEt : Eᵀ = E := pdSqrt_transpose hK22
    have hDt : Dᵀ = D := pdSqrt_transpose hS
    have hEu : IsUnit E := hE.isUnit
    have hDu : IsUnit D := hD.isUnit
    have hEdetu : IsUnit E.det := (Matrix.isUnit_iff_isUnit_det E).mp hEu
    have hDdetu : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hDu
    have hK22u : IsUnit K22 := hK22.isUnit
    have hED : W * D⁻¹ * D = W := by
      rw [Matrix.mul_assoc, D.nonsing_inv_mul hDdetu]
      simp
    have hEW : E * W = K21 := by
      change E * (E⁻¹ * K21) = K21
      rw [← Matrix.mul_assoc, E.mul_nonsing_inv hEdetu]
      simp
    have hWtE : Wᵀ * E = K12 := by
      rw [← hEt, ← Matrix.transpose_mul, hEW, hKsym,
        Matrix.transpose_transpose]
    have hWtW : Wᵀ * W = K12 * K22⁻¹ * K12ᵀ := by
      change (E⁻¹ * K21)ᵀ * (E⁻¹ * K21) = _
      rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hEt, hKsym]
      have hEinvSq : E⁻¹ * E⁻¹ = K22⁻¹ := by
        rw [← Matrix.mul_inv_rev, hEsq]
      rw [Matrix.transpose_transpose]
      calc
        (K12 * E⁻¹) * (E⁻¹ * K12ᵀ) =
            K12 * (E⁻¹ * E⁻¹) * K12ᵀ := by noncomm_ring
        _ = _ := by rw [hEinvSq]
    rw [← Matrix.fromBlocks_toBlocks K]
    rw [graphFrame, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply]
    apply Matrix.fromBlocks_inj.mpr
    constructor
    · change K11 = Dᵀ * D + (M * D)ᵀ * (M * D)
      rw [hDt, show M * D = W by exact hED, hDsq, hWtW]
      dsimp [S]
      abel
    constructor
    · change K12 = Dᵀ * 0 + (M * D)ᵀ * E
      simp [show M * D = W by exact hED, hWtE]
    constructor
    · change K21 = 0ᵀ * D + Eᵀ * (M * D)
      simp [hEt, show M * D = W by exact hED, hEW]
    · change K22 = 0ᵀ * 0 + Eᵀ * E
      simp [hEt, hEsq]

/--
@isnad1 id=eq.0h1v.s8.4e5e10e80f59 from=translated src=- shape=44b85815 vocab=e4ff7962
-/
lemma so3_mul_transpose (U : SO3) :
    (U : Mat3) * (U : Mat3)ᵀ = 1 :=
  (Matrix.mem_orthogonalGroup_iff I3 ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1

/--
@isnad1 id=eq.0h1v.s8.a2f174f88b75 from=translated src=- shape=ee403c13 vocab=e4ff7962
-/
lemma so3_transpose_mul (U : SO3) :
    (U : Mat3)ᵀ * (U : Mat3) = 1 :=
  (Matrix.mem_orthogonalGroup_iff' I3 ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1

/--
@isnad1 id=posdef.1h2v.s8.35f2fcf808c4 from=translated src=- shape=cbcd7142 vocab=132b260a
-/
lemma posDef_conjugate_so3 {A : Mat3} (hA : A.PosDef) (U : SO3) :
    ((U : Mat3)ᵀ * A * U).PosDef := by
  have hunit : IsUnit (U : Mat3) :=
    IsUnit.of_mul_eq_one (U : Mat3)ᵀ (so3_mul_transpose U)
  have hinj : Function.Injective (U : Mat3).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hA.conjTranspose_mul_mul_same hinj

/--
@isnad1 id=eq.3h2v.s6.7de2ce76d1db from=translated src=- shape=75f11a0d vocab=74f9cc3b
-/
lemma posDef_sqrt_unique {A B : Mat3} (hA : A.PosDef) (hB : B.PosDef)
    (hsq : A * A = B * B) : A = B := by
  exact (CFC.mul_self_eq_mul_self_iff A B
    hA.posSemidef.nonneg hB.posSemidef.nonneg).mp hsq

/--
@isnad1 id=eq.0h5v.s10.f5339c99f102 from=translated src=- shape=746b3840 vocab=3446883e
-/
lemma graphFrame_conjugate (D E M : Mat3) (U V : SO3) :
    Matrix.fromBlocks (U : Mat3)ᵀ 0 0 (V : Mat3)ᵀ *
        graphFrame D E M *
        Matrix.fromBlocks (U : Mat3) 0 0 (V : Mat3) =
      graphFrame ((U : Mat3)ᵀ * D * U) ((V : Mat3)ᵀ * E * V)
        ((V : Mat3)ᵀ * M * U) := by
  rw [graphFrame, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  apply Matrix.fromBlocks_inj.mpr
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp
    calc
      (V : Mat3)ᵀ * (M * D) * U =
          (V : Mat3)ᵀ * M *
            ((U : Mat3) * (U : Mat3)ᵀ) * D * U := by
        rw [so3_mul_transpose]
        simp
        noncomm_ring
      _ = ((V : Mat3)ᵀ * M * U) *
          ((U : Mat3)ᵀ * D * U) := by noncomm_ring
  · simp

noncomputable def GraphData.pullback (d : GraphData g) (U V : SO3) :
    GraphData (pullbackMetric (U, V) g) := by
  let P' : Mat3 := (U : Mat3)ᵀ * d.P * U
  let Q' : Mat3 := (V : Mat3)ᵀ * d.Q * V
  let M' : Mat3 := (V : Mat3)ᵀ * d.M * U
  let D' : Mat3 := (U : Mat3)ᵀ * d.D * U
  let E' : Mat3 := (V : Mat3)ᵀ * d.E * V
  have hP' : P'.PosDef := posDef_conjugate_so3 d.P_pos U
  have hQ' : Q'.PosDef := posDef_conjugate_so3 d.Q_pos V
  have hD' : D'.PosDef := posDef_conjugate_so3 d.D_pos U
  have hE' : E'.PosDef := posDef_conjugate_so3 d.E_pos V
  refine
    { P := P', Q := Q', M := M', D := D', E := E'
      P_pos := hP', Q_pos := hQ', D_pos := hD', E_pos := hE'
      D_sq := ?_, E_sq := ?_, cometric_eq := ?_ }
  · change ((U : Mat3)ᵀ * d.D * U) * ((U : Mat3)ᵀ * d.D * U) =
      cofactor3 ((U : Mat3)ᵀ * d.P * U)
    calc
      ((U : Mat3)ᵀ * d.D * U) * ((U : Mat3)ᵀ * d.D * U) =
          (U : Mat3)ᵀ * (d.D * d.D) * U := by
        calc
          _ = (U : Mat3)ᵀ * d.D *
              ((U : Mat3) * (U : Mat3)ᵀ) * d.D * U := by noncomm_ring
          _ = _ := by rw [so3_mul_transpose]; simp; noncomm_ring
      _ = (U : Mat3)ᵀ * cofactor3 d.P * U := by rw [d.D_sq]
      _ = _ := (cofactor3_so3_conjugate U d.P).symm
  · change ((V : Mat3)ᵀ * d.E * V) * ((V : Mat3)ᵀ * d.E * V) =
      cofactor3 ((V : Mat3)ᵀ * d.Q * V)
    calc
      ((V : Mat3)ᵀ * d.E * V) * ((V : Mat3)ᵀ * d.E * V) =
          (V : Mat3)ᵀ * (d.E * d.E) * V := by
        calc
          _ = (V : Mat3)ᵀ * d.E *
              ((V : Mat3) * (V : Mat3)ᵀ) * d.E * V := by noncomm_ring
          _ = _ := by rw [so3_mul_transpose]; simp; noncomm_ring
      _ = (V : Mat3)ᵀ * cofactor3 d.Q * V := by rw [d.E_sq]
      _ = _ := (cofactor3_so3_conjugate V d.Q).symm
  · let A : Mat6 := graphFrame d.D d.E d.M
    let A' : Mat6 := graphFrame D' E' M'
    let T : Mat6 := innerMatrix (U, V)
    have hA' : A' = Tᵀ * A * T := by
      dsimp [A', D', E', M', T, innerMatrix]
      rw [Matrix.fromBlocks_transpose]
      simp only [Matrix.transpose_zero]
      exact (graphFrame_conjugate d.D d.E d.M U V).symm
    have hTT' : T * Tᵀ = 1 := innerMatrix_mul_transpose (U, V)
    rw [pullbackMetric_gram_inv, d.cometric_eq]
    change Tᵀ * (Aᵀ * A) * T = A'ᵀ * A'
    rw [hA', Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    calc
      Tᵀ * (Aᵀ * A) * T =
          Tᵀ * Aᵀ * (T * Tᵀ) * A * T := by rw [hTT']; simp; noncomm_ring
      _ = Tᵀ * (Aᵀ * T) * (Tᵀ * A * T) := by
        noncomm_ring

def orientationCorrection (W : Mat3) : Mat3 :=
  Matrix.diagonal ![W.det, (1 : ℝ), (1 : ℝ)]

def orientedMatrix (W : Mat3) : Mat3 := W * orientationCorrection W

/--
@isnad1 id=eq.1h1v.s6.3ec715364fdc from=translated src=- shape=f3ea7001 vocab=58bd75b7
-/
lemma det_sq_of_transpose_mul_eq_one {W : Mat3} (hW : Wᵀ * W = 1) :
    W.det ^ 2 = 1 := by
  have h := congrArg Matrix.det hW
  rw [Matrix.det_mul, Matrix.det_transpose] at h
  simpa [pow_two] using h

/--
@isnad1 id=eq.0h1v.s3.2e8f33498a4d from=translated src=- shape=972a3510 vocab=066e126d
-/
lemma orientationCorrection_transpose (W : Mat3) :
    (orientationCorrection W)ᵀ = orientationCorrection W := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [orientationCorrection]

/--
@isnad1 id=eq.1h1v.s6.176a411ab6ac from=translated src=- shape=b1154ac1 vocab=c07c2294
-/
lemma orientationCorrection_sq {W : Mat3} (hW : Wᵀ * W = 1) :
    orientationCorrection W * orientationCorrection W = 1 := by
  have hd := det_sq_of_transpose_mul_eq_one hW
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orientationCorrection, Matrix.mul_apply, Fin.sum_univ_succ] ;
    nlinarith

/--
@isnad1 id=eq.1h1v.s6.0d2d8150372e from=translated src=- shape=39d5b57d vocab=32b77216
-/
lemma orientedMatrix_transpose_mul {W : Mat3} (hW : Wᵀ * W = 1) :
    (orientedMatrix W)ᵀ * orientedMatrix W = 1 := by
  rw [orientedMatrix, Matrix.transpose_mul, orientationCorrection_transpose]
  calc
    orientationCorrection W * Wᵀ * (W * orientationCorrection W) =
        orientationCorrection W * (Wᵀ * W) * orientationCorrection W := by
      noncomm_ring
    _ = 1 := by rw [hW]; simpa using orientationCorrection_sq hW

/--
@isnad1 id=eq.1h1v.s6.637ab2b99912 from=translated src=- shape=188719ef vocab=02d46750
-/
lemma orientedMatrix_det {W : Mat3} (hW : Wᵀ * W = 1) :
    (orientedMatrix W).det = 1 := by
  have hd := det_sq_of_transpose_mul_eq_one hW
  rw [orientedMatrix, Matrix.det_mul]
  have hc : (orientationCorrection W).det = W.det := by
    rw [orientationCorrection, Matrix.det_diagonal]
    simp [Fin.prod_univ_succ]
  rw [hc]
  simpa [pow_two] using hd

def orientedSO3 (W : Mat3) (hW : Wᵀ * W = 1) : SO3 :=
  ⟨orientedMatrix W, (Matrix.mem_specialOrthogonalGroup_iff).2
    ⟨(Matrix.mem_orthogonalGroup_iff' I3 ℝ).2
      (orientedMatrix_transpose_mul hW), orientedMatrix_det hW⟩⟩

end S3xS3.Trivial.Graph
