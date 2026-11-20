import Tengoku.S3xs3LiEinstein.S3xS3.Trivial.Euler

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.EinsteinBridge

open S3xS3.Naturality
open S3xS3.Trivial.Graph
open S3xS3.Trivial.Euler

structure RawGraph where
  d : I3 → ℝ
  e : I3 → ℝ
  M : Mat3

structure RawPositive (r : RawGraph) : Prop where
  d_pos : ∀ i, 0 < r.d i
  e_pos : ∀ i, 0 < r.e i

def RawGraph.D (r : RawGraph) : Mat3 := Matrix.diagonal r.d
def RawGraph.E (r : RawGraph) : Mat3 := Matrix.diagonal r.e
def RawGraph.frame (r : RawGraph) : Mat6 := graphFrame r.D r.E r.M

noncomputable def RawGraph.p (r : RawGraph) : I3 → ℝ :=
  ![r.d 1 * r.d 2 / r.d 0,
    r.d 0 * r.d 2 / r.d 1,
    r.d 0 * r.d 1 / r.d 2]

noncomputable def RawGraph.q (r : RawGraph) : I3 → ℝ :=
  ![r.e 1 * r.e 2 / r.e 0,
    r.e 0 * r.e 2 / r.e 1,
    r.e 0 * r.e 1 / r.e 2]

noncomputable def RawGraph.P (r : RawGraph) : Mat3 := Matrix.diagonal r.p
noncomputable def RawGraph.Q (r : RawGraph) : Mat3 := Matrix.diagonal r.q

lemma RawPositive.p_pos {r : RawGraph} (h : RawPositive r) (i : I3) :
    0 < r.p i := by
  fin_cases i
  · simpa [RawGraph.p] using div_pos (mul_pos (h.d_pos 1) (h.d_pos 2)) (h.d_pos 0)
  · simpa [RawGraph.p] using div_pos (mul_pos (h.d_pos 0) (h.d_pos 2)) (h.d_pos 1)
  · simpa [RawGraph.p] using div_pos (mul_pos (h.d_pos 0) (h.d_pos 1)) (h.d_pos 2)

lemma RawPositive.q_pos {r : RawGraph} (h : RawPositive r) (i : I3) :
    0 < r.q i := by
  fin_cases i
  · simpa [RawGraph.q] using div_pos (mul_pos (h.e_pos 1) (h.e_pos 2)) (h.e_pos 0)
  · simpa [RawGraph.q] using div_pos (mul_pos (h.e_pos 0) (h.e_pos 2)) (h.e_pos 1)
  · simpa [RawGraph.q] using div_pos (mul_pos (h.e_pos 0) (h.e_pos 1)) (h.e_pos 2)

lemma RawPositive.D_posDef {r : RawGraph} (h : RawPositive r) : r.D.PosDef := by
  exact Matrix.posDef_diagonal_iff.mpr h.d_pos

lemma RawPositive.E_posDef {r : RawGraph} (h : RawPositive r) : r.E.PosDef := by
  exact Matrix.posDef_diagonal_iff.mpr h.e_pos

lemma RawPositive.P_posDef {r : RawGraph} (h : RawPositive r) : r.P.PosDef := by
  exact Matrix.posDef_diagonal_iff.mpr h.p_pos

lemma RawPositive.Q_posDef {r : RawGraph} (h : RawPositive r) : r.Q.PosDef := by
  exact Matrix.posDef_diagonal_iff.mpr h.q_pos

lemma RawGraph.D_sq_cofactor_P (r : RawGraph) (h : RawPositive r) :
    r.D * r.D = cofactor3 r.P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RawGraph.D, RawGraph.P, RawGraph.p, cofactor3,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt (h.d_pos 0), ne_of_gt (h.d_pos 1),
      ne_of_gt (h.d_pos 2)]

lemma RawGraph.E_sq_cofactor_Q (r : RawGraph) (h : RawPositive r) :
    r.E * r.E = cofactor3 r.Q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RawGraph.E, RawGraph.Q, RawGraph.q, cofactor3,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt (h.e_pos 0), ne_of_gt (h.e_pos 1),
      ne_of_gt (h.e_pos 2)]

lemma RawGraph.frame_det_ne_zero (r : RawGraph) (h : RawPositive r) :
    r.frame.det ≠ 0 :=
  graphFrame_det_ne_zero h.D_posDef h.E_posDef

noncomputable def RawGraph.metric (r : RawGraph) (h : RawPositive r) :
    LeftInvariantMetric := metricOfFrame r.frame (r.frame_det_ne_zero h)

noncomputable def RawGraph.graphData (r : RawGraph) (h : RawPositive r) :
    GraphData (r.metric h) where
  P := r.P
  Q := r.Q
  M := r.M
  D := r.D
  E := r.E
  P_pos := h.P_posDef
  Q_pos := h.Q_posDef
  D_pos := h.D_posDef
  E_pos := h.E_posDef
  D_sq := r.D_sq_cofactor_P h
  E_sq := r.E_sq_cofactor_Q h
  cometric_eq := by
    simpa [RawGraph.metric, RawGraph.frame] using
      metricOfFrame_gram_inv r.frame (r.frame_det_ne_zero h)

noncomputable def RawGraph.Dinv (r : RawGraph) : Mat3 :=
  Matrix.diagonal (fun i ↦ (r.d i)⁻¹)

noncomputable def RawGraph.Einv (r : RawGraph) : Mat3 :=
  Matrix.diagonal (fun i ↦ (r.e i)⁻¹)

noncomputable def RawGraph.inverseTranspose (r : RawGraph) : Mat6 :=
  Matrix.fromBlocks r.Dinv (-(r.Mᵀ * r.Einv)) 0 r.Einv

def frameVec (V : Mat6) (i : I6) : LieVec := V *ᵥ basisVec i

@[simp] lemma frameVec_apply (V : Mat6) (i j : I6) :
    frameVec V i j = V j i := by
  simp [frameVec, basisVec, Matrix.mulVec, dotProduct]

noncomputable def RawGraph.bracketCoeff (r : RawGraph) (i j k : I6) : ℝ :=
  (r.inverseTranspose *ᵥ bracket (frameVec r.frameᵀ i) (frameVec r.frameᵀ j)) k

noncomputable def RawGraph.gamma (r : RawGraph) (i j k : I6) : ℝ :=
  (r.bracketCoeff i j k - r.bracketCoeff j k i + r.bracketCoeff k i j) / 2

noncomputable def RawGraph.curvatureCoeff (r : RawGraph)
    (i j k n : I6) : ℝ :=
  (∑ m, r.gamma j k m * r.gamma i m n) -
    (∑ m, r.gamma i k m * r.gamma j m n) -
      ∑ m, r.bracketCoeff i j m * r.gamma m k n

noncomputable def RawGraph.ricciCoeff (r : RawGraph) (j k : I6) : ℝ :=
  ∑ i, r.curvatureCoeff i j k i

noncomputable def metricInnerLeftLinear (g : LeftInvariantMetric) (y : LieVec) :
    LieVec →ₗ[ℝ] ℝ where
  toFun := fun x ↦ metricInner g x y
  map_add' := fun x x' ↦ metricInner_add_left g x x' y
  map_smul' c x := by
    simp only [metricInner_smul_left, RingHom.id_apply, smul_eq_mul]

noncomputable def coordinateLinear (D : Mat6) (n : I6) :
    LieVec →ₗ[ℝ] ℝ where
  toFun := fun x ↦ (D *ᵥ x) n
  map_add' x y := by rw [Matrix.mulVec_add]; rfl
  map_smul' c x := by rw [Matrix.mulVec_smul]; rfl

noncomputable def RawGraph.residual (r : RawGraph) : Mat3 :=
  S3xS3.Trivial.Euler.residual r.P r.Q r.M

noncomputable def RawGraph.gradMExpr (r : RawGraph) : Mat3 :=
  -(r.M * lop' r.P) - dcof r.M (r.residual * r.P) + r.Q * r.residual

noncomputable def RawGraph.gradPExpr (r : RawGraph) : Mat3 :=
  r.P.trace • (1 : Mat3) - (2 : ℝ) • r.P -
      (r.Mᵀ * r.M).trace • r.P +
      (1 / 2 : ℝ) • (r.Mᵀ * r.M * r.P + r.P * (r.Mᵀ * r.M)) +
      dcof r.P (r.Mᵀ * r.M) -
      (1 / 2 : ℝ) •
        ((cofactor3 r.M)ᵀ * r.residual +
          ((cofactor3 r.M)ᵀ * r.residual)ᵀ)

noncomputable def RawGraph.gradQExpr (r : RawGraph) : Mat3 :=
  r.Q.trace • (1 : Mat3) - (2 : ℝ) • r.Q +
    (1 / 2 : ℝ) • (r.residual * r.Mᵀ + r.M * r.residualᵀ)

def otherJ : I3 → I3 := ![1, 0, 0]
def otherK : I3 → I3 := ![2, 2, 1]

end S3xS3.Trivial.EinsteinBridge
