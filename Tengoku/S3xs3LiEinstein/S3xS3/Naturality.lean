import Tengoku.S3xs3LiEinstein.S3xS3.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix BigOperators

namespace S3xS3.Naturality

@[simp] lemma bracket_add_left (x x' y : LieVec) :
    bracket (x + x') y = bracket x y + bracket x' y := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, cross_apply] <;> ring

@[simp] lemma bracket_add_right (x y y' : LieVec) :
    bracket x (y + y') = bracket x y + bracket x y' := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, cross_apply] <;> ring

@[simp] lemma bracket_smul_left (c : ℝ) (x y : LieVec) :
    bracket (c • x) y = c • bracket x y := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, cross_apply] <;> ring

@[simp] lemma bracket_smul_right (c : ℝ) (x y : LieVec) :
    bracket x (c • y) = c • bracket x y := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, cross_apply] <;> ring

@[simp] lemma metricInner_add_left (g : LeftInvariantMetric) (x x' y : LieVec) :
    metricInner g (x + x') y = metricInner g x y + metricInner g x' y := by
  simp [metricInner, add_dotProduct]

@[simp] lemma metricInner_add_right (g : LeftInvariantMetric) (x y y' : LieVec) :
    metricInner g x (y + y') = metricInner g x y + metricInner g x y' := by
  simp [metricInner, Matrix.mulVec_add, dotProduct_add]

@[simp] lemma metricInner_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    metricInner g (c • x) y = c * metricInner g x y := by
  simp [metricInner, smul_dotProduct]

@[simp] lemma metricInner_smul_right (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    metricInner g x (c • y) = c * metricInner g x y := by
  simp [metricInner, Matrix.mulVec_smul, dotProduct_smul]

/-- Koszul's trilinear expression before raising its final index.-/
noncomputable def koszulForm (g : LeftInvariantMetric) (x y z : LieVec) : ℝ :=
  (metricInner g (bracket x y) z - metricInner g (bracket y z) x +
    metricInner g (bracket z x) y) / 2

@[simp] lemma koszulForm_add_right (g : LeftInvariantMetric) (x y z z' : LieVec) :
    koszulForm g x y (z + z') =
      koszulForm g x y z + koszulForm g x y z' := by
  simp [koszulForm]
  ring

@[simp] lemma koszulForm_smul_right (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    koszulForm g x y (c • z) = c * koszulForm g x y z := by
  simp [koszulForm]
  ring

noncomputable def koszulFormRight (g : LeftInvariantMetric) (x y : LieVec) :
    LieVec →ₗ[ℝ] ℝ where
  toFun := koszulForm g x y
  map_add' := koszulForm_add_right g x y
  map_smul' c z := by
    simp only [koszulForm_smul_right, RingHom.id_apply, smul_eq_mul]

/-- The covector obtained from Koszul's expression by inserting coordinate
basis vectors in its final slot.-/
noncomputable def koszulCovector (g : LeftInvariantMetric) (x y : LieVec) :
    LieVec := fun i ↦ koszulForm g x y (basisVec i)

/-- The Levi-Civita connection on arbitrary coordinate vectors, obtained by
raising the Koszul covector with the inverse Gram matrix.-/
noncomputable def connectionVec (g : LeftInvariantMetric) (x y : LieVec) :
    LieVec := g.gram⁻¹ *ᵥ koszulCovector g x y

/-- Curvature on arbitrary coordinate vectors, with the same sign convention
as `curvatureComponent`.-/
noncomputable def curvatureVec (g : LeftInvariantMetric)
    (x y z : LieVec) : LieVec :=
  connectionVec g x (connectionVec g y z) -
    connectionVec g y (connectionVec g x z) -
      connectionVec g (bracket x y) z

lemma metricInner_bracket_basis (g : LeftInvariantMetric) (i j k : I6) :
    metricInner g (bracket (basisVec i) (basisVec j)) (basisVec k) =
      loweredBracket g i j k := by
  simp [metricInner, loweredBracket, structureConstant, basisVec,
    Matrix.mulVec, dotProduct]

lemma koszulForm_basis (g : LeftInvariantMetric) (i j k : I6) :
    koszulForm g (basisVec i) (basisVec j) (basisVec k) =
      koszulLower g i j k := by
  simp only [koszulForm, koszulLower, metricInner_bracket_basis]

@[simp] lemma koszulForm_add_left (g : LeftInvariantMetric)
    (x x' y z : LieVec) :
    koszulForm g (x + x') y z =
      koszulForm g x y z + koszulForm g x' y z := by
  simp [koszulForm]
  ring

@[simp] lemma koszulForm_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    koszulForm g (c • x) y z = c * koszulForm g x y z := by
  simp [koszulForm]
  ring

@[simp] lemma koszulForm_add_middle (g : LeftInvariantMetric)
    (x y y' z : LieVec) :
    koszulForm g x (y + y') z =
      koszulForm g x y z + koszulForm g x y' z := by
  simp [koszulForm]
  ring

@[simp] lemma koszulForm_smul_middle (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    koszulForm g x (c • y) z = c * koszulForm g x y z := by
  simp [koszulForm]
  ring

@[simp] lemma connectionVec_add_left (g : LeftInvariantMetric)
    (x x' y : LieVec) :
    connectionVec g (x + x') y =
      connectionVec g x y + connectionVec g x' y := by
  have hcov : koszulCovector g (x + x') y =
      koszulCovector g x y + koszulCovector g x' y := by
    funext k
    simp [koszulCovector]
  simp [connectionVec, hcov, Matrix.mulVec_add]

@[simp] lemma connectionVec_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    connectionVec g (c • x) y = c • connectionVec g x y := by
  have hcov : koszulCovector g (c • x) y = c • koszulCovector g x y := by
    funext k
    simp [koszulCovector]
  simp [connectionVec, hcov, Matrix.mulVec_smul]

@[simp] lemma connectionVec_add_right (g : LeftInvariantMetric)
    (x y y' : LieVec) :
    connectionVec g x (y + y') =
      connectionVec g x y + connectionVec g x y' := by
  have hcov : koszulCovector g x (y + y') =
      koszulCovector g x y + koszulCovector g x y' := by
    funext k
    simp [koszulCovector]
  simp [connectionVec, hcov, Matrix.mulVec_add]

@[simp] lemma connectionVec_smul_right (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    connectionVec g x (c • y) = c • connectionVec g x y := by
  have hcov : koszulCovector g x (c • y) = c • koszulCovector g x y := by
    funext k
    simp [koszulCovector]
  simp [connectionVec, hcov, Matrix.mulVec_smul]

noncomputable def connectionRight (g : LeftInvariantMetric) (x : LieVec) :
    LieVec →ₗ[ℝ] LieVec where
  toFun := connectionVec g x
  map_add' := connectionVec_add_right g x
  map_smul' c y := by
    simpa only [RingHom.id_apply] using connectionVec_smul_right g c x y

noncomputable def connectionLeft (g : LeftInvariantMetric) (y : LieVec) :
    LieVec →ₗ[ℝ] LieVec where
  toFun := fun x ↦ connectionVec g x y
  map_add' := fun x x' ↦ connectionVec_add_left g x x' y
  map_smul' c x := by
    simpa only [RingHom.id_apply] using connectionVec_smul_left g c x y

@[simp] lemma curvatureVec_add_left (g : LeftInvariantMetric)
    (x x' y z : LieVec) :
    curvatureVec g (x + x') y z =
      curvatureVec g x y z + curvatureVec g x' y z := by
  simp [curvatureVec]
  module

@[simp] lemma curvatureVec_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    curvatureVec g (c • x) y z = c • curvatureVec g x y z := by
  simp [curvatureVec]
  module

noncomputable def curvatureLeft (g : LeftInvariantMetric) (y z : LieVec) :
    LieVec →ₗ[ℝ] LieVec where
  toFun := fun x ↦ curvatureVec g x y z
  map_add' := fun x x' ↦ curvatureVec_add_left g x x' y z
  map_smul' c x := by
    simpa only [RingHom.id_apply] using curvatureVec_smul_left g c x y z

/-- Matrix of the curvature endomorphism `w ↦ R(w,x)y`; its column indexed
by `i` is the curvature vector evaluated on the `i`th basis vector.-/
noncomputable def curvatureEndomorphism (g : LeftInvariantMetric)
    (x y : LieVec) : Mat6 :=
  fun n i ↦ curvatureVec g (basisVec i) x y n

/-- Ricci as the trace of the curvature endomorphism.-/
noncomputable def ricciForm (g : LeftInvariantMetric) (x y : LieVec) : ℝ :=
  Matrix.trace (curvatureEndomorphism g x y)

@[simp] lemma curvatureVec_add_middle (g : LeftInvariantMetric)
    (x y y' z : LieVec) :
    curvatureVec g x (y + y') z =
      curvatureVec g x y z + curvatureVec g x y' z := by
  simp [curvatureVec]
  module

@[simp] lemma curvatureVec_smul_middle (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    curvatureVec g x (c • y) z = c • curvatureVec g x y z := by
  simp [curvatureVec]
  module

@[simp] lemma curvatureVec_add_right (g : LeftInvariantMetric)
    (x y z z' : LieVec) :
    curvatureVec g x y (z + z') =
      curvatureVec g x y z + curvatureVec g x y z' := by
  simp [curvatureVec]
  module

@[simp] lemma curvatureVec_smul_right (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    curvatureVec g x y (c • z) = c • curvatureVec g x y z := by
  simp [curvatureVec]
  module

@[simp] lemma ricciForm_add_left (g : LeftInvariantMetric)
    (x x' y : LieVec) :
    ricciForm g (x + x') y = ricciForm g x y + ricciForm g x' y := by
  have hM : curvatureEndomorphism g (x + x') y =
      curvatureEndomorphism g x y + curvatureEndomorphism g x' y := by
    ext i j
    simp [curvatureEndomorphism]
  rw [ricciForm, hM, Matrix.trace_add]
  rfl

@[simp] lemma ricciForm_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    ricciForm g (c • x) y = c * ricciForm g x y := by
  have hM : curvatureEndomorphism g (c • x) y =
      c • curvatureEndomorphism g x y := by
    ext i j
    simp [curvatureEndomorphism]
  rw [ricciForm, hM, Matrix.trace_smul]
  rfl

@[simp] lemma ricciForm_add_right (g : LeftInvariantMetric)
    (x y y' : LieVec) :
    ricciForm g x (y + y') = ricciForm g x y + ricciForm g x y' := by
  have hM : curvatureEndomorphism g x (y + y') =
      curvatureEndomorphism g x y + curvatureEndomorphism g x y' := by
    ext i j
    simp [curvatureEndomorphism]
  rw [ricciForm, hM, Matrix.trace_add]
  rfl

@[simp] lemma ricciForm_smul_right (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    ricciForm g x (c • y) = c * ricciForm g x y := by
  have hM : curvatureEndomorphism g x (c • y) =
      c • curvatureEndomorphism g x y := by
    ext i j
    simp [curvatureEndomorphism]
  rw [ricciForm, hM, Matrix.trace_smul]
  rfl

noncomputable def ricciLeft (g : LeftInvariantMetric) (y : LieVec) :
    LieVec →ₗ[ℝ] ℝ where
  toFun := fun x ↦ ricciForm g x y
  map_add' := fun x x' ↦ ricciForm_add_left g x x' y
  map_smul' c x := by
    simp only [ricciForm_smul_left, RingHom.id_apply, smul_eq_mul]

noncomputable def ricciRight (g : LeftInvariantMetric) (x : LieVec) :
    LieVec →ₗ[ℝ] ℝ where
  toFun := ricciForm g x
  map_add' := ricciForm_add_right g x
  map_smul' c y := by
    simp only [ricciForm_smul_right, RingHom.id_apply, smul_eq_mul]

end S3xS3.Naturality
