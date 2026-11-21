import Tengoku.S3xs3LiEinstein.S3xS3.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix BigOperators

namespace S3xS3.Naturality

/--
@isnad1 id=eq.0h3v.s5.6a64af63bc1e from=translated src=- shape=2f6dc6a8 vocab=ea96859d
-/
@[simp] lemma bracket_add_left (x x' y : LieVec) :
    bracket (x + x') y = bracket x y + bracket x' y := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, cross_apply] <;> ring

/--
@isnad1 id=eq.0h3v.s5.f6af1e0b13c2 from=translated src=- shape=4a33f3d9 vocab=ea96859d
-/
@[simp] lemma bracket_add_right (x y y' : LieVec) :
    bracket x (y + y') = bracket x y + bracket x y' := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, cross_apply] <;> ring

/--
@isnad1 id=eq.0h3v.s5.ce9f911e0572 from=translated src=- shape=ce527358 vocab=0a6015b0
-/
@[simp] lemma bracket_smul_left (c : ℝ) (x y : LieVec) :
    bracket (c • x) y = c • bracket x y := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, cross_apply] <;> ring

/--
@isnad1 id=eq.0h3v.s5.2a28b5842f0a from=translated src=- shape=b5dd2775 vocab=0a6015b0
-/
@[simp] lemma bracket_smul_right (c : ℝ) (x y : LieVec) :
    bracket x (c • y) = c • bracket x y := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [bracket, cross_apply] <;> ring

/--
@isnad1 id=eq.0h4v.s5.f9095df6020f from=translated src=- shape=02dc05aa vocab=fb55e9ff
-/
@[simp] lemma metricInner_add_left (g : LeftInvariantMetric) (x x' y : LieVec) :
    metricInner g (x + x') y = metricInner g x y + metricInner g x' y := by
  simp [metricInner, add_dotProduct]

/--
@isnad1 id=eq.0h4v.s5.d49b9df0e918 from=translated src=- shape=cf435447 vocab=fb55e9ff
-/
@[simp] lemma metricInner_add_right (g : LeftInvariantMetric) (x y y' : LieVec) :
    metricInner g x (y + y') = metricInner g x y + metricInner g x y' := by
  simp [metricInner, Matrix.mulVec_add, dotProduct_add]

/--
@isnad1 id=eq.0h4v.s5.757d7fa89f70 from=translated src=- shape=ebdea9e6 vocab=24675053
-/
@[simp] lemma metricInner_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    metricInner g (c • x) y = c * metricInner g x y := by
  simp [metricInner, smul_dotProduct]

/--
@isnad1 id=eq.0h4v.s5.a820fda0aee8 from=translated src=- shape=79b88d46 vocab=24675053
-/
@[simp] lemma metricInner_smul_right (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    metricInner g x (c • y) = c * metricInner g x y := by
  simp [metricInner, Matrix.mulVec_smul, dotProduct_smul]

/-- Koszul's trilinear expression before raising its final index.-/
noncomputable def koszulForm (g : LeftInvariantMetric) (x y z : LieVec) : ℝ :=
  (metricInner g (bracket x y) z - metricInner g (bracket y z) x +
    metricInner g (bracket z x) y) / 2

/--
@isnad1 id=eq.0h5v.s5.befbc553bf91 from=translated src=- shape=5b3d9db2 vocab=6d936d70
-/
@[simp] lemma koszulForm_add_right (g : LeftInvariantMetric) (x y z z' : LieVec) :
    koszulForm g x y (z + z') =
      koszulForm g x y z + koszulForm g x y z' := by
  simp [koszulForm]
  ring

/--
@isnad1 id=eq.0h5v.s5.798dbf1e30f6 from=translated src=- shape=9b6c4778 vocab=418268cf
-/
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

/--
@isnad1 id=eq.0h4v.s4.daa1dec0e263 from=translated src=- shape=7c4f392e vocab=24c69dc2
-/
lemma metricInner_bracket_basis (g : LeftInvariantMetric) (i j k : I6) :
    metricInner g (bracket (basisVec i) (basisVec j)) (basisVec k) =
      loweredBracket g i j k := by
  simp [metricInner, loweredBracket, structureConstant, basisVec,
    Matrix.mulVec, dotProduct]

/--
@isnad1 id=eq.0h4v.s4.0cd436913190 from=translated src=- shape=2b01edbd vocab=e56c1192
-/
lemma koszulForm_basis (g : LeftInvariantMetric) (i j k : I6) :
    koszulForm g (basisVec i) (basisVec j) (basisVec k) =
      koszulLower g i j k := by
  simp only [koszulForm, koszulLower, metricInner_bracket_basis]

/--
@isnad1 id=eq.0h5v.s5.dde32250c7d4 from=translated src=- shape=89d76935 vocab=6d936d70
-/
@[simp] lemma koszulForm_add_left (g : LeftInvariantMetric)
    (x x' y z : LieVec) :
    koszulForm g (x + x') y z =
      koszulForm g x y z + koszulForm g x' y z := by
  simp [koszulForm]
  ring

/--
@isnad1 id=eq.0h5v.s5.4b0862ac78df from=translated src=- shape=ba05a98f vocab=418268cf
-/
@[simp] lemma koszulForm_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    koszulForm g (c • x) y z = c * koszulForm g x y z := by
  simp [koszulForm]
  ring

/--
@isnad1 id=eq.0h5v.s5.2f84f4068520 from=translated src=- shape=080ccab0 vocab=6d936d70
-/
@[simp] lemma koszulForm_add_middle (g : LeftInvariantMetric)
    (x y y' z : LieVec) :
    koszulForm g x (y + y') z =
      koszulForm g x y z + koszulForm g x y' z := by
  simp [koszulForm]
  ring

/--
@isnad1 id=eq.0h5v.s5.9b7e652ad519 from=translated src=- shape=5d13e84d vocab=418268cf
-/
@[simp] lemma koszulForm_smul_middle (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    koszulForm g x (c • y) z = c * koszulForm g x y z := by
  simp [koszulForm]
  ring

/--
@isnad1 id=eq.0h4v.s5.bf1679928c8a from=translated src=- shape=5c22fb93 vocab=959e3611
-/
@[simp] lemma connectionVec_add_left (g : LeftInvariantMetric)
    (x x' y : LieVec) :
    connectionVec g (x + x') y =
      connectionVec g x y + connectionVec g x' y := by
  have hcov : koszulCovector g (x + x') y =
      koszulCovector g x y + koszulCovector g x' y := by
    funext k
    simp [koszulCovector]
  simp [connectionVec, hcov, Matrix.mulVec_add]

/--
@isnad1 id=eq.0h4v.s5.9fe888bcaf8f from=translated src=- shape=da5a528a vocab=ba39978a
-/
@[simp] lemma connectionVec_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    connectionVec g (c • x) y = c • connectionVec g x y := by
  have hcov : koszulCovector g (c • x) y = c • koszulCovector g x y := by
    funext k
    simp [koszulCovector]
  simp [connectionVec, hcov, Matrix.mulVec_smul]

/--
@isnad1 id=eq.0h4v.s5.8b07b257db71 from=translated src=- shape=5584fc98 vocab=959e3611
-/
@[simp] lemma connectionVec_add_right (g : LeftInvariantMetric)
    (x y y' : LieVec) :
    connectionVec g x (y + y') =
      connectionVec g x y + connectionVec g x y' := by
  have hcov : koszulCovector g x (y + y') =
      koszulCovector g x y + koszulCovector g x y' := by
    funext k
    simp [koszulCovector]
  simp [connectionVec, hcov, Matrix.mulVec_add]

/--
@isnad1 id=eq.0h4v.s5.3bbfb9d73c1f from=translated src=- shape=d95a1542 vocab=ba39978a
-/
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

/--
@isnad1 id=eq.0h5v.s5.b6751664a63c from=translated src=- shape=740dbaee vocab=c00d8eb5
-/
@[simp] lemma curvatureVec_add_left (g : LeftInvariantMetric)
    (x x' y z : LieVec) :
    curvatureVec g (x + x') y z =
      curvatureVec g x y z + curvatureVec g x' y z := by
  simp [curvatureVec]
  module

/--
@isnad1 id=eq.0h5v.s5.3ee2bd295a41 from=translated src=- shape=e796a132 vocab=d249912b
-/
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

/--
@isnad1 id=eq.0h5v.s5.b181a36d0f73 from=translated src=- shape=a89f9f87 vocab=c00d8eb5
-/
@[simp] lemma curvatureVec_add_middle (g : LeftInvariantMetric)
    (x y y' z : LieVec) :
    curvatureVec g x (y + y') z =
      curvatureVec g x y z + curvatureVec g x y' z := by
  simp [curvatureVec]
  module

/--
@isnad1 id=eq.0h5v.s5.ac227c0812cc from=translated src=- shape=141320a3 vocab=d249912b
-/
@[simp] lemma curvatureVec_smul_middle (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    curvatureVec g x (c • y) z = c • curvatureVec g x y z := by
  simp [curvatureVec]
  module

/--
@isnad1 id=eq.0h5v.s5.23f4a643ae74 from=translated src=- shape=3909cec5 vocab=c00d8eb5
-/
@[simp] lemma curvatureVec_add_right (g : LeftInvariantMetric)
    (x y z z' : LieVec) :
    curvatureVec g x y (z + z') =
      curvatureVec g x y z + curvatureVec g x y z' := by
  simp [curvatureVec]
  module

/--
@isnad1 id=eq.0h5v.s5.c290e98ff45f from=translated src=- shape=a06051a8 vocab=d249912b
-/
@[simp] lemma curvatureVec_smul_right (g : LeftInvariantMetric) (c : ℝ)
    (x y z : LieVec) :
    curvatureVec g x y (c • z) = c • curvatureVec g x y z := by
  simp [curvatureVec]
  module

/--
@isnad1 id=eq.0h4v.s5.ce5cbba7faf0 from=translated src=- shape=02dc05aa vocab=3aec0623
-/
@[simp] lemma ricciForm_add_left (g : LeftInvariantMetric)
    (x x' y : LieVec) :
    ricciForm g (x + x') y = ricciForm g x y + ricciForm g x' y := by
  have hM : curvatureEndomorphism g (x + x') y =
      curvatureEndomorphism g x y + curvatureEndomorphism g x' y := by
    ext i j
    simp [curvatureEndomorphism]
  rw [ricciForm, hM, Matrix.trace_add]
  rfl

/--
@isnad1 id=eq.0h4v.s5.daa721faa672 from=translated src=- shape=ebdea9e6 vocab=d0e6c777
-/
@[simp] lemma ricciForm_smul_left (g : LeftInvariantMetric) (c : ℝ)
    (x y : LieVec) :
    ricciForm g (c • x) y = c * ricciForm g x y := by
  have hM : curvatureEndomorphism g (c • x) y =
      c • curvatureEndomorphism g x y := by
    ext i j
    simp [curvatureEndomorphism]
  rw [ricciForm, hM, Matrix.trace_smul]
  rfl

/--
@isnad1 id=eq.0h4v.s5.ad110d3ceb31 from=translated src=- shape=cf435447 vocab=3aec0623
-/
@[simp] lemma ricciForm_add_right (g : LeftInvariantMetric)
    (x y y' : LieVec) :
    ricciForm g x (y + y') = ricciForm g x y + ricciForm g x y' := by
  have hM : curvatureEndomorphism g x (y + y') =
      curvatureEndomorphism g x y + curvatureEndomorphism g x y' := by
    ext i j
    simp [curvatureEndomorphism]
  rw [ricciForm, hM, Matrix.trace_add]
  rfl

/--
@isnad1 id=eq.0h4v.s5.3c164776a3aa from=translated src=- shape=79b88d46 vocab=d0e6c777
-/
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
