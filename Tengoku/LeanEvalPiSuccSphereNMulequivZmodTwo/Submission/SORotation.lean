import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SphereClose

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical short-distance rotations in `SO(n)`

For non-antipodal unit vectors `x, y ∈ Sⁿ⁻¹ ⊆ ℝⁿ` we construct the canonical rotation
`Submission.rotTo x y ∈ SO(n)` that maps `x` to `y`, rotates in the plane `span {x, y}`,
and fixes its orthogonal complement pointwise.  It is defined as the product of two
Householder reflections,

  `rotTo x y = reflMatrix (x + y) * reflMatrix x`,

which makes orthogonality, `det = 1`, the evaluation `rotTo x y • x = y`, the identity
`rotTo x x = 1`, and joint continuity in `(x, y)` all short computations.

Main declarations:

* `Submission.reflMatrix u`: the Householder reflection `1 - (2 / ⟨u,u⟩) • u uᵀ`;
* `Submission.rotToAux x y`: raw-matrix rotation, with `rotToAux_mem_specialOrthogonalGroup`,
  `rotToAux_mulVec_self`, `rotToAux_same`;
* `Submission.rotTo x y : SO n` (junk value `1` for antipodal pairs) with
  `rotTo_coe`, `rotTo_mulVec`, `rotTo_self`, `Submission.continuous_rotTo`;
* topology: `Submission.instContinuousInvSO`, `Submission.instIsTopologicalGroupSO`;
* sphere bookkeeping: `Submission.coords`, `coords_dotProduct_self`,
  `neg_one_lt_coords_dot_of_dist_lt_two`.
-/

noncomputable section

open Matrix
open scoped RealInnerProductSpace

namespace Submission

/-! ## The special orthogonal group as a topological group -/

/-- Shorthand for the special orthogonal group `SO(n)` over `ℝ`.-/
abbrev SOGroup (n : ℕ) := Matrix.specialOrthogonalGroup (Fin n) ℝ

theorem continuous_SOGroup_val {n : ℕ} :
    Continuous fun A : SOGroup n => (A : Matrix (Fin n) (Fin n) ℝ) :=
  continuous_subtype_val

/-- Inversion in `SO(n)` is (conjugate-)transposition, hence continuous.-/
instance instContinuousInvSO (n : ℕ) : ContinuousInv (SOGroup n) := by
  refine ⟨?_⟩
  have h : ∀ A : SOGroup n,
      ((A⁻¹ : SOGroup n) : Matrix (Fin n) (Fin n) ℝ)
        = star (A : Matrix (Fin n) (Fin n) ℝ) := fun A => rfl
  apply continuous_induced_rng.2
  have hc : Continuous fun A : SOGroup n => star (A : Matrix (Fin n) (Fin n) ℝ) :=
    continuous_star.comp continuous_subtype_val
  simpa [Function.comp_def, h] using hc

/-! ## Householder reflections -/

variable {n : ℕ}

/-- The Householder reflection about the hyperplane orthogonal to `u`
(with the junk value `1` for `u = 0`, since `2 / 0 = 0`).-/
def reflMatrix (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (2 / (u ⬝ᵥ u)) • Matrix.vecMulVec u u

theorem reflMatrix_apply (u : Fin n → ℝ) (i j : Fin n) :
    reflMatrix u i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j - 2 / (u ⬝ᵥ u) * (u i * u j) := by
  simp [reflMatrix, Matrix.vecMulVec_apply]

theorem reflMatrix_transpose (u : Fin n → ℝ) : (reflMatrix u)ᵀ = reflMatrix u := by
  ext i j
  simp only [Matrix.transpose_apply, reflMatrix_apply]
  rw [Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; ring
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]; ring

theorem vecMulVec_mul_vecMulVec (u v w z : Fin n → ℝ) :
    Matrix.vecMulVec u v * Matrix.vecMulVec w z = (v ⬝ᵥ w) • Matrix.vecMulVec u z := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, dotProduct,
    smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => by ring

theorem vecMulVec_mulVec (u v w : Fin n → ℝ) :
    Matrix.vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => by ring

theorem vecMulVec_smul_left (a : ℝ) (u v : Fin n → ℝ) :
    Matrix.vecMulVec (a • u) v = a • Matrix.vecMulVec u v := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem vecMulVec_smul_right (a : ℝ) (u v : Fin n → ℝ) :
    Matrix.vecMulVec u (a • v) = a • Matrix.vecMulVec u v := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `reflMatrix` is invariant under nonzero rescaling of `u`.-/
theorem reflMatrix_smul {a : ℝ} (ha : a ≠ 0) (u : Fin n → ℝ) :
    reflMatrix (a • u) = reflMatrix u := by
  have hdot : (a • u) ⬝ᵥ (a • u) = a * a * (u ⬝ᵥ u) := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  have hvv : Matrix.vecMulVec (a • u) (a • u) = (a * a) • Matrix.vecMulVec u u := by
    rw [vecMulVec_smul_left, vecMulVec_smul_right, smul_smul]
  have hcoef : 2 / (a * a * (u ⬝ᵥ u)) * (a * a) = 2 / (u ⬝ᵥ u) := by
    by_cases hu : u ⬝ᵥ u = 0
    · simp [hu]
    · field_simp
  rw [reflMatrix, reflMatrix, hdot, hvv, smul_smul, hcoef]

theorem reflMatrix_mulVec (u w : Fin n → ℝ) :
    reflMatrix u *ᵥ w = w - (2 / (u ⬝ᵥ u) * (u ⬝ᵥ w)) • u := by
  rw [reflMatrix, Matrix.sub_mulVec, Matrix.one_mulVec, smul_mulVec, vecMulVec_mulVec,
    smul_smul]

theorem reflMatrix_mulVec_self {u : Fin n → ℝ} (hu : u ⬝ᵥ u ≠ 0) :
    reflMatrix u *ᵥ u = -u := by
  rw [reflMatrix_mulVec, div_mul_cancel₀ 2 hu]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

theorem reflMatrix_mul_self {u : Fin n → ℝ} (hu : u ⬝ᵥ u ≠ 0) :
    reflMatrix u * reflMatrix u = 1 := by
  have hMM : Matrix.vecMulVec u u * Matrix.vecMulVec u u
      = (u ⬝ᵥ u) • Matrix.vecMulVec u u := vecMulVec_mul_vecMulVec u u u u
  have hs : (2 / (u ⬝ᵥ u) * (2 / (u ⬝ᵥ u))) * (u ⬝ᵥ u)
      = 2 / (u ⬝ᵥ u) + 2 / (u ⬝ᵥ u) := by
    field_simp
    ring
  set c : ℝ := 2 / (u ⬝ᵥ u)
  set M := Matrix.vecMulVec u u
  have expand : (1 - c • M) * (1 - c • M) = 1 - c • M - c • M + (c * c) • (M * M) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    abel
  show (1 - c • M) * (1 - c • M) = 1
  rw [expand, hMM, smul_smul, hs, add_smul]
  abel

theorem reflMatrix_mem_orthogonalGroup {u : Fin n → ℝ} (hu : u ⬝ᵥ u ≠ 0) :
    reflMatrix u ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, reflMatrix_transpose]
  exact reflMatrix_mul_self hu

theorem det_reflMatrix {u : Fin n → ℝ} (hu : u ⬝ᵥ u ≠ 0) :
    (reflMatrix u).det = -1 := by
  have h1 : reflMatrix u
      = 1 + Matrix.replicateCol Unit ((-(2 / (u ⬝ᵥ u))) • u) * Matrix.replicateRow Unit u := by
    rw [← Matrix.vecMulVec_eq, vecMulVec_smul_left, reflMatrix, neg_smul, ← sub_eq_add_neg]
  rw [h1, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul]
  field_simp
  norm_num

/-! ## The canonical rotation, raw-matrix level -/

/-- The rotation taking `x` to `y` (for unit vectors with `x ⬝ᵥ y ≠ -1`): product of the
Householder reflections in `x + y` and in `x`.-/
def rotToAux (x y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  reflMatrix (x + y) * reflMatrix x

section RotToAux

variable {x y : Fin n → ℝ}

theorem add_dotProduct_add (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1) :
    (x + y) ⬝ᵥ (x + y) = 2 + 2 * (x ⬝ᵥ y) := by
  rw [add_dotProduct, dotProduct_add, dotProduct_add, hx, hy, dotProduct_comm y x]
  ring

theorem add_dotProduct_add_ne_zero (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1)
    (hxy : -1 < x ⬝ᵥ y) : (x + y) ⬝ᵥ (x + y) ≠ 0 := by
  rw [add_dotProduct_add hx hy]
  nlinarith

theorem rotToAux_mem_specialOrthogonalGroup (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1)
    (hxy : -1 < x ⬝ᵥ y) :
    rotToAux x y ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ := by
  have hs : (x + y) ⬝ᵥ (x + y) ≠ 0 := add_dotProduct_add_ne_zero hx hy hxy
  have hx0 : x ⬝ᵥ x ≠ 0 := by rw [hx]; norm_num
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · exact mul_mem (reflMatrix_mem_orthogonalGroup hs) (reflMatrix_mem_orthogonalGroup hx0)
  · rw [rotToAux, Matrix.det_mul, det_reflMatrix hs, det_reflMatrix hx0]
    norm_num

/-- The rotation `rotToAux x y` maps `x` to `y`.-/
theorem rotToAux_mulVec_self (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1)
    (hxy : -1 < x ⬝ᵥ y) : rotToAux x y *ᵥ x = y := by
  have hx0 : x ⬝ᵥ x ≠ 0 := by rw [hx]; norm_num
  have hs : (x + y) ⬝ᵥ (x + y) = 2 + 2 * (x ⬝ᵥ y) := add_dotProduct_add hx hy
  have hsx : (x + y) ⬝ᵥ x = 1 + x ⬝ᵥ y := by
    rw [add_dotProduct, hx, dotProduct_comm y x]
  have hne1 : (1 : ℝ) + x ⬝ᵥ y ≠ 0 := by nlinarith
  have hcoef : 2 / ((x + y) ⬝ᵥ (x + y)) * ((x + y) ⬝ᵥ x) = 1 := by
    rw [hs, hsx, show (2 : ℝ) + 2 * (x ⬝ᵥ y) = 2 * (1 + x ⬝ᵥ y) by ring]
    field_simp
  rw [rotToAux, ← Matrix.mulVec_mulVec, reflMatrix_mulVec_self hx0, Matrix.mulVec_neg,
    reflMatrix_mulVec, hcoef, one_smul]
  ext i
  simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply]
  ring

/-- `rotToAux x x = 1`.-/
theorem rotToAux_same (hx : x ⬝ᵥ x = 1) : rotToAux x x = 1 := by
  have hx0 : x ⬝ᵥ x ≠ 0 := by rw [hx]; norm_num
  have h2 : x + x = (2 : ℝ) • x := by
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [rotToAux, h2, reflMatrix_smul (by norm_num : (2:ℝ) ≠ 0), reflMatrix_mul_self hx0]

end RotToAux

/-- Joint continuity of `reflMatrix` along a family avoiding `u ⬝ᵥ u = 0`.-/
theorem continuous_reflMatrix_comp {α : Type*} [TopologicalSpace α] {g : α → Fin n → ℝ}
    (hg : Continuous g) (hne : ∀ a, g a ⬝ᵥ g a ≠ 0) :
    Continuous fun a => reflMatrix (g a) := by
  have happ : ∀ i : Fin n, Continuous fun a => g a i := fun i => (continuous_apply i).comp hg
  have hd : Continuous fun a => g a ⬝ᵥ g a := by
    unfold dotProduct
    exact continuous_finsetSum _ fun j _ => (happ j).mul (happ j)
  apply continuous_matrix
  intro i j
  have hc : Continuous fun a => (1 : Matrix (Fin n) (Fin n) ℝ) i j
      - 2 / (g a ⬝ᵥ g a) * (g a i * g a j) :=
    continuous_const.sub ((continuous_const.div hd hne).mul ((happ i).mul (happ j)))
  simpa only [reflMatrix_apply] using hc

theorem continuous_rotToAux_comp {α : Type*} [TopologicalSpace α] {f g : α → Fin n → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfne : ∀ a, f a ⬝ᵥ f a ≠ 0) (hsne : ∀ a, (f a + g a) ⬝ᵥ (f a + g a) ≠ 0) :
    Continuous fun a => rotToAux (f a) (g a) :=
  (continuous_reflMatrix_comp (hf.add hg) hsne).matrix_mul
    (continuous_reflMatrix_comp hf hfne)

/-! ## Sphere-level bookkeeping -/

/-- The raw coordinates of a point of the unit sphere in `ℝⁿ`.-/
def coords (x : UnitSphere (EuclideanSpace ℝ (Fin n))) : Fin n → ℝ :=
  WithLp.ofLp (x : EuclideanSpace ℝ (Fin n))

theorem continuous_coords : Continuous (coords (n := n)) :=
  (EuclideanSpace.equiv (Fin n) ℝ).continuous.comp continuous_subtype_val

theorem coords_dotProduct (x y : UnitSphere (EuclideanSpace ℝ (Fin n))) :
    coords x ⬝ᵥ coords y = ⟪(x : EuclideanSpace ℝ (Fin n)), (y : EuclideanSpace ℝ (Fin n))⟫ := by
  rw [PiLp.inner_apply]
  simp only [coords, dotProduct, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem coords_dotProduct_self (x : UnitSphere (EuclideanSpace ℝ (Fin n))) :
    coords x ⬝ᵥ coords x = 1 := by
  rw [coords_dotProduct, real_inner_self_eq_norm_sq, UnitSphere.norm_coe]
  norm_num

/-- Two sphere points at distance `< 2` pair to more than `-1`.-/
theorem neg_one_lt_coords_dot_of_dist_lt_two {x y : UnitSphere (EuclideanSpace ℝ (Fin n))}
    (h : dist x y < 2) : -1 < coords x ⬝ᵥ coords y := by
  have hd : dist x y = ‖(x : EuclideanSpace ℝ (Fin n)) - (y : EuclideanSpace ℝ (Fin n))‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
  have hsq : ‖(x : EuclideanSpace ℝ (Fin n)) - (y : EuclideanSpace ℝ (Fin n))‖ ^ 2
      = 2 - 2 * ⟪(x : EuclideanSpace ℝ (Fin n)), (y : EuclideanSpace ℝ (Fin n))⟫ := by
    rw [norm_sub_sq_real, UnitSphere.norm_coe, UnitSphere.norm_coe]
    ring
  rw [coords_dotProduct]
  have hnonneg : (0 : ℝ) ≤ dist x y := dist_nonneg
  nlinarith [hsq, hd]

/-! ## The canonical rotation, sphere level -/

open Classical in
/-- The canonical rotation of `SO(n)` taking the sphere point `x` to `y`, rotating in
`span {x, y}` and fixing its orthogonal complement.  Junk value `1` for antipodal pairs.-/
def rotTo (x y : UnitSphere (EuclideanSpace ℝ (Fin n))) : SOGroup n :=
  if h : -1 < coords x ⬝ᵥ coords y then
    ⟨rotToAux (coords x) (coords y),
      rotToAux_mem_specialOrthogonalGroup (coords_dotProduct_self x)
        (coords_dotProduct_self y) h⟩
  else 1

theorem rotTo_coe {x y : UnitSphere (EuclideanSpace ℝ (Fin n))}
    (h : -1 < coords x ⬝ᵥ coords y) :
    (rotTo x y : Matrix (Fin n) (Fin n) ℝ) = rotToAux (coords x) (coords y) := by
  rw [rotTo, dite_eq_left h]

/-- `rotTo x y` maps `x` to `y` (as raw coordinate vectors).-/
theorem rotTo_mulVec {x y : UnitSphere (EuclideanSpace ℝ (Fin n))}
    (h : -1 < coords x ⬝ᵥ coords y) :
    (rotTo x y : Matrix (Fin n) (Fin n) ℝ) *ᵥ coords x = coords y := by
  rw [rotTo_coe h]
  exact rotToAux_mulVec_self (coords_dotProduct_self x) (coords_dotProduct_self y) h

@[simp]
theorem rotTo_self (x : UnitSphere (EuclideanSpace ℝ (Fin n))) : rotTo x x = 1 := by
  have h : -1 < coords x ⬝ᵥ coords x := by rw [coords_dotProduct_self]; norm_num
  apply Subtype.ext
  rw [rotTo_coe h]
  exact rotToAux_same (coords_dotProduct_self x)

/-- Joint continuity of `rotTo` along families of non-antipodal pairs.-/
theorem continuous_rotTo {α : Type*} [TopologicalSpace α]
    {f g : α → UnitSphere (EuclideanSpace ℝ (Fin n))}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ a, -1 < coords (f a) ⬝ᵥ coords (g a)) :
    Continuous fun a => rotTo (f a) (g a) := by
  have heq : (fun a => rotTo (f a) (g a))
      = fun a => (⟨rotToAux (coords (f a)) (coords (g a)),
          rotToAux_mem_specialOrthogonalGroup (coords_dotProduct_self (f a))
            (coords_dotProduct_self (g a)) (h a)⟩ : SOGroup n) := by
    funext a
    exact Subtype.ext (rotTo_coe (h a))
  rw [heq]
  apply Continuous.subtype_mk
  exact continuous_rotToAux_comp (continuous_coords.comp hf) (continuous_coords.comp hg)
    (fun a => by rw [coords_dotProduct_self]; norm_num)
    (fun a => add_dotProduct_add_ne_zero (coords_dotProduct_self (f a))
      (coords_dotProduct_self (g a)) (h a))

end Submission
