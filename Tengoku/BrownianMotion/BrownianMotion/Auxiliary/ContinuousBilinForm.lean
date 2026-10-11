module

public import Tengoku.BrownianMotion.BrownianMotion.Auxiliary.LinearAlgebra
public import Tengoku

/-!
# Continuous bilinear forms
-/

@[expose] public section

open Module
open scoped Matrix

namespace ContinuousBilinForm

variable {𝕜 E n : Type*} [NormedAddCommGroup E]

section RCLike

variable [RCLike 𝕜] [NormedSpace 𝕜 E]

variable (𝕜 E) in
/- The type of continuous bilinear forms. -/
abbrev _root_.ContinuousBilinForm := E →L[𝕜] E →L[𝕜] 𝕜

variable (f : ContinuousBilinForm 𝕜 E) (b : Basis n 𝕜 E)

/-- The underlying bilinear form of a continuous bilinear form -/
def toBilinForm : LinearMap.BilinForm 𝕜 E where
  toFun x := f x
  map_add' x y := by simp
  map_smul' m x := by simp

/--
@isnad1 id=eq.0h3v.s6.3621e8d92b7b from=translated src=- shape=ff93b434 vocab=a624ad1b
-/
lemma toBilinForm_eq : f.toBilinForm = ContinuousLinearMap.toBilinForm f := rfl

/--
@isnad1 id=eq.0h5v.s10.d99aaeadf1e0 from=translated src=- shape=8895b291 vocab=bc82f29e
-/
@[simp]
lemma toBilinForm_apply (x y : E) : f.toBilinForm x y = f x y := rfl

/--
@isnad1 id=eq.1h6v.s11.965f0be3b5b8 from=translated src=- shape=7f6045fe vocab=9a0681dd
-/
lemma ext_basis {f g : ContinuousBilinForm 𝕜 E} (h : ∀ i, ∀ j, f (b i) (b j) = g (b i) (b j)) :
    f = g := by
  ext x y
  rw [← toBilinForm_apply, ← toBilinForm_apply]
  have : f.toBilinForm = g.toBilinForm := by
    apply LinearMap.BilinForm.ext_basis b
    simpa
  rw [this]

section IsSymm

/-- A continuous bilinear form `f` is symmetric if for any `x, y` we have `f x y = f y x`. -/
structure IsSymm : Prop where
  map_symm : ∀ x y, f x y = f y x

/--
@isnad1 id=iff.0h3v.s10.2ac0ef4617b2 from=translated src=- shape=f01dc634 vocab=f8d965af
-/
lemma isSymm_def : f.IsSymm ↔ ∀ x y, f x y = f y x where
  mp := fun ⟨h⟩ ↦ h
  mpr h := ⟨h⟩

variable {f}

/-- Polarization identity: a symmetric continuous bilinear form can be expressed through values
it takes on the diagonal.
@isnad1 id=eq.1h5v.s11.ca3627d4d0e1 from=translated src=- shape=960a291b vocab=95c25236
-/
lemma IsSymm.polarization (x y : E) (hf : f.IsSymm) :
    f x y = (f (x + y) (x + y) - f x x - f y y) / 2 := by
  simp only [map_add, add_apply]
  rw [hf.map_symm y x]
  ring

/-- A symmetric continuous bilinear form is characterized by the values it takes on the diagonal.
@isnad1 id=eq.3h4v.s10.eb0bfbcbe196 from=translated src=- shape=5c4d501a vocab=f8d965af
-/
lemma ext_of_isSymm {g : ContinuousBilinForm 𝕜 E} (hf : IsSymm f) (hg : IsSymm g)
    (h : ∀ x, f x x = g x x) : f = g := by
  ext x y
  rw [hf.polarization, hg.polarization]
  simp_rw [h]

/-- A symmetric continuous bilinear form is characterized by the values it takes on the diagonal.
@isnad1 id=iff.2h4v.s10.63ef06ce8ba9 from=translated src=- shape=f13e3a73 vocab=f8d965af
-/
lemma ext_iff_of_isSymm {g : ContinuousBilinForm 𝕜 E} (hf : IsSymm f) (hg : IsSymm g) :
    f = g ↔ ∀ x, f x x = g x x where
  mp h := by simp [h]
  mpr := ext_of_isSymm hf hg

variable (f)

/--
@isnad1 id=iff.0h5v.s11.2081629f46bf from=translated src=- shape=aef107b8 vocab=c5a3db93
-/
lemma isSymm_iff_basis : f.IsSymm ↔ ∀ i j, f (b i) (b j) = f (b j) (b i) where
  mp := fun ⟨h⟩ i j ↦ h _ _
  mpr := by
    refine fun h ↦ ⟨fun x y ↦ ?_⟩
    obtain ⟨fx, tx, ix, -, hx⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : x ∈ Submodule.span 𝕜 (Set.range b))
    obtain ⟨fy, ty, iy, -, hy⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : y ∈ Submodule.span 𝕜 (Set.range b))
    rw [← hx, ← hy]
    simp only [map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b₁ h₁ ↦ Finset.sum_congr rfl fun b₂ h₂ ↦ ?_)
    rw [mul_left_comm]
    obtain ⟨i, rfl⟩ := ix h₁
    obtain ⟨j, rfl⟩ := iy h₂
    rw [h]

end IsSymm

section Matrix

variable [Fintype n] [DecidableEq n]

section toMatrix

/-- A continuous bilinear map on a finite dimensional space can be represented by a matrix. -/
noncomputable def toMatrix : Matrix n n 𝕜 :=
  LinearMap.BilinForm.toMatrix b f.toBilinForm

/--
@isnad1 id=eq.0h7v.s10.613700fec53e from=translated src=- shape=65c1bebc vocab=76e5a9fd
-/
@[simp]
lemma toMatrix_apply (i j : n) : f.toMatrix b i j = f (b i) (b j) := by
  simp [toMatrix]

/--
@isnad1 id=eq.0h7v.s11.71725e033d5d from=translated src=- shape=32f8dcc8 vocab=57c452c0
-/
lemma dotProduct_toMatrix_mulVec (x y : n → 𝕜) :
    x ⬝ᵥ (f.toMatrix b) *ᵥ y = f (b.equivFun.symm x) (b.equivFun.symm y) := by
  simp only [dotProduct, Matrix.mulVec_eq_sum, op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply,
    Matrix.transpose_apply, toMatrix_apply, smul_eq_mul, Finset.mul_sum, Basis.equivFun_symm_apply,
    map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_)
  ring

/--
@isnad1 id=eq.0h7v.s11.9db97c3d22c9 from=translated src=- shape=011d0073 vocab=c8bb2ba0
-/
lemma apply_eq_dotProduct_toMatrix_mulVec (x y : E) :
    f x y = (b.repr x) ⬝ᵥ (f.toMatrix b) *ᵥ (b.repr y) := by
  nth_rw 1 [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, dotProduct, Matrix.mulVec_eq_sum,
    op_smul_eq_smul, Matrix.transpose_apply, toMatrix_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_)
  ring

end toMatrix

section ofMatrix

variable (M : Matrix n n 𝕜) (b : Basis n 𝕜 E)

noncomputable
def ofMatrix : ContinuousBilinForm 𝕜 E :=
  haveI : FiniteDimensional 𝕜 E := Module.Basis.finiteDimensional_of_finite b
  LinearMap.mkContinuous₂OfFiniteDimensional (M.toBilin b)

/--
@isnad1 id=eq.0h7v.s12.5d64c4349f1c from=translated src=- shape=0e402013 vocab=ca4261f8
-/
lemma ofMatrix_apply' (x y : E) : ofMatrix M b x y = M.toBilin b x y := rfl

open scoped Matrix in
/--
@isnad1 id=eq.0h7v.s11.22708d9bbe4e from=translated src=- shape=a251ddfa vocab=e971f1d9
-/
lemma ofMatrix_apply (x y : E) :
    ofMatrix M b x y = b.repr x ⬝ᵥ M *ᵥ b.repr y := by
  simp [ofMatrix_apply', Matrix.toBilin_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/--
@isnad1 id=eq.0h7v.s10.ba81cb692a4c from=translated src=- shape=49712a46 vocab=0584d7e9
-/
lemma ofMatrix_basis (i j : n) : ofMatrix M b (b i) (b j) = M i j := by
  simp [ofMatrix_apply, Finsupp.single_eq_pi_single]

/--
@isnad1 id=eq.0h7v.s10.6653b89b8521 from=translated src=- shape=218007e2 vocab=4d61494e
-/
lemma ofMatrix_orthonormalBasis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (b : OrthonormalBasis n 𝕜 E) (i j : n) :
    ofMatrix M b.toBasis (b i) (b j) = M i j := by
  rw [← b.coe_toBasis, ofMatrix_basis]

/--
@isnad1 id=eq.0h5v.s6.fbbfb30c6b1f from=translated src=- shape=d21c8a46 vocab=5aa59639
-/
lemma toMatrix_ofMatrix : ofMatrix (f.toMatrix b) b = f := by
  ext x y
  rw [ofMatrix_apply, f.apply_eq_dotProduct_toMatrix_mulVec b]

/--
@isnad1 id=eq.0h5v.s6.ccdb05dfdd77 from=translated src=- shape=08ddad78 vocab=da943e92
-/
lemma ofMatrix_toMatrix : (ofMatrix M b).toMatrix b = M := by
  ext i j
  rw [toMatrix_apply, ofMatrix_basis]

end ofMatrix

end Matrix

section IsPos

/-- A continuous bilinear map `f` is positive if for any `0 ≤ x`, `0 ≤ re (f x x)` -/
structure IsPos : Prop where
  nonneg_re_apply_self : ∀ x, 0 ≤ RCLike.re (f x x)

/--
@isnad1 id=iff.0h3v.s10.43b4b1cb801e from=translated src=- shape=5879555e vocab=49ca2349
-/
lemma isPos_def : f.IsPos ↔ ∀ x, 0 ≤ RCLike.re (f x x) where
  mp := fun ⟨h⟩ ↦ h
  mpr h := ⟨h⟩

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ContinuousBilinForm ℝ E)
    (b : Basis n ℝ E)

/--
@isnad1 id=iff.0h2v.s9.8e04762aca42 from=translated src=- shape=0f6bbb71 vocab=70497c80
-/
lemma isPos_def_real : f.IsPos ↔ ∀ x, 0 ≤ f x x := by simp [isPos_def]

variable {f} in
/--
@isnad1 id=le.1h3v.s9.ecdf109a3e3a from=translated src=- shape=aa624189 vocab=70497c80
-/
lemma IsPos.nonneg_apply_self (hf : IsPos f) (x : E) : 0 ≤ f x x := f.isPos_def_real.1 hf x

variable [Fintype n] [DecidableEq n]

/--
@isnad1 id=iff.0h4v.s6.5dc9c10531b9 from=translated src=- shape=ff2f5c59 vocab=bb31c0d5
-/
lemma isSymm_iff_isHermitian_toMatrix : f.IsSymm ↔ (f.toMatrix b).IsHermitian := by
  rw [isSymm_iff_basis f b, Matrix.IsHermitian.ext_iff]
  simp [Eq.comm]

end Real

end IsPos

end RCLike

section Real

section NormedSpace

variable [NormedSpace ℝ E] (f : ContinuousBilinForm ℝ E) (b : Basis n ℝ E)

section IsPosSemidef

/-- A continuous bilinear map is positive semidefinite if it is symmetric and positive. We only
define it for the real field, because for the complex case we may want to consider sesquilinear
forms instead. -/
structure IsPosSemidef : Prop extends f.IsSymm, f.IsPos

variable {f}

/--
@isnad1 id=issymm.1h2v.s5.10c441b69a39 from=translated src=- shape=ec8044c1 vocab=e03c898d
-/
lemma IsPosSemidef.isSymm (hf : IsPosSemidef f) : IsSymm f := hf.toIsSymm

/--
@isnad1 id=ispos.1h2v.s5.11e19fee60d2 from=translated src=- shape=ec8044c1 vocab=5ae022a1
-/
lemma IsPosSemidef.isPos (hf : IsPosSemidef f) : IsPos f := hf.toIsPos

variable (f)

/--
@isnad1 id=iff.0h2v.s5.a30f5d1fce11 from=translated src=- shape=b3f0e577 vocab=7716a6f7
-/
lemma isPosSemidef_iff : f.IsPosSemidef ↔ f.IsSymm ∧ f.IsPos where
  mp h := ⟨h.isSymm, h.isPos⟩
  mpr := fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩

/--
@isnad1 id=iff.0h2v.s6.7bfad1e3d5b1 from=translated src=- shape=914a430b vocab=fdd7f41f
-/
lemma isPosSemidef_iff_bilinForm :
    f.IsPosSemidef ↔ (f.toBilinForm).IsPosSemidef := by
  rw [isPosSemidef_iff, LinearMap.BilinForm.isPosSemidef_def]
  simp [ContinuousBilinForm.isSymm_def, LinearMap.BilinForm.isSymm_def,
    ContinuousBilinForm.isPos_def, LinearMap.BilinForm.isNonneg_def]

variable {f} [Fintype n] [DecidableEq n]

lemma _root_.LinearMap.BilinForm.isPosSemidef_iff_posSemidef_toMatrix (f : LinearMap.BilinForm ℝ E)
    (b : Basis n ℝ E) :
    f.IsPosSemidef ↔ (LinearMap.BilinForm.toMatrix b f).PosSemidef := by
  rw [LinearMap.BilinForm.isPosSemidef_iff, LinearMap.BilinForm.toMatrix,
    LinearMap.isPosSemidef_iff_posSemidef_toMatrix b]

/--
@isnad1 id=iff.0h4v.s6.9f5368f1b7db from=translated src=- shape=02a1236d vocab=c9409ffe
-/
lemma isPosSemidef_iff_posSemidef_toMatrix : f.IsPosSemidef ↔ (f.toMatrix b).PosSemidef := by
  rw [isPosSemidef_iff, Matrix.posSemidef_iff_dotProduct_mulVec]
  apply and_congr (f.isSymm_iff_isHermitian_toMatrix b)
  rw [isPos_def]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · rw [dotProduct_toMatrix_mulVec]
    exact h _
  · rw [apply_eq_dotProduct_toMatrix_mulVec f b]
    exact h _

end IsPosSemidef

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E]

open scoped InnerProductSpace

variable (E) in
/-- The inner product as continuous bilinear form. -/
protected noncomputable def inner : ContinuousBilinForm ℝ E :=
  letI f : LinearMap.BilinForm ℝ E := LinearMap.mk₂ ℝ
    (fun x y ↦ ⟪x, y⟫_ℝ)
    inner_add_left
    (fun c m n ↦ real_inner_smul_left m n c)
    inner_add_right
    (fun c m n ↦ real_inner_smul_right m n c)
  f.mkContinuous₂ 1 <| by
    intro x y
    simp only [LinearMap.mk₂_apply, Real.norm_eq_abs, one_mul, f]
    exact abs_real_inner_le_norm x y

/--
@isnad1 id=eq.0h3v.s10.cdebeb0b91b7 from=translated src=- shape=8b9f9cbe vocab=f5064d3e
-/
@[simp]
lemma inner_apply (x y : E) : ContinuousBilinForm.inner E x y = ⟪x, y⟫_ℝ := rfl

/--
@isnad1 id=eq.0h2v.s10.b2a921123412 from=translated src=- shape=3df51c1b vocab=f5064d3e
-/
lemma inner_apply' (x : E) : ContinuousBilinForm.inner E x = fun y ↦ ⟪x, y⟫_ℝ := rfl

/--
@isnad1 id=eq.0h2v.s10.f787400ab629 from=translated src=- shape=6cb643e1 vocab=f5064d3e
-/
lemma inner_apply'' (x : E) : ContinuousBilinForm.inner E x = inner ℝ x := rfl

/--
@isnad1 id=ispossem.0h1v.s4.098964f98993 from=translated src=- shape=6bebe499 vocab=bfdde2b5
-/
lemma isPosSemidef_inner : IsPosSemidef (ContinuousBilinForm.inner E) where
  map_symm := by simp [real_inner_comm]
  nonneg_re_apply_self x := real_inner_self_nonneg

variable [Fintype n] [DecidableEq n] (b : OrthonormalBasis n ℝ E)

/--
@isnad1 id=eq.0h3v.s6.0edd8d7460d1 from=translated src=- shape=737f3053 vocab=9466f229
-/
lemma inner_toMatrix_eq_one : (ContinuousBilinForm.inner E).toMatrix b.toBasis = 1 := by
  ext i j
  simp [Matrix.one_apply, b.inner_eq]

end InnerProductSpace

end Real

section Diagonal

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]

section RCLike

variable [RCLike 𝕜] [∀ i, NormedSpace 𝕜 (E i)]
    (L : (i : ι) → ContinuousBilinForm 𝕜 (StrongDual 𝕜 (E i)))

open ContinuousLinearMap in
/-- Given `L i : (E i)' × (E i)' → 𝕜` a family of continuous bilinear forms,
`diagonalStrongDual L` is a continuous bilinear form is the continuous bilinear form over
`(Π i, E i)'` which maps `(x, y) : (Π i, E i)' × (Π i, E i)'` to
`∑ i, L i (fun a ↦ x aᵢ) (fun a ↦ y aᵢ)`. -/
noncomputable
def diagonalStrongDual : ContinuousBilinForm 𝕜 (StrongDual 𝕜 (Π i, E i)) :=
  letI g : LinearMap.BilinForm 𝕜 (StrongDual 𝕜 (Π i, E i)) := LinearMap.mk₂ 𝕜
    (fun x y ↦ ∑ i, L i (x ∘L (single 𝕜 E i)) (y ∘L (single 𝕜 E i)))
    (fun x y z ↦ by simp [Finset.sum_add_distrib])
    (fun c m n ↦ by simp [Finset.mul_sum])
    (fun x y z ↦ by simp [Finset.sum_add_distrib])
    (fun c m n ↦ by simp [Finset.mul_sum])
  g.mkContinuous₂ (∑ i, ‖L i‖) <| by
    intro x y
    simp only [LinearMap.mk₂_apply, g]
    grw [norm_sum_le, Finset.sum_mul, Finset.sum_mul]
    gcongr with i _
    grw [le_opNorm₂, opNorm_comp_le, opNorm_comp_le, norm_single_le_one, norm_single_le_one]
    simp

/--
@isnad1 id=eq.0h6v.s14.9c206ba5bb30 from=translated src=- shape=70dbdd08 vocab=d077dea2
-/
lemma diagonalStrongDual_apply (x y : StrongDual 𝕜 (Π i, E i)) :
    diagonalStrongDual L x y = ∑ i, L i (x ∘L (.single 𝕜 E i)) (y ∘L (.single 𝕜 E i)) := rfl

end RCLike

section Real

variable [∀ i, NormedSpace ℝ (E i)] {L : (i : ι) → ContinuousBilinForm ℝ (StrongDual ℝ (E i))}

/--
@isnad1 id=ispossem.1h3v.s9.79e53b29bce3 from=translated src=- shape=a00dd452 vocab=1e247d3f
-/
lemma isPosSemidef_diagonalStrongDual (hL : ∀ i, (L i).IsPosSemidef) :
    (diagonalStrongDual L).IsPosSemidef where
  map_symm x y := by
    simp_rw [diagonalStrongDual_apply, fun i ↦ (hL i).map_symm]
  nonneg_re_apply_self x := by
    simp only [diagonalStrongDual_apply, map_sum, RCLike.re_to_real]
    exact Finset.sum_nonneg fun i _ ↦ (hL i).nonneg_apply_self _

end Real

end Diagonal

end ContinuousBilinForm
