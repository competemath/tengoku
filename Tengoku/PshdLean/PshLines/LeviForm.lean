import Tengoku.Seed.Analysis.InnerProductSpace.Laplacian
import Tengoku.Seed.Analysis.InnerProductSpace.Calculus
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The real Hessian and the Levi quadratic form

The Hessian in this file is the actual second Fréchet derivative of a real-valued
function.  The Levi quadratic form uses the normalization
`(D²u(v,v) + D²u(Iv,Iv))/4`.  For a C² function its value is one quarter of the
ordinary Laplacian along the corresponding complex affine line.

No equivalence with plurisubharmonicity is assumed in this file.
-/

noncomputable section

open Laplacian

namespace PshLines

section RealHessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The real Hessian, evaluated on two vectors.-/
def realHessian (u : E → ℝ) (x v w : E) : ℝ :=
  iteratedFDeriv ℝ 2 u x ![v, w]

/--
@isnad1 id=eq.0h5v.s10.f8847541d486 from=translated src=- shape=d7d994c4 vocab=80e58362
-/
theorem realHessian_eq_fderiv (u : E → ℝ) (x v w : E) :
    realHessian u x v w = fderiv ℝ (fderiv ℝ u) x v w := by
  simp [realHessian, iteratedFDeriv_two_apply]

/--
@isnad1 id=eq.0h5v.s5.8db9aa51da0b from=translated src=- shape=4ed5317a vocab=3ca400b0
-/
@[simp] theorem realHessian_const (c : ℝ) (x v w : E) :
    realHessian (fun _ : E ↦ c) x v w = 0 := by
  simp [realHessian, iteratedFDeriv_const_of_ne two_ne_zero]

/--
@isnad1 id=eq.2h6v.s7.01f4a1193e1d from=translated src=- shape=bd754e59 vocab=e7d1a53a
-/
theorem realHessian_add {u v : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a b : E) :
    realHessian (u + v) x a b = realHessian u x a b + realHessian v x a b := by
  simp [realHessian, iteratedFDeriv_add_apply hu hv]

/--
@isnad1 id=eq.1h6v.s6.f5c14b0a68d7 from=translated src=- shape=0f0315f1 vocab=8995c158
-/
theorem realHessian_smul {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (c : ℝ) (a b : E) :
    realHessian (c • u) x a b = c * realHessian u x a b := by
  simp [realHessian, iteratedFDeriv_const_smul_apply hu]

/--
@isnad1 id=eq.0h5v.s5.47e34ae1e8b5 from=translated src=- shape=83a55d05 vocab=5ff78b51
-/
@[simp] theorem realHessian_neg (u : E → ℝ) (x a b : E) :
    realHessian (-u) x a b = -realHessian u x a b := by
  simp [realHessian, iteratedFDeriv_neg_apply]

/--
@isnad1 id=eq.0h4v.s5.8417fce9df81 from=translated src=- shape=1a738c8e vocab=3ca400b0
-/
@[simp] theorem realHessian_zero_left (u : E → ℝ) (x b : E) :
    realHessian u x 0 b = 0 := by
  simp [realHessian_eq_fderiv]

/--
@isnad1 id=eq.0h4v.s5.8e7bdf0b9763 from=translated src=- shape=93a71360 vocab=3ca400b0
-/
@[simp] theorem realHessian_zero_right (u : E → ℝ) (x a : E) :
    realHessian u x a 0 = 0 := by
  simp [realHessian_eq_fderiv]

/--
@isnad1 id=eq.0h6v.s6.ff54dde666a4 from=translated src=- shape=1ce4ece9 vocab=e7965def
-/
theorem realHessian_smul_left (u : E → ℝ) (x a b : E) (c : ℝ) :
    realHessian u x (c • a) b = c * realHessian u x a b := by
  simp [realHessian_eq_fderiv]

/--
@isnad1 id=eq.0h6v.s6.498dc85309da from=translated src=- shape=c763b1a4 vocab=e7965def
-/
theorem realHessian_smul_right (u : E → ℝ) (x a b : E) (c : ℝ) :
    realHessian u x a (c • b) = c * realHessian u x a b := by
  simp [realHessian_eq_fderiv]

/-- Translation and linear pullback of the genuine second derivative.
@isnad1 id=eq.1h8v.s9.95a04a7045d2 from=translated src=- shape=82e149cf vocab=8eb59322
-/
theorem realHessian_comp_affine {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (A : F →L[ℝ] E) (x : E) (z a b : F) :
    realHessian (fun y ↦ u (x + A y)) z a b =
      realHessian u (x + A z) (A a) (A b) := by
  have hshift : ContDiff ℝ 2 (fun y : E ↦ u (x + y)) :=
    hu.comp (contDiff_const.add contDiff_id)
  have h := congrArg (fun B ↦ B ![a, b])
    (A.iteratedFDeriv_comp_right hshift z (i := 2) le_rfl)
  have hvec : (fun i ↦ A (![a, b] i)) = ![A a, A b] := by
    ext i
    fin_cases i <;> rfl
  simpa only [realHessian, Function.comp_def,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left, hvec] using h

end RealHessian

section NormSquare

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Hessian of the squared norm is twice the real inner product.
@isnad1 id=eq.0h4v.s6.d116c958c854 from=translated src=- shape=f7233559 vocab=e47aacad
-/
theorem realHessian_norm_sq (x a b : H) :
    realHessian (fun y : H ↦ ‖y‖ ^ 2) x a b = 2 * inner ℝ a b := by
  rw [realHessian_eq_fderiv, fderiv_norm_sq,
    fderiv_const_smul (innerSL ℝ).differentiableAt]
  simp
  rfl

end NormSquare

section LeviForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E]

/-- The Levi quadratic form of a real-valued function.-/
def leviForm (u : E → ℝ) (x v : E) : ℝ :=
  (realHessian u x v v + realHessian u x (Complex.I • v) (Complex.I • v)) / 4

/--
@isnad1 id=eq.0h4v.s5.81f959a2169c from=translated src=- shape=412c4f12 vocab=b6ec9b1a
-/
@[simp] theorem leviForm_const (c : ℝ) (x v : E) :
    leviForm (fun _ : E ↦ c) x v = 0 := by
  simp [leviForm]

/--
@isnad1 id=eq.0h3v.s5.0753c3fa905f from=translated src=- shape=930ea9cb vocab=b6ec9b1a
-/
@[simp] theorem leviForm_zero (u : E → ℝ) (x : E) : leviForm u x 0 = 0 := by
  simp [leviForm]

/--
@isnad1 id=eq.2h5v.s7.ea74cfcf7f89 from=translated src=- shape=9a5db5cc vocab=1bee06f6
-/
theorem leviForm_add {u v : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a : E) :
    leviForm (u + v) x a = leviForm u x a + leviForm v x a := by
  simp only [leviForm, realHessian_add hu hv]
  ring

/--
@isnad1 id=eq.1h5v.s6.225c223ab49b from=translated src=- shape=e663d016 vocab=5676b952
-/
theorem leviForm_smul {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (c : ℝ) (a : E) :
    leviForm (c • u) x a = c * leviForm u x a := by
  simp only [leviForm, realHessian_smul hu]
  ring

/--
@isnad1 id=eq.0h4v.s5.6d50795d71bf from=translated src=- shape=4bd2b5ea vocab=832382f3
-/
@[simp] theorem leviForm_neg (u : E → ℝ) (x a : E) :
    leviForm (-u) x a = -leviForm u x a := by
  simp only [leviForm, realHessian_neg]
  ring

variable [IsScalarTower ℝ ℂ E]

/-- Multiplication by a fixed vector, viewed as a real continuous linear map.-/
def complexLineLinear (v : E) : ℂ →L[ℝ] E :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight v).restrictScalars ℝ

/--
@isnad1 id=eq.0h3v.s8.ed337011e0b8 from=translated src=- shape=02e6047a vocab=5224a7c4
-/
@[simp] theorem complexLineLinear_apply (v : E) (z : ℂ) :
    complexLineLinear v z = z • v := rfl

/-- The Hessian chain rule along a complex affine line.
@isnad1 id=eq.1h7v.s9.dce3e01f4dad from=translated src=- shape=3d4f32d4 vocab=f752f215
-/
theorem realHessian_complexLine {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (x v : E) (z a b : ℂ) :
    realHessian (fun t : ℂ ↦ u (x + t • v)) z a b =
      realHessian u (x + z • v) (a • v) (b • v) := by
  exact realHessian_comp_affine hu (complexLineLinear v) x z a b

/-- The ordinary real Laplacian along a complex line is four times the Levi form.
@isnad1 id=eq.1h5v.s8.c8f13375e291 from=translated src=- shape=cfefad5e vocab=7870c53e
-/
theorem laplacian_complexLine {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (x v : E) (z : ℂ) :
    Δ (fun t : ℂ ↦ u (x + t • v)) z = 4 * leviForm u (x + z • v) v := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  change realHessian (fun t : ℂ ↦ u (x + t • v)) z 1 1 +
    realHessian (fun t : ℂ ↦ u (x + t • v)) z Complex.I Complex.I = _
  rw [realHessian_complexLine hu, realHessian_complexLine hu]
  simp only [one_smul, leviForm]
  ring

/--
@isnad1 id=iff.1h5v.s8.cb6d8e5d1bcc from=translated src=- shape=6f801a07 vocab=a5442ca0
-/
theorem laplacian_complexLine_nonneg_iff {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (x v : E) (z : ℂ) :
    0 ≤ Δ (fun t : ℂ ↦ u (x + t • v)) z ↔ 0 ≤ leviForm u (x + z • v) v := by
  rw [laplacian_complexLine hu]
  exact mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 4)

end LeviForm

section NormSquareLevi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E]

/-- The squared norm has positive definite Levi form with this normalization.
@isnad1 id=eq.0h3v.s6.cfd7270ddb49 from=translated src=- shape=b0d15235 vocab=6355eb8b
-/
theorem leviForm_norm_sq (x v : E) :
    leviForm (fun y : E ↦ ‖y‖ ^ 2) x v = ‖v‖ ^ 2 := by
  simp only [leviForm, realHessian_norm_sq, real_inner_self_eq_norm_sq,
    norm_smul, Complex.norm_I, one_mul]
  ring

/--
@isnad1 id=le.0h3v.s6.7aefe2db50f1 from=translated src=- shape=fa366240 vocab=f4497755
-/
theorem leviForm_norm_sq_nonneg (x v : E) :
    0 ≤ leviForm (fun y : E ↦ ‖y‖ ^ 2) x v := by
  rw [leviForm_norm_sq]
  positivity

/--
@isnad1 id=lt.1h3v.s6.2d2456afcab9 from=translated src=- shape=69aa3f47 vocab=0902bc27
-/
theorem leviForm_norm_sq_pos (x : E) {v : E} (hv : v ≠ 0) :
    0 < leviForm (fun y : E ↦ ‖y‖ ^ 2) x v := by
  rw [leviForm_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hv)

end NormSquareLevi

end PshLines
