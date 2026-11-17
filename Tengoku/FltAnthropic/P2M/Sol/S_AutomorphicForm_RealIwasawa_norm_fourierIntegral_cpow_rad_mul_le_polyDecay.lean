import Tengoku.Seed.Analysis.Fourier.FourierTransformDeriv
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean`: wrote out 19 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 19 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open scoped ContDiff Nat

namespace M4aP3B
namespace RealIwasawa

def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem rot_zero : rot 0 = 1 := by
  rw [rot, Matrix.one_fin_two, Real.cos_zero, Real.sin_zero, neg_zero]

theorem rot_add (s t : ℝ) : rot (s + t) = rot s * rot t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem rot_mul_rot_neg (θ : ℝ) : rot θ * rot (-θ) = 1 := by
  rw [← rot_add, add_neg_cancel, rot_zero]

theorem rot_neg_mul_rot (θ : ℝ) : rot (-θ) * rot θ = 1 := by
  rw [← rot_add, neg_add_cancel, rot_zero]

def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  ⟨rot θ, rot (-θ), rot_mul_rot_neg θ, rot_neg_mul_rot θ⟩

variable (g : Matrix (Fin 2) (Fin 2) ℝ)

def weylUnip (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0] * !![1, u; 0, 1] * g

def botNormSq : ℝ := g 1 0 ^ 2 + g 1 1 ^ 2

def foot : ℝ := -(g 0 0 * g 1 0 + g 0 1 * g 1 1) / botNormSq g

def center : ℂ := ⟨foot g, -(g.det / botNormSq g)⟩

def dir : ℂ := ⟨g 1 1, g 1 0⟩

def botRow (u : ℝ) : ℂ := ⟨g 0 1 + u * g 1 1, g 0 0 + u * g 1 0⟩

def rad (u : ℝ) : ℝ := ‖botRow g u‖

variable {g}

theorem botNormSq_pos (hg : g.det ≠ 0) : 0 < botNormSq g := by
  unfold botNormSq
  rcases (add_nonneg (sq_nonneg (g 1 0)) (sq_nonneg (g 1 1))).lt_or_eq with h | h
  · exact h
  · exfalso
    have hc : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have hd : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    apply hg
    rw [Matrix.det_fin_two, hc, hd, mul_zero, mul_zero, sub_zero]

theorem norm_dir_sq (g : Matrix (Fin 2) (Fin 2) ℝ) : ‖dir g‖ ^ 2 = botNormSq g := by
  rw [Complex.sq_norm, dir, Complex.normSq_mk, botNormSq]
  ring

theorem norm_dir_pos (hg : g.det ≠ 0) : 0 < ‖dir g‖ := by
  have h := norm_dir_sq g
  have hA := botNormSq_pos hg
  nlinarith [norm_nonneg (dir g)]

theorem botRow_eq (hg : g.det ≠ 0) (u : ℝ) : botRow g u = dir g * ((u : ℂ) - center g) := by
  have hA : botNormSq g ≠ 0 := (botNormSq_pos hg).ne'
  apply Complex.ext
  · simp only [botRow, dir, center, foot, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, Matrix.det_fin_two]
    unfold botNormSq at hA ⊢
    field_simp
    ring
  · simp only [botRow, dir, center, foot, Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, Matrix.det_fin_two]
    unfold botNormSq at hA ⊢
    field_simp
    ring

theorem im_sub_center (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    ((u : ℂ) - center g).im = g.det / botNormSq g := by
  simp [center]

theorem re_sub_center (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) : ((u : ℂ) - center g).re = u - foot g := by
  simp [center]

theorem sub_center_mem_slitPlane (hg : g.det ≠ 0) (u : ℝ) : (u : ℂ) - center g ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inr (by
    rw [im_sub_center]
    exact div_ne_zero hg (botNormSq_pos hg).ne'))

theorem sub_center_ne_zero (hg : g.det ≠ 0) (u : ℝ) : (u : ℂ) - center g ≠ 0 :=
  Complex.slitPlane_ne_zero (sub_center_mem_slitPlane hg u)

theorem abs_det_div_le_norm_sub_center (hg : g.det ≠ 0) (u : ℝ) :
    |g.det| / botNormSq g ≤ ‖(u : ℂ) - center g‖ := by
  have h := Complex.abs_im_le_norm ((u : ℂ) - center g)
  rwa [im_sub_center, abs_div, abs_of_pos (botNormSq_pos hg)] at h

theorem rad_eq (hg : g.det ≠ 0) (u : ℝ) : rad g u = ‖dir g‖ * ‖(u : ℂ) - center g‖ := by
  rw [rad, botRow_eq hg, norm_mul]

theorem rad_pos (hg : g.det ≠ 0) (u : ℝ) : 0 < rad g u := by
  rw [rad_eq hg]
  exact mul_pos (norm_dir_pos hg) (norm_pos_iff.2 (sub_center_ne_zero hg u))

theorem rad_sq (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    rad g u ^ 2 = (g 0 0 + u * g 1 0) ^ 2 + (g 0 1 + u * g 1 1) ^ 2 := by
  rw [rad, Complex.sq_norm, botRow, Complex.normSq_mk]
  ring

theorem rad_eq_sqrt (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    rad g u = Real.sqrt ((g 0 0 + u * g 1 0) ^ 2 + (g 0 1 + u * g 1 1) ^ 2) := by
  rw [← rad_sq, Real.sqrt_sq (show 0 ≤ rad g u from norm_nonneg _)]

theorem rad_sq_eq (hg : g.det ≠ 0) (u : ℝ) :
    rad g u ^ 2 = botNormSq g * (u - foot g) ^ 2 + g.det ^ 2 / botNormSq g := by
  have hA : botNormSq g ≠ 0 := (botNormSq_pos hg).ne'
  rw [rad_eq hg, mul_pow, norm_dir_sq, Complex.sq_norm, ← Complex.re_add_im ((u : ℂ) - center g),
    re_sub_center, im_sub_center]
  rw [Complex.normSq_add_mul_I]
  field_simp

variable (g)

def logLine (u : ℝ) : ℂ := Complex.log ((u : ℂ) - center g)

def angle (u : ℝ) : ℝ := Complex.arg (dir g) + (logLine g u).im

variable {g}

theorem log_rad_eq (hg : g.det ≠ 0) (u : ℝ) : Real.log (rad g u) = Real.log ‖dir g‖ + (logLine g u).re := by
  rw [rad_eq hg, Real.log_mul (norm_dir_pos hg).ne' (norm_pos_iff.2 (sub_center_ne_zero hg u)).ne', logLine,
    Complex.log_re]

variable (g)

def borel (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-g.det / rad g u, (g 1 0 * (g 0 0 + u * g 1 0) + g 1 1 * (g 0 1 + u * g 1 1)) / rad g u; 0, rad g u]

variable {g}

theorem det_borel (hg : g.det ≠ 0) (u : ℝ) : (borel g u).det = -g.det := by
  rw [borel, Matrix.det_fin_two_of, mul_zero, sub_zero, div_mul_cancel₀ _ (rad_pos hg u).ne']

def borelGL (hg : g.det ≠ 0) (u : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (borel g u) (by rw [det_borel hg]; exact neg_ne_zero.2 hg)

def weylR : GL (Fin 2) ℝ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

def unipR (u : ℝ) : GL (Fin 2) ℝ :=
  ⟨!![1, u; 0, 1], !![1, -u; 0, 1],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

def invTower (g : Matrix (Fin 2) (Fin 2) ℝ) (k : ℕ) (u : ℝ) : ℂ :=
  (-1) ^ k * (k ! : ℂ) * ((u : ℂ) - center g) ^ (-1 - (k : ℤ))

theorem invTower_zero (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) : invTower g 0 u = ((u : ℂ) - center g)⁻¹ := by
  simp [invTower]

theorem hasDerivAt_logLine (hg : g.det ≠ 0) (u : ℝ) : HasDerivAt (logLine g) (invTower g 0 u) u := by
  have h : HasDerivAt (fun y : ℝ => (y : ℂ) - center g) 1 u := (hasDerivAt_id u).ofReal_comp.sub_const _
  have h2 := h.clog_real (sub_center_mem_slitPlane hg u)
  rw [invTower_zero, ← one_div]
  exact h2

theorem hasDerivAt_invTower (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    HasDerivAt (invTower g k) (invTower g (k + 1) u) u := by
  have hz := sub_center_ne_zero hg u
  have h1 : HasDerivAt (fun z : ℂ => (z - center g) ^ (-1 - (k : ℤ)))
      (((-1 - (k : ℤ) : ℤ) : ℂ) * ((u : ℂ) - center g) ^ (-1 - (k : ℤ) - 1)) (u : ℂ) := by
    have := (hasDerivAt_zpow (-1 - (k : ℤ)) ((u : ℂ) - center g) (Or.inl hz)).comp (u : ℂ)
      ((hasDerivAt_id (u : ℂ)).sub_const (center g))
    simp at this ⊢
    exact this
  have h2 := (h1.comp_ofReal).const_mul ((-1) ^ k * (k ! : ℂ))
  refine h2.congr_deriv ?_
  have he : (-1 - (k : ℤ) - 1) = (-1 - ((k + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [invTower, he, Nat.factorial_succ]
  push_cast
  ring

theorem hasDerivAt_re {F : ℝ → ℂ} {F' : ℂ} {u : ℝ} (h : HasDerivAt F F' u) :
    HasDerivAt (fun y => (F y).re) F'.re u := by
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u h
  simpa [Function.comp_def] using h2

theorem iteratedDeriv_re_logLine_succ (hg : g.det ≠ 0) (k : ℕ) :
    iteratedDeriv (k + 1) (fun u => (logLine g u).re) = fun u => (invTower g k u).re := by
  induction k with
  | zero =>
    rw [zero_add, iteratedDeriv_one]
    funext u
    exact (hasDerivAt_re (hasDerivAt_logLine hg u)).deriv
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    exact (hasDerivAt_re (hasDerivAt_invTower hg k u)).deriv

theorem iteratedDeriv_log_rad_succ (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    iteratedDeriv (k + 1) (fun u => Real.log (rad g u)) u = (invTower g k u).re := by
  have h : (fun u => Real.log (rad g u)) = fun u => Real.log ‖dir g‖ + (logLine g u).re :=
    funext (log_rad_eq hg)
  rw [h, iteratedDeriv_const_add (Nat.succ_pos k), iteratedDeriv_re_logLine_succ hg k]

theorem contDiff_logLine (hg : g.det ≠ 0) : ContDiff ℝ ∞ (logLine g) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => (y : ℂ) - center g) u :=
    (Complex.ofRealCLM.contDiff.sub contDiff_const).contDiffAt
  have h2 : ContDiffAt ℝ ∞ Complex.log ((u : ℂ) - center g) :=
    (Complex.contDiffAt_log (sub_center_mem_slitPlane hg u)).restrict_scalars ℝ
  exact h2.comp u h1

theorem contDiff_log_rad (hg : g.det ≠ 0) : ContDiff ℝ ∞ (fun u => Real.log (rad g u)) := by
  have h : (fun u => Real.log (rad g u)) = fun u => Real.log ‖dir g‖ + (logLine g u).re :=
    funext (log_rad_eq hg)
  rw [h]
  exact contDiff_const.add (Complex.reCLM.contDiff.comp (contDiff_logLine hg))

theorem contDiff_rad (hg : g.det ≠ 0) : ContDiff ℝ ∞ (rad g) := by
  have h : rad g = fun u => Real.exp (Real.log (rad g u)) :=
    funext fun u => (Real.exp_log (rad_pos hg u)).symm
  rw [h]
  exact Real.contDiff_exp.comp (contDiff_log_rad hg)

theorem norm_invTower_le (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    ‖invTower g k u‖ ≤ k ! * (botNormSq g / |g.det|) ^ (k + 1) := by
  have hz := sub_center_ne_zero hg u
  have hpos : 0 < |g.det| / botNormSq g := div_pos (abs_pos.2 hg) (botNormSq_pos hg)
  have hle := abs_det_div_le_norm_sub_center hg u
  have hk : (-1 - (k : ℤ)) = -(((k + 1 : ℕ)) : ℤ) := by push_cast; ring
  rw [invTower, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast, hk,
    zpow_neg, zpow_natCast, norm_inv, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  calc (‖(u : ℂ) - center g‖ ^ (k + 1))⁻¹ ≤ ((|g.det| / botNormSq g) ^ (k + 1))⁻¹ :=
        inv_anti₀ (pow_pos hpos _) (pow_le_pow_left₀ hpos.le hle _)
    _ = (botNormSq g / |g.det|) ^ (k + 1) := by rw [← inv_pow, inv_div]

theorem abs_iteratedDeriv_log_rad_le (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    |iteratedDeriv (k + 1) (fun u => Real.log (rad g u)) u| ≤ k ! * (botNormSq g / |g.det|) ^ (k + 1) := by
  rw [iteratedDeriv_log_rad_succ hg]
  exact (Complex.abs_re_le_norm _).trans (norm_invTower_le hg k u)

end M4aP3B.RealIwasawa
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B

end
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa

set_option autoImplicit false

noncomputable section

open MeasureTheory intervalIntegral Filter Topology
open scoped ContDiff

namespace M4aP3B
namespace AutoSmooth

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

structure IsOneParamGroup (R : ℝ → A) : Prop where
  map_zero : R 0 = 1
  map_add : ∀ s t : ℝ, R (s + t) = R s * R t
  continuous : Continuous R

def prim (R : ℝ → A) (t : ℝ) : A := ∫ u in (0 : ℝ)..t, R u

namespace IsOneParamGroup

variable {R : ℝ → A}

theorem hasDerivAt_prim (hR : IsOneParamGroup R) (t : ℝ) : HasDerivAt (prim R) (R t) t :=
  (hR.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem deriv_prim (hR : IsOneParamGroup R) : deriv (prim R) = R :=
  funext fun t => (hR.hasDerivAt_prim t).deriv

theorem differentiable_prim (hR : IsOneParamGroup R) : Differentiable ℝ (prim R) :=
  fun t => (hR.hasDerivAt_prim t).differentiableAt

theorem mul_prim (hR : IsOneParamGroup R) (t ε : ℝ) :
    R t * prim R ε = prim R (t + ε) - prim R t := by
  have h1 : R t * prim R ε = ∫ u in (0 : ℝ)..ε, R t * R u := by
    have h := (ContinuousLinearMap.mul ℝ A (R t)).intervalIntegral_comp_comm
      (hR.continuous.intervalIntegrable (μ := volume) 0 ε)
    simpa [prim] using h.symm
  have h2 : (∫ u in (0 : ℝ)..ε, R t * R u) = ∫ u in (0 : ℝ)..ε, R (t + u) := by
    congr 1
    funext u
    rw [hR.map_add]
  have h3 : (∫ u in (0 : ℝ)..ε, R (t + u)) = ∫ v in t..t + ε, R v := by
    rw [intervalIntegral.integral_comp_add_left R t, add_zero]
  have h4 : prim R (t + ε) - prim R t = ∫ v in t..t + ε, R v := by
    unfold prim
    exact intervalIntegral.integral_interval_sub_left (hR.continuous.intervalIntegrable _ _)
      (hR.continuous.intervalIntegrable _ _)
  rw [h1, h2, h3, h4]

theorem exists_isUnit_prim (hR : IsOneParamGroup R) : ∃ ε : ℝ, 0 < ε ∧ IsUnit (prim R ε) := by
  have hc : ContinuousAt R 0 := hR.continuous.continuousAt
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hball⟩ := hc (1 / 2) (by norm_num)
  have hε0 : (0 : ℝ) < δ / 2 := by positivity
  refine ⟨δ / 2, hε0, ?_⟩
  set ε : ℝ := δ / 2 with hεdef

  have hbound : ‖∫ u in (0 : ℝ)..ε, (R u - 1)‖ ≤ 1 / 2 * |ε - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le hε0.le] at hu
    have hud : dist u 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hu.1]
      linarith [hu.2]
    have h := hball hud
    rw [hR.map_zero, dist_eq_norm] at h
    exact h.le
  have hsplit : (∫ u in (0 : ℝ)..ε, (R u - 1)) = prim R ε - ε • (1 : A) := by
    rw [intervalIntegral.integral_sub (hR.continuous.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero]
    rfl

  have hx : ‖(1 : A) - ε⁻¹ • prim R ε‖ < 1 := by
    have hrw : (1 : A) - ε⁻¹ • prim R ε = -(ε⁻¹ • (prim R ε - ε • (1 : A))) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hε0.ne', one_smul, neg_sub]
    rw [hrw, norm_neg, norm_smul, ← hsplit, Real.norm_eq_abs, abs_inv, abs_of_pos hε0]
    calc ε⁻¹ * ‖∫ u in (0 : ℝ)..ε, (R u - 1)‖ ≤ ε⁻¹ * (1 / 2 * |ε - 0|) := by gcongr
      _ = 1 / 2 := by rw [sub_zero, abs_of_pos hε0]; field_simp
      _ < 1 := by norm_num
  have hu : IsUnit (ε⁻¹ • prim R ε) := by
    have h := (Units.oneSub ((1 : A) - ε⁻¹ • prim R ε) hx).isUnit
    rwa [Units.val_oneSub, sub_sub_cancel] at h
  have hεA : IsUnit (algebraMap ℝ A ε) := (isUnit_iff_ne_zero.2 hε0.ne').map (algebraMap ℝ A)
  have hrw : prim R ε = algebraMap ℝ A ε * (ε⁻¹ • prim R ε) := by
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hε0.ne', one_smul]
  rw [hrw]
  exact hεA.mul hu

theorem eq_sub_mul_inv (hR : IsOneParamGroup R) {ε : ℝ} (u : Aˣ) (hu : (u : A) = prim R ε) (t : ℝ) :
    R t = (prim R (t + ε) - prim R t) * (u⁻¹ : Aˣ) := by
  rw [← hR.mul_prim t ε, ← hu, Units.mul_inv_cancel_right]

theorem contDiff_nat (hR : IsOneParamGroup R) : ∀ n : ℕ, ContDiff ℝ n R := by
  obtain ⟨ε, _hε, hunit⟩ := hR.exists_isUnit_prim
  obtain ⟨u, hu⟩ := hunit
  have hformula : R = fun t => (prim R (t + ε) - prim R t) * ((u⁻¹ : Aˣ) : A) :=
    funext (hR.eq_sub_mul_inv u hu)
  intro n
  induction n with
  | zero => rw [Nat.cast_zero]; exact contDiff_zero.2 hR.continuous
  | succ n ih =>
    have hP : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (prim R) := by
      rw [contDiff_succ_iff_deriv]
      refine ⟨hR.differentiable_prim, fun h => absurd h (WithTop.natCast_ne_top n), ?_⟩
      rw [hR.deriv_prim]
      exact ih
    rw [Nat.cast_succ, hformula]
    exact ((hP.comp (contDiff_id.add contDiff_const)).sub hP).mul contDiff_const

theorem contDiff (hR : IsOneParamGroup R) : ContDiff ℝ ∞ R :=
  contDiff_infty.2 hR.contDiff_nat

theorem differentiable (hR : IsOneParamGroup R) : Differentiable ℝ R :=
  (hR.contDiff_nat 1).differentiable (by simp)

theorem deriv_eq_mul (hR : IsOneParamGroup R) (t : ℝ) : deriv R t = R t * deriv R 0 := by
  have hd := hR.differentiable
  have heq : (fun s => R (t + s)) = fun s => R t * R s := funext fun s => hR.map_add t s
  calc deriv R t = deriv (fun s => R (t + s)) 0 := by rw [deriv_comp_const_add, add_zero]
    _ = deriv (fun s => R t * R s) 0 := by rw [heq]
    _ = R t * deriv R 0 := deriv_const_mul _ (hd 0)

theorem iteratedDeriv_eq (hR : IsOneParamGroup R) (k : ℕ) :
    iteratedDeriv k R = fun t => R t * deriv R 0 ^ k := by
  induction k with
  | zero => funext t; simp [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [deriv_mul_const (hR.differentiable t), hR.deriv_eq_mul t, mul_assoc, ← pow_succ']

theorem norm_iteratedDeriv_le (hR : IsOneParamGroup R) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k R t‖ ≤ ‖R t‖ * ‖deriv R 0‖ ^ k := by
  rw [hR.iteratedDeriv_eq k]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact (norm_mul_le _ _).trans (by gcongr; exact norm_pow_le' _ hk)

end IsOneParamGroup
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa

theorem isOneParamGroup_cexp (c : ℂ) : IsOneParamGroup (fun t : ℝ => Complex.exp (t * c)) := by
  refine ⟨by simp, fun s t => ?_, Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)⟩
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem deriv_cexp_zero (c : ℂ) : deriv (fun t : ℝ => Complex.exp (t * c)) 0 = c := by
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (w * c))
      (Complex.exp ((((0 : ℝ) : ℂ)) * c) * (1 * c)) ((0 : ℝ) : ℂ) :=
    ((hasDerivAt_id' ((0 : ℝ) : ℂ)).mul_const c).cexp
  have h2 := h1.comp_ofReal
  rw [h2.deriv]
  simp

end M4aP3B.AutoSmooth
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa

end
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa

noncomputable section

open scoped ContDiff Nat
open M4aP3B.RealIwasawa M4aP3B.AutoSmooth

namespace M4aP3B
namespace ScalarMajorant

section Constants

variable (g : Matrix (Fin 2) (Fin 2) ℝ)

def towerRatio : ℝ := botNormSq g / |g.det|

def towerD (n : ℕ) : ℝ := n ! * max 1 (towerRatio g)

def radFloor : ℝ := min ((g.det ^ 2 / botNormSq g) / (1 + 2 * foot g ^ 2)) (botNormSq g / 2)

variable {g}

theorem towerRatio_nonneg : 0 ≤ towerRatio g :=
  div_nonneg (by unfold botNormSq; positivity) (abs_nonneg _)

theorem one_le_towerD (n : ℕ) : 1 ≤ towerD g n :=
  one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos n) (le_max_left _ _)

theorem towerD_pos (n : ℕ) : 0 < towerD g n := one_pos.trans_le (one_le_towerD n)

theorem radFloor_pos (hg : g.det ≠ 0) : 0 < radFloor g := by
  have hA := botNormSq_pos hg
  unfold radFloor
  exact lt_min (by positivity) (by linarith)

theorem floor_aux {A D f : ℝ} (hA : 0 < A) (hD : 0 < D) (u : ℝ) :
    min (D / (1 + 2 * f ^ 2)) (A / 2) * (1 + u ^ 2) ≤ A * (u - f) ^ 2 + D := by
  have h1 : 1 + u ^ 2 ≤ (1 + 2 * f ^ 2) + 2 * (u - f) ^ 2 := by nlinarith [sq_nonneg (u - 2 * f), sq_nonneg f]
  have hf2 : 0 < 1 + 2 * f ^ 2 := by positivity
  have hmin0 : 0 ≤ min (D / (1 + 2 * f ^ 2)) (A / 2) := le_min (div_nonneg hD.le hf2.le) (by linarith)
  calc min (D / (1 + 2 * f ^ 2)) (A / 2) * (1 + u ^ 2)
      ≤ min (D / (1 + 2 * f ^ 2)) (A / 2) * ((1 + 2 * f ^ 2) + 2 * (u - f) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hmin0
    _ = min (D / (1 + 2 * f ^ 2)) (A / 2) * (1 + 2 * f ^ 2)
          + min (D / (1 + 2 * f ^ 2)) (A / 2) * (2 * (u - f) ^ 2) := by ring
    _ ≤ D / (1 + 2 * f ^ 2) * (1 + 2 * f ^ 2) + A / 2 * (2 * (u - f) ^ 2) := by
        gcongr
        · exact min_le_left _ _
        · exact min_le_right _ _
    _ = A * (u - f) ^ 2 + D := by
        field_simp
        ring

theorem radFloor_mul_le_rad_sq (hg : g.det ≠ 0) (u : ℝ) : radFloor g * (1 + u ^ 2) ≤ rad g u ^ 2 := by
  rw [rad_sq_eq hg]
  exact floor_aux (botNormSq_pos hg) (by have := botNormSq_pos hg; positivity) u

end Constants
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa

section Towers

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

theorem factorial_mul_pow_le {k n : ℕ} (hkn : k + 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    (k ! : ℝ) * r ^ (k + 1) ≤ ((n ! : ℝ) * max 1 r) ^ (k + 1) := by
  have hn1 : (1 : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_pos n
  have h1 : (k ! : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_le (by omega)
  have h2 : (n ! : ℝ) ≤ (n ! : ℝ) ^ (k + 1) := le_self_pow₀ hn1 (Nat.succ_ne_zero k)
  have h3 : r ^ (k + 1) ≤ max 1 r ^ (k + 1) := pow_le_pow_left₀ hr (le_max_right _ _) _
  calc (k ! : ℝ) * r ^ (k + 1) ≤ (n ! : ℝ) ^ (k + 1) * max 1 r ^ (k + 1) :=
        mul_le_mul (h1.trans h2) h3 (by positivity) (by positivity)
    _ = ((n ! : ℝ) * max 1 r) ^ (k + 1) := (mul_pow _ _ _).symm

theorem norm_iteratedFDeriv_log_rad_le (hg : g.det ≠ 0) {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (u : ℝ) :
    ‖iteratedFDeriv ℝ i (fun u => Real.log (rad g u)) u‖ ≤ towerD g n ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (abs_iteratedDeriv_log_rad_le hg k u).trans (factorial_mul_pow_le hin towerRatio_nonneg)

end Towers
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa

section Composition

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

theorem norm_iteratedFDeriv_comp_log_rad_le (hg : g.det ≠ 0) {Ψ : ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ)
    {κ : ℝ} (hκ : 0 ≤ κ) (hΨd : ∀ (j : ℕ) (t : ℝ), ‖iteratedDeriv j Ψ t‖ ≤ κ ^ j * ‖Ψ t‖)
    {n i : ℕ} (hin : i ≤ n) (u : ℝ) :
    ‖iteratedFDeriv ℝ i (fun u => Ψ (Real.log (rad g u))) u‖
      ≤ n ! * (max 1 κ ^ n * ‖Ψ (Real.log (rad g u))‖) * towerD g n ^ n := by
  have hC : ∀ j, j ≤ i → ‖iteratedFDeriv ℝ j Ψ (Real.log (rad g u))‖
      ≤ max 1 κ ^ n * ‖Ψ (Real.log (rad g u))‖ := by
    intro j hj
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    refine (hΨd j _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (pow_le_pow_left₀ hκ (le_max_right 1 κ) j).trans (pow_le_pow_right₀ (le_max_left 1 κ) (hj.trans hin))
  have hD : ∀ j, 1 ≤ j → j ≤ i → ‖iteratedFDeriv ℝ j (fun u => Real.log (rad g u)) u‖ ≤ towerD g n ^ j :=
    fun j hj1 hji => norm_iteratedFDeriv_log_rad_le hg hj1 (hji.trans hin) u
  have h := norm_iteratedFDeriv_comp_le (g := Ψ) (f := fun u => Real.log (rad g u)) (n := i)
    hΨ (contDiff_log_rad hg) (by exact_mod_cast le_top) u hC hD
  rw [Function.comp_def] at h
  refine h.trans ?_
  have hfac : (i ! : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_le hin
  have hpow : towerD g n ^ i ≤ towerD g n ^ n := pow_le_pow_right₀ (one_le_towerD n) hin
  have h0 : 0 ≤ max 1 κ ^ n * ‖Ψ (Real.log (rad g u))‖ := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_right hfac h0) hpow (pow_nonneg (towerD_pos n).le _) (by positivity)

end Composition
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa

end M4aP3B.ScalarMajorant
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa

end
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa

open MeasureTheory Real VectorFourier
open scoped FourierTransform

noncomputable section

namespace M4aP3B
namespace FourierDecay

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem pow_mul_norm_fourierIntegral_le_of_coercive (L : V →L[ℝ] W →L[ℝ] ℝ)
    {μ : Measure V} [μ.IsAddHaarMeasure] {f : V → E} {n : ℕ} (hf : ContDiff ℝ n f)
    (h'f : ∀ j : ℕ, j ≤ n → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) μ)
    {c : ℝ} (hc : 0 ≤ c) (hL : ∀ w : W, ∃ v : V, ‖v‖ ≤ 1 ∧ c * ‖w‖ ≤ ‖L v w‖) (w : W) :
    (c * ‖w‖) ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖
      ≤ 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂μ := by
  obtain ⟨v, hv1, hvw⟩ := hL w
  have h'f' : ∀ (k j : ℕ), (k : ℕ∞) ≤ (0 : ℕ) → (j : ℕ∞) ≤ (n : ℕ) →
      Integrable (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖) μ := by
    intro k j hk hj
    have hk0 : k = 0 := by exact_mod_cast (nonpos_iff_eq_zero.mp (by exact_mod_cast hk))
    subst hk0
    simpa using h'f j (by exact_mod_cast hj)
  have key := pow_mul_norm_iteratedFDeriv_fourierIntegral_le L (K := (0 : ℕ)) (N := (n : ℕ))
    (hf := hf) h'f' (k := 0) (n := n) le_rfl le_rfl v w
  rw [norm_iteratedFDeriv_zero, pow_zero, mul_one] at key
  have hsum : ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
        ∫ x, ‖x‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f x‖ ∂μ
      = ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
    rw [Finset.sum_product, zero_add, Finset.range_one, Finset.sum_singleton]
    simp
  rw [hsum] at key
  have hS : 0 ≤ ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun x => norm_nonneg _
  calc (c * ‖w‖) ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖
      ≤ |L v w| ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖ := by
        gcongr
        exact hvw.trans_eq (Real.norm_eq_abs _)
    _ ≤ ‖v‖ ^ n * (2 * 0 + 2) ^ n
          * ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
        simpa using key
    _ ≤ 1 ^ n * (2 * 0 + 2) ^ n
          * ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
        gcongr
    _ = 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂μ := by norm_num

end M4aP3B.FourierDecay
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa

end
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa

set_option autoImplicit false

noncomputable section

open MeasureTheory
open M4aP3B.RealIwasawa M4aP3B.AutoSmooth M4aP3B.ScalarMajorant
open scoped ContDiff FourierTransform Nat

namespace M4aP3C
namespace RealDecay

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

def Ψ (u : ℂ) (t : ℝ) : ℂ := Complex.exp (↑t * (-u))

theorem isOneParamGroup_Ψ (u : ℂ) : IsOneParamGroup (Ψ u) := isOneParamGroup_cexp (-u)

theorem deriv_Ψ_zero (u : ℂ) : deriv (Ψ u) 0 = -u := deriv_cexp_zero (-u)

theorem norm_Ψ (u : ℂ) (t : ℝ) : ‖Ψ u t‖ = Real.exp (-u.re * t) := by
  unfold Ψ
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    zero_mul, sub_zero]
  ring

theorem norm_iteratedDeriv_Ψ_le (u : ℂ) (j : ℕ) (t : ℝ) :
    ‖iteratedDeriv j (Ψ u) t‖ ≤ ‖u‖ ^ j * ‖Ψ u t‖ := by
  have h := (isOneParamGroup_Ψ u).norm_iteratedDeriv_le j t
  rw [deriv_Ψ_zero, norm_neg] at h
  calc ‖iteratedDeriv j (Ψ u) t‖ ≤ ‖Ψ u t‖ * ‖u‖ ^ j := h
    _ = ‖u‖ ^ j * ‖Ψ u t‖ := mul_comm _ _

theorem norm_Ψ_log_rad (hg : g.det ≠ 0) (u : ℂ) (x : ℝ) :
    ‖Ψ u (Real.log (rad g x))‖ = rad g x ^ (-u.re) := by
  rw [norm_Ψ, Real.rpow_def_of_pos (rad_pos hg x), mul_comm (-u.re)]

theorem weight_eq (hg : g.det ≠ 0) (u : ℂ) (x : ℝ) :
    ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))
      = Ψ u (Real.log (rad g x)) := by
  rw [← rad_eq_sqrt g x]
  have hr := rad_pos hg x
  unfold Ψ
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'), ← Complex.ofReal_log hr.le]

theorem weightFun_eq (hg : g.det ≠ 0) (u : ℂ) :
    (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)))
      = fun x => Ψ u (Real.log (rad g x)) :=
  funext (weight_eq hg u)

theorem contDiff_Ψ_log_rad (hg : g.det ≠ 0) (u : ℂ) :
    ContDiff ℝ ∞ (fun x => Ψ u (Real.log (rad g x))) :=
  (isOneParamGroup_Ψ u).contDiff.comp (contDiff_log_rad hg)

theorem contDiff_weight (hg : g.det ≠ 0) (u : ℂ) :
    ContDiff ℝ ∞
      (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))) := by
  rw [weightFun_eq hg u]
  exact contDiff_Ψ_log_rad hg u

theorem norm_iteratedFDeriv_Ψ_log_rad_le (hg : g.det ≠ 0) (u : ℂ) (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (fun x => Ψ u (Real.log (rad g x))) x‖
      ≤ (n ! * max 1 ‖u‖ ^ n * towerD g n ^ n) * rad g x ^ (-u.re) := by
  have h := norm_iteratedFDeriv_comp_log_rad_le (g := g) hg (Ψ := Ψ u) (isOneParamGroup_Ψ u).contDiff
    (κ := ‖u‖) (norm_nonneg u) (norm_iteratedDeriv_Ψ_le u) (le_refl n) x
  rw [norm_Ψ_log_rad hg u x] at h
  calc ‖iteratedFDeriv ℝ n (fun x => Ψ u (Real.log (rad g x))) x‖
      ≤ n ! * (max 1 ‖u‖ ^ n * rad g x ^ (-u.re)) * towerD g n ^ n := h
    _ = (n ! * max 1 ‖u‖ ^ n * towerD g n ^ n) * rad g x ^ (-u.re) := by ring

theorem exists_bound_iteratedFDeriv_weight (hg : g.det ≠ 0) (u : ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖iteratedFDeriv ℝ n
          (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))) x‖
        ≤ C * rad g x ^ (-u.re) := by
  refine ⟨n ! * max 1 ‖u‖ ^ n * towerD g n ^ n, ?_, fun x => ?_⟩
  · have h1 : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    have h2 : (0 : ℝ) < max 1 ‖u‖ ^ n := pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) n
    exact mul_pos (mul_pos h1 h2) (pow_pos (towerD_pos n) n)
  · rw [weightFun_eq hg u]
    exact norm_iteratedFDeriv_Ψ_log_rad_le hg u n x

theorem rad_rpow_neg_le_one_add_sq (hg : g.det ≠ 0) {κ : ℝ} (hκ : 0 ≤ κ) (x : ℝ) :
    rad g x ^ (-κ) ≤ radFloor g ^ (-κ / 2) * (1 + ‖x‖ ^ 2) ^ (-κ / 2) := by
  have hF := radFloor_pos hg
  have hr := rad_pos hg x
  have hx2 : ‖x‖ ^ 2 = x ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [hx2]
  have h1 : rad g x ^ (-κ) = (rad g x ^ 2) ^ (-κ / 2) := by
    rw [← Real.rpow_natCast (rad g x) 2, ← Real.rpow_mul hr.le]
    congr 1
    push_cast
    ring
  rw [h1, ← Real.mul_rpow hF.le (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (radFloor_mul_le_rad_sq hg x) (by linarith)

theorem integrable_rpow_neg_rad (hg : g.det ≠ 0) {κ : ℝ} (hκ : 1 < κ) :
    Integrable (fun x => rad g x ^ (-κ)) (volume : Measure ℝ) := by
  have hint : Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-κ / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (μ := volume) (by rw [Module.finrank_self]; exact_mod_cast hκ)
  refine (hint.const_mul (radFloor g ^ (-κ / 2))).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((contDiff_rad hg).continuous.rpow_const fun x => Or.inl (rad_pos hg x).ne').aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg (rad_pos hg x).le _)]
    exact rad_rpow_neg_le_one_add_sq hg (by linarith) x

theorem exists_bound_iteratedFDeriv_weight_mul (hg : g.det ≠ 0) (u : ℂ)
    {P : ℝ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n P x‖ ≤ C) :
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖iteratedFDeriv ℝ n
          (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))
            * P x) x‖
        ≤ C * rad g x ^ (-u.re) := by
  intro n
  choose Cf hCf using fun i => exists_bound_iteratedFDeriv_weight hg u i
  choose Ch hCh using hPB
  have hpos : (0:ℝ) < ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cf i * Ch (n - i) := by
    refine Finset.sum_pos (fun i hi => ?_) ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
    have h1 : (0:ℝ) < (n.choose i : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    exact mul_pos (mul_pos h1 (hCf i).1) (hCh (n - i)).1
  refine ⟨_, hpos, fun x => ?_⟩
  have hrad := rad_pos hg x
  refine (norm_iteratedFDeriv_mul_le (contDiff_weight hg u) hPC x
    (mod_cast le_top)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  calc (n.choose i : ℝ)
        * ‖iteratedFDeriv ℝ i
            (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))) x‖
        * ‖iteratedFDeriv ℝ (n - i) P x‖
      ≤ (n.choose i : ℝ) * (Cf i * rad g x ^ (-u.re)) * Ch (n - i) := by
        gcongr
        · exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (hCf i).1.le (Real.rpow_nonneg hrad.le _))
        · exact (hCf i).2 x
        · exact (hCh (n - i)).2 x
    _ = (n.choose i : ℝ) * Cf i * Ch (n - i) * rad g x ^ (-u.re) := by ring

theorem norm_fourierIntegral_cpow_radR_mul_le_polyDecay
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {u : ℂ} (hu : 1 < u.re)
    {P : ℝ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n P x‖ ≤ C)
    (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun x => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P x) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  set f : ℝ → ℂ := fun x =>
    ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P x with hfdef

  obtain ⟨CB, hCB⟩ := Classical.axiom_of_choice
    (fun n => exists_bound_iteratedFDeriv_weight_mul hg u hPC hPB n)
  have hintr : Integrable (fun x => rad g x ^ (-u.re)) volume :=
    integrable_rpow_neg_rad hg hu
  have hfC : ContDiff ℝ ∞ f := (contDiff_weight hg u).mul hPC
  have hfCn : ContDiff ℝ (N : ℕ∞) f := hfC.of_le (mod_cast le_top)
  have h'f : ∀ j : ℕ, j ≤ N → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) volume := by
    intro j _
    refine (hintr.const_mul (CB j)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hfC.continuous_iteratedFDeriv (mod_cast le_top)).norm.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact (hCB j).2 x

  have key := M4aP3B.FourierDecay.pow_mul_norm_fourierIntegral_le_of_coercive L
    (f := f) hfCn h'f hc.le hL
  set MN : ℝ := 2 ^ N * ∑ j ∈ Finset.range (N + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume
  have hMN0 : (0:ℝ) ≤ MN :=
    mul_nonneg (pow_nonneg (by norm_num) N)
      (Finset.sum_nonneg fun j _ => integral_nonneg fun v => norm_nonneg _)

  have hfint : Integrable f volume := by
    refine (hintr.const_mul (CB 0)).mono' hfC.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h0 := (hCB 0).2 x
    rwa [norm_iteratedFDeriv_zero] at h0
  set M0 : ℝ := ∫ v, ‖f v‖ ∂volume
  have hM00 : (0:ℝ) ≤ M0 := integral_nonneg fun v => norm_nonneg _
  refine ⟨(M0 * 2 ^ N + MN * (2 / c) ^ N) + 1, by positivity, fun ξ => ?_⟩
  have hξ0 : (0:ℝ) ≤ ‖ξ‖ := norm_nonneg _
  have h1ξ : (0:ℝ) < 1 + ‖ξ‖ := by linarith
  have hrpow0 : (0:ℝ) < (1 + ‖ξ‖) ^ (-(N:ℝ)) := Real.rpow_pos_of_pos h1ξ _
  rcases lt_or_ge ‖ξ‖ 1 with hlt | hge
  ·
    have hbd : (2:ℝ) ^ (-(N:ℝ)) ≤ (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos h1ξ (by linarith)
        (neg_nonpos_of_nonneg (Nat.cast_nonneg N))
    have hstep1 : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖ ≤ M0 :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    have hstep2 : (M0 : ℝ) = M0 * 2 ^ N * (2:ℝ) ^ (-(N:ℝ)) := by
      rw [mul_assoc, show ((2:ℝ)^N : ℝ) = (2:ℝ)^(N:ℝ) from (Real.rpow_natCast 2 N).symm,
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2), add_neg_cancel, Real.rpow_zero, mul_one]
    have hstep3 : M0 * 2 ^ N * (2:ℝ) ^ (-(N:ℝ))
        ≤ M0 * 2 ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
      mul_le_mul_of_nonneg_left hbd
        (mul_nonneg hM00 (pow_nonneg (by norm_num) N))
    have hstep4 : (M0 * 2 ^ N : ℝ) ≤ M0 * 2 ^ N + MN * (2 / c) ^ N + 1 := by
      nlinarith [mul_nonneg hMN0
        (pow_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hc.le) N)]
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ M0 := hstep1
      _ = M0 * 2 ^ N * (2:ℝ) ^ (-(N:ℝ)) := hstep2
      _ ≤ M0 * 2 ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := hstep3
      _ ≤ (M0 * 2 ^ N + MN * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le
  ·
    have hkey := key ξ
    have hcξ : (0:ℝ) < c * ‖ξ‖ := mul_pos hc (by linarith)
    have hdiv : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ MN * (c * ‖ξ‖) ^ (-(N:ℝ)) := by
      rw [Real.rpow_neg hcξ.le, Real.rpow_natCast, ← div_eq_mul_inv,
        le_div_iff₀ (pow_pos hcξ N), mul_comm]
      exact hkey
    have h2 : (1:ℝ) + ‖ξ‖ ≤ 2 * ‖ξ‖ := by linarith
    have hcmp : (c * ‖ξ‖) ^ (-(N:ℝ)) ≤ (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := by
      have hsplit : (c * ‖ξ‖ : ℝ) = (c / 2) * (2 * ‖ξ‖) := by ring
      rw [hsplit, Real.mul_rpow (div_nonneg hc.le (by norm_num)) (by linarith)]
      have hp1 : ((c / 2 : ℝ)) ^ (-(N:ℝ)) = (2 / c) ^ N := by
        rw [Real.rpow_neg (div_nonneg hc.le (by norm_num)), Real.rpow_natCast,
          ← inv_pow, inv_div]
      rw [hp1]
      refine mul_le_mul_of_nonneg_left ?_
        (pow_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hc.le) N)
      exact Real.rpow_le_rpow_of_nonpos h1ξ h2 (neg_nonpos_of_nonneg (Nat.cast_nonneg N))
    have hstep4 : (MN * (2 / c) ^ N : ℝ) ≤ M0 * 2 ^ N + MN * (2 / c) ^ N + 1 := by
      nlinarith [mul_nonneg hM00 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) N)]
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ MN * (c * ‖ξ‖) ^ (-(N:ℝ)) := hdiv
      _ ≤ MN * ((2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ))) :=
          mul_le_mul_of_nonneg_left hcmp hMN0
      _ = MN * (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := by ring
      _ ≤ (M0 * 2 ^ N + MN * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le

end M4aP3C.RealDecay
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa

end
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa

open MeasureTheory
open scoped ContDiff FourierTransform

theorem solution
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {u : ℂ} (hu : 1 < u.re)
    {P : ℝ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n P x‖ ≤ C)
    (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun x => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P x) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
  M4aP3C.RealDecay.norm_fourierIntegral_cpow_radR_mul_le_polyDecay hg hu hPC hPB L hc hL N
