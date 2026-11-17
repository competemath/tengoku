import Tengoku.Seed.Analysis.Fourier.FourierTransformDeriv
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.lean`: wrote out 12 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 12 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open scoped ContDiff Nat

namespace M4aP3B
namespace RealIwasawa

def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/--
@isnad1 id=eq.0h1v.s5.c6656c68a198 from=translated src=- shape=b464c013 vocab=c98ac1c9
-/
@[scoped simp] theorem rot_apply_00 (θ : ℝ) : rot θ 0 0 = Real.cos θ := rfl
/--
@isnad1 id=eq.0h1v.s5.406bdeda2faa from=translated src=- shape=84fb2a41 vocab=a9494e64
-/
@[scoped simp] theorem rot_apply_01 (θ : ℝ) : rot θ 0 1 = -Real.sin θ := rfl
/--
@isnad1 id=eq.0h1v.s5.a832928ef5bc from=translated src=- shape=b464c013 vocab=fecf42b5
-/
@[scoped simp] theorem rot_apply_10 (θ : ℝ) : rot θ 1 0 = Real.sin θ := rfl
/--
@isnad1 id=eq.0h1v.s5.1a448efc6981 from=translated src=- shape=b464c013 vocab=c98ac1c9
-/
@[scoped simp] theorem rot_apply_11 (θ : ℝ) : rot θ 1 1 = Real.cos θ := rfl

/--
@isnad1 id=eq.0h0v.s6.43d6122e1aa3 from=translated src=- shape=4a8cf6c6 vocab=f102bebf
-/
theorem rot_zero : rot 0 = 1 := by
  rw [rot, Matrix.one_fin_two, Real.cos_zero, Real.sin_zero, neg_zero]

/--
@isnad1 id=eq.0h2v.s6.c69a92efadd4 from=translated src=- shape=095e2330 vocab=6307e38c
-/
theorem rot_add (s t : ℝ) : rot (s + t) = rot s * rot t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

/--
@isnad1 id=eq.0h1v.s7.5355030c587b from=translated src=- shape=b59b86e9 vocab=e07f3550
-/
theorem rot_mul_rot_neg (θ : ℝ) : rot θ * rot (-θ) = 1 := by
  rw [← rot_add, add_neg_cancel, rot_zero]

/--
@isnad1 id=eq.0h1v.s7.c5284d0e59c9 from=translated src=- shape=63d35e59 vocab=e07f3550
-/
theorem rot_neg_mul_rot (θ : ℝ) : rot (-θ) * rot θ = 1 := by
  rw [← rot_add, neg_add_cancel, rot_zero]

/--
@isnad1 id=contdiff.0h2v.s5.e6c39cb27213 from=translated src=- shape=f7509f7a vocab=a2b1e643
-/
theorem contDiff_rot_apply (i j : Fin 2) : ContDiff ℝ ∞ (fun θ => rot θ i j) := by
  fin_cases i <;> fin_cases j
  · show ContDiff ℝ ∞ fun θ => Real.cos θ
    exact Real.contDiff_cos
  · show ContDiff ℝ ∞ fun θ => -Real.sin θ
    exact Real.contDiff_sin.neg
  · show ContDiff ℝ ∞ fun θ => Real.sin θ
    exact Real.contDiff_sin
  · show ContDiff ℝ ∞ fun θ => Real.cos θ
    exact Real.contDiff_cos

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

/--
@isnad1 id=lt.1h1v.s5.9c447f9f7da5 from=translated src=- shape=56b50453 vocab=7e400c20
-/
theorem botNormSq_pos (hg : g.det ≠ 0) : 0 < botNormSq g := by
  unfold botNormSq
  rcases (add_nonneg (sq_nonneg (g 1 0)) (sq_nonneg (g 1 1))).lt_or_eq with h | h
  · exact h
  · exfalso
    have hc : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have hd : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    apply hg
    rw [Matrix.det_fin_two, hc, hd, mul_zero, mul_zero, sub_zero]

/--
@isnad1 id=eq.0h1v.s5.a9925af3738c from=translated src=- shape=3b240de4 vocab=feb17b74
-/
theorem norm_dir_sq (g : Matrix (Fin 2) (Fin 2) ℝ) : ‖dir g‖ ^ 2 = botNormSq g := by
  rw [Complex.sq_norm, dir, Complex.normSq_mk, botNormSq]
  ring

/--
@isnad1 id=lt.1h1v.s5.a00beb04dfa0 from=translated src=- shape=6a73246c vocab=0157d7e7
-/
theorem norm_dir_pos (hg : g.det ≠ 0) : 0 < ‖dir g‖ := by
  have h := norm_dir_sq g
  have hA := botNormSq_pos hg
  nlinarith [norm_nonneg (dir g)]

/--
@isnad1 id=eq.1h2v.s6.de5e09ac28ce from=translated src=- shape=93038de9 vocab=7aea8ce0
-/
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

/--
@isnad1 id=eq.0h2v.s6.e20881b420e6 from=translated src=- shape=7e4b4967 vocab=20bae742
-/
theorem im_sub_center (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    ((u : ℂ) - center g).im = g.det / botNormSq g := by
  simp [center]

/--
@isnad1 id=mem.1h2v.s6.56714d8929f1 from=translated src=- shape=69a04b94 vocab=d0574742
-/
theorem sub_center_mem_slitPlane (hg : g.det ≠ 0) (u : ℝ) : (u : ℂ) - center g ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inr (by
    rw [im_sub_center]
    exact div_ne_zero hg (botNormSq_pos hg).ne'))

/--
@isnad1 id=ne.1h2v.s6.ac868549da20 from=translated src=- shape=b689f707 vocab=56f6fce4
-/
theorem sub_center_ne_zero (hg : g.det ≠ 0) (u : ℝ) : (u : ℂ) - center g ≠ 0 :=
  Complex.slitPlane_ne_zero (sub_center_mem_slitPlane hg u)

/--
@isnad1 id=le.1h2v.s6.025890be13a5 from=translated src=- shape=e11c7fdd vocab=b52883bd
-/
theorem abs_det_div_le_norm_sub_center (hg : g.det ≠ 0) (u : ℝ) :
    |g.det| / botNormSq g ≤ ‖(u : ℂ) - center g‖ := by
  have h := Complex.abs_im_le_norm ((u : ℂ) - center g)
  rwa [im_sub_center, abs_div, abs_of_pos (botNormSq_pos hg)] at h

/--
@isnad1 id=eq.1h2v.s6.1fade9c1079a from=translated src=- shape=98549103 vocab=8a74734e
-/
theorem rad_eq (hg : g.det ≠ 0) (u : ℝ) : rad g u = ‖dir g‖ * ‖(u : ℂ) - center g‖ := by
  rw [rad, botRow_eq hg, norm_mul]

/--
@isnad1 id=lt.1h2v.s5.da59414c7aa9 from=translated src=- shape=099086ba vocab=40c6839b
-/
theorem rad_pos (hg : g.det ≠ 0) (u : ℝ) : 0 < rad g u := by
  rw [rad_eq hg]
  exact mul_pos (norm_dir_pos hg) (norm_pos_iff.2 (sub_center_ne_zero hg u))

/--
@isnad1 id=eq.0h2v.s7.022b230039df from=translated src=- shape=ff7c9e0b vocab=2b0c5002
-/
theorem rad_sq (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    rad g u ^ 2 = (g 0 0 + u * g 1 0) ^ 2 + (g 0 1 + u * g 1 1) ^ 2 := by
  rw [rad, Complex.sq_norm, botRow, Complex.normSq_mk]
  ring

/--
@isnad1 id=eq.0h2v.s7.07112ac790c2 from=translated src=- shape=7c123561 vocab=dc7d09d5
-/
theorem rad_eq_sqrt (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    rad g u = Real.sqrt ((g 0 0 + u * g 1 0) ^ 2 + (g 0 1 + u * g 1 1) ^ 2) := by
  rw [← rad_sq, Real.sqrt_sq (show 0 ≤ rad g u from norm_nonneg _)]

variable (g)

def logLine (u : ℝ) : ℂ := Complex.log ((u : ℂ) - center g)

def angle (u : ℝ) : ℝ := Complex.arg (dir g) + (logLine g u).im

variable {g}

/--
@isnad1 id=eq.0h2v.s5.4a6445e5baa3 from=translated src=- shape=0ee76720 vocab=763ecb29
-/
theorem angle_eq_arg_add_arg (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    angle g u = Complex.arg (dir g) + Complex.arg ((u : ℂ) - center g) := by
  rw [angle, logLine, Complex.log_im]

/--
@isnad1 id=eq.1h2v.s6.3fdc6dc3410e from=translated src=- shape=4498e195 vocab=9d465c93
-/
theorem exp_angle_mul_I (hg : g.det ≠ 0) (u : ℝ) :
    Complex.exp (angle g u * Complex.I) = botRow g u / rad g u := by
  have h1 : Complex.exp (Complex.arg (dir g) * Complex.I) = dir g / ‖dir g‖ := by
    rw [eq_div_iff (Complex.ofReal_ne_zero.2 (norm_dir_pos hg).ne')]
    exact (mul_comm _ _).trans (Complex.norm_mul_exp_arg_mul_I (dir g))
  have h2 : Complex.exp (Complex.arg ((u : ℂ) - center g) * Complex.I)
      = ((u : ℂ) - center g) / ‖(u : ℂ) - center g‖ := by
    rw [eq_div_iff (Complex.ofReal_ne_zero.2 (norm_pos_iff.2 (sub_center_ne_zero hg u)).ne')]
    exact (mul_comm _ _).trans (Complex.norm_mul_exp_arg_mul_I _)
  rw [angle_eq_arg_add_arg, Complex.ofReal_add, add_mul, Complex.exp_add, h1, h2, div_mul_div_comm,
    ← botRow_eq hg, rad_eq hg, Complex.ofReal_mul]

/--
@isnad1 id=eq.1h2v.s7.049d996a2293 from=translated src=- shape=b1162068 vocab=a22c5b17
-/
theorem cos_angle (hg : g.det ≠ 0) (u : ℝ) : Real.cos (angle g u) = (g 0 1 + u * g 1 1) / rad g u := by
  have h := congrArg Complex.re (exp_angle_mul_I hg u)
  rw [Complex.exp_ofReal_mul_I_re, Complex.div_ofReal_re] at h
  rw [h, botRow]

/--
@isnad1 id=eq.1h2v.s7.6315f04a4f05 from=translated src=- shape=b1162068 vocab=d6acfd6b
-/
theorem sin_angle (hg : g.det ≠ 0) (u : ℝ) : Real.sin (angle g u) = (g 0 0 + u * g 1 0) / rad g u := by
  have h := congrArg Complex.im (exp_angle_mul_I hg u)
  rw [Complex.exp_ofReal_mul_I_im, Complex.div_ofReal_im] at h
  rw [h, botRow]

variable (g)

def borel (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-g.det / rad g u, (g 1 0 * (g 0 0 + u * g 1 0) + g 1 1 * (g 0 1 + u * g 1 1)) / rad g u; 0, rad g u]

variable {g}

/--
@isnad1 id=eq.1h2v.s6.28be625163ba from=translated src=- shape=c055a3b6 vocab=08fe554c
-/
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

/--
@isnad1 id=eq.0h2v.s5.e15993cfd38e from=translated src=- shape=9a87429d vocab=2c29782f
-/
theorem invTower_zero (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) : invTower g 0 u = ((u : ℂ) - center g)⁻¹ := by
  simp [invTower]

/--
@isnad1 id=hasderiv.1h2v.s6.06a0e69e4951 from=translated src=- shape=73c739c4 vocab=6d9d7df4
-/
theorem hasDerivAt_logLine (hg : g.det ≠ 0) (u : ℝ) : HasDerivAt (logLine g) (invTower g 0 u) u := by
  have h : HasDerivAt (fun y : ℝ => (y : ℂ) - center g) 1 u := (hasDerivAt_id u).ofReal_comp.sub_const _
  have h2 := h.clog_real (sub_center_mem_slitPlane hg u)
  rw [invTower_zero, ← one_div]
  exact h2

/--
@isnad1 id=hasderiv.1h3v.s6.bd00c0e08ab1 from=translated src=- shape=e1e8e6a5 vocab=43a1ec81
-/
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

/--
@isnad1 id=hasderiv.1h3v.s6.2dad86aeded5 from=translated src=- shape=d9f49a33 vocab=7cc57c7f
-/
theorem hasDerivAt_im {F : ℝ → ℂ} {F' : ℂ} {u : ℝ} (h : HasDerivAt F F' u) :
    HasDerivAt (fun y => (F y).im) F'.im u := by
  have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt u h
  simpa [Function.comp_def] using h2

/--
@isnad1 id=eq.1h2v.s6.589904d57954 from=translated src=- shape=5cefad22 vocab=9fe0af79
-/
theorem iteratedDeriv_im_logLine_succ (hg : g.det ≠ 0) (k : ℕ) :
    iteratedDeriv (k + 1) (fun u => (logLine g u).im) = fun u => (invTower g k u).im := by
  induction k with
  | zero =>
    rw [zero_add, iteratedDeriv_one]
    funext u
    exact (hasDerivAt_im (hasDerivAt_logLine hg u)).deriv
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    exact (hasDerivAt_im (hasDerivAt_invTower hg k u)).deriv

/--
@isnad1 id=eq.1h3v.s6.faeb166a25c8 from=translated src=- shape=5d0476f4 vocab=1eeaca5c
-/
theorem iteratedDeriv_angle_succ (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    iteratedDeriv (k + 1) (angle g) u = (invTower g k u).im := by
  have h : angle g = fun u => Complex.arg (dir g) + (logLine g u).im := rfl
  rw [h, iteratedDeriv_const_add (Nat.succ_pos k), iteratedDeriv_im_logLine_succ hg k]

/--
@isnad1 id=contdiff.1h1v.s6.d63aae4c69ab from=translated src=- shape=ac69f61a vocab=0f1e0ac3
-/
theorem contDiff_logLine (hg : g.det ≠ 0) : ContDiff ℝ ∞ (logLine g) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => (y : ℂ) - center g) u :=
    (Complex.ofRealCLM.contDiff.sub contDiff_const).contDiffAt
  have h2 : ContDiffAt ℝ ∞ Complex.log ((u : ℂ) - center g) :=
    (Complex.contDiffAt_log (sub_center_mem_slitPlane hg u)).restrict_scalars ℝ
  exact h2.comp u h1

/--
@isnad1 id=contdiff.1h1v.s6.f01d13399b77 from=translated src=- shape=510efdfd vocab=bffa081b
-/
theorem contDiff_angle (hg : g.det ≠ 0) : ContDiff ℝ ∞ (angle g) :=
  contDiff_const.add (Complex.imCLM.contDiff.comp (contDiff_logLine hg))

/--
@isnad1 id=contdiff.1h3v.s6.c3915d207141 from=translated src=- shape=9eee8fd7 vocab=fcfe6b97
-/
theorem contDiff_rot_angle_apply (hg : g.det ≠ 0) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun u => rot (angle g u) i j) :=
  (contDiff_rot_apply i j).comp (contDiff_angle hg)

/--
@isnad1 id=le.1h3v.s7.1a2fe75c178c from=translated src=- shape=14262aa6 vocab=844c62fe
-/
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

/--
@isnad1 id=le.1h3v.s7.983b653f2baa from=translated src=- shape=95b6f957 vocab=c9e4fecd
-/
theorem abs_iteratedDeriv_angle_le (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    |iteratedDeriv (k + 1) (angle g) u| ≤ k ! * (botNormSq g / |g.det|) ^ (k + 1) := by
  rw [iteratedDeriv_angle_succ hg]
  exact (Complex.abs_im_le_norm _).trans (norm_invTower_le hg k u)

end M4aP3B.RealIwasawa
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B

end
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa

noncomputable section

open scoped ContDiff Nat
open M4aP3B.RealIwasawa

namespace M4aP3B
namespace ScalarMajorant

section Constants

variable (g : Matrix (Fin 2) (Fin 2) ℝ)

def towerRatio : ℝ := botNormSq g / |g.det|

def towerD (n : ℕ) : ℝ := n ! * max 1 (towerRatio g)

def radFloor : ℝ := min ((g.det ^ 2 / botNormSq g) / (1 + 2 * foot g ^ 2)) (botNormSq g / 2)

variable {g}

/--
@isnad1 id=le.0h1v.s4.f4fb4eb6d74f from=translated src=- shape=0c5cd9ab vocab=99f48e69
-/
theorem towerRatio_nonneg : 0 ≤ towerRatio g :=
  div_nonneg (by unfold botNormSq; positivity) (abs_nonneg _)

/--
@isnad1 id=le.0h2v.s4.ed9c92ed02ba from=translated src=- shape=037c33e6 vocab=6fe34408
-/
theorem one_le_towerD (n : ℕ) : 1 ≤ towerD g n :=
  one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos n) (le_max_left _ _)

/--
@isnad1 id=lt.0h2v.s4.2c875be16552 from=translated src=- shape=037c33e6 vocab=892097e9
-/
theorem towerD_pos (n : ℕ) : 0 < towerD g n := one_pos.trans_le (one_le_towerD n)

end Constants
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa

section Towers

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

/--
@isnad1 id=le.2h3v.s6.af42a6419c86 from=translated src=- shape=83720135 vocab=2fce4b88
-/
theorem factorial_mul_pow_le {k n : ℕ} (hkn : k + 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    (k ! : ℝ) * r ^ (k + 1) ≤ ((n ! : ℝ) * max 1 r) ^ (k + 1) := by
  have hn1 : (1 : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_pos n
  have h1 : (k ! : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_le (by omega)
  have h2 : (n ! : ℝ) ≤ (n ! : ℝ) ^ (k + 1) := le_self_pow₀ hn1 (Nat.succ_ne_zero k)
  have h3 : r ^ (k + 1) ≤ max 1 r ^ (k + 1) := pow_le_pow_left₀ hr (le_max_right _ _) _
  calc (k ! : ℝ) * r ^ (k + 1) ≤ (n ! : ℝ) ^ (k + 1) * max 1 r ^ (k + 1) :=
        mul_le_mul (h1.trans h2) h3 (by positivity) (by positivity)
    _ = ((n ! : ℝ) * max 1 r) ^ (k + 1) := (mul_pow _ _ _).symm

/--
@isnad1 id=le.3h4v.s8.a02c558f420b from=translated src=- shape=37182055 vocab=7e58b01c
-/
theorem norm_iteratedFDeriv_angle_le (hg : g.det ≠ 0) {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (u : ℝ) :
    ‖iteratedFDeriv ℝ i (angle g) u‖ ≤ towerD g n ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (abs_iteratedDeriv_angle_le hg k u).trans (factorial_mul_pow_le hin towerRatio_nonneg)

end Towers
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa

end M4aP3B.ScalarMajorant
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa

end
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa

noncomputable section

open scoped ContDiff Nat
open M4aP3B.RealIwasawa M4aP3B.ScalarMajorant

namespace M4aP3C
namespace RealKTower

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

/--
@isnad1 id=le.3h4v.s8.75bc3cfe8f35 from=translated src=- shape=f3e469bc vocab=23f82598
-/
theorem norm_iteratedFDeriv_comp_angle_le_of_abs_le_one (hg : g.det ≠ 0) {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c)
    (hcb : ∀ (j : ℕ) (θ : ℝ), |iteratedDeriv j c θ| ≤ 1) (n : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ n (fun u => c (angle g u)) u‖ ≤ n ! * towerD g n ^ n := by
  have hC : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j c (angle g u)‖ ≤ 1 := by
    intro j _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hcb j _
  have hD : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j (angle g) u‖ ≤ towerD g n ^ j :=
    fun j hj1 hjn => norm_iteratedFDeriv_angle_le hg hj1 hjn u
  have h := norm_iteratedFDeriv_comp_le (g := c) (f := angle g) (n := n)
    hc (contDiff_angle hg) (by exact_mod_cast le_top) u hC hD
  rw [Function.comp_def, mul_one] at h
  exact h

/--
@isnad1 id=le.1h3v.s8.eb96d6037c9e from=translated src=- shape=d6df3018 vocab=2003b9b7
-/
theorem norm_iteratedFDeriv_cos_angle_le (hg : g.det ≠ 0) (n : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ n (fun u => Real.cos (angle g u)) u‖ ≤ n ! * towerD g n ^ n :=
  norm_iteratedFDeriv_comp_angle_le_of_abs_le_one hg Real.contDiff_cos Real.abs_iteratedDeriv_cos_le_one n u

/--
@isnad1 id=le.1h3v.s8.de1e956a4045 from=translated src=- shape=d6df3018 vocab=8af00edd
-/
theorem norm_iteratedFDeriv_sin_angle_le (hg : g.det ≠ 0) (n : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ n (fun u => Real.sin (angle g u)) u‖ ≤ n ! * towerD g n ^ n :=
  norm_iteratedFDeriv_comp_angle_le_of_abs_le_one hg Real.contDiff_sin Real.abs_iteratedDeriv_sin_le_one n u

/--
@isnad1 id=le.1h3v.s8.dabf03d13976 from=translated src=- shape=0a7b6ada vocab=b9bd5c67
-/
theorem norm_iteratedFDeriv_neg_sin_angle_le (hg : g.det ≠ 0) (n : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ n (fun u => -Real.sin (angle g u)) u‖ ≤ n ! * towerD g n ^ n := by
  have hneg : (fun u => -Real.sin (angle g u)) = -(fun u => Real.sin (angle g u)) := rfl
  rw [hneg, iteratedFDeriv_neg_apply, norm_neg]
  exact norm_iteratedFDeriv_sin_angle_le hg n u

/--
@isnad1 id=le.1h5v.s8.fd7c8921d394 from=translated src=- shape=856bf5d9 vocab=a1695cd9
-/
theorem norm_iteratedFDeriv_rot_angle_apply_le (hg : g.det ≠ 0) (n : ℕ) (u : ℝ) :
    ∀ i j : Fin 2, ‖iteratedFDeriv ℝ n (fun x => rot (angle g x) i j) u‖ ≤ n ! * towerD g n ^ n := by
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · exact norm_iteratedFDeriv_cos_angle_le hg n u
  · exact norm_iteratedFDeriv_neg_sin_angle_le hg n u
  · exact norm_iteratedFDeriv_sin_angle_le hg n u
  · exact norm_iteratedFDeriv_cos_angle_le hg n u

/--
@isnad1 id=eq.1h3v.s9.270e4af0764c from=translated src=- shape=941c37e5 vocab=0d2cd7a8
-/
theorem kR_literal_eq_rot_angle (hg : g.det ≠ 0) : ∀ i j : Fin 2,
    (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)
      = fun x => rot (angle g x) i j := by
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · funext x
    show (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ * (g 0 1 + x * g 1 1)
      = rot (angle g x) 0 0
    rw [rot_apply_00, cos_angle hg, rad_eq_sqrt, div_eq_inv_mul]
  · funext x
    show (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ * (-(g 0 0 + x * g 1 0))
      = rot (angle g x) 0 1
    rw [rot_apply_01, sin_angle hg, rad_eq_sqrt, div_eq_inv_mul, mul_neg]
  · funext x
    show (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ * (g 0 0 + x * g 1 0)
      = rot (angle g x) 1 0
    rw [rot_apply_10, sin_angle hg, rad_eq_sqrt, div_eq_inv_mul]
  · funext x
    show (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ * (g 0 1 + x * g 1 1)
      = rot (angle g x) 1 1
    rw [rot_apply_11, cos_angle hg, rad_eq_sqrt, div_eq_inv_mul]

/--
@isnad1 id=and.1h1v.s10.a45dac6dff9e from=translated src=- shape=5f7d738d vocab=c4aeb885
-/
theorem contDiff_and_exists_bound (hg : g.det ≠ 0) :
    (∀ i j : Fin 2, ContDiff ℝ ∞
      (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (u : ℝ),
      ‖iteratedFDeriv ℝ n (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j) u‖ ≤ C := by
  refine ⟨fun i j => ?_, fun n => ⟨n ! * towerD g n ^ n,
    mul_pos (by exact_mod_cast Nat.factorial_pos n) (pow_pos (towerD_pos n) n), fun i j u => ?_⟩⟩
  · rw [kR_literal_eq_rot_angle hg i j]
    exact contDiff_rot_angle_apply hg i j
  · rw [kR_literal_eq_rot_angle hg i j]
    exact norm_iteratedFDeriv_rot_angle_apply_le hg n u i j

end M4aP3C.RealKTower
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa

end
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa

noncomputable section

open scoped ContDiff

/--
@isnad1 id=and.1h1v.s10.a45dac6dff9e from=translated src=- shape=5f7d738d vocab=c4aeb885
-/
theorem solution
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) :
    (∀ i j : Fin 2, ContDiff ℝ ∞
      (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (u : ℝ),
      ‖iteratedFDeriv ℝ n (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j) u‖ ≤ C :=
  M4aP3C.RealKTower.contDiff_and_exists_bound hg

end
open scoped _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B _root_.P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa

