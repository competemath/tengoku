import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ComplexIwasawa
import Tengoku.Seed.Analysis.Calculus.ContDiff.Defs
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean`: wrote out 10 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 10 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact

set_option autoImplicit false

noncomputable section

open ComplexConjugate
open scoped ContDiff

namespace M4aP3C
namespace CplxIwasawa

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

def weylUnipC (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0] * !![1, z; 0, 1] * g

def botP (z : ℂ) : ℂ := g 0 0 + z * g 1 0

def botQ (z : ℂ) : ℂ := g 0 1 + z * g 1 1

def botNormSqC : ℝ := Complex.normSq (g 1 0) + Complex.normSq (g 1 1)

def centerC : ℂ := -(conj (g 1 0) * g 0 0 + conj (g 1 1) * g 0 1) / (botNormSqC g : ℂ)

def radC (z : ℂ) : ℝ := Real.sqrt (Complex.normSq (botP g z) + Complex.normSq (botQ g z))

def kC (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![conj (botQ g z) / (radC g z : ℂ), -conj (botP g z) / (radC g z : ℂ);
     botP g z / (radC g z : ℂ), botQ g z / (radC g z : ℂ)]

def borelC (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-g.det / (radC g z : ℂ),
     (g 1 0 * conj (botP g z) + g 1 1 * conj (botQ g z)) / (radC g z : ℂ);
     0, (radC g z : ℂ)]

variable {g}

/--
@isnad1 id=eq.0h2v.s6.c143a3805d60 from=translated src=- shape=0f43f2be vocab=105d6749
-/
theorem radC_sq (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    radC g z ^ 2 = Complex.normSq (botP g z) + Complex.normSq (botQ g z) := by
  rw [radC, Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]

/--
@isnad1 id=lt.1h1v.s5.d55bdf2d9546 from=translated src=- shape=21445356 vocab=cf2dcb52
-/
theorem botNormSqC_pos (hg : g.det ≠ 0) : 0 < botNormSqC g := by
  rw [botNormSqC]
  rcases (add_nonneg (Complex.normSq_nonneg (g 1 0)) (Complex.normSq_nonneg (g 1 1))).lt_or_eq
    with h | h
  · exact h
  · exfalso
    have hc : Complex.normSq (g 1 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (g 1 0), Complex.normSq_nonneg (g 1 1)]
    have hd : Complex.normSq (g 1 1) = 0 := by
      nlinarith [Complex.normSq_nonneg (g 1 0), Complex.normSq_nonneg (g 1 1)]
    apply hg
    rw [Matrix.det_fin_two, Complex.normSq_eq_zero.1 hc, Complex.normSq_eq_zero.1 hd,
      mul_zero, mul_zero, sub_zero]

/--
@isnad1 id=eq.1h2v.s7.9ea66097c766 from=translated src=- shape=28697d87 vocab=fa932536
-/
theorem radC_sq_eq (hg : g.det ≠ 0) (z : ℂ) :
    radC g z ^ 2 = botNormSqC g * Complex.normSq (z - centerC g)
      + Complex.normSq g.det / botNormSqC g := by
  have hA : botNormSqC g ≠ 0 := (botNormSqC_pos hg).ne'
  have hAc : (botNormSqC g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hA
  have hz : z - centerC g = ((botNormSqC g : ℂ) * z + ((starRingEnd ℂ) (g 1 0) * g 0 0
      + (starRingEnd ℂ) (g 1 1) * g 0 1)) / (botNormSqC g : ℂ) := by
    rw [centerC]
    field_simp
    try ring
  rw [radC_sq, hz, Complex.normSq_div, Complex.normSq_ofReal, Matrix.det_fin_two]
  field_simp
  simp only [botP, botQ, botNormSqC, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/--
@isnad1 id=lt.1h2v.s5.f4b8329a3ca5 from=translated src=- shape=606d29bf vocab=0c1013b2
-/
theorem radC_pos (hg : g.det ≠ 0) (z : ℂ) : 0 < radC g z := by
  rw [radC]
  apply Real.sqrt_pos.2
  rcases (add_nonneg (Complex.normSq_nonneg (botP g z)) (Complex.normSq_nonneg (botQ g z))).lt_or_eq
    with h | h
  · exact h
  · exfalso
    have hP : Complex.normSq (botP g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hQ : Complex.normSq (botQ g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hP0 := Complex.normSq_eq_zero.1 hP
    have hQ0 := Complex.normSq_eq_zero.1 hQ
    rw [botP] at hP0
    rw [botQ] at hQ0
    apply hg
    rw [Matrix.det_fin_two]
    have ha : g 0 0 = -(z * g 1 0) := by linear_combination hP0
    have hb : g 0 1 = -(z * g 1 1) := by linear_combination hQ0
    rw [ha, hb]
    ring

/--
@isnad1 id=eq.1h2v.s7.864bf5ec03e1 from=translated src=- shape=aa38f7ec vocab=c806b7be
-/
theorem kC_mul_conjTranspose (hg : g.det ≠ 0) (z : ℂ) :
    kC g z * (kC g z).conjTranspose = 1 := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos hg z).ne'
  have key : botP g z * (starRingEnd ℂ) (botP g z) + botQ g z * (starRingEnd ℂ) (botQ g z)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, ← Complex.ofReal_mul]
    norm_cast
    rw [← pow_two]
    linarith [radC_sq g z]
  rw [kC, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, map_div₀, map_neg,
      Complex.conj_ofReal] <;>
    (try field_simp) <;>
    first
    | linear_combination key
    | ring

/--
@isnad1 id=eq.1h2v.s7.8ee4c960d5eb from=translated src=- shape=9aac7860 vocab=c806b7be
-/
theorem conjTranspose_mul_kC (hg : g.det ≠ 0) (z : ℂ) :
    (kC g z).conjTranspose * kC g z = 1 := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos hg z).ne'
  have key : botP g z * (starRingEnd ℂ) (botP g z) + botQ g z * (starRingEnd ℂ) (botQ g z)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, ← Complex.ofReal_mul]
    norm_cast
    rw [← pow_two]
    linarith [radC_sq g z]
  rw [kC, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, map_div₀, map_neg,
      Complex.conj_ofReal] <;>
    (try field_simp) <;>
    first
    | linear_combination key
    | ring

/--
@isnad1 id=eq.1h2v.s6.4d853536989b from=translated src=- shape=c055a3b6 vocab=b2be34fb
-/
theorem det_borelC (hg : g.det ≠ 0) (z : ℂ) : (borelC g z).det = -g.det := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos hg z).ne'
  rw [borelC, Matrix.det_fin_two_of, mul_zero, sub_zero, div_mul_cancel₀ _ hr]

/--
@isnad1 id=contdiff.1h1v.s6.e9850ccad1d2 from=translated src=- shape=ea1704a6 vocab=07146463
-/
theorem contDiff_radC (hg : g.det ≠ 0) : ContDiff ℝ ∞ (radC g) := by
  have hnormSq : ContDiff ℝ ∞ Complex.normSq := by
    have h : (Complex.normSq : ℂ → ℝ) = fun z => z.re * z.re + z.im * z.im := by
      funext w
      exact Complex.normSq_apply w
    rw [h]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hP : ContDiff ℝ ∞ (botP g) := by
    unfold botP
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hQ : ContDiff ℝ ∞ (botQ g) := by
    unfold botQ
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hinner : ContDiff ℝ ∞ (fun z => Complex.normSq (botP g z) + Complex.normSq (botQ g z)) :=
    (hnormSq.comp hP).add (hnormSq.comp hQ)
  rw [contDiff_iff_contDiffAt]
  intro z
  have hpos : Complex.normSq (botP g z) + Complex.normSq (botQ g z) ≠ 0 := by
    rw [← radC_sq g z]
    exact (pow_pos (radC_pos hg z) 2).ne'
  have h := (Real.contDiffAt_sqrt hpos).comp z hinner.contDiffAt
  simp [radC, Function.comp_def] at h
  exact h

def kCGL (hg : g.det ≠ 0) (z : ℂ) : GL (Fin 2) ℂ :=
  ⟨kC g z, (kC g z).conjTranspose, kC_mul_conjTranspose hg z, conjTranspose_mul_kC hg z⟩

def borelCGL (hg : g.det ≠ 0) (z : ℂ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (borelC g z)
    (by rw [det_borelC hg z]; exact neg_ne_zero.2 hg)

def weylC : GL (Fin 2) ℂ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

def unipC (z : ℂ) : GL (Fin 2) ℂ :=
  ⟨!![1, z; 0, 1], !![1, -z; 0, 1],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

end M4aP3C.CplxIwasawa
open scoped _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxIwasawa
open scoped _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C

end
open scoped _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxIwasawa

noncomputable section

namespace M4aP3C
namespace CplxSmooth

open scoped ContDiff Nat

open M4aP3C.CplxIwasawa

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

/--
@isnad1 id=eqon.1h3v.s6.2ceb79c5b4ff from=translated src=- shape=d8b32318 vocab=a89afa85
-/
theorem iteratedDerivWithin_rpow_const {c : ℝ} (hc : 0 < c) (r : ℝ) (k : ℕ) :
    Set.EqOn (iteratedDerivWithin k (fun v : ℝ => v ^ r) (Set.Ioi c))
      (fun v => (∏ i ∈ Finset.range k, (r - i)) * v ^ (r - k)) (Set.Ioi c) := by
  induction k with
  | zero =>
    intro v hv
    simp [iteratedDerivWithin_zero]
  | succ k ih =>
    intro v hv
    have hvpos : 0 < v := hc.trans hv
    have hopen : IsOpen (Set.Ioi c) := isOpen_Ioi
    rw [iteratedDerivWithin_succ, derivWithin_of_isOpen hopen hv]
    have hev : iteratedDerivWithin k (fun v : ℝ => v ^ r) (Set.Ioi c)
        =ᶠ[nhds v] fun v => (∏ i ∈ Finset.range k, (r - i)) * v ^ (r - k) := by
      filter_upwards [hopen.mem_nhds hv] with w hw
      exact ih hw
    rw [hev.deriv_eq]
    have hd : HasDerivAt (fun v : ℝ => v ^ (r - k))
        ((r - k) * v ^ (r - k - 1)) v :=
      Real.hasDerivAt_rpow_const (Or.inl hvpos.ne')
    rw [deriv_const_mul _ hd.differentiableAt, hd.deriv]
    rw [Finset.prod_range_succ]
    push_cast
    ring_nf

/--
@isnad1 id=le.2h3v.s7.e4929e636548 from=translated src=- shape=869bcd00 vocab=42eff942
-/
theorem norm_iteratedDerivWithin_rpow_neg_half_le {c : ℝ} (hc : 0 < c) (k : ℕ) {v : ℝ}
    (hv : v ∈ Set.Ioi c) :
    ‖iteratedDerivWithin k (fun v : ℝ => v ^ (-(1 : ℝ) / 2)) (Set.Ioi c) v‖
      ≤ k ! * c ^ (-(1 : ℝ) / 2 - k) := by
  have hvpos : (0 : ℝ) < v := hc.trans hv
  rw [iteratedDerivWithin_rpow_const hc (-(1 : ℝ) / 2) k hv]
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |∏ i ∈ Finset.range k, (-(1 : ℝ) / 2 - i)| ≤ (k ! : ℝ) := by
    rw [Finset.abs_prod]
    have hfac : (k ! : ℝ) = ∏ i ∈ Finset.range k, ((i : ℝ) + 1) := by
      induction k with
      | zero => simp
      | succ n ih => rw [Finset.prod_range_succ, ← ih, Nat.factorial_succ]; push_cast; ring
    rw [hfac]
    refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hneg : (-(1 : ℝ) / 2 - i) < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  have h2 : |v ^ (-(1 : ℝ) / 2 - (k : ℝ))| ≤ c ^ (-(1 : ℝ) / 2 - k) := by
    rw [abs_of_nonneg (Real.rpow_nonneg hvpos.le _)]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)
      (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hvpos) hv.le
  calc |∏ i ∈ Finset.range k, (-(1 : ℝ) / 2 - i)| * |v ^ (-(1 : ℝ) / 2 - (k : ℝ))|
      ≤ (k ! : ℝ) * c ^ (-(1 : ℝ) / 2 - k) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)

def uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ → ℝ := fun w =>
  botNormSqC g * Complex.normSq (w - centerC g) + Complex.normSq g.det / botNormSqC g

/--
@isnad1 id=eq.1h2v.s6.5577cb7aa212 from=translated src=- shape=5006f716 vocab=41465ca6
-/
theorem uQuad_eq_radC_sq (hg : g.det ≠ 0) (w : ℂ) : uQuad g w = radC g w ^ 2 :=
  (radC_sq_eq hg w).symm

/--
@isnad1 id=le.1h2v.s6.68dc66ee78fd from=translated src=- shape=7cfd9da2 vocab=e618920d
-/
theorem uQuad_ge (hg : g.det ≠ 0) (w : ℂ) :
    Complex.normSq g.det / botNormSqC g ≤ uQuad g w := by
  have h : 0 ≤ botNormSqC g * Complex.normSq (w - centerC g) :=
    mul_nonneg (botNormSqC_pos hg).le (Complex.normSq_nonneg _)
  unfold uQuad
  linarith

/--
@isnad1 id=eq.0h2v.s7.2a8111872f2e from=translated src=- shape=4404b959 vocab=43f6ef26
-/
theorem uQuad_eq_coords (w : ℂ) :
    uQuad g w = botNormSqC g * ((w.re - (centerC g).re) ^ 2 + (w.im - (centerC g).im) ^ 2)
      + Complex.normSq g.det / botNormSqC g := by
  unfold uQuad
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

/--
@isnad1 id=hasfderi.0h2v.s10.35fdefebaab9 from=translated src=- shape=aa68ec95 vocab=d137c03d
-/
theorem hasFDerivAt_uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) (w : ℂ) :
    HasFDerivAt (uQuad g)
      ((2 * botNormSqC g * (w - centerC g).re) • Complex.reCLM
        + (2 * botNormSqC g * (w - centerC g).im) • Complex.imCLM) w := by
  have hre : HasFDerivAt (fun v : ℂ => (v.re - (centerC g).re) ^ 2)
      ((2 * (w.re - (centerC g).re)) • (Complex.reCLM : ℂ →L[ℝ] ℝ)) w := by
    have h1 : HasFDerivAt (fun v : ℂ => v.re - (centerC g).re)
        (Complex.reCLM : ℂ →L[ℝ] ℝ) w :=
      (Complex.reCLM.hasFDerivAt).sub_const _
    simpa [pow_one, mul_comm, mul_assoc, smul_smul] using h1.pow 2
  have him : HasFDerivAt (fun v : ℂ => (v.im - (centerC g).im) ^ 2)
      ((2 * (w.im - (centerC g).im)) • (Complex.imCLM : ℂ →L[ℝ] ℝ)) w := by
    have h1 : HasFDerivAt (fun v : ℂ => v.im - (centerC g).im)
        (Complex.imCLM : ℂ →L[ℝ] ℝ) w :=
      (Complex.imCLM.hasFDerivAt).sub_const _
    simpa [pow_one, mul_comm, mul_assoc, smul_smul] using h1.pow 2
  have hsum := ((hre.add him).const_mul (botNormSqC g)).add_const
    (Complex.normSq g.det / botNormSqC g)
  have huq : HasFDerivAt (uQuad g)
      (botNormSqC g • ((2 * (w.re - (centerC g).re)) • (Complex.reCLM : ℂ →L[ℝ] ℝ)
        + (2 * (w.im - (centerC g).im)) • (Complex.imCLM : ℂ →L[ℝ] ℝ))) w := by
    apply hsum.congr_of_eventuallyEq
    filter_upwards with v
    rw [uQuad_eq_coords]
    simp only [Pi.add_apply]
  convert huq using 1
  ext v
  simp [smul_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.sub_re, Complex.sub_im]
  ring

def lamQuad (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  Complex.reCLM.smulRight ((2 * botNormSqC g) • (Complex.reCLM : ℂ →L[ℝ] ℝ))
    + Complex.imCLM.smulRight ((2 * botNormSqC g) • (Complex.imCLM : ℂ →L[ℝ] ℝ))

/--
@isnad1 id=eq.0h3v.s9.cad6bf9256ef from=translated src=- shape=a1bbf4f0 vocab=190c5172
-/
@[scoped simp] theorem lamQuad_apply_apply (g : Matrix (Fin 2) (Fin 2) ℂ) (v w : ℂ) :
    lamQuad g v w = 2 * botNormSqC g * v.re * w.re + 2 * botNormSqC g * v.im * w.im := by
  simp [lamQuad, ContinuousLinearMap.smulRight_apply]
  ring

/--
@isnad1 id=le.0h2v.s9.920de25a0117 from=translated src=- shape=391c3bad vocab=c7721a72
-/
theorem norm_lamQuad_apply_le (g : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ) :
    ‖lamQuad g v‖ ≤ 4 * botNormSqC g * ‖v‖ := by
  have hA : 0 ≤ botNormSqC g := by
    unfold botNormSqC
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (by norm_num) hA) (norm_nonneg v)) fun w => ?_
  rw [lamQuad_apply_apply, Real.norm_eq_abs]
  have hre : |v.re * w.re| ≤ ‖v‖ * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (Complex.abs_re_le_norm v) (Complex.abs_re_le_norm w)
      (abs_nonneg _) (norm_nonneg _)
  have him : |v.im * w.im| ≤ ‖v‖ * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (Complex.abs_im_le_norm v) (Complex.abs_im_le_norm w)
      (abs_nonneg _) (norm_nonneg _)
  have hre' := abs_le.1 hre
  have him' := abs_le.1 him
  refine abs_le.2 ⟨?_, ?_⟩ <;>
    nlinarith [mul_le_mul_of_nonneg_left hre'.2 hA, mul_le_mul_of_nonneg_left hre'.1 hA,
      mul_le_mul_of_nonneg_left him'.2 hA, mul_le_mul_of_nonneg_left him'.1 hA]

/--
@isnad1 id=le.0h1v.s9.f6c6dd3130be from=translated src=- shape=1526bc53 vocab=f8fd6e90
-/
theorem norm_lamQuad_le (g : Matrix (Fin 2) (Fin 2) ℂ) : ‖lamQuad g‖ ≤ 4 * botNormSqC g := by
  have hA : 0 ≤ botNormSqC g := by
    unfold botNormSqC
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hA)
    fun v => norm_lamQuad_apply_le g v

/--
@isnad1 id=eq.0h2v.s9.9605c10cd7ef from=translated src=- shape=9e15c5ea vocab=f6c0d9a7
-/
theorem fderiv_uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    fderiv ℝ (uQuad g) z = lamQuad g (z - centerC g) := by
  rw [(hasFDerivAt_uQuad g z).fderiv]
  ext w
  simp [smul_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.sub_re, Complex.sub_im]
  ring

/--
@isnad1 id=hasfderi.0h2v.s8.a5b72c4d19b5 from=translated src=- shape=f365c968 vocab=47dc242e
-/
theorem hasFDerivAt_fderiv_uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    HasFDerivAt (fderiv ℝ (uQuad g)) (lamQuad g) z := by
  have heq : fderiv ℝ (uQuad g) = fun w => lamQuad g (w - centerC g) :=
    funext (fderiv_uQuad g)
  rw [heq]
  have hcomp := (lamQuad g).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const (centerC g))
  exact hcomp

/--
@isnad1 id=le.0h2v.s8.a7e293c07e03 from=translated src=- shape=2938557c vocab=e4d174d0
-/
theorem norm_iteratedFDeriv_uQuad_one (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ 1 (uQuad g) z‖ ≤ 4 * botNormSqC g * ‖z - centerC g‖ := by
  have h1 : ‖iteratedFDeriv ℝ 1 (uQuad g) z‖
      = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (uQuad g)) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := 0)).symm
  rw [h1, norm_iteratedFDeriv_zero, fderiv_uQuad]
  exact norm_lamQuad_apply_le g _

/--
@isnad1 id=le.0h2v.s7.06f248c02acf from=translated src=- shape=1e12ce57 vocab=bbf5872d
-/
theorem norm_iteratedFDeriv_uQuad_two (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ 2 (uQuad g) z‖ ≤ 4 * botNormSqC g := by
  have h2 : ‖iteratedFDeriv ℝ 2 (uQuad g) z‖
      = ‖iteratedFDeriv ℝ 1 (fderiv ℝ (uQuad g)) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := 1)).symm
  have h1 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ (uQuad g)) z‖
      = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (fderiv ℝ (uQuad g))) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := 0)).symm
  have hfd : fderiv ℝ (fderiv ℝ (uQuad g)) z = lamQuad g :=
    (hasFDerivAt_fderiv_uQuad g z).fderiv
  rw [h2, h1, norm_iteratedFDeriv_zero, hfd]
  exact norm_lamQuad_le g

/--
@isnad1 id=eq.1h3v.s7.ad18a4458563 from=translated src=- shape=57a78262 vocab=df8afbc7
-/
theorem norm_iteratedFDeriv_uQuad_ge_three (g : Matrix (Fin 2) (Fin 2) ℂ) {i : ℕ}
    (hi : 3 ≤ i) (z : ℂ) : ‖iteratedFDeriv ℝ i (uQuad g) z‖ = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 3 := ⟨i - 3, by omega⟩
  have hfd2 : fderiv ℝ (fderiv ℝ (uQuad g)) = fun _ => lamQuad g :=
    funext fun w => (hasFDerivAt_fderiv_uQuad g w).fderiv
  have h3 : ‖iteratedFDeriv ℝ (k + 3) (uQuad g) z‖
      = ‖iteratedFDeriv ℝ (k + 2) (fderiv ℝ (uQuad g)) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := k + 2)).symm
  have h4 : ‖iteratedFDeriv ℝ (k + 2) (fderiv ℝ (uQuad g)) z‖
      = ‖iteratedFDeriv ℝ (k + 1) (fderiv ℝ (fderiv ℝ (uQuad g))) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := k + 1)).symm
  rw [h3, h4, hfd2, iteratedFDeriv_const_of_ne (by omega : k + 1 ≠ 0)]
  simp

/--
@isnad1 id=contdiff.0h1v.s5.78e3cac8ef43 from=translated src=- shape=d78a4f35 vocab=79f477e3
-/
theorem contDiff_uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) : ContDiff ℝ ∞ (uQuad g) := by
  have h : uQuad g = fun w =>
      botNormSqC g * ((w.re - (centerC g).re) ^ 2 + (w.im - (centerC g).im) ^ 2)
        + Complex.normSq g.det / botNormSqC g :=
    funext fun w => uQuad_eq_coords w
  rw [h]
  exact (contDiff_const.mul (((Complex.reCLM.contDiff.sub contDiff_const).pow 2).add
    ((Complex.imCLM.contDiff.sub contDiff_const).pow 2))).add contDiff_const

/--
@isnad1 id=contdiff.1h1v.s6.05d9707c870e from=translated src=- shape=8432ec42 vocab=a3bd6afa
-/
theorem contDiff_inv_radC (hg : g.det ≠ 0) : ContDiff ℝ ∞ fun w => (radC g w)⁻¹ :=
  (contDiff_radC hg).inv fun z => (radC_pos hg z).ne'

/--
@isnad1 id=eq.1h1v.s5.58dfe6f82da4 from=translated src=- shape=7b4f5cea vocab=85c136b9
-/
theorem rpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(1:ℝ)/2) = (Real.sqrt x)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx]
  norm_num

/--
@isnad1 id=le.0h2v.s8.3b7ec5f3a06c from=translated src=- shape=6308847f vocab=3a5fa845
-/
theorem norm_iteratedFDeriv_uQuad_one_le (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ 1 (uQuad g) z‖ ≤ 4 * botNormSqC g * (1 + ‖z - centerC g‖) := by
  refine (norm_iteratedFDeriv_uQuad_one g z).trans ?_
  have hA : (0:ℝ) ≤ botNormSqC g := by
    unfold botNormSqC
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (z - centerC g)]) (by linarith)

def floorK (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  min (botNormSqC g) (Complex.normSq g.det / botNormSqC g) / 18

/--
@isnad1 id=lt.1h1v.s5.a0c043c129ed from=translated src=- shape=21445356 vocab=da37055f
-/
theorem floorK_pos (hg : g.det ≠ 0) : 0 < floorK g := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hM : (0:ℝ) < Complex.normSq g.det / botNormSqC g :=
    div_pos (Complex.normSq_pos.2 hg) hA
  exact div_pos (lt_min hA hM) (by norm_num)

/--
@isnad1 id=lt.2h3v.s7.060e9210f9f3 from=translated src=- shape=f40ca5dc vocab=c5cac7e1
-/
theorem floorK_mul_lt_uQuad (hg : g.det ≠ 0) (z : ℂ) {v : ℂ} (hv : v ∈ Metric.ball z 1) :
    floorK g * (1 + ‖z - centerC g‖) ^ 2 < uQuad g v := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hM : (0:ℝ) < Complex.normSq g.det / botNormSqC g :=
    div_pos (Complex.normSq_pos.2 hg) hA
  have hmin : (0:ℝ) < min (botNormSqC g) (Complex.normSq g.det / botNormSqC g) := lt_min hA hM
  have hminA : min (botNormSqC g) (Complex.normSq g.det / botNormSqC g) ≤ botNormSqC g :=
    min_le_left _ _
  have hminM : min (botNormSqC g) (Complex.normSq g.det / botNormSqC g)
      ≤ Complex.normSq g.det / botNormSqC g := min_le_right _ _
  have hvz : ‖v - z‖ < 1 := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.1 hv
  have hnv : Complex.normSq (v - centerC g) = ‖v - centerC g‖ ^ 2 := by
    rw [Complex.sq_norm]
  have huv : uQuad g v
      = botNormSqC g * ‖v - centerC g‖ ^ 2 + Complex.normSq g.det / botNormSqC g := by
    unfold uQuad
    rw [hnv]
  have hd0 : (0:ℝ) ≤ ‖z - centerC g‖ := norm_nonneg _
  have hvc0 : (0:ℝ) ≤ ‖v - centerC g‖ := norm_nonneg _
  unfold floorK
  rcases le_total (‖z - centerC g‖) 2 with hcase | hcase
  · have h1 : (1 + ‖z - centerC g‖) ^ 2 ≤ 9 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1
      (le_of_lt (div_pos hmin (by norm_num : (0:ℝ) < 18)))
    have h4 : (0:ℝ) ≤ botNormSqC g * ‖v - centerC g‖ ^ 2 :=
      mul_nonneg hA.le (sq_nonneg _)
    rw [huv]
    linarith
  · have hvc : ‖z - centerC g‖ - 1 < ‖v - centerC g‖ := by
      have htri : ‖z - centerC g‖ ≤ ‖z - v‖ + ‖v - centerC g‖ := by
        calc ‖z - centerC g‖ = ‖z - v + (v - centerC g)‖ := by
              rw [show z - v + (v - centerC g) = z - centerC g from by ring]
          _ ≤ ‖z - v‖ + ‖v - centerC g‖ := norm_add_le _ _
      have hzv : ‖z - v‖ < 1 := by rwa [norm_sub_rev]
      linarith
    have hd1 : (0:ℝ) ≤ ‖z - centerC g‖ - 1 := by linarith
    have h1 : 1 + ‖z - centerC g‖ ≤ 3 * (‖z - centerC g‖ - 1) := by linarith
    have h2 : (1 + ‖z - centerC g‖) ^ 2 ≤ 9 * (‖z - centerC g‖ - 1) ^ 2 := by nlinarith
    have h4 : (‖z - centerC g‖ - 1) ^ 2 < ‖v - centerC g‖ ^ 2 := by nlinarith
    have h5 := mul_lt_mul_of_pos_left h4 hA
    rw [huv]
    nlinarith [sq_nonneg (‖z - centerC g‖ - 1), hmin.le, hM.le]

def conjCLM : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap

/--
@isnad1 id=eq.0h1v.s7.e22db90f8097 from=translated src=- shape=41c5cfe3 vocab=019b4d06
-/
@[scoped simp] theorem conjCLM_apply (w : ℂ) : conjCLM w = (starRingEnd ℂ) w := rfl

end M4aP3C.CplxSmooth
open scoped _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxIwasawa _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxSmooth
open scoped _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxIwasawa

end
open scoped _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxIwasawa _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxSmooth

noncomputable section

namespace KCUnif

open M4aP3C.CplxIwasawa M4aP3C.CplxSmooth
open scoped ContDiff Nat ComplexConjugate

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

/--
@isnad1 id=le.1h3v.s8.f0cd23868bdd from=translated src=- shape=2d83b278 vocab=30f34c2f
-/
theorem decay_explicit (hg : g.det ≠ 0) (n : ℕ) (z : ℂ) :
      ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖
        ≤ ((n ! : ℝ) * n ! * (4 * botNormSqC g / floorK g + 1) ^ n * (Real.sqrt (floorK g))⁻¹) / (1 + ‖z - centerC g‖) ^ (n + 1) := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hK : (0:ℝ) < floorK g := floorK_pos hg
  have hM0 : (0:ℝ) < Complex.normSq g.det / botNormSqC g :=
    div_pos (Complex.normSq_pos.2 hg) hA
  have hupos : ∀ w : ℂ, (0:ℝ) < uQuad g w := fun w => lt_of_lt_of_le hM0 (uQuad_ge hg w)
  have hfac : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hc2 : (0:ℝ) < 4 * botNormSqC g / floorK g + 1 := by
    have h0 : (0:ℝ) ≤ 4 * botNormSqC g / floorK g := div_nonneg (by linarith) hK.le
    linarith
  have hsK : (0:ℝ) < (Real.sqrt (floorK g))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hK)
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  have hW0 : (0:ℝ) < 1 + ‖z - centerC g‖ := by linarith
  have hcz : (0:ℝ) < floorK g * (1 + ‖z - centerC g‖) ^ 2 := mul_pos hK (pow_pos hW0 2)
  have hball : z ∈ Metric.ball z 1 := Metric.mem_ball_self one_pos
  have hmaps : Set.MapsTo (fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2))
      (Metric.ball z 1) (Set.Ioi (1:ℝ)) := fun v hv =>
    Set.mem_Ioi.2 ((one_lt_div hcz).2 (floorK_mul_lt_uQuad hg z hv))
  have hrw : (fun w => (radC g w)⁻¹)
      = fun w => (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
          • ((fun y : ℝ => y ^ (-(1 : ℝ) / 2)) ∘
             fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) w := by
    funext w
    have hu := hupos w
    have h1 : radC g w = Real.sqrt (uQuad g w) := by
      rw [uQuad_eq_radC_sq hg w, Real.sqrt_sq (radC_pos hg w).le]
    have hL : (Real.sqrt (uQuad g w))⁻¹ = uQuad g w ^ (-(1:ℝ)/2) :=
      (rpow_neg_half_eq_inv_sqrt hu.le).symm
    have hne : (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2) ≠ 0 :=
      (Real.rpow_pos_of_pos hcz _).ne'
    have hR : (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
        * (uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) ^ (-(1:ℝ)/2)
        = uQuad g w ^ (-(1:ℝ)/2) := by
      rw [show uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)
          = uQuad g w * (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ from div_eq_mul_inv _ _,
        Real.mul_rpow hu.le (inv_nonneg.2 hcz.le), Real.inv_rpow hcz.le,
        mul_comm (uQuad g w ^ (-(1:ℝ)/2)), ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [h1, hL, smul_eq_mul, Function.comp_apply, hR]
  rw [hrw]
  have hũ : ContDiff ℝ ∞ fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2) :=
    (contDiff_uQuad g).div_const _
  have hũz : (1:ℝ) < uQuad g z / (floorK g * (1 + ‖z - centerC g‖) ^ 2) :=
    (one_lt_div hcz).2 (floorK_mul_lt_uQuad hg z hball)
  have hcomp_cd : ContDiffAt ℝ ∞ ((fun y : ℝ => y ^ (-(1 : ℝ) / 2)) ∘
      fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) z :=
    (Real.contDiffAt_rpow_const_of_ne (by linarith : uQuad g z
      / (floorK g * (1 + ‖z - centerC g‖) ^ 2) ≠ 0)).comp z hũ.contDiffAt
  rw [iteratedFDeriv_const_smul_apply' (hcomp_cd.of_le (mod_cast le_top))]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hcz _)]
  have hgOn : ContDiffOn ℝ ∞ (fun y : ℝ => y ^ (-(1 : ℝ) / 2)) (Set.Ioi (1:ℝ)) :=
    fun y hy => (Real.contDiffAt_rpow_const_of_ne
      (ne_of_gt (lt_trans one_pos (Set.mem_Ioi.1 hy)))).contDiffWithinAt
  have hC : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun y : ℝ => y ^ (-(1 : ℝ) / 2)) (Set.Ioi (1:ℝ))
        ((fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) z)‖ ≤ (n ! : ℝ) := by
    intro i hi
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    calc ‖iteratedDerivWithin i (fun y : ℝ => y ^ (-(1 : ℝ) / 2)) (Set.Ioi 1)
          ((fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) z)‖
        ≤ i ! * (1:ℝ) ^ (-(1 : ℝ) / 2 - i) :=
          norm_iteratedDerivWithin_rpow_neg_half_le one_pos i (hmaps hball)
      _ = (i ! : ℝ) := by rw [Real.one_rpow, mul_one]
      _ ≤ (n ! : ℝ) := by exact_mod_cast Nat.factorial_le hi
  have hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i
          (fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) (Metric.ball z 1) z‖
        ≤ ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ i := by
    intro i hi1 hin
    rw [iteratedFDerivWithin_of_isOpen i Metric.isOpen_ball hball]
    have hsm : (fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2))
        = fun w => (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ • uQuad g w := by
      funext w
      rw [smul_eq_mul, div_eq_inv_mul]
    rw [hsm, iteratedFDeriv_const_smul_apply'
      ((contDiff_uQuad g).contDiffAt.of_le (mod_cast le_top))]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcz)]
    rcases Nat.lt_or_ge i 3 with h3 | h3
    · interval_cases i
      · have hb := norm_iteratedFDeriv_uQuad_one_le g z
        have heq : (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹
            * (4 * botNormSqC g * (1 + ‖z - centerC g‖))
            = 4 * botNormSqC g / floorK g * (1 + ‖z - centerC g‖)⁻¹ := by
          field_simp
        calc (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 1 (uQuad g) z‖
            ≤ (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹
              * (4 * botNormSqC g * (1 + ‖z - centerC g‖)) :=
              mul_le_mul_of_nonneg_left hb (inv_pos.2 hcz).le
          _ = 4 * botNormSqC g / floorK g * (1 + ‖z - centerC g‖)⁻¹ := heq
          _ ≤ (4 * botNormSqC g / floorK g + 1) * (1 + ‖z - centerC g‖)⁻¹ :=
              mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hW0.le)
          _ = ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ 1 := by
              rw [pow_one, ← div_eq_mul_inv]
      · have hb := norm_iteratedFDeriv_uQuad_two g z
        have heq : (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * (4 * botNormSqC g)
            = 4 * botNormSqC g / floorK g * ((1 + ‖z - centerC g‖)⁻¹) ^ 2 := by
          field_simp
        have hX0 : (0:ℝ) ≤ 4 * botNormSqC g / floorK g := div_nonneg (by linarith) hK.le
        have hX1 : 4 * botNormSqC g / floorK g ≤ (4 * botNormSqC g / floorK g + 1) ^ 2 := by
          nlinarith
        calc (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 2 (uQuad g) z‖
            ≤ (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * (4 * botNormSqC g) :=
              mul_le_mul_of_nonneg_left hb (inv_pos.2 hcz).le
          _ = 4 * botNormSqC g / floorK g * ((1 + ‖z - centerC g‖)⁻¹) ^ 2 := heq
          _ ≤ (4 * botNormSqC g / floorK g + 1) ^ 2 * ((1 + ‖z - centerC g‖)⁻¹) ^ 2 :=
              mul_le_mul_of_nonneg_right hX1 (sq_nonneg _)
          _ = ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ 2 := by
              rw [div_pow, inv_pow, ← div_eq_mul_inv]
    · rw [norm_iteratedFDeriv_uQuad_ge_three g h3 z, mul_zero]
      exact pow_nonneg (div_nonneg hc2.le hW0.le) i
  have hcomp := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) hgOn hũ.contDiffOn
    (mod_cast le_top) isOpen_Ioi.uniqueDiffOn Metric.isOpen_ball.uniqueDiffOn
    hmaps hball hC hD
  rw [← iteratedFDerivWithin_of_isOpen n Metric.isOpen_ball hball]
  have hczhalf : (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
      = (Real.sqrt (floorK g))⁻¹ * (1 + ‖z - centerC g‖)⁻¹ := by
    have h1 : floorK g * (1 + ‖z - centerC g‖) ^ 2
        = (Real.sqrt (floorK g) * (1 + ‖z - centerC g‖)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK.le]
    have hb0 : (0:ℝ) ≤ Real.sqrt (floorK g) * (1 + ‖z - centerC g‖) :=
      mul_nonneg (Real.sqrt_nonneg _) hW0.le
    rw [h1, rpow_neg_half_eq_inv_sqrt (sq_nonneg _), Real.sqrt_sq hb0, mul_inv]
  calc (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
        * ‖iteratedFDerivWithin ℝ n ((fun y : ℝ => y ^ (-(1 : ℝ) / 2)) ∘
            fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) (Metric.ball z 1) z‖
      ≤ (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
        * ((n ! : ℝ) * n !
          * ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ n) :=
        mul_le_mul_of_nonneg_left hcomp (Real.rpow_pos_of_pos hcz _).le
    _ = (n ! : ℝ) * n ! * (4 * botNormSqC g / floorK g + 1) ^ n * (Real.sqrt (floorK g))⁻¹
        / (1 + ‖z - centerC g‖) ^ (n + 1) := by
        rw [hczhalf, div_pow, pow_succ]
        have hsne : Real.sqrt (floorK g) ≠ 0 := (Real.sqrt_pos.2 hK).ne'
        field_simp

/--
@isnad1 id=le.5h7v.s10.d2d73e03c206 from=translated src=- shape=abeec2e3 vocab=919caa95
-/
theorem affine_of_bounds (hg : g.det ≠ 0)
    (c₀ : ℂ) (L : ℂ →L[ℝ] ℂ) (n : ℕ) {C0 C1 : ℝ} (hC0 : 0 < C0) (hC1 : 0 < C1)
    (hB0 : ∀ z : ℂ, ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖ ≤ C0 / (1 + ‖z - centerC g‖) ^ (n + 1))
    (hB1 : ∀ z : ℂ, ‖iteratedFDeriv ℝ (n - 1) (fun w => (radC g w)⁻¹) z‖ ≤ C1 / (1 + ‖z - centerC g‖) ^ (n - 1 + 1))
    (z : ℂ) :
      ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹ • (c₀ + L w)) z‖ ≤ 2 ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) + 1 := by
  have hcq0 : (0:ℝ) ≤ ‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖ := by positivity
  have hLC1 : (0:ℝ) ≤ ‖L‖ * C1 := mul_nonneg (norm_nonneg _) hC1.le
  have hcqC0 : (0:ℝ) ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 := mul_nonneg hcq0 hC0.le
  have h2n : (0:ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  have hW0 : (0:ℝ) < 1 + ‖z - centerC g‖ := by linarith
  have hq : ContDiff ℝ ∞ fun w : ℂ => c₀ + L w := contDiff_const.add L.contDiff
  refine (norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (contDiff_inv_radC hg) hq z
    (mod_cast le_top)).trans ?_
  have hq0 : ‖c₀ + L z‖ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * (1 + ‖z - centerC g‖) := by
    have h1 : ‖c₀ + L z‖ ≤ ‖c₀‖ + ‖L‖ * ‖z‖ := by
      refine (norm_add_le _ _).trans ?_
      gcongr
      exact L.le_opNorm z
    have h2 : ‖z‖ ≤ ‖z - centerC g‖ + ‖centerC g‖ := by
      calc ‖z‖ = ‖z - centerC g + centerC g‖ := by
            rw [show z - centerC g + centerC g = z from by ring]
        _ ≤ ‖z - centerC g‖ + ‖centerC g‖ := norm_add_le _ _
    have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg L)
    nlinarith [mul_nonneg (norm_nonneg c₀) (norm_nonneg (z - centerC g)),
      mul_nonneg (mul_nonneg (norm_nonneg L) (norm_nonneg (centerC g)))
        (norm_nonneg (z - centerC g)),
      mul_nonneg (norm_nonneg L) (norm_nonneg (z - centerC g))]
  have hfd : (fderiv ℝ fun w : ℂ => c₀ + L w) = fun _ => L :=
    funext fun w => ((L.hasFDerivAt (x := w)).const_add c₀).fderiv
  have hq1 : ‖iteratedFDeriv ℝ 1 (fun w : ℂ => c₀ + L w) z‖ ≤ ‖L‖ := by
    have h1 : ‖iteratedFDeriv ℝ 1 (fun w : ℂ => c₀ + L w) z‖
        = ‖iteratedFDeriv ℝ 0 (fderiv ℝ fun w : ℂ => c₀ + L w) z‖ :=
      (norm_iteratedFDeriv_fderiv (n := 0)).symm
    rw [h1, norm_iteratedFDeriv_zero, hfd]
  have hq2 : ∀ k : ℕ, ‖iteratedFDeriv ℝ (k + 2) (fun w : ℂ => c₀ + L w) z‖ = 0 := by
    intro k
    have h1 : ‖iteratedFDeriv ℝ (k + 2) (fun w : ℂ => c₀ + L w) z‖
        = ‖iteratedFDeriv ℝ (k + 1) (fderiv ℝ fun w : ℂ => c₀ + L w) z‖ :=
      (norm_iteratedFDeriv_fderiv (n := k + 1)).symm
    rw [h1, hfd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
    simp
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w => (radC g w)⁻¹) z‖
          * ‖iteratedFDeriv ℝ (n - i) (fun w : ℂ => c₀ + L w) z‖
        ≤ (n.choose i : ℝ) * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hbin : (0:ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hbin
    rcases Nat.lt_or_ge (n - i) 2 with h2 | h2
    · have hcase : n - i = 0 ∨ n - i = 1 := by omega
      rcases hcase with h0 | h1
      · have hieq : i = n := by omega
        rw [hieq, Nat.sub_self, norm_iteratedFDeriv_zero]
        calc ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖ * ‖c₀ + L z‖
            ≤ (C0 / (1 + ‖z - centerC g‖) ^ (n + 1))
              * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * (1 + ‖z - centerC g‖)) :=
              mul_le_mul (hB0 z) hq0 (norm_nonneg _)
                (div_nonneg hC0.le (pow_nonneg hW0.le _))
          _ = (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 / (1 + ‖z - centerC g‖) ^ n := by
              rw [pow_succ]
              field_simp
          _ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 :=
              div_le_self hcqC0 (one_le_pow₀ hW1)
          _ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1 := by linarith
      · have hieq : i = n - 1 := by omega
        have hn1 : 1 ≤ n := by omega
        rw [hieq, show n - (n - 1) = 1 from by omega]
        calc ‖iteratedFDeriv ℝ (n - 1) (fun w => (radC g w)⁻¹) z‖
              * ‖iteratedFDeriv ℝ 1 (fun w : ℂ => c₀ + L w) z‖
            ≤ (C1 / (1 + ‖z - centerC g‖) ^ (n - 1 + 1)) * ‖L‖ :=
              mul_le_mul (hB1 z) hq1 (norm_nonneg _)
                (div_nonneg hC1.le (pow_nonneg hW0.le _))
          _ ≤ C1 * ‖L‖ :=
              mul_le_mul_of_nonneg_right
                (div_le_self hC1.le (one_le_pow₀ hW1)) (norm_nonneg _)
          _ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1 := by
              nlinarith
    · obtain ⟨k, hk⟩ : ∃ k, n - i = k + 2 := ⟨n - i - 2, by omega⟩
      rw [hk, hq2 k, mul_zero]
      nlinarith
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
        * ‖iteratedFDeriv ℝ i (fun w => (radC g w)⁻¹) z‖
        * ‖iteratedFDeriv ℝ (n - i) (fun w : ℂ => c₀ + L w) z‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) := Finset.sum_le_sum hterm
    _ = (2:ℝ) ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
    _ ≤ 2 ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) + 1 := by linarith

end KCUnif
open scoped _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxIwasawa _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxSmooth

end
open scoped _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxIwasawa _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxSmooth

noncomputable section

namespace KCUnif

open M4aP3C.CplxIwasawa M4aP3C.CplxSmooth
open scoped ContDiff Nat ComplexConjugate

/--
@isnad1 id=continuo.0h0v.s6.bb07d1a14923 from=translated src=- shape=9907cdae vocab=e49835f5
-/
theorem continuous_botNormSqC : Continuous fun g : Matrix (Fin 2) (Fin 2) ℂ => botNormSqC g := by
  unfold botNormSqC
  exact (Complex.continuous_normSq.comp (continuous_id.matrix_elem 1 0)).add
    (Complex.continuous_normSq.comp (continuous_id.matrix_elem 1 1))

/--
@isnad1 id=continuo.0h0v.s6.b2af40c02acc from=translated src=- shape=62ec8e45 vocab=a134058e
-/
theorem continuous_detC : Continuous fun g : Matrix (Fin 2) (Fin 2) ℂ => g.det := by
  have : (fun g : Matrix (Fin 2) (Fin 2) ℂ => g.det) = fun g => g 0 0 * g 1 1 - g 0 1 * g 1 0 :=
    funext fun g => Matrix.det_fin_two g
  rw [this]; fun_prop

/--
@isnad1 id=continuo.0h0v.s8.3bab3f7977f3 from=translated src=- shape=b63e0636 vocab=c451b8a2
-/
theorem continuous_centerC_num : Continuous fun g : Matrix (Fin 2) (Fin 2) ℂ => -(conj (g 1 0) * g 0 0 + conj (g 1 1) * g 0 1) := by
  fun_prop

def Kdec (g : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) : ℝ :=
  (n ! : ℝ) * n ! * (4 * botNormSqC g / floorK g + 1) ^ n * (Real.sqrt (floorK g))⁻¹

def KdecU (A₁ f₀ : ℝ) (n : ℕ) : ℝ := (n ! : ℝ) * n ! * (4 * A₁ / f₀ + 1) ^ n * (Real.sqrt f₀)⁻¹

/--
@isnad1 id=lt.2h3v.s5.2fee6d62ee6f from=translated src=- shape=7904d8a2 vocab=a4417fec
-/
theorem KdecU_pos {A₁ f₀ : ℝ} (hA : 0 ≤ A₁) (hf : 0 < f₀) (n : ℕ) : 0 < KdecU A₁ f₀ n := by
  unfold KdecU
  have h1 : (0 : ℝ) < n ! := by positivity
  have h2 : 0 < 4 * A₁ / f₀ + 1 := by positivity
  exact mul_pos (mul_pos (mul_pos h1 h1) (pow_pos h2 n)) (inv_pos.2 (Real.sqrt_pos.2 hf))

/--
@isnad1 id=le.4h4v.s6.69a9456d6a9f from=translated src=- shape=faf72287 vocab=e7228270
-/
theorem Kdec_le_KdecU {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) {A₁ f₀ : ℝ} (hf : 0 < f₀)
    (hA : botNormSqC g ≤ A₁) (hfl : f₀ ≤ floorK g) (n : ℕ) : Kdec g n ≤ KdecU A₁ f₀ n := by
  unfold Kdec KdecU
  have hA0 : 0 < botNormSqC g := botNormSqC_pos hg
  have hK : 0 < floorK g := floorK_pos hg
  have h1 : 4 * botNormSqC g / floorK g + 1 ≤ 4 * A₁ / f₀ + 1 := by
    have : botNormSqC g / floorK g ≤ A₁ / f₀ := div_le_div₀ (hA0.le.trans hA) hA hf hfl
    have e1 : 4 * botNormSqC g / floorK g = 4 * (botNormSqC g / floorK g) := by ring
    have e2 : 4 * A₁ / f₀ = 4 * (A₁ / f₀) := by ring
    linarith
  have h2 : (Real.sqrt (floorK g))⁻¹ ≤ (Real.sqrt f₀)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 hf) (Real.sqrt_le_sqrt hfl)
  have h0 : (0 : ℝ) ≤ n ! * n ! := by positivity
  have h3 : (0 : ℝ) ≤ 4 * A₁ / f₀ + 1 := by
    have : 0 ≤ A₁ := hA0.le.trans hA
    positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 n) h0) h2
    (inv_nonneg.2 (Real.sqrt_nonneg _)) (mul_nonneg h0 (pow_nonneg h3 n))

/--
@isnad1 id=ex.2h1v.s8.833be19c5064 from=translated src=- shape=83251143 vocab=bebd7e51
-/
theorem exists_uniform_constants (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0) :
    ∃ A₁ f₀ Zc E : ℝ, 0 ≤ A₁ ∧ 0 < f₀ ∧ 0 ≤ Zc ∧ 0 ≤ E ∧ ∀ g ∈ 𝒢,
      botNormSqC g ≤ A₁ ∧ f₀ ≤ floorK g ∧ ‖centerC g‖ ≤ Zc ∧ ∀ i j : Fin 2, ‖g i j‖ ≤ E := by
  obtain ⟨A₁, hA₁⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => botNormSqC g) continuous_botNormSqC.continuousOn
  obtain ⟨cA, hcA⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => (botNormSqC g)⁻¹)
    ((continuous_botNormSqC.continuousOn).inv₀ fun g hg => (botNormSqC_pos (hdet g hg)).ne')
  obtain ⟨cD, hcD⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => ‖g.det‖⁻¹)
    (continuous_detC.continuousOn.norm.inv₀ fun g hg => (norm_pos_iff.2 (hdet g hg)).ne')
  obtain ⟨Zc, hZc⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => centerC g)
    (continuous_centerC_num.continuousOn.div (Complex.continuous_ofReal.comp continuous_botNormSqC).continuousOn
      fun g hg => Complex.ofReal_ne_zero.2 (botNormSqC_pos (hdet g hg)).ne')
  have hE : ∀ i j : Fin 2, ∃ Eij : ℝ, ∀ g ∈ 𝒢, ‖g i j‖ ≤ Eij := fun i j =>
    h𝒢.exists_bound_of_continuousOn (f := fun g => g i j) (continuous_id.matrix_elem i j).continuousOn
  choose Ef hEf using hE
  set A := max 1 A₁ with hAdef
  set a := max 1 cA with hadef
  set d := max 1 cD with hddef
  set E := max 0 (max (max (Ef 0 0) (Ef 0 1)) (max (Ef 1 0) (Ef 1 1))) with hEdef
  have hA1 : 1 ≤ A := le_max_left _ _
  have ha1 : 1 ≤ a := le_max_left _ _
  have hd1 : 1 ≤ d := le_max_left _ _
  refine ⟨A, min a⁻¹ ((d ^ 2)⁻¹ * A⁻¹) / 18, max 0 Zc, E, by positivity, by positivity, le_max_left _ _, le_max_left _ _,
    fun g hg => ⟨?_, ?_, ?_, ?_⟩⟩
  · have := hA₁ g hg
    rw [Real.norm_of_nonneg (botNormSqC_pos (hdet g hg)).le] at this
    exact this.trans (le_max_right _ _)
  · have hApos := botNormSqC_pos (hdet g hg)
    have hdet0 : 0 < ‖g.det‖ := norm_pos_iff.2 (hdet g hg)
    have h1 : (botNormSqC g)⁻¹ ≤ a := by
      have := hcA g hg; rw [norm_inv, Real.norm_of_nonneg hApos.le] at this
      exact this.trans (le_max_right _ _)
    have h2 : ‖g.det‖⁻¹ ≤ d := by
      have := hcD g hg; rw [norm_inv, norm_norm] at this
      exact this.trans (le_max_right _ _)
    have hAup : botNormSqC g ≤ A := by
      have := hA₁ g hg; rw [Real.norm_of_nonneg hApos.le] at this
      exact this.trans (le_max_right _ _)

    have hb1 : a⁻¹ ≤ botNormSqC g := by
      rw [inv_le_comm₀ (by positivity) hApos]; exact h1
    have hb2 : (d ^ 2)⁻¹ * A⁻¹ ≤ Complex.normSq g.det / botNormSqC g := by
      rw [Complex.normSq_eq_norm_sq, div_eq_mul_inv]
      refine mul_le_mul ?_ ((inv_le_inv₀ (by positivity) hApos).mpr hAup) (by positivity) (sq_nonneg _)
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) ((inv_le_comm₀ (by positivity) hdet0).mpr h2) 2
    unfold floorK
    exact div_le_div_of_nonneg_right (le_min ((min_le_left _ _).trans hb1) ((min_le_right _ _).trans hb2)) (by norm_num)
  · exact (hZc g hg).trans (le_max_right _ _)
  · intro i j
    refine (hEf i j g hg).trans ?_
    fin_cases i <;> fin_cases j <;> simp [hEdef]

/--
@isnad1 id=ex.2h2v.s8.cd97db77b22c from=translated src=- shape=cc625ebe vocab=db67a8dc
-/
theorem main (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ (i j : Fin 2) (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C := by
  obtain ⟨A₁, f₀, Zc, E, hA₁, hf₀, hZc, hE, hG⟩ := exists_uniform_constants 𝒢 h𝒢 hdet
  set C0 := KdecU A₁ f₀ n with hC0def
  set C1 := KdecU A₁ f₀ (n - 1) with hC1def
  have hC0 : 0 < C0 := KdecU_pos hA₁ hf₀ n
  have hC1 : 0 < C1 := KdecU_pos hA₁ hf₀ (n - 1)
  set U : ℝ := 2 ^ n * ((E + E * Zc + E) * C0 + E * C1) + 1 with hU
  refine ⟨U, by positivity, fun g hg i j z => ?_⟩
  obtain ⟨hA, hfl, hZ, hEg⟩ := hG g hg
  have hgd := hdet g hg

  have hW : ∀ z : ℂ, 0 < 1 + ‖z - centerC g‖ := fun z => by positivity
  have hB0 : ∀ z : ℂ, ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖ ≤ C0 / (1 + ‖z - centerC g‖) ^ (n + 1) := fun z =>
    (decay_explicit hgd n z).trans (div_le_div_of_nonneg_right (Kdec_le_KdecU hgd hf₀ hA hfl n) (by positivity))
  have hB1 : ∀ z : ℂ, ‖iteratedFDeriv ℝ (n - 1) (fun w => (radC g w)⁻¹) z‖ ≤ C1 / (1 + ‖z - centerC g‖) ^ (n - 1 + 1) :=
    fun z => (decay_explicit hgd (n - 1) z).trans
      (div_le_div_of_nonneg_right (Kdec_le_KdecU hgd hf₀ hA hfl (n - 1)) (by positivity))

  have hunif : ∀ (c₀ : ℂ) (L : ℂ →L[ℝ] ℂ), ‖c₀‖ ≤ E → ‖L‖ ≤ E →
      2 ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) + 1 ≤ U := by
    intro c₀ L hc hL
    have h1 : ‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖ ≤ E + E * Zc + E := by
      have := mul_le_mul hL hZ (norm_nonneg _) hE
      linarith
    have h2 : (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1 ≤ (E + E * Zc + E) * C0 + E * C1 :=
      add_le_add (mul_le_mul_of_nonneg_right h1 hC0.le) (mul_le_mul_of_nonneg_right hL hC1.le)
    have h3 := mul_le_mul_of_nonneg_left h2 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n)
    simp only [hU]; linarith
  have hconj : ∀ x : ℂ, ‖(starRingEnd ℂ) x‖ = ‖x‖ := fun x => Complex.norm_conj x
  have hconjCLM : ‖(conjCLM : ℂ →L[ℝ] ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      rw [conjCLM_apply, one_mul]; exact (hconj w).le
  have hidCLM : ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hLconj : ∀ x : ℂ, ‖x • (conjCLM : ℂ →L[ℝ] ℂ)‖ ≤ ‖x‖ := fun x =>
    (norm_smul_le x (conjCLM : ℂ →L[ℝ] ℂ)).trans (by nlinarith [norm_nonneg x, norm_nonneg (conjCLM : ℂ →L[ℝ] ℂ)])
  have hLid : ∀ x : ℂ, ‖x • ContinuousLinearMap.id ℝ ℂ‖ ≤ ‖x‖ := fun x =>
    (norm_smul_le x (ContinuousLinearMap.id ℝ ℂ)).trans
      (by nlinarith [norm_nonneg x, norm_nonneg (ContinuousLinearMap.id ℝ ℂ)])
  fin_cases i <;> fin_cases j
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 0 0) z‖ ≤ _
    have heq : (fun w => kC g w 0 0)
        = fun w => (radC g w)⁻¹ • ((starRingEnd ℂ) (g 0 1) + ((starRingEnd ℂ) (g 1 1) • conjCLM) w) := by
      funext w
      show (starRingEnd ℂ) (botQ g w) / ((radC g w : ℝ) : ℂ) = _
      simp only [botQ, map_add, map_mul, smul_apply, conjCLM_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    refine (affine_of_bounds hgd _ _ n hC0 hC1 hB0 hB1 z).trans (hunif _ _ ?_ ?_)
    · rw [hconj]; exact hEg 0 1
    · exact (hLconj _).trans (by rw [hconj]; exact hEg 1 1)
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 0 1) z‖ ≤ _
    have heq : (fun w => kC g w 0 1)
        = fun w => (radC g w)⁻¹ • (-(starRingEnd ℂ) (g 0 0) + ((-(starRingEnd ℂ) (g 1 0)) • conjCLM) w) := by
      funext w
      show -(starRingEnd ℂ) (botP g w) / ((radC g w : ℝ) : ℂ) = _
      simp only [botP, map_add, map_mul, smul_apply, conjCLM_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    refine (affine_of_bounds hgd _ _ n hC0 hC1 hB0 hB1 z).trans (hunif _ _ ?_ ?_)
    · rw [norm_neg, hconj]; exact hEg 0 0
    · exact (hLconj _).trans (by rw [norm_neg, hconj]; exact hEg 1 0)
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 1 0) z‖ ≤ _
    have heq : (fun w => kC g w 1 0)
        = fun w => (radC g w)⁻¹ • (g 0 0 + (g 1 0 • ContinuousLinearMap.id ℝ ℂ) w) := by
      funext w
      show botP g w / ((radC g w : ℝ) : ℂ) = _
      simp only [botP, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    refine (affine_of_bounds hgd _ _ n hC0 hC1 hB0 hB1 z).trans (hunif _ _ (hEg 0 0) ((hLid _).trans (hEg 1 0)))
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 1 1) z‖ ≤ _
    have heq : (fun w => kC g w 1 1)
        = fun w => (radC g w)⁻¹ • (g 0 1 + (g 1 1 • ContinuousLinearMap.id ℝ ℂ) w) := by
      funext w
      show botQ g w / ((radC g w : ℝ) : ℂ) = _
      simp only [botQ, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    refine (affine_of_bounds hgd _ _ n hC0 hC1 hB0 hB1 z).trans (hunif _ _ (hEg 0 1) ((hLid _).trans (hEg 1 1)))

end KCUnif
open scoped _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxIwasawa _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxSmooth

end
open scoped _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxIwasawa _root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.M4aP3C.CplxSmooth

open AutomorphicForm.ComplexIwasawa in
open scoped ContDiff in
/--
@isnad1 id=ex.2h2v.s8.c1406a222f70 from=translated src=- shape=cc625ebe vocab=9a9104c7
-/
theorem solution
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ (i j : Fin 2) (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C :=
  KCUnif.main 𝒢 h𝒢 hdet n
