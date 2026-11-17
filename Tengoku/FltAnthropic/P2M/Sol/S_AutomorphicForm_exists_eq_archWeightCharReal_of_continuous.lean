import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchWeightChar
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_exists_eq_archWeightCharReal_of_continuous.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_exists_eq_archWeightCharReal_of_continuous

set_option autoImplicit false

open AutomorphicForm Real Complex MeasureTheory intervalIntegral

noncomputable section

namespace CircleCharChi

def rotM (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

/--
@isnad1 id=eq.0h2v.s6.5a12d1db5ac2 from=translated src=- shape=3b625e93 vocab=f6e2f4f4
-/
theorem rotM_mul (θ η : ℝ) : rotM θ * rotM η = rotM (θ + η) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotM, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

/--
@isnad1 id=eq.0h0v.s6.c1a0cbed369f from=translated src=- shape=4a8cf6c6 vocab=ebac6d51
-/
theorem rotM_zero : rotM 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotM]

/--
@isnad1 id=eq.0h1v.s7.a62c46df07bc from=translated src=- shape=63d35e59 vocab=0ce63ee5
-/
theorem rotM_neg_mul (θ : ℝ) : rotM (-θ) * rotM θ = 1 := by rw [rotM_mul, neg_add_cancel, rotM_zero]
/--
@isnad1 id=eq.0h1v.s7.9f3ab3addb28 from=translated src=- shape=b59b86e9 vocab=0ce63ee5
-/
theorem rotM_mul_neg (θ : ℝ) : rotM θ * rotM (-θ) = 1 := by rw [rotM_mul, add_neg_cancel, rotM_zero]

def rotGL (θ : ℝ) : GL (Fin 2) ℝ := ⟨rotM θ, rotM (-θ), rotM_mul_neg θ, rotM_neg_mul θ⟩

/--
@isnad1 id=eq.0h1v.s6.20263b6533d9 from=translated src=- shape=cfe8a7d9 vocab=af5dcd36
-/
@[scoped simp] theorem rotGL_coe (θ : ℝ) : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM θ := rfl

/--
@isnad1 id=mem.0h1v.s8.ff9d2e397eb6 from=translated src=- shape=348377b1 vocab=dadc19e0
-/
theorem rotGL_mem (θ : ℝ) : rotGL θ ∈ rowIsometrySubgroup₀ ℝ := by
  refine (mem_rowIsometrySubgroup₀_iff ℝ).mpr ⟨?_, ?_, ?_⟩
  · rw [rotGL_coe, rotM, Matrix.det_fin_two_of]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  · rw [rotGL_coe, rotM, Matrix.det_fin_two_of]
    have : Real.cos θ * Real.cos θ - Real.sin θ * -Real.sin θ = 1 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [this]; simp
  · intro x y
    rw [rotGL_coe]
    simp only [rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq θ]

def rot (θ : ℝ) : rowIsometrySubgroup₀ ℝ := ⟨rotGL θ, rotGL_mem θ⟩

/--
@isnad1 id=eq.0h2v.s11.d7ec4bccae3a from=translated src=- shape=0eb29773 vocab=fcf409a6
-/
theorem rot_add (θ η : ℝ) : rot (θ + η) = rot θ * rot η := by
  apply Subtype.ext
  apply Units.ext
  show rotM (θ + η) = rotM θ * rotM η
  rw [rotM_mul]

/--
@isnad1 id=eq.0h0v.s10.1413894a9c8b from=translated src=- shape=ac11af2a vocab=91efac8d
-/
theorem rot_zero : rot 0 = 1 := by
  apply Subtype.ext; apply Units.ext
  show rotM 0 = 1
  exact rotM_zero

/--
@isnad1 id=continuo.0h0v.s5.2153750064b9 from=translated src=- shape=8a8db92f vocab=d7e2ba89
-/
theorem continuous_rotM : Continuous rotM := by
  unfold rotM
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/--
@isnad1 id=continuo.0h0v.s6.62629ce87480 from=translated src=- shape=8c4e1e81 vocab=ab65f0e7
-/
theorem continuous_rotGL : Continuous rotGL := by
  rw [Units.continuous_iff]
  constructor
  · exact continuous_rotM
  · show Continuous fun θ => rotM (-θ)
    exact continuous_rotM.comp continuous_neg

/--
@isnad1 id=continuo.0h0v.s9.94d55ada5861 from=translated src=- shape=9d909ccb vocab=1803b040
-/
theorem continuous_rot : Continuous rot :=
  continuous_rotGL.subtype_mk _

/--
@isnad1 id=eq.0h1v.s12.4658a4864ced from=translated src=- shape=fb1de579 vocab=ef01e514
-/
theorem archWeightOne_rot (θ : ℝ) : ((archWeightOneℝ (rot θ) : ℂˣ) : ℂ) = Complex.exp (θ * Complex.I) := by
  rw [Complex.exp_mul_I]
  show firstRowℂ (rotGL θ) = _
  apply Complex.ext
  · simp [firstRowℂ, rotGL_coe, rotM, Complex.cos_ofReal_re]
  · simp [firstRowℂ, rotGL_coe, rotM, Complex.sin_ofReal_re]

/--
@isnad1 id=ex.0h1v.s9.4c78695314c1 from=translated src=- shape=e62f6e3c vocab=91efac8d
-/
theorem exists_rot_eq (k : rowIsometrySubgroup₀ ℝ) : ∃ θ : ℝ, rot θ = k := by
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ k.2
  set a := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb

  set z : ℂ := ⟨a, b⟩ with hz
  have hnorm : ‖z‖ = 1 := by
    have : Complex.normSq z = 1 := by rw [hz, Complex.normSq_mk]; nlinarith
    rw [Complex.norm_def, this, Real.sqrt_one]
  have hexp : Complex.exp (Complex.arg z * Complex.I) = z := by
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hnorm, Complex.ofReal_one, one_mul] at this
    exact this
  refine ⟨Complex.arg z, ?_⟩
  apply Subtype.ext; apply Units.ext
  have hc : Real.cos (Complex.arg z) = a := by
    have := congrArg Complex.re hexp
    rw [Complex.exp_mul_I] at this
    simpa [Complex.cos_ofReal_re, Complex.sin_ofReal_im] using this
  have hs : Real.sin (Complex.arg z) = b := by
    have := congrArg Complex.im hexp
    rw [Complex.exp_mul_I] at this
    simpa [Complex.cos_ofReal_im, Complex.sin_ofReal_re] using this
  show rotM (Complex.arg z) = ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [rotM] using hc
  · simpa [rotM] using hs
  · simp [rotM, hs, h10]
  · simp [rotM, hc, h11]

/--
@isnad1 id=ex.3h1v.s6.105cba935a5a from=translated src=- shape=39e734e5 vocab=effaf7ac
-/
theorem exists_exp_of_continuous_mul (f : ℝ → ℂ) (hf : Continuous f) (h0 : f 0 = 1)
    (hmul : ∀ s t : ℝ, f (s + t) = f s * f t) : ∃ a : ℂ, ∀ s : ℝ, f s = Complex.exp (a * s) := by

  obtain ⟨δ, hδ, hδb⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ δ → ‖f t - 1‖ ≤ 1 / 2 := by
    have hc : ContinuousAt f 0 := hf.continuousAt
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨ε, hε, hεb⟩ := hc (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun t ht => ?_⟩
    have : dist t 0 < ε := by rw [dist_zero_right, Real.norm_eq_abs]; linarith
    have h := hεb this
    rw [h0, dist_eq_norm] at h
    exact h.le
  set c : ℂ := ∫ t in (0 : ℝ)..δ, f t with hc
  have hci : IntervalIntegrable f volume 0 δ := hf.intervalIntegrable 0 δ
  have hc0 : c ≠ 0 := by
    have hbound : ‖c - δ‖ ≤ 1 / 2 * |δ - 0| := by
      have : c - δ = ∫ t in (0 : ℝ)..δ, (f t - 1) := by
        rw [hc, intervalIntegral.integral_sub hci (intervalIntegrable_const), intervalIntegral.integral_const]
        simp
      rw [this]
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
      rw [Set.uIoc_of_le hδ.le] at ht
      exact hδb t (by rw [abs_of_pos ht.1]; exact ht.2)
    intro h
    rw [h, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ, sub_zero, abs_of_pos hδ] at hbound
    linarith

  have hG : ∀ s : ℝ, ∫ t in s..s + δ, f t = f s * c := by
    intro s
    rw [hc, ← intervalIntegral.integral_const_mul]
    have : (∫ t in s..s + δ, f t) = ∫ t in (0 : ℝ)..δ, f (s + t) := by
      rw [intervalIntegral.integral_comp_add_left f s, add_zero]
    rw [this]
    refine intervalIntegral.integral_congr fun t _ => ?_
    exact hmul s t

  set P : ℝ → ℂ := fun u => ∫ t in (0 : ℝ)..u, f t with hP
  have hPd : ∀ u : ℝ, HasDerivAt P (f u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 u) (hf.stronglyMeasurableAtFilter _ _)
      hf.continuousAt
  have hfP : ∀ s : ℝ, f s = (P (s + δ) - P s) / c := by
    intro s
    rw [eq_div_iff hc0, ← hG s, hP]
    simp only
    rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable 0 (s + δ)) (hf.intervalIntegrable 0 s)]

  set a : ℂ := (f δ - 1) / c with ha
  have hfd : ∀ s : ℝ, HasDerivAt f (a * f s) s := by
    intro s
    have h1 : HasDerivAt (fun s => (P (s + δ) - P s) / c) ((f (s + δ) - f s) / c) s := by
      have hsh : HasDerivAt (fun s => P (s + δ)) (f (s + δ)) s := (hPd (s + δ)).comp_add_const s δ
      exact (hsh.sub (hPd s)).div_const c
    have hfun : (fun s => (P (s + δ) - P s) / c) = f := funext fun s => (hfP s).symm
    rw [hfun] at h1
    convert h1 using 1
    rw [hmul s δ, ha]
    field_simp

  set g : ℝ → ℂ := fun s => f s * Complex.exp (-(a * s)) with hg
  have hgd : ∀ s : ℝ, HasDerivAt g 0 s := by
    intro s
    have he : HasDerivAt (fun s : ℝ => Complex.exp (-(a * s))) (Complex.exp (-(a * s)) * (-a)) s := by
      have h1 : HasDerivAt (fun s : ℝ => -(a * (s : ℂ))) (-a) s := by
        have := ((hasDerivAt_id (s : ℂ)).const_mul a).neg.comp_ofReal
        simpa using this
      exact h1.cexp
    have := (hfd s).mul he
    convert this using 1
    · rfl
    · rfl
    ring
  have hgc : ∀ s, g s = g 0 := by
    have hdiff : Differentiable ℝ g := fun s => (hgd s).differentiableAt
    have hder : ∀ s, deriv g s = 0 := fun s => (hgd s).deriv
    intro s
    exact is_const_of_deriv_eq_zero hdiff hder s 0
  refine ⟨a, fun s => ?_⟩
  have h1 := hgc s
  simp only [hg, h0, mul_zero, neg_zero, Complex.exp_zero, one_mul, Complex.ofReal_zero] at h1
  have hexp : Complex.exp (-(a * s)) ≠ 0 := Complex.exp_ne_zero _
  calc f s = f s * Complex.exp (-(a * s)) * Complex.exp (a * s) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp (a * s) := by rw [h1, one_mul]

/--
@isnad1 id=ex.1h1v.s13.efe36a7c792a from=translated src=- shape=5782d3ee vocab=fd17e447
-/
theorem main (χ : rowIsometrySubgroup₀ ℝ →* ℂˣ)
    (hχ : Continuous fun k : rowIsometrySubgroup₀ ℝ => ((χ k : ℂˣ) : ℂ)) :
    ∃ m : ℤ, χ = archWeightCharℝ m := by
  set f : ℝ → ℂ := fun θ => ((χ (rot θ) : ℂˣ) : ℂ) with hf
  have hfc : Continuous f := hχ.comp continuous_rot
  have hf0 : f 0 = 1 := by simp [hf, rot_zero]
  have hfmul : ∀ s t : ℝ, f (s + t) = f s * f t := by
    intro s t; simp [hf, rot_add]
  obtain ⟨a, ha⟩ := exists_exp_of_continuous_mul f hfc hf0 hfmul

  have hper : rot (2 * Real.pi) = 1 := by
    apply Subtype.ext; apply Units.ext
    show rotM (2 * Real.pi) = 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotM]
  have h2π : Complex.exp (a * (2 * Real.pi : ℝ)) = 1 := by
    rw [← ha]; simp [hf, hper]
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h2π
  have haI : a = m * Complex.I := by
    have hπ : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    have : a * (2 * Real.pi) = (m * Complex.I) * (2 * Real.pi) := by
      push_cast at hm ⊢
      linear_combination hm
    exact mul_right_cancel₀ hπ this
  refine ⟨m, MonoidHom.ext fun k => ?_⟩
  obtain ⟨θ, rfl⟩ := exists_rot_eq k
  apply Units.ext
  show f θ = ((archWeightCharℝ m (rot θ) : ℂˣ) : ℂ)
  rw [ha θ, haI]
  show Complex.exp (m * Complex.I * θ) = (((archWeightOneℝ (rot θ)) ^ m : ℂˣ) : ℂ)
  rw [Units.val_zpow_eq_zpow_val, archWeightOne_rot, ← Complex.exp_int_mul]
  ring_nf

end CircleCharChi
open scoped _root_.P2MW.S_AutomorphicForm_exists_eq_archWeightCharReal_of_continuous.CircleCharChi

end
open scoped _root_.P2MW.S_AutomorphicForm_exists_eq_archWeightCharReal_of_continuous.CircleCharChi

/--
@isnad1 id=ex.1h1v.s13.efe36a7c792a from=translated src=- shape=5782d3ee vocab=fd17e447
-/
theorem solution
    (χ : rowIsometrySubgroup₀ ℝ →* ℂˣ)
    (hχ : Continuous fun k : rowIsometrySubgroup₀ ℝ => ((χ k : ℂˣ) : ℂ)) :
    ∃ m : ℤ, χ = archWeightCharℝ m :=
  CircleCharChi.main χ hχ
