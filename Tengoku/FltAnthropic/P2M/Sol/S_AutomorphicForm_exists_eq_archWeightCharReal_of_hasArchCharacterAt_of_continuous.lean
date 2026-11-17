import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchWeightCharTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous

set_option autoImplicit false

open scoped Classical
open NumberField AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain

noncomputable section

namespace CircleCharacterClassification

/--
@isnad1 id=ex.3h1v.s6.105cba935a5a from=translated src=- shape=39e734e5 vocab=effaf7ac
-/
theorem exists_eq_exp_of_continuous_mul (f : ℝ → ℂ) (hf : Continuous f) (h0 : f 0 = 1)
    (hmul : ∀ s t : ℝ, f (s + t) = f s * f t) :
    ∃ α : ℂ, ∀ t : ℝ, f t = Complex.exp (α * t) := by
  set Φ : ℝ → ℂ := fun t => ∫ x in (0 : ℝ)..t, f x with hΦ
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (f t) t := fun t =>
    (hf.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b := fun a b =>
    hf.intervalIntegrable a b

  have htrans : ∀ s t : ℝ, Φ (t + s) = Φ t + f t * Φ s := by
    intro s t
    have h1 : Φ (t + s) = (∫ x in (0 : ℝ)..t, f x) + ∫ x in t..t + s, f x :=
      (intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t (t + s))).symm
    have h2 : (∫ x in t..t + s, f x) = ∫ x in (0 : ℝ)..s, f (x + t) := by
      rw [intervalIntegral.integral_comp_add_right f t, zero_add, add_comm s t]
    have h3 : (fun x : ℝ => f (x + t)) = fun x => f t * f x := by
      funext x
      rw [add_comm, hmul]
    rw [h1, h2, h3, intervalIntegral.integral_const_mul]
  by_cases hzero : ∀ s : ℝ, Φ s = 0
  · exfalso
    have hΦ0 : Φ = fun _ => (0 : ℂ) := funext hzero
    have hd := hΦderiv 0
    rw [hΦ0] at hd
    have : f 0 = 0 := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    rw [h0] at this
    exact one_ne_zero this
  · push Not at hzero
    obtain ⟨s, hs⟩ := hzero
    set c : ℂ := (f s - 1) / Φ s with hc
    have hf_eq : ∀ t : ℝ, f t = 1 + c * Φ t := by
      intro t
      have h1 := htrans s t
      have h2 := htrans t s
      rw [add_comm t s] at h1
      have key : f t * Φ s = Φ s + (f s - 1) * Φ t := by
        linear_combination h1.symm.trans h2
      calc f t = f t * Φ s / Φ s := by field_simp
        _ = 1 + c * Φ t := by
          rw [key, hc]
          field_simp
    have hfderiv : ∀ t : ℝ, HasDerivAt f (c * f t) t := by
      intro t
      have h := ((hΦderiv t).const_mul c).const_add 1
      have hfun : (fun x : ℝ => 1 + c * Φ x) = f := (funext hf_eq).symm
      rw [hfun] at h
      exact h
    refine ⟨c, fun t => ?_⟩

    have hexp : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (-(c * y)))
        (Complex.exp (-(c * x)) * (-(c * 1))) x := by
      intro x
      have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(c * z)))
          (Complex.exp (-(c * (x : ℂ))) * (-(c * 1))) (x : ℂ) :=
        ((hasDerivAt_id (x : ℂ)).const_mul c).neg.cexp
      exact h1.comp_ofReal
    have hg : ∀ x y : ℝ, Complex.exp (-(c * x)) * f x = Complex.exp (-(c * y)) * f y := by
      apply is_const_of_deriv_eq_zero
      · intro x
        exact ((hexp x).mul (hfderiv x)).differentiableAt
      · intro x
        change deriv ((fun y : ℝ => Complex.exp (-(c * y))) * f) x = 0
        rw [((hexp x).mul (hfderiv x)).deriv]
        ring
    have h1 := hg t 0
    rw [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul, h0] at h1
    calc f t = Complex.exp (c * t) * (Complex.exp (-(c * t)) * f t) := by
          rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
      _ = Complex.exp (c * t) := by rw [h1, mul_one]

def rotMat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

/--
@isnad1 id=eq.0h1v.s5.4f144bf15c56 from=translated src=- shape=b464c013 vocab=a4cf8922
-/
@[scoped simp] theorem rotMat_apply_00 (θ : ℝ) : rotMat θ 0 0 = Real.cos θ := rfl
/--
@isnad1 id=eq.0h1v.s5.65fe00f2e8ac from=translated src=- shape=b464c013 vocab=0e6b6191
-/
@[scoped simp] theorem rotMat_apply_01 (θ : ℝ) : rotMat θ 0 1 = Real.sin θ := rfl
/--
@isnad1 id=eq.0h1v.s5.d50f0b6bad42 from=translated src=- shape=84fb2a41 vocab=eb387028
-/
@[scoped simp] theorem rotMat_apply_10 (θ : ℝ) : rotMat θ 1 0 = -Real.sin θ := rfl
/--
@isnad1 id=eq.0h1v.s5.375a1ca1eb8b from=translated src=- shape=b464c013 vocab=a4cf8922
-/
@[scoped simp] theorem rotMat_apply_11 (θ : ℝ) : rotMat θ 1 1 = Real.cos θ := rfl

/--
@isnad1 id=eq.0h1v.s5.df6414151f9a from=translated src=- shape=548109e9 vocab=2a1c1eb8
-/
theorem det_rotMat (θ : ℝ) : (rotMat θ).det = 1 := by
  rw [Matrix.det_fin_two, rotMat_apply_00, rotMat_apply_01, rotMat_apply_10, rotMat_apply_11]
  nlinarith [Real.cos_sq_add_sin_sq θ]

/--
@isnad1 id=continuo.0h2v.s5.d9aeda574281 from=translated src=- shape=568c8f10 vocab=484e4c35
-/
theorem continuous_rotMat_apply (i j : Fin 2) : Continuous fun θ : ℝ => rotMat θ i j := by
  fin_cases i <;> fin_cases j
  · simpa using Real.continuous_cos
  · simpa using Real.continuous_sin
  · simp
    exact Real.continuous_sin.neg
  · simpa using Real.continuous_cos

def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotMat θ) (by rw [det_rotMat]; exact one_ne_zero)

/--
@isnad1 id=eq.0h1v.s6.851938d55625 from=translated src=- shape=cfe8a7d9 vocab=38b5b950
-/
theorem rotGL_coe (θ : ℝ) : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat θ := rfl

/--
@isnad1 id=mem.0h1v.s8.3f8d9e19cb3b from=translated src=- shape=348377b1 vocab=f8d9a0f8
-/
theorem rotGL_mem (θ : ℝ) : rotGL θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨det_rotMat θ, ?_, ?_⟩
  · rw [rotGL_coe, det_rotMat, norm_one]
  · intro x y
    rw [rotGL_coe, rotMat_apply_00, rotMat_apply_01, rotMat_apply_10, rotMat_apply_11,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      sq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq θ

def rotSO (θ : ℝ) : rowIsometrySubgroup₀ ℝ := ⟨rotGL θ, rotGL_mem θ⟩

/--
@isnad1 id=eq.0h2v.s11.c7cca831f70e from=translated src=- shape=0eb29773 vocab=0b87de60
-/
theorem rotSO_add (a b : ℝ) : rotSO (a + b) = rotSO a * rotSO b := by
  apply Subtype.ext
  apply Units.ext
  change rotMat (a + b) = rotMat a * rotMat b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

/--
@isnad1 id=eq.0h0v.s10.aec202668eeb from=translated src=- shape=ac11af2a vocab=50c95cb3
-/
theorem rotSO_zero : rotSO 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change rotMat 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/--
@isnad1 id=eq.0h0v.s10.519d8657bf69 from=translated src=- shape=2f633666 vocab=cd764086
-/
theorem rotSO_two_pi : rotSO (2 * Real.pi) = 1 := by
  apply Subtype.ext
  apply Units.ext
  change rotMat (2 * Real.pi) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/--
@isnad1 id=eq.0h1v.s12.ef4a5ce78102 from=translated src=- shape=d7a28846 vocab=2b82d713
-/
theorem archWeightOneℝ_rotSO (θ : ℝ) :
    ((archWeightOneℝ (rotSO θ) : ℂˣ) : ℂ) = ⟨Real.cos θ, Real.sin θ⟩ := rfl

/--
@isnad1 id=eq.0h1v.s12.049ef3f0e4d7 from=translated src=- shape=fb1de579 vocab=7bf63165
-/
theorem archWeightOneℝ_rotSO_eq_exp (θ : ℝ) :
    ((archWeightOneℝ (rotSO θ) : ℂˣ) : ℂ) = Complex.exp (θ * Complex.I) := by
  rw [archWeightOneℝ_rotSO, Complex.exp_mul_I]
  apply Complex.ext <;>
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im]

/--
@isnad1 id=surjecti.0h0v.s8.ebde482b518f from=translated src=- shape=9d909ccb vocab=7bc7bbaf
-/
theorem rotSO_surjective : Function.Surjective rotSO := by
  intro k
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ k.2
  set a : ℝ := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b : ℝ := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set z : ℂ := ⟨a, b⟩ with hz
  have hnorm : ‖z‖ = 1 := by
    have : Complex.normSq z = 1 := by
      rw [hz, Complex.normSq_mk]
      nlinarith [hab]
    have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact this
    have h3 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [h2, h3]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  refine ⟨Complex.arg z, ?_⟩
  have hc : Real.cos (Complex.arg z) = a := by rw [Complex.cos_arg hz0, hnorm, div_one]
  have hs : Real.sin (Complex.arg z) = b := by rw [Complex.sin_arg, hnorm, div_one]
  apply Subtype.ext
  apply Units.ext
  change rotMat (Complex.arg z) = ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Matrix.eta_fin_two ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), ← ha, ← hb, h10, h11,
    rotMat, hc, hs]

section Adelic

variable (F : Type) [Field F] [NumberField F]

def rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm he (rotSO θ)

omit [NumberField F] in
/--
@isnad1 id=eq.1h3v.s8.aed828e65b05 from=translated src=- shape=2fab8b68 vocab=a9805e69
-/
theorem norm_symm_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  have := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

variable {F}

omit [NumberField F] in
/--
@isnad1 id=eq.2h5v.s10.0ea95c7e41ed from=translated src=- shape=9c0c90ff vocab=e201affa
-/
theorem rotAt_coe_apply {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) (i j : Fin 2) :
    (((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) i j = (ringEquivRealOfIsReal hw).symm (rotMat θ i j) :=
  rfl

omit [NumberField F] in

/--
@isnad1 id=eq.2h3v.s13.376cb78b64a9 from=translated src=- shape=353487b2 vocab=7f4cc997
-/
theorem rowIsometrySubgroup₀Map_rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      (rotAt F hw he θ) = rotSO θ := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (ringEquivRealOfIsReal hw) ((ringEquivRealOfIsReal hw).symm (rotMat θ i j)) = rotMat θ i j
  exact RingEquiv.apply_symm_apply _ _

omit [NumberField F] in
/--
@isnad1 id=eq.2h4v.s11.d6c6a44d51f7 from=translated src=- shape=36c26865 vocab=e005ef13
-/
theorem rotAt_add {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (a b : ℝ) :
    rotAt F hw he (a + b) = rotAt F hw he a * rotAt F hw he b := by
  rw [rotAt, rotSO_add, map_mul]
  rfl

omit [NumberField F] in
/--
@isnad1 id=eq.2h2v.s11.0a74b144e71e from=translated src=- shape=c060fdde vocab=e8357a5c
-/
theorem rotAt_zero {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) : rotAt F hw he 0 = 1 := by
  rw [rotAt, rotSO_zero, map_one]

def adelicRot {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) : AdelicGL2 (𝓞 F) F :=
  adelicArchGLInclAt F w
    ((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)

/--
@isnad1 id=eq.2h4v.s9.9e65c3e8f9ad from=translated src=- shape=3f14c49f vocab=b8528d93
-/
theorem adelicRot_add {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (a b : ℝ) :
    adelicRot hw he (a + b) = adelicRot hw he a * adelicRot hw he b := by
  rw [adelicRot, rotAt_add, Subgroup.coe_mul, map_mul]
  rfl

/--
@isnad1 id=eq.2h2v.s9.37b7b950571f from=translated src=- shape=cd909514 vocab=4f623837
-/
theorem adelicRot_zero {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) : adelicRot hw he 0 = 1 := by
  rw [adelicRot, rotAt_zero, OneMemClass.coe_one, map_one]

/--
@isnad1 id=eq.2h3v.s9.42ba632e622b from=translated src=- shape=4e3d107d vocab=9cccbfed
-/
theorem adelicRot_neg {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (a : ℝ) :
    adelicRot hw he (-a) = (adelicRot hw he a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← adelicRot_add, neg_add_cancel, adelicRot_zero]

/--
@isnad1 id=eq.2h5v.s10.84766d9bfe8b from=translated src=- shape=c8e78916 vocab=d35995b7
-/
theorem adelicRot_coe_apply {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) (i j : Fin 2) :
    ((adelicRot hw he θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      ((fun v : InfinitePlace F =>
          (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w
            (((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion) v) i j : InfiniteAdeleRing F),
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :=
  rfl

/--
@isnad1 id=continuo.2h2v.s9.0d93cf1da8ec from=translated src=- shape=190c8bb7 vocab=79917de4
-/
theorem continuous_adelicRot {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) :
    Continuous fun θ : ℝ => adelicRot hw he θ := by
  have hval : Continuous fun θ : ℝ =>
      ((adelicRot hw he θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [adelicRot_coe_apply]
    refine Continuous.prodMk ?_ continuous_const
    apply continuous_pi
    intro v
    by_cases hv : v = w
    · subst hv
      simp only [Function.update_self, rotAt_coe_apply]
      exact (isometryEquivRealOfIsReal hw).symm.continuous.comp (continuous_rotMat_apply i j)
    · simp only [Function.update_of_ne hv]
      exact continuous_const
  rw [Units.continuous_iff]
  refine ⟨hval, ?_⟩
  have : (fun θ : ℝ => (((adelicRot hw he θ)⁻¹ : AdelicGL2 (𝓞 F) F) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) =
      fun θ : ℝ => ((adelicRot hw he (-θ) : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    funext θ
    rw [adelicRot_neg]
  rw [this]
  exact hval.comp continuous_neg

end Adelic

/--
@isnad1 id=ex.4h4v.s13.00a46c101117 from=translated src=- shape=2e579eed vocab=16e3afb0
-/
theorem main (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (χ : rowIsometrySubgroup₀ ℝ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφ0 : ∃ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0)
    (hχ : HasArchCharacterAt₀ F w
      (χ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)))
      φ) :
    ∃ n : ℤ, χ = archWeightCharℝ n := by
  obtain ⟨g₀, hg₀⟩ := hφ0
  have he := norm_symm_ringEquivRealOfIsReal F hw

  set f : ℝ → ℂ := fun θ => ((χ (rotSO θ) : ℂˣ) : ℂ) with hf
  have hmulf : ∀ s t : ℝ, f (s + t) = f s * f t := by
    intro s t
    simp only [hf, rotSO_add, map_mul, Units.val_mul]
  have hf0 : f 0 = 1 := by
    simp only [hf, rotSO_zero, map_one, Units.val_one]

  have hfφ : ∀ θ : ℝ, f θ = φ (g₀ * adelicRot hw he θ) / φ g₀ := by
    intro θ
    have h := hχ (rotAt F hw he θ) g₀
    rw [MonoidHom.comp_apply, rowIsometrySubgroup₀Map_rotAt] at h
    change φ (g₀ * adelicRot hw he θ) = f θ * φ g₀ at h
    rw [h, mul_div_assoc, div_self hg₀, mul_one]
  have hfcont : Continuous f := by
    have hfun : f = fun θ => φ (g₀ * adelicRot hw he θ) / φ g₀ := funext hfφ
    rw [hfun]
    exact (hφ.comp (continuous_const.mul (continuous_adelicRot hw he))).div_const _
  obtain ⟨α, hα⟩ := exists_eq_exp_of_continuous_mul f hfcont hf0 hmulf

  have h2π : f (2 * Real.pi) = 1 := by
    simp only [hf, rotSO_two_pi, map_one, Units.val_one]
  rw [hα] at h2π
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2π
  have hαn : α = n * Complex.I := by
    have h2 : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      positivity
    apply mul_right_cancel₀ h2
    rw [hn]
    push_cast
    ring
  refine ⟨n, MonoidHom.ext fun k => ?_⟩
  obtain ⟨θ, rfl⟩ := rotSO_surjective k
  apply Units.ext
  change f θ = ((archWeightCharℝ n (rotSO θ) : ℂˣ) : ℂ)
  rw [hα θ, hαn, archWeightCharℝ, MonoidHom.comp_apply, zpowGroupHom_apply,
    Units.val_zpow_eq_zpow_val, archWeightOneℝ_rotSO_eq_exp, ← Complex.exp_int_mul]
  congr 1
  ring

end CircleCharacterClassification
open scoped _root_.P2MW.S_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous.CircleCharacterClassification

end
open scoped _root_.P2MW.S_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous.CircleCharacterClassification

/--
@isnad1 id=ex.4h4v.s13.00a46c101117 from=translated src=- shape=2e579eed vocab=16e3afb0
-/
theorem solution
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (χ : rowIsometrySubgroup₀ ℝ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφ0 : ∃ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0)
    (hχ : HasArchCharacterAt₀ F w
      (χ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)))
      φ) :
    ∃ n : ℤ, χ = archWeightCharℝ n :=
  CircleCharacterClassification.main F w hw χ φ hφ hφ0 hχ
