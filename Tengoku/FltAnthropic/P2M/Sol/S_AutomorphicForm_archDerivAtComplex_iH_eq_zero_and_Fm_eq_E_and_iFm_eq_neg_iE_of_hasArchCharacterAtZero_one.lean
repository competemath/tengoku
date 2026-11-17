import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchWeightChar
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

namespace Ws50KDER0

open Matrix Complex AutomorphicForm.WindowedSiegel

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
/--
@isnad1 id=eq.1h3v.s8.868a6a7f1d53 from=translated src=- shape=8114c758 vocab=dcb5c795
-/
theorem norm_ringEquivComplexOfIsComplex_symm {w : InfinitePlace F} (hw : w.IsComplex) (z : ℂ) :
    ‖(ringEquivComplexOfIsComplex hw).symm z‖ = ‖z‖ := by
  have h : ∀ x : w.Completion, ‖ringEquivComplexOfIsComplex hw x‖ = ‖x‖ := fun x =>
    (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
  conv_rhs => rw [← (ringEquivComplexOfIsComplex hw).apply_symm_apply z]
  rw [h]

/--
@isnad1 id=eq.3h5v.s13.5879ee824c23 from=translated src=- shape=4082d0a0 vocab=7045eb9d
-/
theorem apply_mul_archComplexGLAt_of_mem {w : InfinitePlace F} (hw : w.IsComplex)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hχ : HasArchCharacterAt₀ F w 1 φ)
    (m : GL (Fin 2) ℂ) (hm : m ∈ rowIsometrySubgroup₀ ℂ) (g : AdelicGL2 (𝓞 F) F) :
    φ (g * archComplexGLAt hw m) = φ g := by
  have hk := map_mem_rowIsometrySubgroup₀_of_normPreserving (ringEquivComplexOfIsComplex hw).symm
    (norm_ringEquivComplexOfIsComplex_symm hw) m hm
  have h := hχ ⟨_, hk⟩ g
  rw [MonoidHom.one_apply, Units.val_one, one_mul] at h
  exact h

/--
@isnad1 id=mem.2h1v.s9.dda306d0ccab from=translated src=- shape=9958e5e8 vocab=fa88b774
-/
theorem mem_rowIsometrySubgroup₀_complex (m : GL (Fin 2) ℂ)
    (hdet : (m : Matrix (Fin 2) (Fin 2) ℂ).det = 1)
    (hiso : ∀ x y : ℂ,
      ‖x * (m : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + y * (m : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2
        + ‖x * (m : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + y * (m : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2) :
    m ∈ rowIsometrySubgroup₀ ℂ :=
  (mem_rowIsometrySubgroup₀_iff ℂ).mpr ⟨hdet, by rw [hdet]; exact norm_one, hiso⟩

noncomputable def rotGL (t : ℝ) : GL (Fin 2) ℂ where
  val := !![(Real.cos t : ℂ), -(Real.sin t : ℂ); (Real.sin t : ℂ), (Real.cos t : ℂ)]
  inv := !![(Real.cos t : ℂ), (Real.sin t : ℂ); -(Real.sin t : ℂ), (Real.cos t : ℂ)]
  val_inv := by
    have h : (Real.cos t : ℂ) ^ 2 + (Real.sin t : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
      first | linear_combination h | linear_combination -h | ring
  inv_val := by
    have h : (Real.cos t : ℂ) ^ 2 + (Real.sin t : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
      first | linear_combination h | linear_combination -h | ring

noncomputable def swayGL (t : ℝ) : GL (Fin 2) ℂ where
  val := !![(Real.cos t : ℂ), (Real.sin t : ℂ) * I; (Real.sin t : ℂ) * I, (Real.cos t : ℂ)]
  inv := !![(Real.cos t : ℂ), -((Real.sin t : ℂ) * I); -((Real.sin t : ℂ) * I), (Real.cos t : ℂ)]
  val_inv := by
    have h : (Real.cos t : ℂ) ^ 2 + (Real.sin t : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_cos, -Complex.ofReal_sin] <;> ring_nf <;>
      simp only [Complex.I_sq] <;> first | linear_combination h | linear_combination -h | ring
  inv_val := by
    have h : (Real.cos t : ℂ) ^ 2 + (Real.sin t : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_cos, -Complex.ofReal_sin] <;> ring_nf <;>
      simp only [Complex.I_sq] <;> first | linear_combination h | linear_combination -h | ring

/--
@isnad1 id=mem.0h1v.s8.36ab709065a2 from=translated src=- shape=21e1e76d vocab=8090d3ca
-/
theorem rotGL_mem (t : ℝ) : rotGL t ∈ rowIsometrySubgroup₀ ℂ := by
  have h : (Real.cos t : ℂ) ^ 2 + (Real.sin t : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
  refine mem_rowIsometrySubgroup₀_complex _ ?_ ?_
  · simp [rotGL, Matrix.det_fin_two, -Complex.ofReal_cos, -Complex.ofReal_sin]; linear_combination h
  · intro x y
    simp only [rotGL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have hr := Real.cos_sq_add_sin_sq t
    ring_nf
    nlinarith [hr, sq_nonneg x.re, sq_nonneg x.im, sq_nonneg y.re, sq_nonneg y.im]

/--
@isnad1 id=mem.0h1v.s8.d705d29ed0be from=translated src=- shape=21e1e76d vocab=e8c03c91
-/
theorem swayGL_mem (t : ℝ) : swayGL t ∈ rowIsometrySubgroup₀ ℂ := by
  have h : (Real.cos t : ℂ) ^ 2 + (Real.sin t : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq t
  refine mem_rowIsometrySubgroup₀_complex _ ?_ ?_
  · simp [swayGL, Matrix.det_fin_two, -Complex.ofReal_cos, -Complex.ofReal_sin]; ring_nf; simp only [Complex.I_sq]; linear_combination h
  · intro x y
    simp only [swayGL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have hr := Real.cos_sq_add_sin_sq t
    ring_nf
    nlinarith [hr, sq_nonneg x.re, sq_nonneg x.im, sq_nonneg y.re, sq_nonneg y.im]

/--
@isnad1 id=mem.0h1v.s8.9dc00c335023 from=translated src=- shape=5c742940 vocab=7223b0fe
-/
theorem flow_iH_mem (t : ℝ) : archFlowMatrixComplex .iH t ∈ rowIsometrySubgroup₀ ℂ := by
  have hcoe : ((archFlowMatrixComplex .iH t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp ((t : ℂ) * I), 0; 0, Complex.exp (-((t : ℂ) * I))] := by
    show ((splitTorusGL2Complex ((t : ℂ) * I) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [splitTorusGL2Complex_coe]
  have hn1 : ‖Complex.exp ((t : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
  have hn2 : ‖Complex.exp (-((t : ℂ) * I))‖ = 1 := by
    rw [show -((t : ℂ) * I) = ((-t : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I (-t)
  refine mem_rowIsometrySubgroup₀_complex _ ?_ ?_
  · rw [hcoe, Matrix.det_fin_two_of, ← Complex.exp_add]; simp
  · intro x y
    rw [hcoe]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, mul_zero, add_zero, zero_add, norm_mul, hn1, hn2, mul_one]

/--
@isnad1 id=eq.1h3v.s9.c7229c8525c7 from=translated src=- shape=00faa551 vocab=20f8dbd0
-/
theorem archComplexGLAt_eq_lift {w : InfinitePlace F} (hw : w.IsComplex) (m : GL (Fin 2) ℂ) :
    archComplexGLAt hw m = archComplexLiftAt hw (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]; exact one_ne_zero
  have h := archComplexLiftAt_mul_archComplexGLAt hw hdet m
  rw [archComplexLiftAt_of_symm_one, one_mul, Equiv.apply_symm_apply, one_mul] at h
  exact h

/--
@isnad1 id=hasderiv.4h6v.s11.5e0f3495a4e7 from=translated src=- shape=6eb01b97 vocab=15eb270b
-/
theorem hasDerivAt_chart {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (g : AdelicGL2 (𝓞 F) F)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (M' : Matrix (Fin 2) (Fin 2) ℂ) (hM0 : M 0 = 1)
    (hM : HasDerivAt (fun t : ℝ => (Matrix.of.symm (M t) : Fin 2 → Fin 2 → ℂ)) (Matrix.of.symm M') 0) :
    HasDerivAt (fun t : ℝ => φ (g * archComplexLiftAt hw (Matrix.of.symm (M t))))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) (Matrix.of.symm M')) 0 := by
  have hopen := isOpen_setOf_det_ne_zero_complex
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]; exact one_ne_zero
  have hdiff : HasFDerivAt (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)))
      (Matrix.of.symm (M 0)) := by
    rw [hM0]
    exact (((hφ g).contDiffAt (hopen.mem_nhds hdet)).differentiableAt (by simp)).hasFDerivAt
  exact hdiff.comp_hasDerivAt (0 : ℝ) hM

/--
@isnad1 id=eq.2h5v.s10.4ac4166daa11 from=translated src=- shape=acdb8462 vocab=08f0a0fe
-/
theorem archDerivAtComplex_eq {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAtComplex hw d φ g =
      fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) (Matrix.of.symm (archDirMatrixComplex d)) := by
  have hM : HasDerivAt (fun t : ℝ => (Matrix.of.symm ((archFlowMatrixComplex d t : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) : Fin 2 → Fin 2 → ℂ)) (Matrix.of.symm (archDirMatrixComplex d)) 0 := by
    have h := hasDerivAt_of_symm_mul_archFlowMatrixComplex (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) d
    simp only [Equiv.apply_symm_apply, one_mul] at h
    exact h
  have h := hasDerivAt_chart hφ g (fun t => ((archFlowMatrixComplex d t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))
    (archDirMatrixComplex d)
    (by show ((archFlowMatrixComplex d 0 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1; rw [archFlowMatrixComplex_zero, Units.val_one])
    hM
  have hfun : (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) =
      fun t : ℝ => φ (g * archComplexLiftAt hw (Matrix.of.symm
        ((archFlowMatrixComplex d t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))) := by
    funext t; rw [archFlowAtComplex, archComplexGLAt_eq_lift]
  unfold archDerivAtComplex
  rw [hfun]
  exact h.deriv

/--
@isnad1 id=eq.6h6v.s13.3acb19561037 from=translated src=- shape=693383d0 vocab=fa068468
-/
theorem fderiv_apply_eq_zero_of_mem {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hχ : HasArchCharacterAt₀ F w 1 φ) (g : AdelicGL2 (𝓞 F) F)
    (M : ℝ → GL (Fin 2) ℂ) (hmem : ∀ t, M t ∈ rowIsometrySubgroup₀ ℂ) (M' : Matrix (Fin 2) (Fin 2) ℂ)
    (hM0 : M 0 = 1)
    (hM : HasDerivAt (fun t : ℝ => (Matrix.of.symm ((M t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :
      Fin 2 → Fin 2 → ℂ)) (Matrix.of.symm M') 0) :
    fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
        (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) (Matrix.of.symm M') = 0 := by
  have h := hasDerivAt_chart hφ g (fun t => ((M t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) M'
    (by show ((M 0 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1; rw [hM0, Units.val_one]) hM
  have hconst : (fun t : ℝ => φ (g * archComplexLiftAt hw (Matrix.of.symm
      ((M t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)))) = fun _ => φ g := by
    funext t
    rw [← archComplexGLAt_eq_lift, apply_mul_archComplexGLAt_of_mem hw hχ (M t) (hmem t) g]
  rw [hconst] at h
  exact (h.unique (hasDerivAt_const (0 : ℝ) (φ g))).symm ▸ rfl

/--
@isnad1 id=hasderiv.0h0v.s9.e9e0d920b592 from=translated src=- shape=a9052840 vocab=fd33ccdb
-/
theorem hasDerivAt_rotGL :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm ((rotGL t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :
      Fin 2 → Fin 2 → ℂ)) (Matrix.of.symm (archDirMatrixComplex .Fm - archDirMatrixComplex .E)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0).ofReal_comp
  have hs : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ)) 1 0 := by
    simpa using (Real.hasDerivAt_sin 0).ofReal_comp
  rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j
  fin_cases i <;> fin_cases j
  · simpa [rotGL, archDirMatrixComplex] using hc
  · have h__af := hs.neg
    simp [rotGL, archDirMatrixComplex] at h__af ⊢
    exact h__af
  · simpa [rotGL, archDirMatrixComplex] using hs
  · simpa [rotGL, archDirMatrixComplex] using hc

/--
@isnad1 id=hasderiv.0h0v.s9.e11c1cff53cd from=translated src=- shape=a9052840 vocab=813849e4
-/
theorem hasDerivAt_swayGL :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm ((swayGL t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :
      Fin 2 → Fin 2 → ℂ)) (Matrix.of.symm (archDirMatrixComplex .iE + archDirMatrixComplex .iFm)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0).ofReal_comp
  have hs : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ) * I) I 0 := by
    simpa using ((Real.hasDerivAt_sin 0).ofReal_comp).mul_const I
  rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j
  fin_cases i <;> fin_cases j
  · simpa [swayGL, archDirMatrixComplex] using hc
  · simpa [swayGL, archDirMatrixComplex] using hs
  · simpa [swayGL, archDirMatrixComplex] using hs
  · simpa [swayGL, archDirMatrixComplex] using hc

/--
@isnad1 id=eq.0h0v.s6.3959b264ba76 from=translated src=- shape=1300b827 vocab=00bd513b
-/
theorem rotGL_zero : rotGL 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotGL]

/--
@isnad1 id=eq.0h0v.s6.ee33f35cea16 from=translated src=- shape=1300b827 vocab=0870d98f
-/
theorem swayGL_zero : swayGL 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swayGL]

end Ws50KDER0

open Ws50KDER0 in

/--
@isnad1 id=and.3h3v.s13.76cd85996896 from=translated src=- shape=c82c40ab vocab=5f25d937
-/
theorem solution
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hχ : HasArchCharacterAt₀ F w 1 φ) :
    archDerivAtComplex hw .iH φ = 0 ∧
    archDerivAtComplex hw .Fm φ = archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .iFm φ = -archDerivAtComplex hw .iE φ := by
  set L := fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (1 * archComplexLiftAt hw e))
    (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) with hL
  refine ⟨?_, ?_, ?_⟩
  ·
    funext g
    have hconst : (fun t : ℝ => φ (g * archFlowAtComplex hw .iH t)) = fun _ => φ g := by
      funext t
      exact apply_mul_archComplexGLAt_of_mem hw hχ _ (flow_iH_mem t) g
    show deriv (fun t : ℝ => φ (g * archFlowAtComplex hw .iH t)) 0 = 0
    rw [hconst, deriv_const]
  · funext g
    have h0 := fderiv_apply_eq_zero_of_mem hφ hχ g rotGL rotGL_mem _ rotGL_zero hasDerivAt_rotGL
    rw [archDerivAtComplex_eq hφ, archDerivAtComplex_eq hφ]
    have hsub : (Matrix.of.symm (archDirMatrixComplex .Fm - archDirMatrixComplex .E) : Fin 2 → Fin 2 → ℂ) =
        Matrix.of.symm (archDirMatrixComplex .Fm) - Matrix.of.symm (archDirMatrixComplex .E) := rfl
    rw [hsub, map_sub, sub_eq_zero] at h0
    exact h0
  · funext g
    have h0 := fderiv_apply_eq_zero_of_mem hφ hχ g swayGL swayGL_mem _ swayGL_zero hasDerivAt_swayGL
    rw [Pi.neg_apply, archDerivAtComplex_eq hφ, archDerivAtComplex_eq hφ]
    have hadd : (Matrix.of.symm (archDirMatrixComplex .iE + archDirMatrixComplex .iFm) : Fin 2 → Fin 2 → ℂ) =
        Matrix.of.symm (archDirMatrixComplex .iE) + Matrix.of.symm (archDirMatrixComplex .iFm) := rfl
    rw [hadd, map_add, add_eq_zero_iff_neg_eq] at h0
    exact h0.symm
