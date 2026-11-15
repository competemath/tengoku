import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

open NumberField NumberField.InfinitePlace.Completion Matrix Complex

variable {F : Type} [Field F] [NumberField F]

/--
@isnad1 id=eq.0h1v.s8.a94ffeb4d01f from=translated src=- shape=0190e490 vocab=a8b4cb04
-/
theorem splitTorusGL2Complex_coe (z : ℂ) :
    (splitTorusGL2Complex z : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.exp z, 0; 0, Complex.exp (-z)] :=
  rfl

def archDirMatrixComplex : ArchDirComplex → Matrix (Fin 2) (Fin 2) ℂ
  | .H => !![1, 0; 0, -1]
  | .E => !![0, 1; 0, 0]
  | .Fm => !![0, 0; 1, 0]
  | .iH => !![I, 0; 0, -I]
  | .iE => !![0, I; 0, 0]
  | .iFm => !![0, 0; I, 0]

/--
@isnad1 id=hasderiv.0h2v.s6.df2a3964ce88 from=translated src=- shape=6e0b42a2 vocab=7f0edd17
-/
theorem hasDerivAt_ofReal_mul_const (c : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * c) c t := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const c

/--
@isnad1 id=hasderiv.0h1v.s6.6d9c64bc2870 from=translated src=- shape=2c443d48 vocab=a4119832
-/
theorem hasDerivAt_cexp_ofReal_mul_const (c : ℂ) :
    HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * c)) c 0 := by
  have h := (Complex.hasDerivAt_exp ((0 : ℝ) * c)).comp (0 : ℝ) (hasDerivAt_ofReal_mul_const c 0)
  simp at h
  exact h

/--
@isnad1 id=hasderiv.0h1v.s6.d77fee80665e from=translated src=- shape=2cd38068 vocab=8a998b00
-/
theorem hasDerivAt_cexp_neg_ofReal_mul_const (c : ℂ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * c))) (-c) 0 := by
  have h0 : HasDerivAt (fun s : ℝ => -((s : ℂ) * c)) (-c) 0 := (hasDerivAt_ofReal_mul_const c 0).neg
  have h := (Complex.hasDerivAt_exp (-((0 : ℝ) * c))).comp (0 : ℝ) h0
  simp at h
  exact h

/--
@isnad1 id=hasderiv.0h3v.s7.63142616e890 from=translated src=- shape=14a2dc4c vocab=57c0a78f
-/
theorem hasDerivAt_archFlowMatrixComplex_apply (d : ArchDirComplex) (i j : Fin 2) :
    HasDerivAt (fun t : ℝ => (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) i j)
      (archDirMatrixComplex d i j) 0 := by
  have e1 : HasDerivAt (fun s : ℝ => Complex.exp (s : ℂ)) 1 0 := by
    simpa using hasDerivAt_cexp_ofReal_mul_const 1
  have e2 : HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ))) (-1) 0 := by
    simpa using hasDerivAt_cexp_neg_ofReal_mul_const 1
  have e3 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * I)) I 0 := hasDerivAt_cexp_ofReal_mul_const I
  have e4 : HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * I))) (-I) 0 := hasDerivAt_cexp_neg_ofReal_mul_const I
  have e5 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 0 := by simpa using hasDerivAt_ofReal_mul_const 1 0
  have e6 : HasDerivAt (fun s : ℝ => (s : ℂ) * I) I 0 := hasDerivAt_ofReal_mul_const I 0
  cases d <;> fin_cases i <;> fin_cases j <;>
    simp only [archFlowMatrixComplex, archDirMatrixComplex, splitTorusGL2Complex_coe, unipotentGL2_coe,
      lowerUnipotentGL2_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first
      | exact hasDerivAt_const _ _
      | exact e1 | exact e2 | exact e3 | exact e4 | exact e5 | exact e6

/--
@isnad1 id=eq.2h4v.s10.4b55a7356f9c from=translated src=- shape=10ade2f5 vocab=9a420100
-/
theorem archComplexLiftAt_mul_archComplexGLAt {w : InfinitePlace F} (hw : w.IsComplex) {e : Fin 2 → Fin 2 → ℂ}
    (h : (Matrix.of e).det ≠ 0) (m : GL (Fin 2) ℂ) :
    archComplexLiftAt hw e * archComplexGLAt hw m =
      archComplexLiftAt hw (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℂ))) := by
  have hm : ((m : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero
  have h' : (Matrix.of (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℂ)))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero h hm
  rw [archComplexLiftAt_of_det_ne_zero hw h, archComplexLiftAt_of_det_ne_zero hw h', ← map_mul]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

/--
@isnad1 id=contdiff.0h1v.s9.557b26cd2377 from=translated src=- shape=c93c059c vocab=911bb1b2
-/
theorem contDiff_of_symm_mul_const_complex (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 2 → Fin 2 → ℂ => (Matrix.of.symm (Matrix.of e * A) : Fin 2 → Fin 2 → ℂ) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply ℝ ℂ k).comp (contDiff_apply ℝ (Fin 2 → ℂ) i)).mul contDiff_const

/--
@isnad1 id=hasderiv.0h2v.s10.27cd60b6b8c6 from=translated src=- shape=a41c3521 vocab=14c5bc53
-/
theorem hasDerivAt_of_symm_mul_archFlowMatrixComplex (e : Fin 2 → Fin 2 → ℂ) (d : ArchDirComplex) :
    HasDerivAt
      (fun t : ℝ => (Matrix.of.symm (Matrix.of e * (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ)) :
        Fin 2 → Fin 2 → ℂ))
      (Matrix.of.symm (Matrix.of e * archDirMatrixComplex d)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_archFlowMatrixComplex_apply d k j).const_mul (e i k)

/--
@isnad1 id=eq.0h2v.s9.813205feea52 from=translated src=- shape=92744cc2 vocab=c1fea0da
-/
theorem of_symm_mul_archFlowMatrixComplex_zero (e : Fin 2 → Fin 2 → ℂ) (d : ArchDirComplex) :
    (Matrix.of.symm (Matrix.of e * (archFlowMatrixComplex d 0 : Matrix (Fin 2) (Fin 2) ℂ)) : Fin 2 → Fin 2 → ℂ) = e := by
  rw [archFlowMatrixComplex_zero, Units.val_one, mul_one, Equiv.symm_apply_apply]

/--
@isnad1 id=isarchsm.2h4v.s5.5a56fc9d2483 from=translated src=- shape=8b9017e4 vocab=7cc8fe7e
-/
theorem IsArchSmoothAtComplex.archDerivAtComplex {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex) : IsArchSmoothAtComplex hw (archDerivAtComplex hw d φ) := by
  intro g
  have hΦ := hφ g
  have hopen := isOpen_setOf_det_ne_zero_complex
  refine contDiffOn_infty.2 fun n => ?_
  refine ((hΦ.fderiv_of_isOpen hopen (by exact_mod_cast le_top)).clm_apply
    ((contDiff_of_symm_mul_const_complex (archDirMatrixComplex d)).contDiffOn.of_le (by exact_mod_cast le_top))).congr ?_
  intro e he
  have hdiff : HasFDerivAt (fun e' => φ (g * archComplexLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (g * archComplexLiftAt hw e')) e)
      (Matrix.of.symm (Matrix.of e * (archFlowMatrixComplex d 0 : Matrix (Fin 2) (Fin 2) ℂ))) := by
    rw [of_symm_mul_archFlowMatrixComplex_zero]
    exact ((hΦ.contDiffAt (hopen.mem_nhds he)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun t : ℝ => φ (g * archComplexLiftAt hw e * archFlowAtComplex hw d t)) =
      fun t : ℝ => φ (g * archComplexLiftAt hw
        (Matrix.of.symm (Matrix.of e * (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ)))) := by
    funext t
    rw [archFlowAtComplex, mul_assoc, archComplexLiftAt_mul_archComplexGLAt hw he]
  show deriv (fun t : ℝ => φ (g * archComplexLiftAt hw e * archFlowAtComplex hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrixComplex e d)).deriv

/--
@isnad1 id=eq.1h2v.s8.e20660d450bf from=translated src=- shape=0f7a0381 vocab=966fb49d
-/
theorem archComplexLiftAt_of_symm_one {w : InfinitePlace F} (hw : w.IsComplex) :
    archComplexLiftAt hw (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  rw [archComplexLiftAt_of_det_ne_zero hw hdet, ← map_one (archComplexGLAt hw)]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

/--
@isnad1 id=differen.2h5v.s8.9faf7c4d8308 from=translated src=- shape=4bc33a1d vocab=efeb100a
-/
theorem IsArchSmoothAtComplex.differentiableAt_flow {w : InfinitePlace F} {hw : w.IsComplex}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex) (g : AdelicGL2 (𝓞 F) F) :
    DifferentiableAt ℝ (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) 0 := by
  have hopen := isOpen_setOf_det_ne_zero_complex
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  have hdiff : DifferentiableAt ℝ (fun e' => φ (g * archComplexLiftAt hw e'))
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
        (archFlowMatrixComplex d 0 : Matrix (Fin 2) (Fin 2) ℂ))) := by
    rw [of_symm_mul_archFlowMatrixComplex_zero]
    exact ((hφ g).contDiffAt (hopen.mem_nhds hdet)).differentiableAt (by simp)
  have hfun : (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) =
      fun t : ℝ => φ (g * archComplexLiftAt hw
        (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ)))) := by
    funext t
    rw [← archComplexLiftAt_mul_archComplexGLAt hw hdet, archComplexLiftAt_of_symm_one, one_mul, archFlowAtComplex]
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrixComplex _ d)).differentiableAt

/--
@isnad1 id=eq.3h5v.s8.44604c18b513 from=translated src=- shape=fde0201f vocab=510290cd
-/
theorem archDerivAtComplex_add {w : InfinitePlace F} {hw : w.IsComplex} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) (d : ArchDirComplex) :
    archDerivAtComplex hw d (φ + ψ) = archDerivAtComplex hw d φ + archDerivAtComplex hw d ψ := by
  funext g
  show deriv (fun t : ℝ => (φ + ψ) (g * archFlowAtComplex hw d t)) 0 =
    deriv (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) 0 + deriv (fun t : ℝ => ψ (g * archFlowAtComplex hw d t)) 0
  simp only [Pi.add_apply]
  exact deriv_fun_add (hφ.differentiableAt_flow d g) (hψ.differentiableAt_flow d g)

/--
@isnad1 id=eq.1h5v.s7.c9fc948299db from=translated src=- shape=7c0209de vocab=38b6851e
-/
theorem archDerivAtComplex_smul {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) (c : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : archDerivAtComplex hw d (c • φ) = c • archDerivAtComplex hw d φ := by
  funext g
  show deriv (fun t : ℝ => (c • φ) (g * archFlowAtComplex hw d t)) 0 =
    c • deriv (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) 0
  simp only [Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

/--
@isnad1 id=isarchsm.3h4v.s7.9ba3f0912dc9 from=translated src=- shape=6c80c9c8 vocab=ec785496
-/
theorem IsArchSmoothAtComplex.add {w : InfinitePlace F} {hw : w.IsComplex} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) : IsArchSmoothAtComplex hw (φ + ψ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archComplexLiftAt hw e) + ψ (g * archComplexLiftAt hw e)) _
  exact (hφ g).add (hψ g)

/--
@isnad1 id=isarchsm.2h4v.s6.b732337af4fb from=translated src=- shape=94d9e948 vocab=0a2ed81f
-/
theorem IsArchSmoothAtComplex.smul {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (c : ℂ) : IsArchSmoothAtComplex hw (c • φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => c * φ (g * archComplexLiftAt hw e)) _
  exact contDiffOn_const.mul (hφ g)

/--
@isnad1 id=isarchsm.2h3v.s6.5d3946f4758c from=translated src=- shape=f0e9f4cd vocab=0868a16e
-/
theorem IsArchSmoothAtComplex.neg {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) : IsArchSmoothAtComplex hw (-φ) := by
  rw [← neg_one_smul ℂ φ]
  exact hφ.smul (-1)

/--
@isnad1 id=isarchsm.3h4v.s7.e3ad33cec1e9 from=translated src=- shape=6c80c9c8 vocab=bd23c781
-/
theorem IsArchSmoothAtComplex.sub {w : InfinitePlace F} {hw : w.IsComplex} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) : IsArchSmoothAtComplex hw (φ - ψ) := by
  rw [sub_eq_add_neg]
  exact hφ.add hψ.neg

/--
@isnad1 id=isarchsm.2h4v.s5.55dbe581b6ad from=translated src=- shape=8b9017e4 vocab=84bec3e2
-/
theorem IsArchSmoothAtComplex.archDelAt {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDir) : IsArchSmoothAtComplex hw (archDelAt hw d φ) := by
  unfold AutomorphicForm.archDelAt
  exact ((hφ.archDerivAtComplex _).sub ((hφ.archDerivAtComplex _).smul _)).smul _

/--
@isnad1 id=isarchsm.2h4v.s5.77fdc09f66d6 from=translated src=- shape=8b9017e4 vocab=d226a826
-/
theorem IsArchSmoothAtComplex.archDelBarAt {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDir) : IsArchSmoothAtComplex hw (archDelBarAt hw d φ) := by
  unfold AutomorphicForm.archDelBarAt
  exact ((hφ.archDerivAtComplex _).add ((hφ.archDerivAtComplex _).smul _)).smul _

/--
@isnad1 id=isarchsm.2h3v.s5.285d585a639b from=translated src=- shape=c4f85946 vocab=5814857e
-/
theorem IsArchSmoothAtComplex.archCasimirAtComplex {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) : IsArchSmoothAtComplex hw (archCasimirAtComplex hw φ) := by
  unfold AutomorphicForm.archCasimirAtComplex
  exact (((((hφ.archDelAt .H).archDelAt .H).smul _).sub ((hφ.archDelAt .H).smul _)).add
    ((hφ.archDelAt .Fm).archDelAt .E)).neg

/--
@isnad1 id=isarchsm.2h3v.s5.001b23c8406a from=translated src=- shape=c4f85946 vocab=662b766e
-/
theorem IsArchSmoothAtComplex.archCasimirBarAtComplex {w : InfinitePlace F} {hw : w.IsComplex}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) :
    IsArchSmoothAtComplex hw (archCasimirBarAtComplex hw φ) := by
  unfold AutomorphicForm.archCasimirBarAtComplex
  exact (((((hφ.archDelBarAt .H).archDelBarAt .H).smul _).sub ((hφ.archDelBarAt .H).smul _)).add
    ((hφ.archDelBarAt .Fm).archDelBarAt .E)).neg

/--
@isnad1 id=eq.2h4v.s11.d15bb2543833 from=translated src=- shape=c456b241 vocab=71138bc6
-/
theorem archComplexGLAt_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsComplex) (m : GL (Fin 2) ℂ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archComplexGLAt hw m * k = k * archComplexGLAt hw m := by
  have hfin : AdelicLevel.glFin (𝓞 F) F (archComplexGLAt hw m) = 1 := glFin_adelicArchGLIncl F _
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, hk, mul_one, one_mul]
  · rw [map_mul, map_mul, hfin, mul_one, one_mul]

/--
@isnad1 id=eq.2h4v.s10.6fc5d5a5e4ae from=translated src=- shape=30bd4fe3 vocab=2b9c1f5a
-/
theorem archComplexLiftAt_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsComplex) (e : Fin 2 → Fin 2 → ℂ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archComplexLiftAt hw e * k = k * archComplexLiftAt hw e := by
  unfold archComplexLiftAt
  split_ifs
  · exact archComplexGLAt_mul_comm_of_glArch_eq_one hw _ hk
  · rw [one_mul, mul_one]

/--
@isnad1 id=eq.2h5v.s10.df60d5b479ee from=translated src=- shape=8057e597 vocab=912f9df6
-/
theorem archFlowAtComplex_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex)
    (t : ℝ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archFlowAtComplex hw d t * k = k * archFlowAtComplex hw d t :=
  archComplexGLAt_mul_comm_of_glArch_eq_one hw _ hk

/--
@isnad1 id=isarchsm.3h4v.s10.f53f90ee4e9d from=translated src=- shape=989b2c8c vocab=654b4b29
-/
theorem IsArchSmoothAtComplex.comp_mul_right {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    IsArchSmoothAtComplex hw fun g => φ (g * k) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archComplexLiftAt hw e * k)) _
  have hfun : (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e * k)) =
      fun e => φ (g * k * archComplexLiftAt hw e) := by
    funext e
    rw [mul_assoc, archComplexLiftAt_mul_comm_of_glArch_eq_one hw e hk, ← mul_assoc]
  rw [hfun]
  exact hφ (g * k)

/--
@isnad1 id=eq.2h5v.s10.5a3aeb69fe88 from=translated src=- shape=8c829493 vocab=fe92f8c1
-/
theorem archDerivAtComplex_comp_mul_right {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archDerivAtComplex hw d (fun g => φ (g * k)) = fun g => archDerivAtComplex hw d φ (g * k) := by
  funext g
  show deriv (fun t : ℝ => φ (g * archFlowAtComplex hw d t * k)) 0 =
    deriv (fun t : ℝ => φ (g * k * archFlowAtComplex hw d t)) 0
  congr 1
  funext t
  rw [mul_assoc, archFlowAtComplex_mul_comm_of_glArch_eq_one hw d t hk, ← mul_assoc]

/--
@isnad1 id=eq.2h5v.s10.2d2bbb1b078f from=translated src=- shape=8c829493 vocab=2f33f529
-/
theorem archDelAt_comp_mul_right {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDir)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archDelAt hw d (fun g => φ (g * k)) = fun g => archDelAt hw d φ (g * k) := by
  unfold AutomorphicForm.archDelAt
  rw [archDerivAtComplex_comp_mul_right hw _ φ hk, archDerivAtComplex_comp_mul_right hw _ φ hk]
  funext g
  simp only [Pi.smul_apply, Pi.sub_apply]

/--
@isnad1 id=eq.2h5v.s10.1737b3e6e3b4 from=translated src=- shape=8c829493 vocab=98282883
-/
theorem archDelBarAt_comp_mul_right {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDir)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archDelBarAt hw d (fun g => φ (g * k)) = fun g => archDelBarAt hw d φ (g * k) := by
  unfold AutomorphicForm.archDelBarAt
  rw [archDerivAtComplex_comp_mul_right hw _ φ hk, archDerivAtComplex_comp_mul_right hw _ φ hk]
  funext g
  simp only [Pi.smul_apply, Pi.add_apply]

/--
@isnad1 id=eq.2h4v.s10.3722ae62845f from=translated src=- shape=1e15cf08 vocab=ce179c25
-/
theorem archCasimirAtComplex_comp_mul_right {w : InfinitePlace F} (hw : w.IsComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archCasimirAtComplex hw (fun g => φ (g * k)) = fun g => archCasimirAtComplex hw φ (g * k) := by
  unfold AutomorphicForm.archCasimirAtComplex
  rw [archDelAt_comp_mul_right hw .H φ hk, archDelAt_comp_mul_right hw .H (archDelAt hw .H φ) hk,
    archDelAt_comp_mul_right hw .Fm φ hk, archDelAt_comp_mul_right hw .E (archDelAt hw .Fm φ) hk]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

/--
@isnad1 id=eq.2h4v.s10.fb8739d3aa30 from=translated src=- shape=1e15cf08 vocab=e15d80a5
-/
theorem archCasimirBarAtComplex_comp_mul_right {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archCasimirBarAtComplex hw (fun g => φ (g * k)) = fun g => archCasimirBarAtComplex hw φ (g * k) := by
  unfold AutomorphicForm.archCasimirBarAtComplex
  rw [archDelBarAt_comp_mul_right hw .H φ hk, archDelBarAt_comp_mul_right hw .H (archDelBarAt hw .H φ) hk,
    archDelBarAt_comp_mul_right hw .Fm φ hk, archDelBarAt_comp_mul_right hw .E (archDelBarAt hw .Fm φ) hk]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

/--
@isnad1 id=isarchsm.2h4v.s8.b04fa11e1e0e from=translated src=- shape=84ccfe17 vocab=52cb9722
-/
theorem IsArchSmoothAtComplex.comp_mul_left {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (h : AdelicGL2 (𝓞 F) F) : IsArchSmoothAtComplex hw fun g => φ (h * g) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (h * (g * archComplexLiftAt hw e))) _
  simp only [← mul_assoc]
  exact hφ (h * g)

/--
@isnad1 id=eq.1h5v.s8.d6938f72a13f from=translated src=- shape=e9f9c3ee vocab=f97ed16b
-/
theorem archDerivAtComplex_comp_mul_left {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (h : AdelicGL2 (𝓞 F) F) :
    archDerivAtComplex hw d (fun g => φ (h * g)) = fun g => archDerivAtComplex hw d φ (h * g) := by
  funext g
  show deriv (fun t : ℝ => φ (h * (g * archFlowAtComplex hw d t))) 0 =
    deriv (fun t : ℝ => φ (h * g * archFlowAtComplex hw d t)) 0
  simp only [mul_assoc]

/--
@isnad1 id=eq.1h3v.s11.f825ee93e97b from=translated src=- shape=5a22bcf2 vocab=6d6bae75
-/
theorem archComplexGLAt_glEquivOfRingEquiv {w : InfinitePlace F} (hw : w.IsComplex) (k : GL (Fin 2) w.Completion) :
    archComplexGLAt hw (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw) k) = adelicArchGLInclAt F w k := by
  show adelicArchGLInclAt F w
    (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm
      (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw) k)) = adelicArchGLInclAt F w k
  congr 1
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
  exact (ringEquivComplexOfIsComplex hw).symm_apply_apply _

def archComplexProjAt {w : InfinitePlace F} (hw : w.IsComplex) : AdelicGL2 (𝓞 F) F →* GL (Fin 2) ℂ :=
  (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw)).toMonoidHom.comp
    ((AdelicLevel.archComponent F w).comp (AdelicLevel.glArch (𝓞 F) F))

/--
@isnad1 id=eq.1h3v.s10.a48afa22b651 from=translated src=- shape=11a9ae22 vocab=8de0ca16
-/
theorem archComplexProjAt_archComplexGLAt {w : InfinitePlace F} (hw : w.IsComplex) (m : GL (Fin 2) ℂ) :
    archComplexProjAt hw (archComplexGLAt hw m) = m := by
  have h1 : AdelicLevel.glArch (𝓞 F) F (archComplexGLAt hw m) =
      archGLIncl F w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm m) :=
    glArch_adelicArchGLIncl F _
  have h2 : AdelicLevel.archComponent F w (AdelicLevel.glArch (𝓞 F) F (archComplexGLAt hw m)) =
      glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm m := by
    rw [h1, archComponent_archGLIncl_self]
  show glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw)
    (AdelicLevel.archComponent F w (AdelicLevel.glArch (𝓞 F) F (archComplexGLAt hw m))) = m
  rw [h2]
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
  exact (ringEquivComplexOfIsComplex hw).apply_symm_apply _

/--
@isnad1 id=eq.0h1v.s8.883421dfde2c from=translated src=- shape=fc496862 vocab=27222edd
-/
theorem circleGL2_coe (ζ : ℂˣ) : (circleGL2 ζ : Matrix (Fin 2) (Fin 2) ℂ) = !![(ζ : ℂ), 0; 0, ((ζ⁻¹ : ℂˣ) : ℂ)] :=
  rfl

/--
@isnad1 id=eq.0h0v.s7.c10b1cbe2bf7 from=translated src=- shape=5051ddc3 vocab=9bbaa76e
-/
theorem circleGL2_one : circleGL2 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [circleGL2]

/--
@isnad1 id=eq.0h2v.s7.ecc460e0777e from=translated src=- shape=240adfc6 vocab=bd907898
-/
theorem circleGL2_mul (ζ ζ' : ℂˣ) : circleGL2 (ζ * ζ') = circleGL2 ζ * circleGL2 ζ' := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [circleGL2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/--
@isnad1 id=eq.1h2v.s7.30b9af76cfeb from=translated src=- shape=52fb6574 vocab=a5d69fe6
-/
theorem archCircleAt_one {w : InfinitePlace F} (hw : w.IsComplex) : archCircleAt hw 1 = 1 := by
  rw [archCircleAt, circleGL2_one, map_one]

/--
@isnad1 id=eq.1h4v.s8.4615788bc6e0 from=translated src=- shape=734ebd50 vocab=f9dba1ff
-/
theorem archCircleAt_mul {w : InfinitePlace F} (hw : w.IsComplex) (ζ ζ' : ℂˣ) :
    archCircleAt hw (ζ * ζ') = archCircleAt hw ζ * archCircleAt hw ζ' := by
  rw [archCircleAt, circleGL2_mul, map_mul]; rfl

/--
@isnad1 id=eq.2h4v.s10.38b86d71421d from=translated src=- shape=5af902b8 vocab=a2b2cfd9
-/
theorem archCircleAt_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsComplex) (ζ : ℂˣ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archCircleAt hw ζ * k = k * archCircleAt hw ζ :=
  archComplexGLAt_mul_comm_of_glArch_eq_one hw _ hk

/--
@isnad1 id=hascircl.3h5v.s10.38688032f042 from=translated src=- shape=a4a588e0 vocab=a7c00b48
-/
theorem HasCircleWeightAt.comp_mul_right {w : InfinitePlace F} {hw : w.IsComplex} {m : ℤ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : HasCircleWeightAt hw m φ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    HasCircleWeightAt hw m fun g => φ (g * k) := by
  intro ζ hζ g
  show φ (g * archCircleAt hw ζ * k) = (ζ : ℂ) ^ m * φ (g * k)
  rw [mul_assoc, archCircleAt_mul_comm_of_glArch_eq_one hw ζ hk, ← mul_assoc]
  exact hφ ζ hζ (g * k)

/--
@isnad1 id=hascircl.3h5v.s7.225ed36b1e69 from=translated src=- shape=8880a792 vocab=d8cb3580
-/
theorem HasCircleWeightAt.add {w : InfinitePlace F} {hw : w.IsComplex} {m : ℤ} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : HasCircleWeightAt hw m φ) (hψ : HasCircleWeightAt hw m ψ) : HasCircleWeightAt hw m (φ + ψ) := by
  intro ζ hζ g
  simp only [Pi.add_apply, hφ ζ hζ g, hψ ζ hζ g, mul_add]

/--
@isnad1 id=hascircl.2h5v.s7.a4356f1c39df from=translated src=- shape=20cc2a72 vocab=a3120517
-/
theorem HasCircleWeightAt.smul {w : InfinitePlace F} {hw : w.IsComplex} {m : ℤ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : HasCircleWeightAt hw m φ) (c : ℂ) : HasCircleWeightAt hw m (c • φ) := by
  intro ζ hζ g
  simp only [Pi.smul_apply, smul_eq_mul, hφ ζ hζ g]
  ring

end AutomorphicForm

end
