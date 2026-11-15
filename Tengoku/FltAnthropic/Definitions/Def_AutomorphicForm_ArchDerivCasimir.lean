import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchType
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchParam
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.RealArchParam

def laplaceEigenvalue : RealArchParam → ℂ
  | principal u₁ _ u₂ _ => 1 / 4 - ((u₁ - u₂) / 2) ^ 2
  | discrete _ k _ => (1 - (k : ℂ) ^ 2) / 4

/--
@isnad1 id=eq.0h4v.s6.6bb4ea398733 from=translated src=- shape=387ea79f vocab=4c387c04
-/
theorem laplaceEigenvalue_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    laplaceEigenvalue (principal u₁ a₁ u₂ a₂) = 1 / 4 - ((u₁ - u₂) / 2) ^ 2 :=
  rfl

/--
@isnad1 id=eq.1h2v.s6.871f788562ed from=translated src=- shape=ad00ed56 vocab=35a8963e
-/
theorem laplaceEigenvalue_discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    laplaceEigenvalue (discrete u k hk) = (1 - (k : ℂ) ^ 2) / 4 :=
  rfl

end LanglandsTunnell.RealArchParam

namespace AutomorphicForm

open NumberField NumberField.InfinitePlace.Completion Matrix

variable (F : Type) [Field F] [NumberField F]

section RealPlaceTransport

variable {F}

def archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) : GL (Fin 2) ℝ →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLInclAt F w).comp (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).toMonoidHom

def archRealLiftAt {w : InfinitePlace F} (hw : w.IsReal) (e : Fin 2 → Fin 2 → ℝ) : AdelicGL2 (𝓞 F) F :=
  if h : (Matrix.of e).det ≠ 0 then archRealGLAt hw (GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h)
  else 1

/--
@isnad1 id=eq.2h3v.s10.096a43ec1009 from=translated src=- shape=77c7832a vocab=7bddffb5
-/
theorem archRealLiftAt_of_det_ne_zero {w : InfinitePlace F} (hw : w.IsReal) {e : Fin 2 → Fin 2 → ℝ}
    (h : (Matrix.of e).det ≠ 0) :
    archRealLiftAt hw e = archRealGLAt hw (GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h) :=
  dite_eq_left h

/--
@isnad1 id=isopen.0h0v.s8.6fb19c52aca0 from=translated src=- shape=4a3c72f1 vocab=b3e47a7a
-/
theorem isOpen_setOf_det_ne_zero :
    IsOpen {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0} :=
  (isClosed_singleton.preimage (continuous_id.matrix_det)).isOpen_compl

def IsArchSmoothAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F,
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e))
      {e | (Matrix.of e).det ≠ 0}

/--
@isnad1 id=isarchsm.1h3v.s5.6b79c7002b66 from=translated src=- shape=e1e53099 vocab=0dfdc833
-/
theorem isArchSmoothAt_const {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) :
    IsArchSmoothAt hw (fun _ => c) :=
  fun _ => contDiffOn_const

end RealPlaceTransport

section Flows

variable {F}

inductive ArchDir where
  | H : ArchDir
  | E : ArchDir
  | Fm : ArchDir

def lowerUnipotentGL2 {R : Type*} [CommRing R] (x : R) : GL (Fin 2) R where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h2v.s8.ef70b967f1d0 from=translated src=- shape=ca907116 vocab=6181916f
-/
theorem lowerUnipotentGL2_coe {R : Type*} [CommRing R] (x : R) :
    (lowerUnipotentGL2 x : Matrix (Fin 2) (Fin 2) R) = !![1, 0; x, 1] :=
  rfl

/--
@isnad1 id=eq.0h1v.s7.e03bf5381cd5 from=translated src=- shape=82a407f1 vocab=61c8db14
-/
theorem lowerUnipotentGL2_zero {R : Type*} [CommRing R] : lowerUnipotentGL2 (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [lowerUnipotentGL2]

/--
@isnad1 id=eq.0h3v.s7.5ec94587d30b from=translated src=- shape=b68454b1 vocab=b0706331
-/
theorem lowerUnipotentGL2_add {R : Type*} [CommRing R] (x y : R) :
    lowerUnipotentGL2 (x + y) = lowerUnipotentGL2 x * lowerUnipotentGL2 y := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotentGL2, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def splitTorusGL2 (t : ℝ) : GL (Fin 2) ℝ where
  val := !![Real.exp t, 0; 0, Real.exp (-t)]
  inv := !![Real.exp (-t), 0; 0, Real.exp t]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]

/--
@isnad1 id=eq.0h1v.s8.634cd59092ba from=translated src=- shape=0190e490 vocab=2d389f93
-/
theorem splitTorusGL2_coe (t : ℝ) :
    (splitTorusGL2 t : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.exp t, 0; 0, Real.exp (-t)] :=
  rfl

/--
@isnad1 id=eq.0h0v.s6.85749f48187d from=translated src=- shape=98680116 vocab=709de403
-/
theorem splitTorusGL2_zero : splitTorusGL2 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitTorusGL2]

/--
@isnad1 id=eq.0h2v.s7.92f82cb978fb from=translated src=- shape=ff03d487 vocab=5ad934d7
-/
theorem splitTorusGL2_add (s t : ℝ) : splitTorusGL2 (s + t) = splitTorusGL2 s * splitTorusGL2 t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add]; ring

def archFlowMatrix : ArchDir → ℝ → GL (Fin 2) ℝ
  | .H, t => splitTorusGL2 t
  | .E, t => unipotentGL2 t
  | .Fm, t => lowerUnipotentGL2 t

/--
@isnad1 id=eq.0h1v.s7.cb346c54ad43 from=translated src=- shape=a2e4f51a vocab=75662374
-/
theorem archFlowMatrix_zero (d : ArchDir) : archFlowMatrix d 0 = 1 := by
  cases d
  · exact splitTorusGL2_zero
  · exact unipotentGL2_zero
  · exact lowerUnipotentGL2_zero

/--
@isnad1 id=eq.0h3v.s7.b66ed69c5dc8 from=translated src=- shape=49f8b010 vocab=c2c5c72c
-/
theorem archFlowMatrix_add (d : ArchDir) (s t : ℝ) :
    archFlowMatrix d (s + t) = archFlowMatrix d s * archFlowMatrix d t := by
  cases d
  · exact splitTorusGL2_add s t
  · exact unipotentGL2_add s t
  · exact lowerUnipotentGL2_add s t

def archFlowAt {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ) : AdelicGL2 (𝓞 F) F :=
  archRealGLAt hw (archFlowMatrix d t)

/--
@isnad1 id=eq.1h3v.s7.91e288e317a9 from=translated src=- shape=62a282a3 vocab=42bfcaa7
-/
theorem archFlowAt_zero {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) : archFlowAt hw d 0 = 1 := by
  rw [archFlowAt, archFlowMatrix_zero, map_one]

/--
@isnad1 id=eq.1h5v.s8.cf69f25b8042 from=translated src=- shape=03cb0c81 vocab=c0eee7df
-/
theorem archFlowAt_add {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (s t : ℝ) :
    archFlowAt hw d (s + t) = archFlowAt hw d s * archFlowAt hw d t := by
  rw [archFlowAt, archFlowMatrix_add, map_mul]; rfl

def archDerivAt {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => deriv (fun t : ℝ => φ (g * archFlowAt hw d t)) 0

def archCasimirAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  -((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H φ) - (1 / 2 : ℂ) • archDerivAt hw .H φ +
    archDerivAt hw .E (archDerivAt hw .Fm φ))

/--
@isnad1 id=eq.1h4v.s6.5a175d7d7341 from=translated src=- shape=5f607d76 vocab=dbbc7890
-/
theorem archDerivAt_const {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (c : ℂ) :
    archDerivAt hw d (fun _ => c) = fun _ => 0 := by
  funext g
  simp [archDerivAt]

/--
@isnad1 id=eq.1h3v.s6.01c0f2baff6a from=translated src=- shape=8c55bf3f vocab=dd2751b4
-/
theorem archCasimirAt_const {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) :
    archCasimirAt hw (fun _ => c) = fun _ => 0 := by
  funext g
  simp [archCasimirAt, archDerivAt_const]

def archDirMatrix : ArchDir → Matrix (Fin 2) (Fin 2) ℝ
  | .H => !![1, 0; 0, -1]
  | .E => !![0, 1; 0, 0]
  | .Fm => !![0, 0; 1, 0]

/--
@isnad1 id=hasderiv.0h3v.s6.793ca8e29b15 from=translated src=- shape=3a2e5dc0 vocab=7cdc58ed
-/
theorem hasDerivAt_archFlowMatrix_apply (d : ArchDir) (i j : Fin 2) :
    HasDerivAt (fun t : ℝ => (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) i j) (archDirMatrix d i j) 0 := by
  cases d <;> fin_cases i <;> fin_cases j <;>
    simp only [archFlowMatrix, archDirMatrix, splitTorusGL2_coe, unipotentGL2_coe, lowerUnipotentGL2_coe,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first
      | exact hasDerivAt_const _ _
      | exact hasDerivAt_id _
      | simpa using Real.hasDerivAt_exp 0
      | exact ((Real.hasDerivAt_exp (-(0 : ℝ))).comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))).congr_deriv (by simp)

/--
@isnad1 id=eq.2h4v.s10.4331e01f868f from=translated src=- shape=10ade2f5 vocab=bb505267
-/
theorem archRealLiftAt_mul_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) {e : Fin 2 → Fin 2 → ℝ}
    (h : (Matrix.of e).det ≠ 0) (m : GL (Fin 2) ℝ) :
    archRealLiftAt hw e * archRealGLAt hw m =
      archRealLiftAt hw (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℝ))) := by
  have hm : ((m : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero
  have h' : (Matrix.of (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℝ)))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero h hm
  rw [archRealLiftAt_of_det_ne_zero hw h, archRealLiftAt_of_det_ne_zero hw h', ← map_mul]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

/--
@isnad1 id=contdiff.0h1v.s9.119369c5dcb5 from=translated src=- shape=3ca30c2e vocab=d5646f01
-/
theorem contDiff_of_symm_mul_const (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of.symm (Matrix.of e * A) : Fin 2 → Fin 2 → ℝ) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply ℝ ℝ k).comp (contDiff_apply ℝ (Fin 2 → ℝ) i)).mul contDiff_const

/--
@isnad1 id=hasderiv.0h2v.s10.05214c1de1ab from=translated src=- shape=14a05a1d vocab=f5a9200e
-/
theorem hasDerivAt_of_symm_mul_archFlowMatrix (e : Fin 2 → Fin 2 → ℝ) (d : ArchDir) :
    HasDerivAt
      (fun t : ℝ => (Matrix.of.symm (Matrix.of e * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)) :
        Fin 2 → Fin 2 → ℝ))
      (Matrix.of.symm (Matrix.of e * archDirMatrix d)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_archFlowMatrix_apply d k j).const_mul (e i k)

/--
@isnad1 id=eq.0h2v.s9.944c8919988c from=translated src=- shape=8ae2c168 vocab=535ffb33
-/
theorem of_symm_mul_archFlowMatrix_zero (e : Fin 2 → Fin 2 → ℝ) (d : ArchDir) :
    (Matrix.of.symm (Matrix.of e * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ)) : Fin 2 → Fin 2 → ℝ) = e := by
  rw [archFlowMatrix_zero, Units.val_one, mul_one, Equiv.symm_apply_apply]

/--
@isnad1 id=isarchsm.2h4v.s5.056792636e07 from=translated src=- shape=8b9017e4 vocab=dc1b6a04
-/
theorem IsArchSmoothAt.archDerivAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (d : ArchDir) : IsArchSmoothAt hw (archDerivAt hw d φ) := by
  intro g
  have hΦ := hφ g
  have hopen := isOpen_setOf_det_ne_zero
  refine contDiffOn_infty.2 fun n => ?_
  refine ((hΦ.fderiv_of_isOpen hopen (by exact_mod_cast le_top)).clm_apply
    ((contDiff_of_symm_mul_const (archDirMatrix d)).contDiffOn.of_le (by exact_mod_cast le_top))).congr ?_
  intro e he
  have hdiff : HasFDerivAt (fun e' => φ (g * archRealLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) e)
      (Matrix.of.symm (Matrix.of e * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact ((hΦ.contDiffAt (hopen.mem_nhds he)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) =
      fun t : ℝ => φ (g * archRealLiftAt hw
        (Matrix.of.symm (Matrix.of e * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)))) := by
    funext t
    rw [archFlowAt, mul_assoc, archRealLiftAt_mul_archRealGLAt hw he]
  show deriv (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrix e d)).deriv

/--
@isnad1 id=eq.1h2v.s8.96aa4c417cd8 from=translated src=- shape=0f7a0381 vocab=6ecb32a2
-/
theorem archRealLiftAt_of_symm_one {w : InfinitePlace F} (hw : w.IsReal) :
    archRealLiftAt hw (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 1 := by
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  rw [archRealLiftAt_of_det_ne_zero hw hdet, ← map_one (archRealGLAt hw)]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

/--
@isnad1 id=differen.2h5v.s8.cddce1d744d7 from=translated src=- shape=4bc33a1d vocab=84fd2dcb
-/
theorem IsArchSmoothAt.differentiableAt_flow {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    DifferentiableAt ℝ (fun t : ℝ => φ (g * archFlowAt hw d t)) 0 := by
  have hopen := isOpen_setOf_det_ne_zero
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  have hdiff : DifferentiableAt ℝ (fun e' => φ (g * archRealLiftAt hw e'))
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact ((hφ g).contDiffAt (hopen.mem_nhds hdet)).differentiableAt (by simp)
  have hfun : (fun t : ℝ => φ (g * archFlowAt hw d t)) =
      fun t : ℝ => φ (g * archRealLiftAt hw
        (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
          (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)))) := by
    funext t
    rw [← archRealLiftAt_mul_archRealGLAt hw hdet, archRealLiftAt_of_symm_one, one_mul, archFlowAt]
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrix _ d)).differentiableAt

/--
@isnad1 id=eq.3h5v.s8.301660cd7f33 from=translated src=- shape=fde0201f vocab=7244a55c
-/
theorem archDerivAt_add {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) (d : ArchDir) :
    archDerivAt hw d (φ + ψ) = archDerivAt hw d φ + archDerivAt hw d ψ := by
  funext g
  show deriv (fun t : ℝ => (φ + ψ) (g * archFlowAt hw d t)) 0 =
    deriv (fun t : ℝ => φ (g * archFlowAt hw d t)) 0 + deriv (fun t : ℝ => ψ (g * archFlowAt hw d t)) 0
  simp only [Pi.add_apply]
  exact deriv_fun_add (hφ.differentiableAt_flow d g) (hψ.differentiableAt_flow d g)

/--
@isnad1 id=eq.1h5v.s7.e26433bf3cdc from=translated src=- shape=7c0209de vocab=4ea54c09
-/
theorem archDerivAt_smul {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (c : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : archDerivAt hw d (c • φ) = c • archDerivAt hw d φ := by
  funext g
  show deriv (fun t : ℝ => (c • φ) (g * archFlowAt hw d t)) 0 = c • deriv (fun t : ℝ => φ (g * archFlowAt hw d t)) 0
  simp only [Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

/--
@isnad1 id=eq.3h4v.s8.36710a1529fb from=translated src=- shape=a35753e9 vocab=a6931193
-/
theorem archCasimirAt_add {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) :
    archCasimirAt hw (φ + ψ) = archCasimirAt hw φ + archCasimirAt hw ψ := by
  simp only [archCasimirAt, archDerivAt_add hφ hψ, archDerivAt_add (hφ.archDerivAt .H) (hψ.archDerivAt .H),
    archDerivAt_add (hφ.archDerivAt .Fm) (hψ.archDerivAt .Fm)]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/--
@isnad1 id=eq.1h4v.s7.635cd03cb5ae from=translated src=- shape=e983c5f4 vocab=0585a6dd
-/
theorem archCasimirAt_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirAt hw (c • φ) = c • archCasimirAt hw φ := by
  simp only [archCasimirAt, archDerivAt_smul]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/--
@isnad1 id=isarchsm.3h4v.s7.3d83b8af6032 from=translated src=- shape=6c80c9c8 vocab=ee1cb44f
-/
theorem IsArchSmoothAt.add {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) : IsArchSmoothAt hw (φ + ψ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archRealLiftAt hw e) + ψ (g * archRealLiftAt hw e)) _
  exact (hφ g).add (hψ g)

/--
@isnad1 id=isarchsm.2h4v.s6.459ad1141e18 from=translated src=- shape=94d9e948 vocab=3efd4f61
-/
theorem IsArchSmoothAt.smul {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (c : ℂ) : IsArchSmoothAt hw (c • φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => c * φ (g * archRealLiftAt hw e)) _
  exact contDiffOn_const.mul (hφ g)

/--
@isnad1 id=isarchsm.2h3v.s6.f8f4748f885a from=translated src=- shape=f0e9f4cd vocab=f6b55638
-/
theorem IsArchSmoothAt.neg {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (-φ) := by
  rw [← neg_one_smul ℂ φ]
  exact hφ.smul (-1)

/--
@isnad1 id=isarchsm.3h4v.s7.3e3f1e0b8474 from=translated src=- shape=6c80c9c8 vocab=a68e8017
-/
theorem IsArchSmoothAt.sub {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) : IsArchSmoothAt hw (φ - ψ) := by
  rw [sub_eq_add_neg]
  exact hφ.add hψ.neg

theorem eq_of_glArch_eq_of_glFin_eq {x y : AdelicGL2 (𝓞 F) F}
    (h₁ : AdelicLevel.glArch (𝓞 F) F x = AdelicLevel.glArch (𝓞 F) F y)
    (h₂ : AdelicLevel.glFin (𝓞 F) F x = AdelicLevel.glFin (𝓞 F) F y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
  have h₂' := congrArg
    (fun m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
      (m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) h₂
  exact Prod.ext h₁' h₂'

/--
@isnad1 id=eq.2h4v.s11.da9ee50c27ae from=translated src=- shape=c456b241 vocab=7ec53c5e
-/
theorem archRealGLAt_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archRealGLAt hw m * k = k * archRealGLAt hw m := by
  have hfin : AdelicLevel.glFin (𝓞 F) F (archRealGLAt hw m) = 1 := glFin_adelicArchGLIncl F _
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, hk, mul_one, one_mul]
  · rw [map_mul, map_mul, hfin, mul_one, one_mul]

/--
@isnad1 id=eq.2h4v.s10.d5ea653afdc2 from=translated src=- shape=30bd4fe3 vocab=c9999b1e
-/
theorem archRealLiftAt_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsReal) (e : Fin 2 → Fin 2 → ℝ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archRealLiftAt hw e * k = k * archRealLiftAt hw e := by
  unfold archRealLiftAt
  split_ifs
  · exact archRealGLAt_mul_comm_of_glArch_eq_one hw _ hk
  · rw [one_mul, mul_one]

/--
@isnad1 id=eq.2h5v.s10.c7f2ee453ec5 from=translated src=- shape=8057e597 vocab=8113666b
-/
theorem archFlowAt_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archFlowAt hw d t * k = k * archFlowAt hw d t :=
  archRealGLAt_mul_comm_of_glArch_eq_one hw _ hk

/--
@isnad1 id=isarchsm.3h4v.s10.ae3138874e58 from=translated src=- shape=989b2c8c vocab=23581191
-/
theorem IsArchSmoothAt.comp_mul_right {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    IsArchSmoothAt hw fun g => φ (g * k) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archRealLiftAt hw e * k)) _
  have hfun : (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e * k)) =
      fun e => φ (g * k * archRealLiftAt hw e) := by
    funext e
    rw [mul_assoc, archRealLiftAt_mul_comm_of_glArch_eq_one hw e hk, ← mul_assoc]
  rw [hfun]
  exact hφ (g * k)

/--
@isnad1 id=eq.2h5v.s10.35a2db7c58b9 from=translated src=- shape=8c829493 vocab=a36d1b06
-/
theorem archDerivAt_comp_mul_right {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archDerivAt hw d (fun g => φ (g * k)) = fun g => archDerivAt hw d φ (g * k) := by
  funext g
  show deriv (fun t : ℝ => φ (g * archFlowAt hw d t * k)) 0 = deriv (fun t : ℝ => φ (g * k * archFlowAt hw d t)) 0
  congr 1
  funext t
  rw [mul_assoc, archFlowAt_mul_comm_of_glArch_eq_one hw d t hk, ← mul_assoc]

/--
@isnad1 id=eq.2h4v.s10.2550553655e2 from=translated src=- shape=1e15cf08 vocab=74788a93
-/
theorem archCasimirAt_comp_mul_right {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archCasimirAt hw (fun g => φ (g * k)) = fun g => archCasimirAt hw φ (g * k) := by
  rw [archCasimirAt, archCasimirAt, archDerivAt_comp_mul_right hw .H φ hk,
    archDerivAt_comp_mul_right hw .H (archDerivAt hw .H φ) hk, archDerivAt_comp_mul_right hw .Fm φ hk,
    archDerivAt_comp_mul_right hw .E (archDerivAt hw .Fm φ) hk]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

/--
@isnad1 id=eq.1h3v.s11.0a422e8d16d4 from=translated src=- shape=5a22bcf2 vocab=12c064e9
-/
theorem archRealGLAt_glEquivOfRingEquiv {w : InfinitePlace F} (hw : w.IsReal) (k : GL (Fin 2) w.Completion) :
    archRealGLAt hw (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) k) = adelicArchGLInclAt F w k := by
  show adelicArchGLInclAt F w
    (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) k)) =
      adelicArchGLInclAt F w k
  congr 1
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
  exact congrArg _ ((ringEquivRealOfIsReal hw).symm_apply_apply _)

def archRealProjAt {w : InfinitePlace F} (hw : w.IsReal) : AdelicGL2 (𝓞 F) F →* GL (Fin 2) ℝ :=
  (glEquivOfRingEquiv (ringEquivRealOfIsReal hw)).toMonoidHom.comp
    ((AdelicLevel.archComponent F w).comp (AdelicLevel.glArch (𝓞 F) F))

/--
@isnad1 id=eq.1h3v.s10.55180e68db49 from=translated src=- shape=11a9ae22 vocab=1bc3a8d7
-/
theorem archRealProjAt_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealProjAt hw (archRealGLAt hw m) = m := by
  have h1 : AdelicLevel.glArch (𝓞 F) F (archRealGLAt hw m) =
      archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :=
    glArch_adelicArchGLIncl F _
  have h2 : AdelicLevel.archComponent F w (AdelicLevel.glArch (𝓞 F) F (archRealGLAt hw m)) =
      glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
    rw [h1, archComponent_archGLIncl_self]
  show glEquivOfRingEquiv (ringEquivRealOfIsReal hw)
    (AdelicLevel.archComponent F w (AdelicLevel.glArch (𝓞 F) F (archRealGLAt hw m))) = m
  rw [h2]
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
  exact (ringEquivRealOfIsReal hw).apply_symm_apply _

/--
@isnad1 id=isarchsm.2h3v.s5.48f912dc8b3a from=translated src=- shape=c4f85946 vocab=a6e21e06
-/
theorem IsArchSmoothAt.archCasimirAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (archCasimirAt hw φ) := by
  unfold AutomorphicForm.archCasimirAt
  exact (((((hφ.archDerivAt .H).archDerivAt .H).smul _).sub ((hφ.archDerivAt .H).smul _)).add
    ((hφ.archDerivAt .Fm).archDerivAt .E)).neg

/--
@isnad1 id=isarchsm.2h4v.s8.9543ec647cdd from=translated src=- shape=84ccfe17 vocab=b648819c
-/
theorem IsArchSmoothAt.comp_mul_left {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (h : AdelicGL2 (𝓞 F) F) : IsArchSmoothAt hw fun g => φ (h * g) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (h * (g * archRealLiftAt hw e))) _
  simp only [← mul_assoc]
  exact hφ (h * g)

/--
@isnad1 id=eq.1h5v.s8.03ff2a915f09 from=translated src=- shape=e9f9c3ee vocab=fb2cb94d
-/
theorem archDerivAt_comp_mul_left {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : AdelicGL2 (𝓞 F) F) : archDerivAt hw d (fun g => φ (h * g)) = fun g => archDerivAt hw d φ (h * g) := by
  funext g
  show deriv (fun t : ℝ => φ (h * (g * archFlowAt hw d t))) 0 = deriv (fun t : ℝ => φ (h * g * archFlowAt hw d t)) 0
  simp only [mul_assoc]

/--
@isnad1 id=eq.1h4v.s8.de2ee97eda21 from=translated src=- shape=63af5840 vocab=5665553d
-/
theorem archCasimirAt_comp_mul_left {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : AdelicGL2 (𝓞 F) F) : archCasimirAt hw (fun g => φ (h * g)) = fun g => archCasimirAt hw φ (h * g) := by
  rw [archCasimirAt, archCasimirAt, archDerivAt_comp_mul_left hw .H φ h,
    archDerivAt_comp_mul_left hw .H (archDerivAt hw .H φ) h, archDerivAt_comp_mul_left hw .Fm φ h,
    archDerivAt_comp_mul_left hw .E (archDerivAt hw .Fm φ) h]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

end Flows

end AutomorphicForm

end
