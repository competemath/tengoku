import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Tengoku.Seed.Analysis.Calculus.ContDiff.Operations
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace R1ArchSmoothMulRight

open AutomorphicForm AutomorphicForm.StandardKernel LanglandsTunnell.CubicInduction WhittakerBlock

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v : InfinitePlace ℚ =>
    ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm : ℝ ≃+* v.Completion).toRingHom

/--
@isnad1 id=eq.0h1v.s5.39b22cc76688 from=translated src=- shape=ef803f15 vocab=52a38c35
-/
theorem ofRealHom_apply (r : ℝ) : ofRealHom r = ofReal r := rfl

/--
@isnad1 id=eq.0h1v.s6.6de393a9f561 from=translated src=- shape=bbaba395 vocab=a31f2a10
-/
theorem ofReal_realCoord' (x : InfiniteAdeleRing ℚ) : ofRealHom (realCoord x) = x := by
  rw [ofRealHom_apply, ofReal_realCoord]

/--
@isnad1 id=eq.0h1v.s8.62f335a51d1a from=translated src=- shape=cfc5d8d3 vocab=3e15d52b
-/
theorem archRealMat3_eq (e : Fin 3 → Fin 3 → ℝ) :
    archRealMat3 e = archMatrixInclN (Fin 3) ℚ ((Matrix.of e).map ofRealHom) := rfl

/--
@isnad1 id=isunit.1h1v.s8.19b9b81fa0a0 from=translated src=- shape=a77a2d64 vocab=f47d08f6
-/
theorem isUnit_archRealMat3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    IsUnit (archRealMat3 e) := by
  have h1 : IsUnit ((Matrix.of e).map ofRealHom) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr he).map _
  rw [archRealMat3_eq]
  exact h1.map (archMatrixInclHomN (Fin 3) ℚ)

/--
@isnad1 id=eq.1h1v.s8.d19d82c9834d from=translated src=- shape=5b5769f3 vocab=87b8d846
-/
theorem coe_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    ((archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = archRealMat3 e := by
  unfold archRealLift3
  rw [dite_eq_left (isUnit_archRealMat3 he)]
  exact (isUnit_archRealMat3 he).unit_spec

def finPart (k : AdelicGL 3 (𝓞 ℚ) ℚ) : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) k

def realPart (k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) ℝ :=
  realMat (archComponentN (Fin 3) (𝓞 ℚ) ℚ k)

/--
@isnad1 id=ne.0h1v.s5.da489819fe93 from=translated src=- shape=7e3207b9 vocab=ec81da0f
-/
theorem det_realPart_ne_zero (k : AdelicGL 3 (𝓞 ℚ) ℚ) : (realPart k).det ≠ 0 := by
  have h : IsUnit (realPart k) := (realGL (archComponentN (Fin 3) (𝓞 ℚ) ℚ k)).isUnit
  rw [Matrix.isUnit_iff_isUnit_det] at h
  exact h.ne_zero

/--
@isnad1 id=eq.0h1v.s10.0bb8f296d338 from=translated src=- shape=7ee185cd vocab=3d7475d5
-/
theorem coe_archComponentN_eq (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((archComponentN (Fin 3) (𝓞 ℚ) ℚ k : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
        Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = (realPart k).map ofRealHom := by
  ext i j
  rw [realPart, realMat_eq, Matrix.map_apply, Matrix.map_apply, ofReal_realCoord']

/--
@isnad1 id=eq.0h1v.s10.3724ddb9a918 from=translated src=- shape=b41dc500 vocab=f1fe90fe
-/
theorem coe_eq_arch_mul_fin (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      archMatrixInclN (Fin 3) ℚ
          ((archComponentN (Fin 3) (𝓞 ℚ) ℚ k : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
            Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) *
        finMatrixInclN (Fin 3) ℚ
          ((finPart k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
            Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  refine Prod.ext ?_ ?_
  · change AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) =
      AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((archMatrixInclN (Fin 3) ℚ _ * finMatrixInclN (Fin 3) ℚ _) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul, adeleArch_archMatrixInclN, adeleArch_finMatrixInclN]
    rw [← Matrix.mul_apply, Matrix.mul_one]
    rfl
  · change AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) =
      AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((archMatrixInclN (Fin 3) ℚ _ * finMatrixInclN (Fin 3) ℚ _) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul, adeleFin_archMatrixInclN, adeleFin_finMatrixInclN]
    rw [← Matrix.mul_apply, Matrix.one_mul]
    rfl

def subst (k : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => (Matrix.of e * realPart k) i j

/--
@isnad1 id=eq.0h2v.s8.61495f4614e3 from=translated src=- shape=b83c3112 vocab=b757ad8d
-/
theorem of_subst (k : AdelicGL 3 (𝓞 ℚ) ℚ) (e : Fin 3 → Fin 3 → ℝ) :
    Matrix.of (subst k e) = Matrix.of e * realPart k := rfl

/--
@isnad1 id=contdiff.0h1v.s8.b8b95d004c13 from=translated src=- shape=e112b650 vocab=92f9e821
-/
theorem contDiff_subst (k : AdelicGL 3 (𝓞 ℚ) ℚ) : ContDiff ℝ (⊤ : ℕ∞) (subst k) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [subst, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun l _ => (contDiff_apply_apply (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (E := ℝ) i l).mul contDiff_const

/--
@isnad1 id=mapsto.0h1v.s9.462bf29d51af from=translated src=- shape=bb73248e vocab=8a526b52
-/
theorem mapsTo_subst (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Set.MapsTo (subst k) {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0}
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  intro e he
  simp only [Set.mem_ofPred_eq] at he ⊢
  rw [of_subst, Matrix.det_mul]
  exact mul_ne_zero he (det_realPart_ne_zero k)

/--
@isnad1 id=eq.1h2v.s11.438ff547b5a5 from=translated src=- shape=76c01f33 vocab=c6503338
-/
theorem archRealLift3_mul (k : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    archRealLift3 e * k = finInclN (Fin 3) ℚ (finPart k) * archRealLift3 (subst k e) := by
  have he' : (Matrix.of (subst k e)).det ≠ 0 := mapsTo_subst k he
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_archRealLift3 he, coe_archRealLift3 he', coe_eq_arch_mul_fin k,
    coe_archComponentN_eq, archRealMat3_eq, archRealMat3_eq, ← mul_assoc, ← archMatrixInclN_mul,
    ← Matrix.map_mul, ← of_subst, archMatrixInclN_mul_finMatrixInclN]
  rfl

end R1ArchSmoothMulRight

end

open LanglandsTunnell.CubicInduction in
open R1ArchSmoothMulRight AutomorphicForm WhittakerBlock in
/--
@isnad1 id=isarchsm.1h2v.s8.531e8c637a0d from=translated src=- shape=f8f86371 vocab=2493b24a
-/
theorem solution (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hu : WhittakerBlock.IsArchSmooth3 u) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.IsArchSmooth3 (fun g => u (g * k)) := by
  intro g
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      ((fun e : Fin 3 → Fin 3 → ℝ => u (g * finInclN (Fin 3) ℚ (finPart k) * archRealLift3 e)) ∘ subst k)
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
    (hu (g * finInclN (Fin 3) ℚ (finPart k))).comp (contDiff_subst k).contDiffOn (mapsTo_subst k)
  refine hcomp.congr fun e he => ?_
  simp only [Function.comp_apply]
  rw [mul_assoc g (archRealLift3 e) k, archRealLift3_mul k he, mul_assoc]
