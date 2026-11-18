import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_archRealLift3_mul_eq_mul_archRealLift3_conj.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_CubicInduction_archRealLift3_mul_eq_mul_archRealLift3_conj

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open _root_.LanglandsTunnell.CubicInduction

namespace LanglandsTunnell
namespace CubicInduction
export _root_.LanglandsTunnell.CubicInduction (AdelicGL archComponent3)
namespace ConjAsm
open _root_.LanglandsTunnell.CubicInduction open _root_.LanglandsTunnell

noncomputable def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

/--
@isnad1 id=eq.0h1v.s5.7eca1c436e45 from=translated src=- shape=ef803f15 vocab=a20e0d70
-/
theorem ofRealHom_apply (r : ℝ) : ofRealHom r = StandardKernel.ofReal r := rfl

/--
@isnad1 id=eq.0h1v.s6.b9546aad6ae6 from=translated src=- shape=df6fcc37 vocab=ead5f65d
-/
theorem realCoord_ofRealHom (r : ℝ) : StandardKernel.realCoord (ofRealHom r) = r := by
  rw [StandardKernel.realCoord_apply]
  show InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)).symm r) = r
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

/--
@isnad1 id=eq.0h1v.s6.9e7595047f50 from=translated src=- shape=bbaba395 vocab=ead5f65d
-/
theorem ofRealHom_realCoord (x : InfiniteAdeleRing ℚ) : ofRealHom (StandardKernel.realCoord x) = x := by
  rw [ofRealHom_apply]; exact StandardKernel.ofReal_realCoord x

/--
@isnad1 id=injectiv.0h0v.s5.4e86c2c09a11 from=translated src=- shape=185df354 vocab=37e982a1
-/
theorem realCoord_injective : Function.Injective (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) :=
  fun x y h => by rw [← ofRealHom_realCoord x, ← ofRealHom_realCoord y, h]

/--
@isnad1 id=eq.0h1v.s8.2f9bbb4a6e5b from=translated src=- shape=cfc5d8d3 vocab=4798b02e
-/
theorem archRealMat3_eq (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e = archMatrixInclN (Fin 3) ℚ ((Matrix.of e).map ofRealHom) := rfl

/--
@isnad1 id=isunit.1h1v.s8.19b9b81fa0a0 from=translated src=- shape=a77a2d64 vocab=f47d08f6
-/
theorem isUnit_archRealMat3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  have hdet : IsUnit ((Matrix.of e).map ofRealHom) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 he).map ofRealHom
  rw [archRealMat3_eq]
  exact hdet.map (archMatrixInclHomN (Fin 3) ℚ)

/--
@isnad1 id=eq.1h1v.s8.d19d82c9834d from=translated src=- shape=5b5769f3 vocab=87b8d846
-/
theorem coe_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (WhittakerBlock.archRealLift3 e : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dite_eq_left (isUnit_archRealMat3 he)]
  exact (isUnit_archRealMat3 he).unit_spec

/--
@isnad1 id=eq.0h3v.s6.cb0d34142fe5 from=translated src=- shape=b25d263e vocab=58d1ae61
-/
theorem fst_archRealMat3 (e : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    (WhittakerBlock.archRealMat3 e i j).1 = ofRealHom (e i j) := by
  rw [archRealMat3_eq, ← AdelicLevel.adeleArch_apply, adeleArch_archMatrixInclN]; rfl

/--
@isnad1 id=eq.0h3v.s8.a05347389bd5 from=translated src=- shape=efc644b0 vocab=eca9b404
-/
theorem snd_archRealMat3 (e : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    (WhittakerBlock.archRealMat3 e i j).2 = (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j := by
  rw [archRealMat3_eq, ← AdelicLevel.adeleFin_apply, adeleFin_archMatrixInclN]

end LanglandsTunnell.CubicInduction.ConjAsm

open LanglandsTunnell.CubicInduction.ConjAsm in

/--
@isnad1 id=and.1h2v.s11.6fa94c21313c from=translated src=- shape=4900aa70 vocab=f4e62cb2
-/
theorem solution
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (m : Fin 3 → Fin 3 → ℝ) (hm : (Matrix.of m).det ≠ 0) :
    (AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g)).det ≠ 0 ∧
    WhittakerBlock.archRealLift3 m * g =
      g * WhittakerBlock.archRealLift3 (fun a b =>
        ((AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g))⁻¹ * Matrix.of m *
          AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g)) a b) := by
  set c : Matrix (Fin 3) (Fin 3) ℝ := AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g) with hc

  have hcinv : c * AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ g)⁻¹ = 1 := by
    rw [hc, ← StandardKernel.realMat_mul, mul_inv_cancel, StandardKernel.realMat_one]
  have hcdet : IsUnit c.det := by
    have h := congrArg Matrix.det hcinv
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact IsUnit.of_mul_eq_one _ h
  have hcdet0 : c.det ≠ 0 := hcdet.ne_zero
  refine ⟨hcdet0, ?_⟩
  set m' : Fin 3 → Fin 3 → ℝ := fun a b => (c⁻¹ * Matrix.of m * c) a b with hm'def
  have hofm' : Matrix.of m' = c⁻¹ * Matrix.of m * c := by ext a b; rfl
  have hm' : (Matrix.of m').det ≠ 0 := by
    rw [hofm', Matrix.det_mul, Matrix.det_mul]
    exact (((Matrix.isUnit_nonsing_inv_det c hcdet).mul (isUnit_iff_ne_zero.2 hm)).mul hcdet).ne_zero

  set A : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) :=
    ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) with hA
  have hAc : A.map StandardKernel.realCoord = c := by rw [hc, StandardKernel.realMat_eq]
  have hA1 : ∀ i j, ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 = A i j := fun i j => rfl

  have hreal : Matrix.of m * c = c * Matrix.of m' := by
    rw [hofm', ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hcdet, Matrix.one_mul]

  have harch : (Matrix.of m).map ofRealHom * A = A * (Matrix.of m').map ofRealHom := by
    have hinj : Function.Injective (fun M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) => M.map StandardKernel.realCoord) :=
      fun M N h => Matrix.ext fun i j => realCoord_injective (by
        have := congrFun (congrFun h i) j; simpa [Matrix.map_apply] using this)
    apply hinj
    show ((Matrix.of m).map ofRealHom * A).map StandardKernel.realCoord = (A * (Matrix.of m').map ofRealHom).map StandardKernel.realCoord
    have hid : ∀ M : Matrix (Fin 3) (Fin 3) ℝ, (M.map ofRealHom).map StandardKernel.realCoord = M := fun M => by
      ext i j; simp only [Matrix.map_apply, realCoord_ofRealHom]
    rw [Matrix.map_mul, Matrix.map_mul, hid, hid, hAc]
    exact hreal

  have hmat : WhittakerBlock.archRealMat3 m * (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * WhittakerBlock.archRealMat3 m' := by
    ext i j
    refine Prod.ext ?_ ?_
    ·
      have h1 : (WhittakerBlock.archRealMat3 m * (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) i j
          = ∑ k, WhittakerBlock.archRealMat3 m i k * (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) k j := Matrix.mul_apply
      have h2 : ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * WhittakerBlock.archRealMat3 m') i j
          = ∑ k, (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i k * WhittakerBlock.archRealMat3 m' k j := Matrix.mul_apply
      rw [h1, h2]
      change AdelicLevel.adeleArch (𝓞 ℚ) ℚ (∑ k, WhittakerBlock.archRealMat3 m i k * (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) k j)
        = AdelicLevel.adeleArch (𝓞 ℚ) ℚ (∑ k, (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i k * WhittakerBlock.archRealMat3 m' k j)
      simp only [map_sum, map_mul, AdelicLevel.adeleArch_apply, fst_archRealMat3, hA1]
      have := congrFun (congrFun harch i) j
      rw [Matrix.mul_apply, Matrix.mul_apply] at this
      simpa only [Matrix.map_apply, Matrix.of_apply] using this
    ·
      have h1 : (WhittakerBlock.archRealMat3 m * (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) i j
          = ∑ k, WhittakerBlock.archRealMat3 m i k * (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) k j := Matrix.mul_apply
      have h2 : ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * WhittakerBlock.archRealMat3 m') i j
          = ∑ k, (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i k * WhittakerBlock.archRealMat3 m' k j := Matrix.mul_apply
      rw [h1, h2]
      change AdelicLevel.adeleFin (𝓞 ℚ) ℚ (∑ k, WhittakerBlock.archRealMat3 m i k * (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) k j)
        = AdelicLevel.adeleFin (𝓞 ℚ) ℚ (∑ k, (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i k * WhittakerBlock.archRealMat3 m' k j)
      simp only [map_sum, map_mul, AdelicLevel.adeleFin_apply, snd_archRealMat3]
      have e1 : ∑ k, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i k * ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) k j).2
          = ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 := by
        rw [Finset.sum_eq_single i (fun k _ hk => by rw [Matrix.one_apply_ne (Ne.symm hk), zero_mul]) (fun h => absurd (Finset.mem_univ i) h)]
        rw [Matrix.one_apply_eq, one_mul]
      have e2 : ∑ k, ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i k).2 * (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) k j
          = ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 := by
        rw [Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero]) (fun h => absurd (Finset.mem_univ j) h)]
        rw [Matrix.one_apply_eq, mul_one]
      rw [e1, e2]

  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_archRealLift3 hm, coe_archRealLift3 hm']
  exact hmat
