import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfOrderData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul
set_option autoImplicit false

open scoped TensorProduct

namespace HopfOrder
export _root_.HopfOrder (tensorSqHom tensorSqHom_tmul baseChangeEquiv baseChangeEquiv_tmul counitS algebraMap_counitS comulS tensorSqHom_comulS moduleFlat_of_finite hopfAlgebraOfFinite)
open _root_.HopfOrder
namespace Points


open WithConv

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
  (S : Subalgebra R A) [Module.Finite R ↥S]
  {L : Type*} [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  (P : Subalgebra R L) (hP : ∀ x : L, IsIntegral R x → x ∈ P)

noncomputable def res (f : A →ₐ[K] L) : ↥S →ₐ[R] ↥P :=
  ((f.restrictScalars R).comp S.val).codRestrict P
    (fun x => hP _ ((Algebra.IsIntegral.isIntegral (R := R) x).map ((f.restrictScalars R).comp S.val)))

/--
@isnad1 id=eq.1h8v.s10.a8271e01bb2f from=translated src=- shape=11be6796 vocab=f61289d7
-/
@[scoped simp] theorem coe_res_apply (f : A →ₐ[K] L) (x : ↥S) : ((res S P hP f x : ↥P) : L) = f (x : A) := rfl

private noncomputable def _root_.HopfOrder.Points.ext (hspan : Submodule.span K (S : Set A) = ⊤) (g : ↥S →ₐ[R] ↥P) : A →ₐ[K] L :=
  haveI := moduleFlat_of_finite (K := K) S
  (AlgHom.liftEquiv R K ↥S L (P.val.comp g)).comp
    ((baseChangeEquiv S hspan).symm : A →ₐ[K] K ⊗[R] ↥S)

export _root_.HopfOrder.Points (ext)
/--
@isnad1 id=eq.1h9v.s11.e1a4f8d899e9 from=translated src=- shape=1eee506b vocab=9fdf30cc
-/
theorem ext_baseChangeEquiv_tmul (hspan : Submodule.span K (S : Set A) = ⊤) (g : ↥S →ₐ[R] ↥P)
    (k : K) (s : ↥S) :
    haveI := moduleFlat_of_finite (K := K) S
    ext S P hspan g (baseChangeEquiv S hspan (k ⊗ₜ[R] s)) = k • ((g s : ↥P) : L) := by
  haveI := moduleFlat_of_finite (K := K) S
  simp only [ext, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
    AlgHom.liftEquiv_tmul, Subalgebra.coe_val]

/--
@isnad1 id=eq.1h8v.s10.6bdabf5a05fa from=translated src=- shape=ba6cbf1a vocab=5201d3e4
-/
theorem ext_coe (hspan : Submodule.span K (S : Set A) = ⊤) (g : ↥S →ₐ[R] ↥P) (s : ↥S) :
    ext S P hspan g (s : A) = ((g s : ↥P) : L) := by
  haveI := moduleFlat_of_finite (K := K) S
  have h := ext_baseChangeEquiv_tmul S P hspan g 1 s
  rwa [baseChangeEquiv_tmul, one_smul, one_smul] at h

/--
@isnad1 id=eq.2h7v.s10.7a60cb56a4e8 from=translated src=- shape=a5a41d37 vocab=3f769984
-/
theorem res_ext (hspan : Submodule.span K (S : Set A) = ⊤) (g : ↥S →ₐ[R] ↥P) :
    res S P hP (ext S P hspan g) = g := by
  apply AlgHom.ext
  intro s
  apply Subtype.ext
  rw [coe_res_apply, ext_coe]

/--
@isnad1 id=eq.2h7v.s9.54f24d754274 from=translated src=- shape=ab9f5600 vocab=3f769984
-/
theorem ext_res (hspan : Submodule.span K (S : Set A) = ⊤) (f : A →ₐ[K] L) :
    ext S P hspan (res S P hP f) = f := by
  haveI := moduleFlat_of_finite (K := K) S
  apply AlgHom.ext
  intro a
  obtain ⟨z, rfl⟩ := (baseChangeEquiv S hspan).surjective a
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul k s =>
    rw [ext_baseChangeEquiv_tmul, coe_res_apply, baseChangeEquiv_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

noncomputable def equiv (hspan : Submodule.span K (S : Set A) = ⊤) : (A →ₐ[K] L) ≃ (↥S →ₐ[R] ↥P) where
  toFun := res S P hP
  invFun := ext S P hspan
  left_inv := ext_res S P hP hspan
  right_inv := res_ext S P hP hspan

/--
@isnad1 id=eq.1h9v.s12.8bb92e0096ab from=translated src=- shape=6cb168cb vocab=2e4636ac
-/
theorem val_lift_res_res (f g : A →ₐ[K] L) (z : ↥S ⊗[R] ↥S) :
    ((Algebra.TensorProduct.lift (res S P hP f) (res S P hP g) (fun _ _ => Commute.all _ _) z : ↥P) : L)
      = Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) (tensorSqHom S z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s t =>
    rw [Algebra.TensorProduct.lift_tmul, tensorSqHom_tmul, Algebra.TensorProduct.lift_tmul,
      Subalgebra.coe_mul, coe_res_apply, coe_res_apply]
  | add x y hx hy => rw [map_add, map_add, Subalgebra.coe_add, map_add, hx, hy]

variable (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)

/--
@isnad1 id=eq.4h8v.s13.61783d5d9acc from=translated src=- shape=c93e2f6e vocab=e38eb774
-/
theorem res_mul (f g : A →ₐ[K] L) :
    letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
    toConv (res S P hP (ofConv (toConv f * toConv g))) = toConv (res S P hP f) * toConv (res S P hP g) := by
  haveI := moduleFlat_of_finite (K := K) S
  letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  change ((toConv f * toConv g) : WithConv (A →ₐ[K] L)) (x : A)
    = (((toConv (res S P hP f) * toConv (res S P hP g) : WithConv (↥S →ₐ[R] ↥P)) x : ↥P) : L)
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply]
  change _ = ((Algebra.TensorProduct.lift (res S P hP f) (res S P hP g) _ (comulS hcomul x) : ↥P) : L)
  rw [val_lift_res_res, tensorSqHom_comulS]

/--
@isnad1 id=eq.4h6v.s13.129fc575be22 from=translated src=- shape=d2f8a14a vocab=1862666b
-/
theorem res_one :
    letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
    toConv (res S P hP (ofConv (1 : WithConv (A →ₐ[K] L)))) = 1 := by
  haveI := moduleFlat_of_finite (K := K) S
  letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  change ((1 : WithConv (A →ₐ[K] L))) (x : A) = (((1 : WithConv (↥S →ₐ[R] ↥P)) x : ↥P) : L)
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply]
  change _ = ((algebraMap R ↥P (counitS hcounit x) : ↥P) : L)
  rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply R K L, algebraMap_counitS]

end Points
open scoped _root_.P2MW.S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul.HopfOrder.Points
end HopfOrder
open scoped _root_.P2MW.S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul.HopfOrder.Points _root_.P2MW.S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul.HopfOrder

/--
@isnad1 id=ex.5h6v.s14.a1684175b723 from=translated src=- shape=9ade7be3 vocab=741ddc66
-/
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    {L : Type*} [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (P : Subalgebra R L) (hP : ∀ x : L, IsIntegral R x → x ∈ P) :
    letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
    ∃ e : (A →ₐ[K] L) ≃ (↥S →ₐ[R] ↥P),
      (∀ (f : A →ₐ[K] L) (x : ↥S), ((e f x : ↥P) : L) = f (x : A)) ∧
      (∀ f g : A →ₐ[K] L,
          WithConv.toConv (e (WithConv.ofConv (WithConv.toConv f * WithConv.toConv g)))
            = WithConv.toConv (e f) * WithConv.toConv (e g)) ∧
      WithConv.toConv (e (WithConv.ofConv (1 : WithConv (A →ₐ[K] L)))) = 1 :=
  ⟨HopfOrder.Points.equiv S P hP hspan, fun _ _ => rfl,
    HopfOrder.Points.res_mul S P hP hcomul hanti hcounit, HopfOrder.Points.res_one S P hP hcomul hanti hcounit⟩
