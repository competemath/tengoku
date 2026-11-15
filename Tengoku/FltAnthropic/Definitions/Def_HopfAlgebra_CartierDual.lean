import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open Coalgebra
open scoped TensorProduct

universe u v

def _root_.Tengoku.FltAnthropic.CartierDual (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A] : Type (max u v) :=
  Module.Dual R A

namespace Tengoku.FltAnthropic.CartierDual

noncomputable section

section TransposeOfComul

variable (R : Type u) (A : Type v) [CommRing R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

omit [Coalgebra R A] in

/--
@isnad1 id=eq.0h4v.s11.87f959aeb709 from=translated src=- shape=3d73502f vocab=41b47e14
-/
theorem dualDistrib_tmul_eq_mul'_comp_map (f g : Module.Dual R A) :
    TensorProduct.dualDistrib R A A (f ⊗ₜ[R] g) =
      LinearMap.mul' R R ∘ₗ TensorProduct.map f g := by
  apply TensorProduct.ext'
  intro a b
  rw [TensorProduct.dualDistrib_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.mul'_apply]

/--
@isnad1 id=eq.0h4v.s9.8c0fa125b73e from=translated src=- shape=6342b984 vocab=196f4a18
-/
theorem convMul_ofConv (f g : Module.Dual R A) :
    (WithConv.toConv f * WithConv.toConv g).ofConv =
      LinearMap.mul' R R ∘ₗ TensorProduct.map f g ∘ₗ Coalgebra.comul :=
  congrArg WithConv.ofConv (LinearMap.convMul_def (WithConv.toConv f) (WithConv.toConv g))

/--
@isnad1 id=eq.0h5v.s11.b193cdf0ea9b from=translated src=- shape=c4f27a1a vocab=ed445c0c
-/
theorem convMul_ofConv_apply (f g : Module.Dual R A) (a : A) :
    (WithConv.toConv f * WithConv.toConv g).ofConv a =
      TensorProduct.dualDistrib R A A (f ⊗ₜ[R] g) (Coalgebra.comul a) := by
  rw [convMul_ofConv, dualDistrib_tmul_eq_mul'_comp_map]
  rfl

def dualMul : Module.Dual R A ⊗[R] Module.Dual R A →ₗ[R] Module.Dual R A :=
  (Coalgebra.comul (R := R) (A := A)).dualMap ∘ₗ TensorProduct.dualDistrib R A A

/--
@isnad1 id=eq.0h4v.s12.4c3d8c44ee6a from=translated src=- shape=c03f7eb8 vocab=0c5ca0c8
-/
theorem dualMul_tmul (f g : Module.Dual R A) :
    dualMul R A (f ⊗ₜ[R] g) =
      (Coalgebra.comul (R := R) (A := A)).dualMap (TensorProduct.dualDistrib R A A (f ⊗ₜ[R] g)) :=
  rfl

/--
@isnad1 id=eq.0h5v.s12.37c0f0b58c7e from=translated src=- shape=8aac380a vocab=96abe9e9
-/
theorem dualMul_pairing (f g : Module.Dual R A) (a : A) :
    dualMul R A (f ⊗ₜ[R] g) a =
      TensorProduct.dualDistrib R A A (f ⊗ₜ[R] g) (Coalgebra.comul a) := by
  rw [dualMul_tmul, LinearMap.dualMap_apply]

/--
@isnad1 id=eq.0h4v.s11.86e663b3f6ba from=translated src=- shape=1600f026 vocab=846039d2
-/
theorem dualMul_tmul_eq_convMul (f g : Module.Dual R A) :
    dualMul R A (f ⊗ₜ[R] g) = (WithConv.toConv f * WithConv.toConv g).ofConv := by
  ext a
  rw [convMul_ofConv_apply, dualMul_pairing]

/--
@isnad1 id=eq.0h2v.s6.f292b4867b83 from=translated src=- shape=09248f2f vocab=65175e19
-/
theorem convOne_ofConv_eq_counit :
    ((1 : WithConv (Module.Dual R A))).ofConv = Coalgebra.counit (R := R) (A := A) := by
  ext a
  show algebraMap R R (Coalgebra.counit a) = Coalgebra.counit a
  simp

end TransposeOfComul

section TransposeOfMul

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A]

/--
@isnad1 id=eq.0h3v.s13.f02381a0b672 from=translated src=- shape=76efa071 vocab=3e431ccf
-/
theorem dualDistribEquiv_apply_eq (w : Module.Dual R A ⊗[R] Module.Dual R A) :
    TensorProduct.dualDistribEquiv R A A w = TensorProduct.dualDistrib R A A w :=
  rfl

def dualComul : Module.Dual R A →ₗ[R] Module.Dual R A ⊗[R] Module.Dual R A :=
  (TensorProduct.dualDistribEquiv R A A).symm.toLinearMap ∘ₗ (LinearMap.mul' R A).dualMap

/--
@isnad1 id=eq.0h3v.s13.83ab1993be65 from=translated src=- shape=448ee61a vocab=c17d053b
-/
theorem dualDistrib_dualComul (φ : Module.Dual R A) :
    TensorProduct.dualDistrib R A A (dualComul R A φ) = (LinearMap.mul' R A).dualMap φ := by
  have h : dualComul R A φ =
      (TensorProduct.dualDistribEquiv R A A).symm ((LinearMap.mul' R A).dualMap φ) := rfl
  rw [h, ← dualDistribEquiv_apply_eq, LinearEquiv.apply_symm_apply]

/--
@isnad1 id=eq.0h5v.s13.722f264b33ee from=translated src=- shape=f68462c6 vocab=666328b3
-/
theorem dualComul_pairing (φ : Module.Dual R A) (a b : A) :
    TensorProduct.dualDistrib R A A (dualComul R A φ) (a ⊗ₜ[R] b) = φ (a * b) := by
  rw [dualDistrib_dualComul, LinearMap.dualMap_apply, LinearMap.mul'_apply]

/--
@isnad1 id=eq.1h4v.s13.f7b29fb94300 from=translated src=- shape=b07c486b vocab=c17d053b
-/
theorem dualComul_eq_of_dualDistrib_eq {φ : Module.Dual R A}
    {w : Module.Dual R A ⊗[R] Module.Dual R A}
    (h : TensorProduct.dualDistrib R A A w = (LinearMap.mul' R A).dualMap φ) :
    dualComul R A φ = w := by
  apply (TensorProduct.dualDistribEquiv R A A).injective
  rw [dualDistribEquiv_apply_eq, dualDistribEquiv_apply_eq, dualDistrib_dualComul, h]

/--
@isnad1 id=eq.0h2v.s12.49db6ae5cb8f from=translated src=- shape=fd3a0bfb vocab=cd9deb40
-/
theorem dualDistribEquiv_comp_dualComul :
    (TensorProduct.dualDistribEquiv R A A).toLinearMap ∘ₗ dualComul R A =
      (LinearMap.mul' R A).dualMap := by
  refine LinearMap.ext fun φ => ?_
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, dualDistribEquiv_apply_eq,
    dualDistrib_dualComul]

end TransposeOfMul

section UnitCounit

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

def dualOneEquiv : Module.Dual R R ≃ₗ[R] R := LinearMap.ringLmapEquivSelf R R R

/--
@isnad1 id=eq.0h2v.s9.ae26536fae5d from=translated src=- shape=46364abf vocab=fce5becd
-/
theorem dualOneEquiv_apply (ψ : Module.Dual R R) : dualOneEquiv R ψ = ψ 1 := rfl

/--
@isnad1 id=eq.0h3v.s9.f60b9d98bc45 from=translated src=- shape=adead85e vocab=cfa48993
-/
theorem dualOneEquiv_symm_apply (r x : R) : (dualOneEquiv R).symm r x = x * r := by
  have h1 : ((dualOneEquiv R).symm r) 1 = r := by
    have h := (dualOneEquiv R).apply_symm_apply r
    rwa [dualOneEquiv_apply] at h
  calc ((dualOneEquiv R).symm r) x = ((dualOneEquiv R).symm r) (x • (1 : R)) := by
        rw [smul_eq_mul, mul_one]
    _ = x • ((dualOneEquiv R).symm r) 1 := map_smul _ x 1
    _ = x * r := by rw [h1, smul_eq_mul]

def dualCounit : Module.Dual R A →ₗ[R] R :=
  (dualOneEquiv R).toLinearMap ∘ₗ (Algebra.linearMap R A).dualMap

/--
@isnad1 id=eq.0h3v.s9.1256a6bf07b9 from=translated src=- shape=c2ff4d74 vocab=cffdba3b
-/
theorem dualCounit_apply (φ : Module.Dual R A) : dualCounit R A φ = φ 1 := by
  have h : dualCounit R A φ = ((Algebra.linearMap R A).dualMap φ) 1 := rfl
  rw [h, LinearMap.dualMap_apply, Algebra.linearMap_apply, map_one]

def dualUnit : R →ₗ[R] Module.Dual R A :=
  (Coalgebra.counit (R := R) (A := A)).dualMap ∘ₗ (dualOneEquiv R).symm.toLinearMap

/--
@isnad1 id=eq.0h4v.s9.bc3e879d702c from=translated src=- shape=9daaed8e vocab=7474330c
-/
theorem dualUnit_apply (r : R) (a : A) :
    dualUnit R A r a = Coalgebra.counit (R := R) a * r := by
  have h : dualUnit R A r a = ((dualOneEquiv R).symm r) (Coalgebra.counit (R := R) a) := rfl
  rw [h, dualOneEquiv_symm_apply]

/--
@isnad1 id=eq.0h3v.s9.a42ed91d3cce from=translated src=- shape=c95ca650 vocab=e498a535
-/
theorem dualUnit_eq_smul_counit (r : R) :
    dualUnit R A r = r • Coalgebra.counit (R := R) (A := A) := by
  ext a
  rw [dualUnit_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm]

/--
@isnad1 id=eq.0h2v.s9.ac2ab9438cde from=translated src=- shape=f5450e04 vocab=2452f8f0
-/
theorem dualUnit_one : dualUnit R A 1 = Coalgebra.counit (R := R) (A := A) := by
  rw [dualUnit_eq_smul_counit, one_smul]

/--
@isnad1 id=eq.0h2v.s9.93fa22f440a6 from=translated src=- shape=e710bef8 vocab=48c2efe5
-/
theorem convOne_ofConv_eq_dualUnit_one :
    ((1 : WithConv (Module.Dual R A))).ofConv = dualUnit R A 1 := by
  rw [dualUnit_one, convOne_ofConv_eq_counit]

end UnitCounit

section DerivableAxioms

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

/--
@isnad1 id=eq.0h2v.s9.fc5d9e8b2b58 from=translated src=- shape=2c7988c3 vocab=94dabc9a
-/
theorem dualCounit_counit :
    dualCounit R A (Coalgebra.counit (R := R) (A := A)) = 1 := by
  rw [dualCounit_apply]
  exact Bialgebra.counit_one

/--
@isnad1 id=eq.0h4v.s12.5d99b76c212e from=translated src=- shape=2cbff588 vocab=301c2b53
-/
theorem dualCounit_dualMul (f g : Module.Dual R A) :
    dualCounit R A (dualMul R A (f ⊗ₜ[R] g)) = dualCounit R A f * dualCounit R A g := by
  rw [dualCounit_apply, dualCounit_apply, dualCounit_apply, dualMul_pairing,
    Bialgebra.comul_one, Algebra.TensorProduct.one_def, TensorProduct.dualDistrib_apply]

variable [Module.Finite R A] [Module.Free R A]

/--
@isnad1 id=eq.0h2v.s12.4f0ff5711259 from=translated src=- shape=4672f98b vocab=8f4c8ed8
-/
theorem dualComul_counit :
    dualComul R A (Coalgebra.counit (R := R) (A := A)) =
      (Coalgebra.counit (R := R) (A := A)) ⊗ₜ[R] (Coalgebra.counit (R := R) (A := A)) := by
  apply dualComul_eq_of_dualDistrib_eq
  apply TensorProduct.ext'
  intro a b
  rw [TensorProduct.dualDistrib_apply, LinearMap.dualMap_apply, LinearMap.mul'_apply,
    Bialgebra.counit_mul]

end DerivableAxioms

section HeldLayer

variable (R : Type u) (A : Type v)

structure DualBialgebraAxioms [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Free R A] : Prop where

  coassoc_apply : ∀ φ : Module.Dual R A,
    TensorProduct.assoc R (Module.Dual R A) (Module.Dual R A) (Module.Dual R A)
        ((dualComul R A).rTensor (Module.Dual R A) (dualComul R A φ)) =
      (dualComul R A).lTensor (Module.Dual R A) (dualComul R A φ)

  rTensor_counit_comul : ∀ φ : Module.Dual R A,
    (dualCounit R A).rTensor (Module.Dual R A) (dualComul R A φ) = (1 : R) ⊗ₜ[R] φ

  lTensor_counit_comul : ∀ φ : Module.Dual R A,
    (dualCounit R A).lTensor (Module.Dual R A) (dualComul R A φ) = φ ⊗ₜ[R] (1 : R)

  dualComul_dualMul : ∀ f g : Module.Dual R A,
    dualComul R A (dualMul R A (f ⊗ₜ[R] g)) =
      TensorProduct.map (dualMul R A) (dualMul R A)
        (TensorProduct.tensorTensorTensorComm R (Module.Dual R A) (Module.Dual R A)
          (Module.Dual R A) (Module.Dual R A) ((dualComul R A f) ⊗ₜ[R] (dualComul R A g)))

structure DualHopfAxioms [CommRing R] [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] [Module.Free R A] : Prop extends DualBialgebraAxioms R A where

  mul_antipode_rTensor_comul : ∀ φ : Module.Dual R A,
    dualMul R A
        (((HopfAlgebra.antipode R (A := A)).dualMap).rTensor (Module.Dual R A)
          (dualComul R A φ)) =
      dualUnit R A (dualCounit R A φ)

  mul_antipode_lTensor_comul : ∀ φ : Module.Dual R A,
    dualMul R A
        (((HopfAlgebra.antipode R (A := A)).dualMap).lTensor (Module.Dual R A)
          (dualComul R A φ)) =
      dualUnit R A (dualCounit R A φ)

@[implicit_reducible] def coalgebraOfDualBialgebraAxioms [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Free R A] (h : DualBialgebraAxioms R A) :
    Coalgebra R (Module.Dual R A) where
  comul := dualComul R A
  counit := dualCounit R A
  coassoc := by
    apply LinearMap.ext
    intro φ
    simpa using h.coassoc_apply φ
  rTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro φ
    simpa using h.rTensor_counit_comul φ
  lTensor_counit_comp_comul := by
    apply LinearMap.ext
    intro φ
    simpa using h.lTensor_counit_comul φ

end HeldLayer

end

noncomputable section

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A]

section PairingToolkit

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

omit [Module.Finite R A] [Module.Free R A] in

/--
@isnad1 id=eq.0h4v.s13.5fc54f3fdee5 from=translated src=- shape=07ba4003 vocab=ee503c6e
-/
theorem dualMul_apply_eq_pairing (w : Module.Dual R A ⊗[R] Module.Dual R A) (a : A) :
    dualMul R A w a = TensorProduct.dualDistrib R A A w (Coalgebra.comul a) := by
  show ((Coalgebra.comul (R := R) (A := A)).dualMap (TensorProduct.dualDistrib R A A w)) a = _
  rw [LinearMap.dualMap_apply]

/--
@isnad1 id=eq.0h3v.s15.14441ae3cca8 from=translated src=- shape=5a4739e4 vocab=3e431ccf
-/
theorem dualDistribEquiv_apply_eq₂ (w : Module.Dual R A ⊗[R] Module.Dual R (A ⊗[R] A)) :
    TensorProduct.dualDistribEquiv R A (A ⊗[R] A) w =
      TensorProduct.dualDistrib R A (A ⊗[R] A) w :=
  rfl

def dualDistribEquiv₃ :
    Module.Dual R A ⊗[R] (Module.Dual R A ⊗[R] Module.Dual R A) ≃ₗ[R]
      Module.Dual R (A ⊗[R] (A ⊗[R] A)) :=
  (TensorProduct.congr (LinearEquiv.refl R (Module.Dual R A))
      (TensorProduct.dualDistribEquiv R A A)).trans
    (TensorProduct.dualDistribEquiv R A (A ⊗[R] A))

/--
@isnad1 id=eq.0h6v.s15.5df598b4b6a0 from=translated src=- shape=3281a372 vocab=e125b874
-/
theorem dualDistribEquiv₃_tmul_pairing (f : Module.Dual R A)
    (v : Module.Dual R A ⊗[R] Module.Dual R A) (a : A) (z : A ⊗[R] A) :
    dualDistribEquiv₃ R A (f ⊗ₜ[R] v) (a ⊗ₜ[R] z) =
      f a * TensorProduct.dualDistrib R A A v z := by
  unfold dualDistribEquiv₃
  rw [LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    dualDistribEquiv_apply_eq, dualDistribEquiv_apply_eq₂, TensorProduct.dualDistrib_apply]

theorem eq_of_dualDistribEquiv₃_pairing
    {x y : Module.Dual R A ⊗[R] (Module.Dual R A ⊗[R] Module.Dual R A)}
    (h : ∀ a b c : A,
      dualDistribEquiv₃ R A x (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
        dualDistribEquiv₃ R A y (a ⊗ₜ[R] (b ⊗ₜ[R] c))) :
    x = y := by
  apply (dualDistribEquiv₃ R A).injective
  apply TensorProduct.ext_threefold'
  exact h

end PairingToolkit

section Coassoc

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

/--
@isnad1 id=eq.0h6v.s15.3dae1940f7dc from=translated src=- shape=9cb4186b vocab=5382c4f3
-/
theorem dualDistribEquiv₃_lTensor_dualComul (w : Module.Dual R A ⊗[R] Module.Dual R A)
    (a b c : A) :
    dualDistribEquiv₃ R A ((dualComul R A).lTensor (Module.Dual R A) w)
        (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      TensorProduct.dualDistrib R A A w (a ⊗ₜ[R] (b * c)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      rw [LinearMap.lTensor_tmul, dualDistribEquiv₃_tmul_pairing, dualComul_pairing,
        TensorProduct.dualDistrib_apply]
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

/--
@isnad1 id=eq.0h7v.s15.bffffc58eeb4 from=translated src=- shape=82d9d837 vocab=3f2738bb
-/
theorem dualDistribEquiv₃_assoc_tmul (u : Module.Dual R A ⊗[R] Module.Dual R A)
    (h : Module.Dual R A) (a b c : A) :
    dualDistribEquiv₃ R A
        (TensorProduct.assoc R (Module.Dual R A) (Module.Dual R A) (Module.Dual R A)
          (u ⊗ₜ[R] h)) (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      TensorProduct.dualDistrib R A A u (a ⊗ₜ[R] b) * h c := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
      rw [TensorProduct.assoc_tmul, dualDistribEquiv₃_tmul_pairing,
        TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply, mul_assoc]
  | add u₁ u₂ ih₁ ih₂ =>
      simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, add_mul, ih₁, ih₂]

/--
@isnad1 id=eq.0h6v.s16.1e96bfbe86c7 from=translated src=- shape=ae8c605a vocab=7f584686
-/
theorem dualDistribEquiv₃_assoc_rTensor_dualComul (w : Module.Dual R A ⊗[R] Module.Dual R A)
    (a b c : A) :
    dualDistribEquiv₃ R A
        (TensorProduct.assoc R (Module.Dual R A) (Module.Dual R A) (Module.Dual R A)
          ((dualComul R A).rTensor (Module.Dual R A) w)) (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      TensorProduct.dualDistrib R A A w ((a * b) ⊗ₜ[R] c) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      rw [LinearMap.rTensor_tmul, dualDistribEquiv₃_assoc_tmul, dualComul_pairing,
        TensorProduct.dualDistrib_apply]
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

/--
@isnad1 id=eq.0h3v.s16.45734e9df9b9 from=translated src=- shape=c19434c4 vocab=b84639f5
-/
theorem coassoc_dualComul (φ : Module.Dual R A) :
    TensorProduct.assoc R (Module.Dual R A) (Module.Dual R A) (Module.Dual R A)
        ((dualComul R A).rTensor (Module.Dual R A) (dualComul R A φ)) =
      (dualComul R A).lTensor (Module.Dual R A) (dualComul R A φ) := by
  apply eq_of_dualDistribEquiv₃_pairing
  intro a b c
  rw [dualDistribEquiv₃_assoc_rTensor_dualComul, dualDistribEquiv₃_lTensor_dualComul,
    dualComul_pairing, dualComul_pairing, mul_assoc]

end Coassoc

section CounitLaws

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

omit [Module.Finite R A] [Module.Free R A] in

/--
@isnad1 id=eq.0h4v.s13.bea948b12dd0 from=translated src=- shape=6fd8cfff vocab=69112168
-/
theorem lid_rTensor_dualCounit_apply (w : Module.Dual R A ⊗[R] Module.Dual R A) (a : A) :
    TensorProduct.lid R (Module.Dual R A) ((dualCounit R A).rTensor (Module.Dual R A) w) a =
      TensorProduct.dualDistrib R A A w ((1 : A) ⊗ₜ[R] a) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, dualCounit_apply,
        LinearMap.smul_apply, smul_eq_mul, TensorProduct.dualDistrib_apply]
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

omit [Module.Finite R A] [Module.Free R A] in

/--
@isnad1 id=eq.0h4v.s13.c07024b81b4a from=translated src=- shape=0737e644 vocab=963b4a98
-/
theorem rid_lTensor_dualCounit_apply (w : Module.Dual R A ⊗[R] Module.Dual R A) (a : A) :
    TensorProduct.rid R (Module.Dual R A) ((dualCounit R A).lTensor (Module.Dual R A) w) a =
      TensorProduct.dualDistrib R A A w (a ⊗ₜ[R] (1 : A)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, dualCounit_apply,
        LinearMap.smul_apply, smul_eq_mul, TensorProduct.dualDistrib_apply]
      ring
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

/--
@isnad1 id=eq.0h3v.s13.4bec1b054e55 from=translated src=- shape=6b3aa0a4 vocab=4f7cd92d
-/
theorem rTensor_dualCounit_dualComul (φ : Module.Dual R A) :
    (dualCounit R A).rTensor (Module.Dual R A) (dualComul R A φ) = (1 : R) ⊗ₜ[R] φ := by
  apply (TensorProduct.lid R (Module.Dual R A)).injective
  ext a
  rw [lid_rTensor_dualCounit_apply, dualComul_pairing, one_mul, TensorProduct.lid_tmul, one_smul]

/--
@isnad1 id=eq.0h3v.s13.4f124dde633f from=translated src=- shape=67d2f5eb vocab=c930ad4a
-/
theorem lTensor_dualCounit_dualComul (φ : Module.Dual R A) :
    (dualCounit R A).lTensor (Module.Dual R A) (dualComul R A φ) = φ ⊗ₜ[R] (1 : R) := by
  apply (TensorProduct.rid R (Module.Dual R A)).injective
  ext a
  rw [rid_lTensor_dualCounit_apply, dualComul_pairing, mul_one, TensorProduct.rid_tmul, one_smul]

end CounitLaws

section Multiplicativity

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

omit [Module.Finite R A] [Module.Free R A] in

/--
@isnad1 id=eq.0h5v.s16.bb64e3518eb5 from=translated src=- shape=719ea7d0 vocab=57e37701
-/
theorem dualDistrib_map_dualMul_dualMul
    (T : (Module.Dual R A ⊗[R] Module.Dual R A) ⊗[R]
      (Module.Dual R A ⊗[R] Module.Dual R A)) (a b : A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.map (dualMul R A) (dualMul R A) T) (a ⊗ₜ[R] b) =
      TensorProduct.dualDistrib R (A ⊗[R] A) (A ⊗[R] A)
        (TensorProduct.map (TensorProduct.dualDistrib R A A) (TensorProduct.dualDistrib R A A) T)
        (Coalgebra.comul a ⊗ₜ[R] Coalgebra.comul b) := by
  induction T using TensorProduct.induction_on with
  | zero => simp
  | tmul s t =>
      simp only [TensorProduct.map_tmul, TensorProduct.dualDistrib_apply,
        dualMul_apply_eq_pairing]
  | add T₁ T₂ ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

omit [Module.Finite R A] [Module.Free R A] in

/--
@isnad1 id=eq.0h2v.s16.8d9632719e03 from=translated src=- shape=01912f01 vocab=ccca5d1f
-/
theorem dualDistrib_map_dualDistrib_ttcomm :
    (TensorProduct.dualDistrib R (A ⊗[R] A) (A ⊗[R] A)) ∘ₗ
        (TensorProduct.map (TensorProduct.dualDistrib R A A)
          (TensorProduct.dualDistrib R A A)) ∘ₗ
        (TensorProduct.tensorTensorTensorComm R (Module.Dual R A) (Module.Dual R A)
          (Module.Dual R A) (Module.Dual R A)).toLinearMap =
      ((TensorProduct.tensorTensorTensorComm R A A A A).toLinearMap.dualMap) ∘ₗ
        (TensorProduct.dualDistrib R (A ⊗[R] A) (A ⊗[R] A)) ∘ₗ
        (TensorProduct.map (TensorProduct.dualDistrib R A A)
          (TensorProduct.dualDistrib R A A)) := by
  apply TensorProduct.ext_fourfold'
  intro p q r s
  apply TensorProduct.ext_fourfold'
  intro x₁ x₂ y₁ y₂
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.dualMap_apply, TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
    TensorProduct.dualDistrib_apply]
  ring

omit [Module.Finite R A] [Module.Free R A] in

/--
@isnad1 id=eq.0h4v.s17.82fe14779382 from=translated src=- shape=19802c00 vocab=570a4254
-/
theorem dualDistrib_map_dualDistrib_ttcomm_apply
    (T : (Module.Dual R A ⊗[R] Module.Dual R A) ⊗[R]
      (Module.Dual R A ⊗[R] Module.Dual R A))
    (W : (A ⊗[R] A) ⊗[R] (A ⊗[R] A)) :
    TensorProduct.dualDistrib R (A ⊗[R] A) (A ⊗[R] A)
        (TensorProduct.map (TensorProduct.dualDistrib R A A) (TensorProduct.dualDistrib R A A)
          (TensorProduct.tensorTensorTensorComm R (Module.Dual R A) (Module.Dual R A)
            (Module.Dual R A) (Module.Dual R A) T)) W =
      TensorProduct.dualDistrib R (A ⊗[R] A) (A ⊗[R] A)
        (TensorProduct.map (TensorProduct.dualDistrib R A A) (TensorProduct.dualDistrib R A A) T)
        (TensorProduct.tensorTensorTensorComm R A A A A W) := by
  have h := LinearMap.congr_fun
    (LinearMap.congr_fun (dualDistrib_map_dualDistrib_ttcomm R A) T) W
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap,
    LinearMap.dualMap_apply] using h

omit [Module.Finite R A] [Module.Free R A] in

/--
@isnad1 id=eq.0h5v.s15.ebd37f02d6b1 from=translated src=- shape=40cc7060 vocab=dab5f811
-/
theorem dualDistrib_dualMap_mul'_tmul (f g : Module.Dual R A)
    (W : (A ⊗[R] A) ⊗[R] (A ⊗[R] A)) :
    TensorProduct.dualDistrib R (A ⊗[R] A) (A ⊗[R] A)
        (((LinearMap.mul' R A).dualMap f) ⊗ₜ[R] ((LinearMap.mul' R A).dualMap g)) W =
      TensorProduct.dualDistrib R A A (f ⊗ₜ[R] g)
        (TensorProduct.map (LinearMap.mul' R A) (LinearMap.mul' R A) W) := by
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul Z W' =>
      simp only [TensorProduct.dualDistrib_apply, LinearMap.dualMap_apply,
        TensorProduct.map_tmul]
  | add W₁ W₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

omit [Module.Finite R A] [Module.Free R A] in

/--
@isnad1 id=eq.0h4v.s13.d1c988e768a8 from=translated src=- shape=3a479ec6 vocab=63eaed00
-/
theorem map_mul'_mul'_ttcomm (X Y : A ⊗[R] A) :
    TensorProduct.map (LinearMap.mul' R A) (LinearMap.mul' R A)
        (TensorProduct.tensorTensorTensorComm R A A A A (X ⊗ₜ[R] Y)) = X * Y := by
  induction X using TensorProduct.induction_on with
  | zero => simp
  | tmul x₁ x₂ =>
      induction Y using TensorProduct.induction_on with
      | zero => simp
      | tmul y₁ y₂ =>
          rw [TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
            LinearMap.mul'_apply, LinearMap.mul'_apply, Algebra.TensorProduct.tmul_mul_tmul]
      | add Y₁ Y₂ ihY₁ ihY₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add, ihY₁, ihY₂, mul_add]
  | add X₁ X₂ ihX₁ ihX₂ =>
      rw [TensorProduct.add_tmul, map_add, map_add, ihX₁, ihX₂, add_mul]

/--
@isnad1 id=eq.0h4v.s16.cfc685170a19 from=translated src=- shape=8e40b5b8 vocab=e09ca077
-/
theorem dualComul_dualMul_tmul (f g : Module.Dual R A) :
    dualComul R A (dualMul R A (f ⊗ₜ[R] g)) =
      TensorProduct.map (dualMul R A) (dualMul R A)
        (TensorProduct.tensorTensorTensorComm R (Module.Dual R A) (Module.Dual R A)
          (Module.Dual R A) (Module.Dual R A) ((dualComul R A f) ⊗ₜ[R] (dualComul R A g))) := by
  apply dualComul_eq_of_dualDistrib_eq
  apply TensorProduct.ext'
  intro a b
  rw [dualDistrib_map_dualMul_dualMul, dualDistrib_map_dualDistrib_ttcomm_apply,
    TensorProduct.map_tmul, dualDistrib_dualComul, dualDistrib_dualComul,
    dualDistrib_dualMap_mul'_tmul, map_mul'_mul'_ttcomm,
    LinearMap.dualMap_apply, LinearMap.mul'_apply, dualMul_pairing, Bialgebra.comul_mul]

end Multiplicativity

section BialgebraBundle

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

/--
@isnad1 id=dualbial.0h2v.s6.5a2884995e4e from=translated src=- shape=5f403a0d vocab=87a16f3a
-/
theorem dualBialgebraAxioms_of_finite_free : DualBialgebraAxioms R A where
  coassoc_apply := coassoc_dualComul R A
  rTensor_counit_comul := rTensor_dualCounit_dualComul R A
  lTensor_counit_comul := lTensor_dualCounit_dualComul R A
  dualComul_dualMul := dualComul_dualMul_tmul R A

@[implicit_reducible] def dualCoalgebraOfFiniteFree : Coalgebra R (Module.Dual R A) :=
  coalgebraOfDualBialgebraAxioms R A (dualBialgebraAxioms_of_finite_free R A)

end BialgebraBundle

section HopfDischarge

variable [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

omit [Module.Finite R A] [Module.Free R A] in

/--
@isnad1 id=eq.0h4v.s14.2a0fbe9e2ebe from=translated src=- shape=1edc52b3 vocab=838dbf92
-/
theorem dualDistrib_rTensor_dualMap (S : A →ₗ[R] A)
    (w : Module.Dual R A ⊗[R] Module.Dual R A) :
    TensorProduct.dualDistrib R A A ((S.dualMap).rTensor (Module.Dual R A) w) =
      (TensorProduct.dualDistrib R A A w) ∘ₗ (S.rTensor A) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      apply TensorProduct.ext'
      intro x y
      simp only [LinearMap.rTensor_tmul, TensorProduct.dualDistrib_apply, LinearMap.comp_apply,
        LinearMap.dualMap_apply]
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂, LinearMap.add_comp]

omit [Module.Finite R A] [Module.Free R A] in

/--
@isnad1 id=eq.0h4v.s14.77ca384fa7dd from=translated src=- shape=1edc52b3 vocab=0878a4cf
-/
theorem dualDistrib_lTensor_dualMap (S : A →ₗ[R] A)
    (w : Module.Dual R A ⊗[R] Module.Dual R A) :
    TensorProduct.dualDistrib R A A ((S.dualMap).lTensor (Module.Dual R A) w) =
      (TensorProduct.dualDistrib R A A w) ∘ₗ (S.lTensor A) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      apply TensorProduct.ext'
      intro x y
      simp only [LinearMap.lTensor_tmul, TensorProduct.dualDistrib_apply, LinearMap.comp_apply,
        LinearMap.dualMap_apply]
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂, LinearMap.add_comp]

/--
@isnad1 id=eq.0h3v.s14.c708e357a0bf from=translated src=- shape=3a0520d4 vocab=678c326c
-/
theorem dualMul_antipode_rTensor_dualComul (φ : Module.Dual R A) :
    dualMul R A
        (((HopfAlgebra.antipode R (A := A)).dualMap).rTensor (Module.Dual R A)
          (dualComul R A φ)) =
      dualUnit R A (dualCounit R A φ) := by
  ext a
  rw [dualMul_apply_eq_pairing, dualDistrib_rTensor_dualMap, LinearMap.comp_apply,
    dualDistrib_dualComul, LinearMap.dualMap_apply,
    HopfAlgebra.mul_antipode_rTensor_comul_apply, Algebra.algebraMap_eq_smul_one, map_smul,
    smul_eq_mul, dualUnit_apply, dualCounit_apply]

/--
@isnad1 id=eq.0h3v.s14.04481e8d2a29 from=translated src=- shape=3a0520d4 vocab=67266bfc
-/
theorem dualMul_antipode_lTensor_dualComul (φ : Module.Dual R A) :
    dualMul R A
        (((HopfAlgebra.antipode R (A := A)).dualMap).lTensor (Module.Dual R A)
          (dualComul R A φ)) =
      dualUnit R A (dualCounit R A φ) := by
  ext a
  rw [dualMul_apply_eq_pairing, dualDistrib_lTensor_dualMap, LinearMap.comp_apply,
    dualDistrib_dualComul, LinearMap.dualMap_apply,
    HopfAlgebra.mul_antipode_lTensor_comul_apply, Algebra.algebraMap_eq_smul_one, map_smul,
    smul_eq_mul, dualUnit_apply, dualCounit_apply]

/--
@isnad1 id=dualhopf.0h2v.s7.3ee519fc63f6 from=translated src=- shape=5f403a0d vocab=02ec1d88
-/
theorem dualHopfAxioms_of_finite_free : DualHopfAxioms R A where
  toDualBialgebraAxioms := dualBialgebraAxioms_of_finite_free R A
  mul_antipode_rTensor_comul := dualMul_antipode_rTensor_dualComul R A
  mul_antipode_lTensor_comul := dualMul_antipode_lTensor_dualComul R A

end HopfDischarge

end

noncomputable section

section ConvIdentities

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

/--
@isnad1 id=eq.0h5v.s13.189476c8ef3e from=translated src=- shape=443edf39 vocab=363167bc
-/
theorem dualMul_assoc (f g h : Module.Dual R A) :
    dualMul R A (dualMul R A (f ⊗ₜ[R] g) ⊗ₜ[R] h) =
      dualMul R A (f ⊗ₜ[R] dualMul R A (g ⊗ₜ[R] h)) := by
  simp only [dualMul_tmul_eq_convMul, WithConv.toConv_ofConv]
  exact congrArg WithConv.ofConv
    (mul_assoc (WithConv.toConv f) (WithConv.toConv g) (WithConv.toConv h))

/--
@isnad1 id=eq.0h3v.s12.737ac7f2d411 from=translated src=- shape=75885ea2 vocab=efe3c37f
-/
theorem dualMul_counit_tmul (f : Module.Dual R A) :
    dualMul R A ((Coalgebra.counit (R := R) (A := A)) ⊗ₜ[R] f) = f := by
  rw [dualMul_tmul_eq_convMul, ← convOne_ofConv_eq_counit R A, WithConv.toConv_ofConv]
  exact congrArg WithConv.ofConv (one_mul (WithConv.toConv f))

/--
@isnad1 id=eq.0h3v.s12.f9e3c65e307f from=translated src=- shape=e9e7b644 vocab=efe3c37f
-/
theorem dualMul_tmul_counit (f : Module.Dual R A) :
    dualMul R A (f ⊗ₜ[R] (Coalgebra.counit (R := R) (A := A))) = f := by
  rw [dualMul_tmul_eq_convMul, ← convOne_ofConv_eq_counit R A, WithConv.toConv_ofConv]
  exact congrArg WithConv.ofConv (mul_one (WithConv.toConv f))

/--
@isnad1 id=eq.0h4v.s12.f96f895778c4 from=translated src=- shape=d73c1edc vocab=86be33a5
-/
theorem dualMul_dualUnit_tmul (r : R) (f : Module.Dual R A) :
    dualMul R A (dualUnit R A r ⊗ₜ[R] f) = r • f := by
  rw [dualUnit_eq_smul_counit, ← TensorProduct.smul_tmul', map_smul, dualMul_counit_tmul]

/--
@isnad1 id=eq.0h4v.s12.1e88333067ba from=translated src=- shape=68ac02b8 vocab=86be33a5
-/
theorem dualMul_tmul_dualUnit (f : Module.Dual R A) (r : R) :
    dualMul R A (f ⊗ₜ[R] dualUnit R A r) = r • f := by
  rw [dualUnit_eq_smul_counit, TensorProduct.tmul_smul, map_smul, dualMul_tmul_counit]

/--
@isnad1 id=eq.0h4v.s12.fb0875bedf75 from=translated src=- shape=f9e453d3 vocab=bbc4b572
-/
theorem dualUnit_mul (r s : R) :
    dualUnit R A (r * s) = dualMul R A (dualUnit R A r ⊗ₜ[R] dualUnit R A s) := by
  rw [dualMul_tmul_dualUnit R A (dualUnit R A r) s, dualUnit_eq_smul_counit R A r,
    dualUnit_eq_smul_counit R A (r * s), smul_smul, mul_comm s r]

end ConvIdentities

section RingCarrier

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

@[reducible] def dualConvRing : Ring (Module.Dual R A) where
  __ := (inferInstance : AddCommMonoid (Module.Dual R A))
  __ := (inferInstance : AddCommGroup (Module.Dual R A))
  mul f g := dualMul R A (f ⊗ₜ[R] g)
  one := Coalgebra.counit (R := R) (A := A)
  mul_assoc := dualMul_assoc R A
  one_mul := dualMul_counit_tmul R A
  mul_one := dualMul_tmul_counit R A
  left_distrib f g h := by
    show dualMul R A (f ⊗ₜ[R] (g + h)) = dualMul R A (f ⊗ₜ[R] g) + dualMul R A (f ⊗ₜ[R] h)
    rw [TensorProduct.tmul_add, map_add]
  right_distrib f g h := by
    show dualMul R A ((f + g) ⊗ₜ[R] h) = dualMul R A (f ⊗ₜ[R] h) + dualMul R A (g ⊗ₜ[R] h)
    rw [TensorProduct.add_tmul, map_add]
  zero_mul f := by
    show dualMul R A ((0 : Module.Dual R A) ⊗ₜ[R] f) = 0
    rw [TensorProduct.zero_tmul, map_zero]
  mul_zero f := by
    show dualMul R A (f ⊗ₜ[R] (0 : Module.Dual R A)) = 0
    rw [TensorProduct.tmul_zero, map_zero]

/--
@isnad1 id=eq.0h2v.s8.47f1b1cb1db7 from=translated src=- shape=e9647793 vocab=cb4c5dcc
-/
theorem dualConvRing_one :
    letI : Ring (Module.Dual R A) := dualConvRing R A;
    (1 : Module.Dual R A) = Coalgebra.counit (R := R) (A := A) := rfl

/--
@isnad1 id=eq.0h4v.s12.e06a187d293d from=translated src=- shape=8b7b0b86 vocab=8595b776
-/
theorem dualConvRing_mul (f g : Module.Dual R A) :
    letI : Ring (Module.Dual R A) := dualConvRing R A;
    f * g = dualMul R A (f ⊗ₜ[R] g) := rfl

/--
@isnad1 id=eq.0h4v.s9.ceff37b1aa9e from=translated src=- shape=260f8665 vocab=ab896fff
-/
theorem dualConvRing_mul_eq_convMul (f g : Module.Dual R A) :
    letI : Ring (Module.Dual R A) := dualConvRing R A;
    f * g = (WithConv.toConv f * WithConv.toConv g).ofConv :=
  Eq.trans (dualConvRing_mul R A f g) (dualMul_tmul_eq_convMul R A f g)

@[reducible] def dualConvCommRing [IsCocomm R A] : CommRing (Module.Dual R A) where
  __ := dualConvRing R A
  mul_comm f g := by
    show dualMul R A (f ⊗ₜ[R] g) = dualMul R A (g ⊗ₜ[R] f)
    simp only [dualMul_tmul_eq_convMul]
    exact congrArg WithConv.ofConv (mul_comm (WithConv.toConv f) (WithConv.toConv g))

end RingCarrier

section AlgebraCarrier

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

attribute [local instance] dualConvRing

@[reducible] def dualConvAlgebra : Algebra R (Module.Dual R A) where
  toSMul := (inferInstance : SMul R (Module.Dual R A))
  algebraMap :=
    { toFun := fun r => dualUnit R A r
      map_one' := dualUnit_one R A
      map_mul' := fun r s => dualUnit_mul R A r s
      map_zero' := map_zero (dualUnit R A)
      map_add' := fun r s => map_add (dualUnit R A) r s }
  commutes' := fun r f => (dualMul_dualUnit_tmul R A r f).trans (dualMul_tmul_dualUnit R A f r).symm
  smul_def' := fun r f => (dualMul_dualUnit_tmul R A r f).symm

attribute [local instance] dualConvAlgebra

/--
@isnad1 id=eq.0h3v.s9.fe30fe86c4be from=translated src=- shape=2bf6acb5 vocab=09737b42
-/
theorem dualConvAlgebra_algebraMap (r : R) :
    algebraMap R (Module.Dual R A) r = dualUnit R A r := rfl

/--
@isnad1 id=eq.0h3v.s9.aef41674e72d from=translated src=- shape=6009b3c8 vocab=182057ee
-/
theorem dualConvAlgebra_algebraMap_eq_smul_counit (r : R) :
    algebraMap R (Module.Dual R A) r = r • Coalgebra.counit (R := R) (A := A) :=
  (dualConvAlgebra_algebraMap R A r).trans (dualUnit_eq_smul_counit R A r)

end AlgebraCarrier

section BialgebraPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A]

attribute [local instance] dualConvRing dualConvAlgebra dualCoalgebraOfFiniteFree

/--
@isnad1 id=eq.0h2v.s12.afa8bd6290b3 from=translated src=- shape=cf362a1b vocab=27aaec64
-/
theorem dualComul_counit_eq_tensorOne :
    dualComul R A (Coalgebra.counit (R := R) (A := A)) =
      (1 : Module.Dual R A ⊗[R] Module.Dual R A) := by
  rw [Algebra.TensorProduct.one_def]
  exact dualComul_counit R A

/--
@isnad1 id=eq.0h4v.s13.9b919b0a2d4a from=translated src=- shape=6a7e26b5 vocab=8795e59d
-/
theorem dualComul_dualMul_eq_mul (f g : Module.Dual R A) :
    dualComul R A (dualMul R A (f ⊗ₜ[R] g)) = dualComul R A f * dualComul R A g := by
  rw [dualComul_dualMul_tmul R A f g]
  generalize dualComul R A f = X
  generalize dualComul R A g = Y
  induction X using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
      induction Y using TensorProduct.induction_on with
      | zero => simp
      | tmul r s =>
          rw [TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul]
          exact (Algebra.TensorProduct.tmul_mul_tmul p r q s).symm
      | add Y₁ Y₂ ih₁ ih₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add, mul_add, ih₁, ih₂]
  | add X₁ X₂ ih₁ ih₂ =>
      rw [TensorProduct.add_tmul, map_add, map_add, add_mul, ih₁, ih₂]

@[reducible] def dualBialgebraOfFiniteFree : Bialgebra R (Module.Dual R A) :=
  Bialgebra.mk' R (Module.Dual R A)
    (dualCounit_counit R A)
    (fun {f g} => dualCounit_dualMul R A f g)
    (dualComul_counit_eq_tensorOne R A)
    (fun {f g} => dualComul_dualMul_eq_mul R A f g)

/--
@isnad1 id=eq.0h2v.s8.50348bfa00f8 from=translated src=- shape=13a85e89 vocab=8ced62a7
-/
theorem dualBialgebraOfFiniteFree_toAlgebra :
    (dualBialgebraOfFiniteFree R A).toAlgebra = dualConvAlgebra R A := rfl

/--
@isnad1 id=eq.0h2v.s9.f7fb8b9607f3 from=translated src=- shape=13a85e89 vocab=3c46cf15
-/
theorem dualBialgebraOfFiniteFree_toCoalgebra :
    (dualBialgebraOfFiniteFree R A).toCoalgebra = dualCoalgebraOfFiniteFree R A := rfl

end BialgebraPackage

section HopfPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A]

attribute [local instance] dualConvRing dualConvAlgebra dualCoalgebraOfFiniteFree

/--
@isnad1 id=eq.0h2v.s13.f445f40f391a from=translated src=- shape=a350a8e3 vocab=088d831d
-/
theorem dualConv_mul'_antipode_rTensor_dualComul :
    LinearMap.mul' R (Module.Dual R A) ∘ₗ
        ((HopfAlgebra.antipode R (A := A)).dualMap).rTensor (Module.Dual R A) ∘ₗ
        dualComul R A =
      Algebra.linearMap R (Module.Dual R A) ∘ₗ dualCounit R A := by
  refine LinearMap.ext fun φ => ?_
  simp only [LinearMap.comp_apply]
  show LinearMap.mul' R (Module.Dual R A)
      (((HopfAlgebra.antipode R (A := A)).dualMap).rTensor (Module.Dual R A)
        (dualComul R A φ)) =
    dualUnit R A (dualCounit R A φ)
  have hmul' : ∀ w : Module.Dual R A ⊗[R] Module.Dual R A,
      LinearMap.mul' R (Module.Dual R A) w = dualMul R A w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => exact LinearMap.mul'_apply
    | add w₁ w₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]
  rw [hmul']
  exact dualMul_antipode_rTensor_dualComul R A φ

/--
@isnad1 id=eq.0h2v.s13.bd4a70863e23 from=translated src=- shape=a350a8e3 vocab=01a71ca5
-/
theorem dualConv_mul'_antipode_lTensor_dualComul :
    LinearMap.mul' R (Module.Dual R A) ∘ₗ
        ((HopfAlgebra.antipode R (A := A)).dualMap).lTensor (Module.Dual R A) ∘ₗ
        dualComul R A =
      Algebra.linearMap R (Module.Dual R A) ∘ₗ dualCounit R A := by
  refine LinearMap.ext fun φ => ?_
  simp only [LinearMap.comp_apply]
  show LinearMap.mul' R (Module.Dual R A)
      (((HopfAlgebra.antipode R (A := A)).dualMap).lTensor (Module.Dual R A)
        (dualComul R A φ)) =
    dualUnit R A (dualCounit R A φ)
  have hmul' : ∀ w : Module.Dual R A ⊗[R] Module.Dual R A,
      LinearMap.mul' R (Module.Dual R A) w = dualMul R A w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => exact LinearMap.mul'_apply
    | add w₁ w₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂]
  rw [hmul']
  exact dualMul_antipode_lTensor_dualComul R A φ

@[reducible] def dualHopfAlgebraOfFiniteFree : HopfAlgebra R (Module.Dual R A) where
  toBialgebra := dualBialgebraOfFiniteFree R A
  antipode := (HopfAlgebra.antipode R (A := A)).dualMap
  mul_antipode_rTensor_comul := dualConv_mul'_antipode_rTensor_dualComul R A
  mul_antipode_lTensor_comul := dualConv_mul'_antipode_lTensor_dualComul R A

attribute [local instance] dualHopfAlgebraOfFiniteFree

/--
@isnad1 id=eq.0h2v.s11.1ca0ddf8ea05 from=translated src=- shape=49337157 vocab=96c005bd
-/
theorem dualHopfAlgebraOfFiniteFree_antipode :
    HopfAlgebra.antipode R (A := Module.Dual R A) =
      (HopfAlgebra.antipode R (A := A)).dualMap := rfl

end HopfPackage

end

noncomputable section

section PairingSwap

variable (R : Type u) (A : Type v) [CommRing R] [AddCommMonoid A] [Module R A]

/--
@isnad1 id=eq.0h5v.s13.f636079c6e73 from=translated src=- shape=19a9e02f vocab=40ae1abd
-/
theorem dualDistrib_comm_apply (w : Module.Dual R A ⊗[R] Module.Dual R A) (a b : A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.comm R (Module.Dual R A) (Module.Dual R A) w) (a ⊗ₜ[R] b) =
      TensorProduct.dualDistrib R A A w (b ⊗ₜ[R] a) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      rw [TensorProduct.comm_tmul, TensorProduct.dualDistrib_apply,
        TensorProduct.dualDistrib_apply]
      exact mul_comm (g a) (f b)
  | add w₁ w₂ ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

end PairingSwap

section Cocomm

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A]

/--
@isnad1 id=eq.0h5v.s14.288b6451154b from=translated src=- shape=cb5ecc5b vocab=91f04f5d
-/
theorem dualDistrib_comm_dualComul_pairing (φ : Module.Dual R A) (a b : A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.comm R (Module.Dual R A) (Module.Dual R A) (dualComul R A φ))
        (a ⊗ₜ[R] b) =
      φ (b * a) := by
  rw [dualDistrib_comm_apply, dualComul_pairing]

/--
@isnad1 id=eq.0h3v.s13.986065820df6 from=translated src=- shape=515ad60e vocab=0f1dc06a
-/
theorem comm_dualComul (φ : Module.Dual R A) :
    TensorProduct.comm R (Module.Dual R A) (Module.Dual R A) (dualComul R A φ) =
      dualComul R A φ := by
  symm
  apply dualComul_eq_of_dualDistrib_eq
  apply TensorProduct.ext'
  intro a b
  rw [dualDistrib_comm_dualComul_pairing, LinearMap.dualMap_apply, LinearMap.mul'_apply]
  exact congrArg φ (mul_comm b a)

/--
@isnad1 id=eq.0h2v.s12.0235ea007ec6 from=translated src=- shape=10303af6 vocab=b4225afd
-/
theorem comm_comp_dualComul :
    (TensorProduct.comm R (Module.Dual R A) (Module.Dual R A)).toLinearMap ∘ₗ dualComul R A =
      dualComul R A :=
  LinearMap.ext fun φ => comm_dualComul R A φ

/--
@isnad1 id=iscocomm.0h2v.s8.7c16a3f37baa from=translated src=- shape=13a02700 vocab=90e1ac07
-/
theorem dualCoalgebraOfFiniteFree_isCocomm :
    letI : Coalgebra R (Module.Dual R A) := dualCoalgebraOfFiniteFree R A
    Coalgebra.IsCocomm R (Module.Dual R A) := by
  letI : Coalgebra R (Module.Dual R A) := dualCoalgebraOfFiniteFree R A
  refine ⟨LinearMap.ext fun φ => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  show TensorProduct.comm R (Module.Dual R A) (Module.Dual R A) (dualComul R A φ) =
    dualComul R A φ
  exact comm_dualComul R A φ

end Cocomm

section CommBialgebraPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]

attribute [local instance] dualConvCommRing dualConvAlgebra dualCoalgebraOfFiniteFree

@[reducible] def dualCommBialgebraOfFiniteFree : Bialgebra R (Module.Dual R A) :=
  Bialgebra.mk' R (Module.Dual R A)
    (dualCounit_counit R A)
    (fun {f g} => dualCounit_dualMul R A f g)
    (dualComul_counit_eq_tensorOne R A)
    (fun {f g} => dualComul_dualMul_eq_mul R A f g)

/--
@isnad1 id=eq.0h2v.s8.b8cfa9cba54c from=translated src=- shape=c54fdaa8 vocab=284c1246
-/
theorem dualCommBialgebraOfFiniteFree_toAlgebra :
    (dualCommBialgebraOfFiniteFree R A).toAlgebra = dualConvAlgebra R A := rfl

/--
@isnad1 id=eq.0h2v.s9.ca8e5c9f838b from=translated src=- shape=c54fdaa8 vocab=b1a06bde
-/
theorem dualCommBialgebraOfFiniteFree_toCoalgebra :
    (dualCommBialgebraOfFiniteFree R A).toCoalgebra = dualCoalgebraOfFiniteFree R A := rfl

/--
@isnad1 id=eq.0h2v.s8.4f3b64b0f64e from=translated src=- shape=ce9b2e70 vocab=8adb5c50
-/
theorem dualCommBialgebraOfFiniteFree_eq_dualBialgebraOfFiniteFree :
    dualCommBialgebraOfFiniteFree R A = dualBialgebraOfFiniteFree R A := rfl

/--
@isnad1 id=iscocomm.0h2v.s8.d069d03e2f5b from=translated src=- shape=bae72e44 vocab=96b7884f
-/
theorem dualCommBialgebraOfFiniteFree_isCocomm :
    letI : Coalgebra R (Module.Dual R A) := (dualCommBialgebraOfFiniteFree R A).toCoalgebra
    Coalgebra.IsCocomm R (Module.Dual R A) := by
  letI : Coalgebra R (Module.Dual R A) := (dualCommBialgebraOfFiniteFree R A).toCoalgebra
  refine ⟨LinearMap.ext fun φ => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  show TensorProduct.comm R (Module.Dual R A) (Module.Dual R A) (dualComul R A φ) =
    dualComul R A φ
  exact comm_dualComul R A φ

end CommBialgebraPackage

section CommHopfPackage

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]

attribute [local instance] dualConvCommRing dualConvAlgebra dualCoalgebraOfFiniteFree

@[reducible] def dualCommHopfAlgebraOfFiniteFree : HopfAlgebra R (Module.Dual R A) where
  toBialgebra := dualCommBialgebraOfFiniteFree R A
  antipode := (HopfAlgebra.antipode R (A := A)).dualMap
  mul_antipode_rTensor_comul := dualConv_mul'_antipode_rTensor_dualComul R A
  mul_antipode_lTensor_comul := dualConv_mul'_antipode_lTensor_dualComul R A

/--
@isnad1 id=eq.0h2v.s9.6f2e3bdf3a7a from=translated src=- shape=c54fdaa8 vocab=50a4f395
-/
theorem dualCommHopfAlgebraOfFiniteFree_toBialgebra :
    (dualCommHopfAlgebraOfFiniteFree R A).toBialgebra = dualCommBialgebraOfFiniteFree R A := rfl

/--
@isnad1 id=eq.0h2v.s8.2a18bb1bc41b from=translated src=- shape=ce9b2e70 vocab=c8959647
-/
theorem dualCommHopfAlgebraOfFiniteFree_eq_dualHopfAlgebraOfFiniteFree :
    dualCommHopfAlgebraOfFiniteFree R A = dualHopfAlgebraOfFiniteFree R A := rfl

attribute [local instance] dualCommHopfAlgebraOfFiniteFree

/--
@isnad1 id=eq.0h2v.s11.6c1d69fa53bf from=translated src=- shape=b28035e7 vocab=a6322d64
-/
theorem dualCommHopfAlgebraOfFiniteFree_antipode :
    HopfAlgebra.antipode R (A := Module.Dual R A) =
      (HopfAlgebra.antipode R (A := A)).dualMap := rfl

end CommHopfPackage

end

noncomputable section

section Instances

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]

instance instAddCommGroup : AddCommGroup (CartierDual R A) :=
  inferInstanceAs (AddCommGroup (Module.Dual R A))

instance instModule : Module R (CartierDual R A) :=
  inferInstanceAs (Module R (Module.Dual R A))

instance instRing : Ring (CartierDual R A) :=
  { instAddCommGroup R A, dualConvRing R A with }

instance instCommRing [IsCocomm R A] : CommRing (CartierDual R A) :=
  { instRing R A with mul_comm := fun f g => (dualConvCommRing R A).mul_comm f g }

instance instAlgebra : Algebra R (CartierDual R A) :=
  { dualConvAlgebra R A with toSMul := (instModule R A).toDistribMulAction.toMulAction.toSMul }

instance instFunLike : FunLike (CartierDual R A) A R :=
  inferInstanceAs (FunLike (A →ₗ[R] R) A R)

/--
@isnad1 id=linearma.0h2v.s6.56cea27093fd from=translated src=- shape=df13bb2a vocab=5a86ee07
-/
instance instLinearMapClass : LinearMapClass (CartierDual R A) R A R :=
  inferInstanceAs (LinearMapClass (A →ₗ[R] R) R A R)

def toDual : CartierDual R A ≃ₗ[R] Module.Dual R A where
  toFun φ := φ
  invFun φ := φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def ofDual : Module.Dual R A ≃ₗ[R] CartierDual R A := (toDual R A).symm

variable {R A}

/--
@isnad1 id=eq.0h4v.s10.da7725e29706 from=translated src=- shape=2ecc3fb3 vocab=5aa23dcb
-/
@[simp] theorem toDual_apply (φ : CartierDual R A) (a : A) : toDual R A φ a = φ a := rfl
/--
@isnad1 id=eq.0h4v.s10.ed8fa52a029a from=translated src=- shape=2ecc3fb3 vocab=e9ca70c6
-/
@[simp] theorem ofDual_apply (φ : Module.Dual R A) (a : A) : ofDual R A φ a = φ a := rfl
/--
@isnad1 id=eq.0h3v.s10.2a9542477b8f from=translated src=- shape=442178f9 vocab=6831e102
-/
@[simp] theorem toDual_ofDual (φ : Module.Dual R A) : toDual R A (ofDual R A φ) = φ := rfl
/--
@isnad1 id=eq.0h3v.s10.a68612f805f9 from=translated src=- shape=442178f9 vocab=6831e102
-/
@[simp] theorem ofDual_toDual (φ : CartierDual R A) : ofDual R A (toDual R A φ) = φ := rfl

/--
@isnad1 id=eq.1h4v.s6.856e1ce65e7a from=translated src=- shape=a8a3e9eb vocab=7bfc9168
-/
@[ext] theorem ext {φ ψ : CartierDual R A} (h : ∀ a, φ a = ψ a) : φ = ψ :=
  LinearMap.ext (M := A) (f := (φ : Module.Dual R A)) (g := (ψ : Module.Dual R A)) h

/--
@isnad1 id=eq.0h4v.s12.da351ef25156 from=translated src=- shape=357944b5 vocab=ea63336f
-/
theorem mul_def (φ ψ : CartierDual R A) :
    φ * ψ = ofDual R A (dualMul R A (toDual R A φ ⊗ₜ[R] toDual R A ψ)) := rfl

/--
@isnad1 id=eq.0h5v.s13.107dad0c67a0 from=translated src=- shape=6b60a654 vocab=2d44c6ef
-/
theorem mul_apply (φ ψ : CartierDual R A) (a : A) :
    (φ * ψ) a = TensorProduct.dualDistrib R A A (toDual R A φ ⊗ₜ[R] toDual R A ψ) (Coalgebra.comul a) :=
  dualMul_pairing R A _ _ a

/--
@isnad1 id=eq.0h4v.s11.ea0819e88395 from=translated src=- shape=d2d1e3cb vocab=1b85530e
-/
theorem mul_eq_convMul (φ ψ : CartierDual R A) :
    toDual R A (φ * ψ) = (WithConv.toConv (toDual R A φ) * WithConv.toConv (toDual R A ψ)).ofConv :=
  dualMul_tmul_eq_convMul R A _ _

/--
@isnad1 id=eq.0h4v.s11.ea0819e88395 from=translated src=- shape=d2d1e3cb vocab=1b85530e
-/
theorem toDual_mul (φ ψ : CartierDual R A) :
    toDual R A (φ * ψ) = (WithConv.toConv (toDual R A φ) * WithConv.toConv (toDual R A ψ)).ofConv :=
  mul_eq_convMul φ ψ

/--
@isnad1 id=eq.0h2v.s10.d4468c77b3a8 from=translated src=- shape=140d4d42 vocab=fbe9ce10
-/
theorem one_def : (1 : CartierDual R A) = ofDual R A (Coalgebra.counit (R := R) (A := A)) := rfl

/--
@isnad1 id=eq.0h3v.s8.eef9654c8806 from=translated src=- shape=33704637 vocab=6ed259a7
-/
@[simp] theorem one_apply (a : A) : (1 : CartierDual R A) a = Coalgebra.counit (R := R) a := rfl

/--
@isnad1 id=eq.0h3v.s10.835a13031c76 from=translated src=- shape=3ca8ccad vocab=78a62a05
-/
theorem algebraMap_def (r : R) :
    algebraMap R (CartierDual R A) r = ofDual R A (dualUnit R A r) := rfl

/--
@isnad1 id=eq.0h4v.s8.a036d310f5f1 from=translated src=- shape=0dfcf6e0 vocab=f9107b1d
-/
@[simp] theorem algebraMap_apply (r : R) (a : A) :
    algebraMap R (CartierDual R A) r a = Coalgebra.counit (R := R) a * r :=
  dualUnit_apply R A r a

variable (R A)
variable [Module.Finite R A] [Module.Free R A]

/--
@isnad1 id=finite.0h2v.s7.f1a79798cf83 from=translated src=- shape=464b8fe9 vocab=074c29f3
-/
instance instModuleFinite : Module.Finite R (CartierDual R A) :=
  inferInstanceAs (Module.Finite R (Module.Dual R A))

/--
@isnad1 id=free.0h2v.s7.6037861dfe8e from=translated src=- shape=a96fd7a1 vocab=074c29f3
-/
instance instModuleFree : Module.Free R (CartierDual R A) :=
  inferInstanceAs (Module.Free R (Module.Dual R A))

/--
@isnad1 id=eq.0h2v.s7.99d2dc87639f from=translated src=- shape=ae8f4b1f vocab=16943957
-/
theorem finrank_eq [Nontrivial R] : Module.finrank R (CartierDual R A) = Module.finrank R A :=
  Module.finrank_linearMap_self R R A

instance instCoalgebra : Coalgebra R (CartierDual R A) := { dualCoalgebraOfFiniteFree R A with }

instance instBialgebra : Bialgebra R (CartierDual R A) :=
  { instAlgebra R A, instCoalgebra R A, dualBialgebraOfFiniteFree R A with }

/--
@isnad1 id=iscocomm.0h2v.s7.d0df0dbe756d from=translated src=- shape=13a02700 vocab=ed439585
-/
instance instIsCocomm : IsCocomm R (CartierDual R A) :=
  ⟨(dualCoalgebraOfFiniteFree_isCocomm R A).comm_comp_comul⟩

variable {R A}

/--
@isnad1 id=eq.0h3v.s13.407f7296edd3 from=translated src=- shape=f03d4aa2 vocab=a6ae9cf9
-/
theorem comul_def (φ : CartierDual R A) :
    TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap (Coalgebra.comul (R := R) φ) =
      dualComul R A (toDual R A φ) := by
  have hid : TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap =
      (LinearMap.id : Module.Dual R A ⊗[R] Module.Dual R A →ₗ[R] Module.Dual R A ⊗[R] Module.Dual R A) :=
    TensorProduct.ext' fun _ _ => rfl
  rw [hid]
  rfl

/--
@isnad1 id=eq.0h5v.s13.7bd692306fe5 from=translated src=- shape=7a8d1845 vocab=1a34abc5
-/
theorem comul_pairing (φ : CartierDual R A) (a b : A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap (Coalgebra.comul (R := R) φ))
        (a ⊗ₜ[R] b) = φ (a * b) := by
  rw [comul_def]
  exact dualComul_pairing R A _ a b

/--
@isnad1 id=eq.0h3v.s12.6eeb32eb9531 from=translated src=- shape=bb7b7b5d vocab=c31f392c
-/
theorem comul_eq_dualComul (φ : CartierDual R A) :
    (Coalgebra.comul (R := R) φ : CartierDual R A ⊗[R] CartierDual R A) = dualComul R A (toDual R A φ) := rfl

/--
@isnad1 id=eq.0h3v.s10.d42fc6f39509 from=translated src=- shape=8e76d011 vocab=74cc654c
-/
theorem counit_eq_dualCounit (φ : CartierDual R A) : Coalgebra.counit (R := R) φ = dualCounit R A (toDual R A φ) := rfl

/--
@isnad1 id=eq.1h4v.s14.63c48235870e from=translated src=- shape=4238b1ae vocab=1cb6bfa3
-/
theorem tmul_eq_of_pairing_eq {x y : CartierDual R A ⊗[R] CartierDual R A}
    (h : ∀ a b : A,
      TensorProduct.dualDistrib R A A (TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap x) (a ⊗ₜ[R] b) =
      TensorProduct.dualDistrib R A A (TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap y) (a ⊗ₜ[R] b)) :
    x = y := by
  have hid : TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap =
      (LinearMap.id : Module.Dual R A ⊗[R] Module.Dual R A →ₗ[R] Module.Dual R A ⊗[R] Module.Dual R A) :=
    TensorProduct.ext' fun _ _ => rfl
  rw [hid] at h
  have hinj : Function.Injective (TensorProduct.dualDistrib R A A) :=
    (TensorProduct.dualDistribEquiv R A A).injective
  exact hinj (TensorProduct.ext' fun a b => h a b)

/--
@isnad1 id=eq.0h3v.s8.bedbae0f4e56 from=translated src=- shape=27b6a2b2 vocab=79106f7e
-/
@[simp] theorem counit_apply (φ : CartierDual R A) : Coalgebra.counit (R := R) φ = φ 1 :=
  dualCounit_apply R A _

end Instances

section HopfInstance

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A]

instance instHopfAlgebra : HopfAlgebra R (CartierDual R A) :=
  { instBialgebra R A, dualHopfAlgebraOfFiniteFree R A with }

variable {R A}

/--
@isnad1 id=eq.0h4v.s11.23fe93737261 from=translated src=- shape=0365e922 vocab=4c624170
-/
@[simp] theorem antipode_apply (φ : CartierDual R A) (a : A) :
    (HopfAlgebra.antipode R (A := CartierDual R A) φ) a = φ (HopfAlgebra.antipode R (A := A) a) := rfl

end HopfInstance

section BidualSanity
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]
end BidualSanity

section BidualSanityHopf
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A] [IsCocomm R A]
end BidualSanityHopf

end

end Tengoku.FltAnthropic.CartierDual

namespace MonoidAlgebra

/--
@isnad1 id=free.0h2v.s5.be7b36849849 from=translated src=- shape=75d40f7d vocab=37476a12
-/
instance instModuleFreeOfCartier {R : Type*} [CommSemiring R] {Γ : Type*} :
    Module.Free R (MonoidAlgebra R Γ) :=
  .of_equiv (MonoidAlgebra.coeffLinearEquiv R).symm

/--
@isnad1 id=finite.0h2v.s5.82a6bd163082 from=translated src=- shape=4e0fc345 vocab=c1ce93a7
-/
instance instModuleFiniteOfCartier {R : Type*} [CommSemiring R] {Γ : Type*} [Finite Γ] :
    Module.Finite R (MonoidAlgebra R Γ) :=
  .equiv (MonoidAlgebra.coeffLinearEquiv R).symm

end MonoidAlgebra

section
variable (R : Type*) [CommRing R] (Γ : Type*) [CommGroup Γ] [Fintype Γ]
end
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
