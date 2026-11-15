import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open scoped TensorProduct

namespace Tengoku.FltAnthropic.CartierDual

noncomputable section

universe u v w x

section Pairing

variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Bialgebra R A]

def pairing : CartierDual R A →ₗ[R] A →ₗ[R] R where
  toFun φ := toDual R A φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
@isnad1 id=eq.0h4v.s9.bc624e7301a3 from=translated src=- shape=bab255f9 vocab=cc667348
-/
@[simp] theorem pairing_apply (φ : CartierDual R A) (a : A) : pairing R A φ a = φ a := rfl

end Pairing

section Map

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
variable {B : Type w} [CommRing B] [Bialgebra R B] [Module.Finite R B] [Module.Free R B]
variable {C : Type x} [CommRing C] [Bialgebra R C] [Module.Finite R C] [Module.Free R C]

def mapLinear (f : A →ₐc[R] B) : CartierDual R B →ₗ[R] CartierDual R A :=
  (ofDual R A).toLinearMap ∘ₗ (f : A →ₗ[R] B).dualMap ∘ₗ (toDual R B).toLinearMap

omit [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B] in
/--
@isnad1 id=eq.0h6v.s9.f656b1b81e1b from=translated src=- shape=a9ef1129 vocab=4282dec5
-/
@[simp] theorem mapLinear_apply (f : A →ₐc[R] B) (φ : CartierDual R B) (a : A) :
    mapLinear f φ a = φ (f a) := rfl

omit [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B] in

/--
@isnad1 id=eq.0h7v.s14.874a53c6b18b from=translated src=- shape=62533640 vocab=f3374fec
-/
theorem dualDistrib_map_map (f : A →ₐc[R] B) (φ ψ : CartierDual R B) (z : A ⊗[R] A) :
    TensorProduct.dualDistrib R B B (toDual R B φ ⊗ₜ[R] toDual R B ψ)
        (TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B) z) =
      TensorProduct.dualDistrib R A A (toDual R A (mapLinear f φ) ⊗ₜ[R] toDual R A (mapLinear f ψ)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/--
@isnad1 id=eq.0h6v.s10.f179ed7a5d06 from=translated src=- shape=2e9c855f vocab=16af5b86
-/
theorem mapLinear_mul (f : A →ₐc[R] B) (φ ψ : CartierDual R B) :
    mapLinear f (φ * ψ) = mapLinear f φ * mapLinear f ψ := by
  apply CartierDual.ext; intro a
  rw [mapLinear_apply, mul_apply, mul_apply, ← dualDistrib_map_map]
  congr 1
  exact (CoalgHomClass.map_comp_comul_apply f a).symm

/--
@isnad1 id=eq.0h4v.s9.a0ce7db2c5ca from=translated src=- shape=ad75246d vocab=e22a9e3b
-/
theorem mapLinear_one (f : A →ₐc[R] B) : mapLinear f 1 = 1 := by
  apply CartierDual.ext; intro a
  rw [mapLinear_apply, one_apply, one_apply]
  exact CoalgHomClass.counit_comp_apply f a

def mapAlgHom (f : A →ₐc[R] B) : CartierDual R B →ₐ[R] CartierDual R A :=
  AlgHom.ofLinearMap (mapLinear f) (mapLinear_one f) (mapLinear_mul f)

/--
@isnad1 id=eq.0h6v.s9.fec5f20ff8b0 from=translated src=- shape=446e5a66 vocab=e92b11b9
-/
@[simp] theorem mapAlgHom_apply (f : A →ₐc[R] B) (φ : CartierDual R B) (a : A) :
    mapAlgHom f φ a = φ (f a) := rfl

/--
@isnad1 id=eq.0h7v.s14.f6764d4070bc from=translated src=- shape=4c11654c vocab=b2b436a6
-/
theorem dualDistrib_map_mapAlgHom (f : A →ₐc[R] B) (w : CartierDual R B ⊗[R] CartierDual R B) (a b : A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap
          (TensorProduct.map (mapLinear f) (mapLinear f) w)) (a ⊗ₜ[R] b) =
      TensorProduct.dualDistrib R B B
        (TensorProduct.map (toDual R B).toLinearMap (toDual R B).toLinearMap w) (f a ⊗ₜ[R] f b) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul φ ψ => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/--
@isnad1 id=eq.0h4v.s9.75495e758f16 from=translated src=- shape=97b6590d vocab=240b701f
-/
theorem counit_comp_mapAlgHom (f : A →ₐc[R] B) :
    (Bialgebra.counitAlgHom R (CartierDual R A)).comp (mapAlgHom f) = Bialgebra.counitAlgHom R (CartierDual R B) := by
  apply AlgHom.ext; intro φ
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply]
  exact (counit_apply (mapAlgHom f φ)).trans ((congrArg φ (map_one f)).trans (counit_apply φ).symm)

/--
@isnad1 id=eq.0h4v.s10.cc28c49bc3c1 from=translated src=- shape=f6980d7a vocab=72d19140
-/
theorem map_comp_comul_mapAlgHom (f : A →ₐc[R] B) :
    (Algebra.TensorProduct.map (mapAlgHom f) (mapAlgHom f)).comp (Bialgebra.comulAlgHom R (CartierDual R B)) =
      (Bialgebra.comulAlgHom R (CartierDual R A)).comp (mapAlgHom f) := by
  apply AlgHom.ext; intro φ
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply]
  have hmap : (Algebra.TensorProduct.map (mapAlgHom f) (mapAlgHom f)).toLinearMap =
      TensorProduct.map (mapLinear f) (mapLinear f) := TensorProduct.ext' fun _ _ => rfl
  rw [← AlgHom.toLinearMap_apply, hmap]
  apply tmul_eq_of_pairing_eq
  intro a b
  have h1 := dualDistrib_map_mapAlgHom f (Coalgebra.comul (R := R) φ) a b
  have h2 := comul_pairing (R := R) (A := B) φ (f a) (f b)
  have h3 := comul_pairing (R := R) (A := A) (mapAlgHom f φ) a b
  exact (h1.trans (h2.trans (congrArg φ (map_mul f a b).symm))).trans h3.symm

def map (f : A →ₐc[R] B) : CartierDual R B →ₐc[R] CartierDual R A :=
  BialgHom.ofAlgHom (mapAlgHom f) (counit_comp_mapAlgHom f) (map_comp_comul_mapAlgHom f)

/--
@isnad1 id=eq.0h6v.s10.9f8b8fc4cde5 from=translated src=- shape=f6f67116 vocab=9043a8a1
-/
@[simp] theorem map_apply (f : A →ₐc[R] B) (φ : CartierDual R B) (a : A) : map f φ a = φ (f a) := rfl

/--
@isnad1 id=eq.0h5v.s11.deeab91d9b09 from=translated src=- shape=1b9db8f6 vocab=c88787f3
-/
theorem toDual_map (f : A →ₐc[R] B) (φ : CartierDual R B) :
    toDual R A (map f φ) = (f : A →ₗ[R] B).dualMap (toDual R B φ) := rfl

/--
@isnad1 id=eq.0h2v.s8.8c20d77f7082 from=translated src=- shape=3b83cf09 vocab=c57ace73
-/
theorem map_id : map (BialgHom.id R A) = BialgHom.id R (CartierDual R A) := by
  apply BialgHom.ext; intro φ; apply CartierDual.ext; intro a; rfl

/--
@isnad1 id=eq.0h6v.s10.a1fc0bcb97f2 from=translated src=- shape=96ae78da vocab=65dc61ff
-/
theorem map_comp (g : B →ₐc[R] C) (f : A →ₐc[R] B) : map (g.comp f) = (map f).comp (map g) := by
  apply BialgHom.ext; intro φ; apply CartierDual.ext; intro a; rfl

def congr (e : A ≃ₐc[R] B) : CartierDual R B ≃ₐc[R] CartierDual R A :=
  BialgEquiv.ofBialgHom (map (e : A →ₐc[R] B)) (map (e.symm : B →ₐc[R] A))
    (by apply BialgHom.ext; intro φ; apply CartierDual.ext; intro a
        show φ (e.symm (e a)) = φ a
        rw [BialgEquiv.symm_apply_apply])
    (by apply BialgHom.ext; intro φ; apply CartierDual.ext; intro b
        show φ (e (e.symm b)) = φ b
        rw [BialgEquiv.apply_symm_apply])

/--
@isnad1 id=eq.0h6v.s10.73788ca69bc6 from=translated src=- shape=f6f67116 vocab=24648244
-/
@[simp] theorem congr_apply (e : A ≃ₐc[R] B) (φ : CartierDual R B) (a : A) : congr e φ a = φ (e a) := rfl

/--
@isnad1 id=eq.0h6v.s10.abafee9c2835 from=translated src=- shape=8f8c036d vocab=3bdd4551
-/
@[simp] theorem congr_symm_apply (e : A ≃ₐc[R] B) (φ : CartierDual R A) (b : B) :
    (congr e).symm φ b = φ (e.symm b) := rfl

end Map

end

end Tengoku.FltAnthropic.CartierDual
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
