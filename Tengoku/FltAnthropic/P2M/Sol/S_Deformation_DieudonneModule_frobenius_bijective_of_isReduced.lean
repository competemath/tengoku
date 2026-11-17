import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittHomColimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Deformation_DieudonneModule_frobenius_bijective_of_isReduced.lean`: wrote out 7 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Deformation_DieudonneModule_frobenius_bijective_of_isReduced

universe v

open scoped TensorProduct

universe u w

namespace Deformation
export _root_.Deformation (wittHom wittHomMap coeff_wittHomMap wittHomFrobenius coeff_wittHomFrobenius DieudonneModule DieudonneModule.induction_on DieudonneModule.frobenius)
namespace DieudonneModule
export _root_.Deformation.DieudonneModule (of induction_on frobenius frobenius_of map map_of map_id map_comp)
namespace FrobBij
open _root_.Deformation.DieudonneModule open _root_.Deformation

open _root_.Deformation open _root_.P2MW.S_Deformation_DieudonneModule_frobenius_bijective_of_isReduced.Deformation open _root_.Deformation.DieudonneModule open _root_.P2MW.S_Deformation_DieudonneModule_frobenius_bijective_of_isReduced.Deformation.DieudonneModule

section Frob

variable (p : ℕ) [hp : Fact p.Prime] (C : Type v) [CommRing C] [Bialgebra (ZMod p) C]

/--
@isnad1 id=charp.0h2v.s5.75935e8b48c8 from=translated src=- shape=7f0d0e74 vocab=ea09b5f7
-/
theorem charP_of_bialgebra : CharP C p :=
  charP_of_injective_algebraMap (Bialgebra.algebraMap_injective (R := ZMod p) C) p

/--
@isnad1 id=expchar.0h2v.s5.32430668fc8e from=translated src=- shape=7f0d0e74 vocab=0bba7f78
-/
theorem expChar_of_bialgebra : ExpChar C p :=
  haveI := charP_of_bialgebra p C
  ExpChar.prime hp.out

noncomputable def frobAlgHom : C →ₐ[ZMod p] C where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow hp.out.ne_zero
  map_add' x y := by
    haveI := charP_of_bialgebra p C
    exact add_pow_char x y p
  commutes' r := by
    show (algebraMap (ZMod p) C r) ^ p = algebraMap (ZMod p) C r
    rw [← map_pow, ZMod.pow_card]

/--
@isnad1 id=eq.0h3v.s7.714d1ffd3ec7 from=translated src=- shape=f51841fa vocab=2212432b
-/
@[scoped simp] theorem frobAlgHom_apply (x : C) : frobAlgHom p C x = x ^ p := rfl

/--
@isnad1 id=eq.0h3v.s12.58f4be19f7da from=translated src=- shape=4fe99c81 vocab=3df35520
-/
theorem map_frobAlgHom (t : TensorProduct (ZMod p) C C) :
    Algebra.TensorProduct.map (frobAlgHom p C) (frobAlgHom p C) t =
      frobAlgHom p (TensorProduct (ZMod p) C C) t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, frobAlgHom_apply, frobAlgHom_apply, frobAlgHom_apply,
      Algebra.TensorProduct.tmul_pow]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

noncomputable def frobBialgHom : C →ₐc[ZMod p] C :=
  BialgHom.ofAlgHom (frobAlgHom p C)
    (AlgHom.ext fun x => by
      rw [AlgHom.comp_apply, frobAlgHom_apply, map_pow, Bialgebra.counitAlgHom_apply, ZMod.pow_card])
    (AlgHom.ext fun x => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, map_frobAlgHom, frobAlgHom_apply, frobAlgHom_apply,
        map_pow])

/--
@isnad1 id=eq.0h3v.s8.c11fecb694d8 from=translated src=- shape=f51841fa vocab=016a4617
-/
@[scoped simp] theorem frobBialgHom_apply (x : C) : frobBialgHom p C x = x ^ p := rfl

/--
@isnad1 id=bijectiv.0h2v.s9.9eb90264ec44 from=translated src=- shape=6dbfded7 vocab=3220002c
-/
theorem frobBialgHom_bijective [Module.Finite (ZMod p) C] [IsReduced C] :
    Function.Bijective (frobBialgHom p C) := by
  haveI := expChar_of_bialgebra p C
  have hinj : Function.Injective (frobBialgHom p C) := fun x y h =>
    frobenius_inj C p (by simpa only [frobenius_def, frobBialgHom_apply] using h)
  have hinj' : Function.Injective ((frobBialgHom p C : C →ₗc[ZMod p] C).toLinearMap) := hinj
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj'⟩

/--
@isnad1 id=eq.0h4v.s12.e9b98998ccd9 from=translated src=- shape=a9c2668b vocab=65b289fb
-/
theorem wittHomFrobenius_eq_wittHomMap (n : ℕ) (x : wittHom (ZMod p) p n C) :
    wittHomFrobenius (ZMod p) p n C x = wittHomMap p n (frobBialgHom p C) x :=
  Subtype.ext (TruncatedWittVector.ext fun i => by
    rw [coeff_wittHomFrobenius, coeff_wittHomMap, frobBialgHom_apply])

/--
@isnad1 id=eq.0h3v.s9.c0aa9cafaa02 from=translated src=- shape=c02c83b4 vocab=a4bf4f4c
-/
theorem frobenius_eq_map (z : DieudonneModule (ZMod p) p C) :
    DieudonneModule.frobenius (ZMod p) p C z = map (ZMod p) p (frobBialgHom p C) z := by
  induction z using DieudonneModule.induction_on with
  | ih n x => rw [frobenius_of, map_of, wittHomFrobenius_eq_wittHomMap]

end Frob

/--
@isnad1 id=bijectiv.1h2v.s8.84e59ef01244 from=translated src=- shape=ebd087bc vocab=48a0fd19
-/
theorem frobenius_bijective (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [Bialgebra (ZMod p) B]
    [Module.Finite (ZMod p) B] (hB : IsReduced B) :
    Function.Bijective (DieudonneModule.frobenius (ZMod p) p B) := by
  let Φ : B ≃ₐc[ZMod p] B := BialgEquiv.ofBijective (frobBialgHom p B) (frobBialgHom_bijective p B)
  have h1 : (frobBialgHom p B).comp (Φ.symm : B →ₐc[ZMod p] B) = BialgHom.id (ZMod p) B :=
    BialgHom.ext fun x => Φ.apply_symm_apply x
  have h2 : (Φ.symm : B →ₐc[ZMod p] B).comp (frobBialgHom p B) = BialgHom.id (ZMod p) B :=
    BialgHom.ext fun x => Φ.symm_apply_apply x
  rw [show (DieudonneModule.frobenius (ZMod p) p B : _ → _) = map (ZMod p) p (frobBialgHom p B) from
    funext (frobenius_eq_map p B)]
  refine Function.bijective_iff_has_inverse.2
    ⟨map (ZMod p) p (Φ.symm : B →ₐc[ZMod p] B), fun z => ?_, fun z => ?_⟩
  · rw [← map_comp, h2, map_id]
  · rw [← map_comp, h1, map_id]

end Deformation.DieudonneModule.FrobBij
open scoped _root_.P2MW.S_Deformation_DieudonneModule_frobenius_bijective_of_isReduced.Deformation _root_.P2MW.S_Deformation_DieudonneModule_frobenius_bijective_of_isReduced.Deformation.DieudonneModule _root_.P2MW.S_Deformation_DieudonneModule_frobenius_bijective_of_isReduced.Deformation.DieudonneModule.FrobBij
open scoped _root_.P2MW.S_Deformation_DieudonneModule_frobenius_bijective_of_isReduced.Deformation _root_.P2MW.S_Deformation_DieudonneModule_frobenius_bijective_of_isReduced.Deformation.DieudonneModule
open scoped _root_.P2MW.S_Deformation_DieudonneModule_frobenius_bijective_of_isReduced.Deformation

/--
@isnad1 id=bijectiv.1h2v.s8.84e59ef01244 from=translated src=- shape=ebd087bc vocab=48a0fd19
-/
theorem solution
    (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [Bialgebra (ZMod p) B] [Module.Finite (ZMod p) B]
    (hB : IsReduced B) :
    Function.Bijective (Deformation.DieudonneModule.frobenius (ZMod p) p B) :=
  Deformation.DieudonneModule.FrobBij.frobenius_bijective p B hB
