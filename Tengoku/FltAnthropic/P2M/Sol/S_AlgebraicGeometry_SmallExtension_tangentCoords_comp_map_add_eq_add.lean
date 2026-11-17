import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_add_eq_add.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_add_eq_add

set_option autoImplicit false

open TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension

universe u

namespace CSAux
open AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]

/--
@isnad1 id=eq.0h5v.s14.dd3a28fa12bb from=translated src=- shape=54279a83 vocab=0b6ac5d2
-/
theorem vPart_map (h : (V × V) →ₗ[ResidueField T'] V) (e : thickening T' (V × V) C) :
    vPart T' V C ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C)) (TrivSqZeroExt.map h)) e) =
      TensorProduct.map LinearMap.id (h ∘ₗ TrivSqZeroExt.sndHom (ResidueField T') (V × V)) e := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul c x =>
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]
    show (TensorProduct.map LinearMap.id (TrivSqZeroExt.sndHom (ResidueField T') V)) (_ ⊗ₜ _) = _
    rw [TensorProduct.map_tmul]
    congr 1
    show (TrivSqZeroExt.map h x).snd = h x.snd
    exact TrivSqZeroExt.snd_map h x
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/--
@isnad1 id=eq.0h5v.s14.8201f5772b75 from=translated src=- shape=031b288d vocab=0eadc681
-/
theorem vPart_map' (h : (V × V) →ₗ[ResidueField T'] V) (e : thickening T' (V × V) C) :
    vPart T' V C ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C)) (TrivSqZeroExt.map h)).toRingHom e) =
      TensorProduct.map LinearMap.id (h ∘ₗ TrivSqZeroExt.sndHom (ResidueField T') (V × V)) e :=
  vPart_map V C h e

end CSAux

open AlgebraicGeometry.SmallExtension

/--
@isnad1 id=eq.0h5v.s14.14af8e53c75a from=translated src=- shape=0e8b187e vocab=51517e51
-/
theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V]
    (C : Type u) [CommRing C] [Algebra T' C]
    {A : Type u} [CommRing A] (ψ : A →+* thickening T' (V × V) C) :
    tangentCoords T' V C ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
        (TrivSqZeroExt.map (LinearMap.fst (ResidueField T') V V + LinearMap.snd (ResidueField T') V V))).toRingHom.comp ψ) =
      tangentCoords T' V C ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
        (TrivSqZeroExt.map (LinearMap.fst (ResidueField T') V V))).toRingHom.comp ψ) +
      tangentCoords T' V C ((Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
        (TrivSqZeroExt.map (LinearMap.snd (ResidueField T') V V))).toRingHom.comp ψ) := by
  funext a
  show tensorToDualHom _ _ _ (vPart T' V C _) = tensorToDualHom _ _ _ (vPart T' V C _) + tensorToDualHom _ _ _ (vPart T' V C _)
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom]
  rw [CSAux.vPart_map', CSAux.vPart_map', CSAux.vPart_map', LinearMap.add_comp, TensorProduct.map_add_right, LinearMap.add_apply, map_add]
