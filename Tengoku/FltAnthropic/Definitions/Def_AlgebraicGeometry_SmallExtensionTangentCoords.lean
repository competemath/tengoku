import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Definitions/Def_AlgebraicGeometry_SmallExtensionTangentCoords.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

noncomputable section

universe u

open TensorProduct IsLocalRing

namespace AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]

variable (T') in

def vPart : thickening T' V C →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V :=
  TensorProduct.map LinearMap.id (TrivSqZeroExt.sndHom (ResidueField T') V)

def tensorToDualHom (k : Type u) [Field k] (M : Type u) [AddCommGroup M] [Module k M]
    (W : Type u) [AddCommGroup W] [Module k W] :
    M ⊗[k] W →ₗ[k] (Module.Dual k W →ₗ[k] M) :=
  TensorProduct.lift
    (LinearMap.mk₂ k (fun (m : M) (w : W) => (LinearMap.smulRight (Module.Dual.eval k W w) m : Module.Dual k W →ₗ[k] M))
      (fun m₁ m₂ w => by ext ξ; simp)
      (fun c m w => by ext ξ; simp [smul_smul, mul_comm])
      (fun m w₁ w₂ => by ext ξ; simp [add_smul])
      (fun c m w => by ext ξ; simp [smul_smul]))

/--
@isnad1 id=eq.0h6v.s10.a3ffd90e1b22 from=translated src=- shape=fedf990c vocab=5a00c672
-/
@[simp] theorem tensorToDualHom_tmul (k : Type u) [Field k] (M : Type u) [AddCommGroup M] [Module k M]
    (W : Type u) [AddCommGroup W] [Module k W] (m : M) (w : W) (ξ : Module.Dual k W) :
    tensorToDualHom k M W (m ⊗ₜ w) ξ = ξ w • m := by
  simp [tensorToDualHom]

variable (T') in

def tangentCoords {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a : A) :
    Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C) :=
  tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C) V (vPart T' V C (φ a))

/--
@isnad1 id=eq.0h7v.s14.ccd9eb77a69c from=translated src=- shape=55c7ba73 vocab=f5d6a21b
-/
theorem tangentCoords_apply {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a : A) (ξ : Module.Dual (ResidueField T') V) :
    tangentCoords T' V C φ a ξ = tensorToDualHom (ResidueField T') (ResidueField T' ⊗[T'] C) V (vPart T' V C (φ a)) ξ := rfl

/--
@isnad1 id=eq.0h7v.s12.dc0274768a3a from=translated src=- shape=4e3cffa1 vocab=1b16307d
-/
theorem tangentCoords_add {A : Type u} [CommRing A] (φ : A →+* thickening T' V C) (a b : A) :
    tangentCoords T' V C φ (a + b) = tangentCoords T' V C φ a + tangentCoords T' V C φ b := by
  unfold tangentCoords
  rw [φ.map_add, LinearMap.map_add, LinearMap.map_add]

end AlgebraicGeometry.SmallExtension

end
