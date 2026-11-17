import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isReduced_of_flat_of_formallyUnramified_of_isIntegral.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isReduced_of_flat_of_formallyUnramified_of_isIntegral

universe u

open CategoryTheory AlgebraicGeometry

section etaleReduced

namespace Algebra export _root_.Algebra (EssFiniteType TensorProduct.includeRight TensorProduct.lid FormallyUnramified TensorProduct.includeRight_apply FormallyUnramified.isReduced_of_field) namespace FormallyUnramified export _root_.Algebra.FormallyUnramified (ext comp isReduced_of_field) end Algebra.FormallyUnramified
open scoped _root_.Algebra _root_.Algebra.FormallyUnramified in
open TensorProduct in

theorem Algebra.FormallyUnramified.isReduced_of_isDomain_of_flat (A B : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [Algebra A B] [Module.Flat A B] [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] : IsReduced B := by
  let K := FractionRing A
  haveI : IsReduced (K ⊗[A] B) := Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[A] B)
  let φ : B →ₐ[A] K ⊗[A] B := Algebra.TensorProduct.includeRight
  have hφ : Function.Injective φ := by
    have h1 : Function.Injective ((Algebra.linearMap A K).rTensor B) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective A K)
    have hφ' : ⇑φ = ((Algebra.linearMap A K).rTensor B) ∘ (TensorProduct.lid A B).symm := by
      ext b
      simp [φ, Algebra.TensorProduct.includeRight_apply, LinearMap.rTensor_tmul]
    rw [hφ']
    exact h1.comp (TensorProduct.lid A B).symm.injective
  exact isReduced_of_injective φ hφ

end etaleReduced

open AlgebraicGeometry in
theorem solution {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [FormallyUnramified f] [LocallyOfFiniteType f] [IsIntegral Y] : IsReduced X := by
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    letI := (f.stalkMap x).hom.toAlgebra
    haveI : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := Flat.stalkMap f x
    haveI : Algebra.FormallyUnramified (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      FormallyUnramified.stalkMap f x
    haveI : Algebra.EssFiniteType (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      LocallyOfFiniteType.stalkMap f x
    exact Algebra.FormallyUnramified.isReduced_of_isDomain_of_flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)
  exact isReduced_of_isReduced_stalk X
