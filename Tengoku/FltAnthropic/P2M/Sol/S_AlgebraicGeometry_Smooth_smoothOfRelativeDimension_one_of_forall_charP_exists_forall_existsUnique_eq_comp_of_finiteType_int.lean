import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.lean`: wrote out 7 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`, 4 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int

set_option autoImplicit false

open _root_.CategoryTheory open _root_.AlgebraicGeometry open _root_.TrivSqZeroExt

universe u

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Spec.map_comp IsOpenImmersion.lift Surjective Spec.map_comp_assoc SmoothOfRelativeDimension Scheme.Hom Smooth.exists_isStandardSmooth range_eq_range_of_surjective IsAffineOpen.SpecMap_appLE_fromSpec LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Smooth IsOpenImmersion Spec.map_injective Scheme.Hom.finiteType_appLE Spec.preimage isAffineOpen_top IsAffineOpen IsOpenImmersion.lift_fac Scheme.Hom.comp_apply Scheme.ΓSpecIso)
namespace Dim1PosChar
open _root_.AlgebraicGeometry

section Ring

variable {R A k : Type u} [CommRing R] [CommRing A] [Algebra R A] [Field k] [Algebra A k]

structure IsTangent (R : Type u) [CommRing R] [Algebra R A] (τ : A →+* DualNumber k) : Prop where
  fst_apply : ∀ a, (τ a).fst = algebraMap A k a
  base : ∀ r, τ (algebraMap R A r) = inl (algebraMap A k (algebraMap R A r))

variable [Algebra R k] [IsScalarTower R A k]

variable {ι : Type*} (b : Module.Basis ι A Ω[A⁄R])

end Ring


section SchemeLevel

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)

variable {Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U) (e : V ≤ f ⁻¹ᵁ U)
  [Algebra Γ(Y, U) Γ(X, V)] (halg : algebraMap Γ(Y, U) Γ(X, V) = (f.appLE U V e).hom)
  {k : Type u} [Field k] [Algebra Γ(X, V) k]

end SchemeLevel


end AlgebraicGeometry.Dim1PosChar
open scoped _root_.P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.AlgebraicGeometry.Dim1PosChar
open scoped _root_.P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.AlgebraicGeometry
