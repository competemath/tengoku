import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.lean`: wrote out 8 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 2 `p2m_open`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry open _root_.Opposite open _root_.TopologicalSpace

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme Scheme.Modules)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (forget Γ Modules Opens evaluation)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (toPresheaf)
open _root_.AlgebraicGeometry.Scheme.Modules open _root_.AlgebraicGeometry.Scheme open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

scoped instance : (toPresheaf X).Additive where
  map_add := by intros; rfl

noncomputable abbrev evalAt (U : X.Opens) : TopCat.Presheaf Ab.{u} X ⥤ Ab.{u} :=
  (CategoryTheory.evaluation _ Ab.{u}).obj (op U)

scoped instance (U : X.Opens) : (evalAt (X := X) U).Additive where
  map_add := by intros; rfl

theorem exists_app_eq_of_exact_of_app_eq_zero (S : ShortComplex X.Modules) (hS : S.Exact) [Mono S.f]
    (U : X.Opens) (m : Γ(S.X₂, U)) (hm : S.g.app U m = 0) :
    ∃ e : Γ(S.X₁, U), S.f.app U e = m := by

  have hK : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
  have hK₁ := KernelFork.mapIsLimit _ hK (toPresheaf X)
  have hPL : PreservesLimitsOfShape WalkingParallelPair (evalAt (X := X) U) :=
    evaluation_preservesLimitsOfShape _
  have hK' := @KernelFork.mapIsLimit _ _ _ _ _ _ _ _ _ _ hK₁ (evalAt (X := X) U) inferInstance
    (hPL.preservesLimit)

  let k : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ (evalAt (X := X) U).obj ((toPresheaf X).obj S.X₂) :=
    AddCommGrpCat.ofHom ((zmultiplesHom Γ(S.X₂, U) m).comp AddEquiv.ulift.toAddMonoidHom)
  have hk1 : k (ULift.up (1 : ℤ)) = m := by
    change (zmultiplesHom Γ(S.X₂, U) m) (1 : ℤ) = m
    simp
  have hk : k ≫ (evalAt (X := X) U).map ((toPresheaf X).map S.g) = 0 := by
    ext ⟨z⟩
    change (S.g.app U) ((zmultiplesHom Γ(S.X₂, U) m) z) = 0
    rw [zmultiplesHom_apply, map_zsmul, hm, smul_zero]
  refine ⟨(KernelFork.IsLimit.lift' hK' k hk).1 (ULift.up (1 : ℤ)), ?_⟩
  have h := (KernelFork.IsLimit.lift' hK' k hk).2
  have h' := congr($h (ULift.up (1 : ℤ)))
  rw [hk1] at h'
  exact h'

end AlgebraicGeometry.Scheme.Modules
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry.Scheme _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry.Scheme.Modules
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry.Scheme
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.AlgebraicGeometry

theorem solution {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.Exact) [Mono S.f]
    (U : X.Opens) (m : Γ(S.X₂, U)) (hm : S.g.app U m = 0) :
    ∃ e : Γ(S.X₁, U), S.f.app U e = m :=
  AlgebraicGeometry.Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero S hS U m hm
