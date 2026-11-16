import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_hom_ext_of_isIso_fromTildeGamma.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_hom_ext_of_isIso_fromTildeGamma

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

theorem solution {R : CommRingCat.{u}}
    {M N : (Spec (.of R)).Modules} [IsIso (Scheme.Modules.fromTildeΓ M)] (φ ψ : M ⟶ N)
    (h : ∀ m : Γ(M, ⊤), φ.app ⊤ m = ψ.app ⊤ m) : φ = ψ := by
  have hΓ : (moduleSpecΓFunctor (R := R)).map φ = (moduleSpecΓFunctor (R := R)).map ψ := by
    ext m
    exact h m
  have n1 := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality φ
  have n2 := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality ψ
  simp only [Functor.comp_map, Functor.id_map] at n1 n2
  rw [← cancel_epi (Scheme.Modules.fromTildeΓ M)]
  change (Scheme.Modules.fromTildeΓNatTrans (R := R)).app M ≫ φ =
    (Scheme.Modules.fromTildeΓNatTrans (R := R)).app M ≫ ψ
  refine n1.symm.trans ?_
  rw [hΓ]
  exact n2
