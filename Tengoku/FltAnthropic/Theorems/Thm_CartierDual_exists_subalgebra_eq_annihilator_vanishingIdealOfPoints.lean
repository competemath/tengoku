import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CharacterClosure
import Tengoku.FltAnthropic.P2M.Sol.S_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open scoped TensorProduct

theorem Tengoku.FltAnthropic.CartierDual.exists_subalgebra_eq_annihilator_vanishingIdealOfPoints
    (F : Type) [Field F] (A : Type) [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
    (L : Type) [Field L] [Algebra F L]
    (S : Submonoid (WithConv (A →ₐ[F] L)))
    (hsep : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
      (∀ (ν ν' : A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (hinv : ∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)) :
    ∃ B : Subalgebra F (CartierDual F A),
      (B : Set (CartierDual F A))
          = {θ | ∀ a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S), θ a = 0} ∧
      (∀ θ ∈ B, Coalgebra.comul (R := F) θ
          ∈ Submodule.span F (Set.image2 (fun φ ψ => φ ⊗ₜ[F] ψ) (B : Set (CartierDual F A)) (B : Set (CartierDual F A)))) ∧
      (∀ θ ∈ B, HopfAlgebraStruct.antipode (R := F) (A := CartierDual F A) θ ∈ B) := by exact @_root_.P2MW.S_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints.solution F _ A _ _ _ L _ _ S hsep hinv
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
