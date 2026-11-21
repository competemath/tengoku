import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.P2M.Sol.S_Deformation_wittHom_nsmul_eq_zero_of_forall_convPow_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Deformation_wittHom_nsmul_eq_zero_of_forall_convPow_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v

/--
@isnad1 id=eq.1h6v.s10.a8f0c8524711 from=translated src=- shape=92121737 vocab=ee188c32
-/
theorem Deformation.wittHom_nsmul_eq_zero_of_forall_convPow_eq_one
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A] (m : ℕ)
    (hA : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (A →ₐ[R] T)), f ^ m = 1)
    (x : Deformation.wittHom R p n A) : m • x = 0 := by exact @_root_.P2MW.S_Deformation_wittHom_nsmul_eq_zero_of_forall_convPow_eq_one.solution R _ p _ n A _ _ m hA x
