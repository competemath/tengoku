import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_cocycle_pow_smul_eq_coboundary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_cocycle_pow_smul_eq_coboundary.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open TensorProduct

universe u v w

theorem AlgebraicGeometry.AdmissibleAlgebra.exists_forall_cocycle_pow_smul_eq_coboundary
    {B : Type u} [CommRing B] [IsNoetherianRing B] {R : Type v} [CommRing R] [Algebra B R] [Module.Finite B R]
    {G : Type w} [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G B R] (t : B) :
    ∃ e : ℕ, ∀ y : G → R, (∀ g h : G, y (g * h) = g • y h + y g) →
      (∃ (k : ℕ) (z : R), ∀ g : G, t ^ k • y g = g • z - z) → ∃ z : R, ∀ g : G, t ^ e • y g = g • z - z := by exact @_root_.P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_cocycle_pow_smul_eq_coboundary.solution B _ _ R _ _ _ G _ _ _ _ t
