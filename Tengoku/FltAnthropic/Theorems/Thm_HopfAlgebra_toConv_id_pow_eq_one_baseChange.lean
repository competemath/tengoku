import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_toConv_id_pow_eq_one_baseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_toConv_id_pow_eq_one_baseChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w

theorem HopfAlgebra.toConv_id_pow_eq_one_baseChange
    {R : Type u} [CommRing R] (R' : Type w) [CommRing R'] [Algebra R R']
    {H : Type v} [CommRing H] [HopfAlgebra R H] (m : ℕ)
    (h : (WithConv.toConv (AlgHom.id R H)) ^ m = 1) :
    (WithConv.toConv (AlgHom.id R' (TensorProduct R R' H))) ^ m = 1 := by exact @_root_.P2MW.S_HopfAlgebra_toConv_id_pow_eq_one_baseChange.solution R _ R' _ _ H _ _ m h
