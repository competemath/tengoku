import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    [Module.Finite R A] (S : Subalgebra R A) (k : Type*) [Field k] [IsAlgClosed k] [Algebra R k] (φ : ↥S →ₐ[R] k) :
    ∃ ψ : A →ₐ[R] k, ψ.comp S.val = φ := by exact @_root_.P2MW.S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed.solution R _ A _ _ _ S k _ _ _ φ
