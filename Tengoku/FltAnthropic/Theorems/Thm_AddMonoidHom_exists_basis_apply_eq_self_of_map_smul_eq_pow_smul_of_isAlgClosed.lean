import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_pow_smul_of_isAlgClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_pow_smul_of_isAlgClosed.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

/--
@isnad1 id=ex.2h4v.s9.a1ccc96d7413 from=translated src=- shape=1db64aad vocab=525b6574
-/
theorem AddMonoidHom.exists_basis_apply_eq_self_of_map_smul_eq_pow_smul_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (φ : V →+ V) (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p • φ x)
    (hinj : Function.Injective φ) :
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k V, ∀ i, φ (b i) = b i := by exact @_root_.P2MW.S_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_pow_smul_of_isAlgClosed.solution p _ k _ _ _ V _ _ _ φ hφ hinj
