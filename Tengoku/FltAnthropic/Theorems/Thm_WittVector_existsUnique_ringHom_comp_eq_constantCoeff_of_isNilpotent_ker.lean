import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_WittVector_existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WittVector_existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

theorem WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (B : Type u) [CommRing B] (ρ : B →+* k) (hρ : Function.Surjective ρ) (hnil : IsNilpotent (RingHom.ker ρ)) :
    ∃! f : WittVector p k →+* B, ρ.comp f = WittVector.constantCoeff := by exact @_root_.P2MW.S_WittVector_existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker.solution p _ k _ _ _ B _ ρ hρ hnil
