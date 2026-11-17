import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HenselianLocalRing_exists_algHom_lift_of_etale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HenselianLocalRing_exists_algHom_lift_of_etale.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u
theorem HenselianLocalRing.exists_algHom_lift_of_etale
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (φ : S →ₐ[R] IsLocalRing.ResidueField R) :
    ∃ ψ : S →ₐ[R] R, ∀ s : S, algebraMap R (IsLocalRing.ResidueField R) (ψ s) = φ s := by exact @_root_.P2MW.S_HenselianLocalRing_exists_algHom_lift_of_etale.solution R _ _ S _ _ _ φ
