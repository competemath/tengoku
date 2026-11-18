import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_nonempty_algEquiv_pi_or_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_irreducible

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_nonempty_algEquiv_pi_or_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_irreducible.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v
theorem HopfAlgebra.nonempty_algEquiv_pi_or_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_irreducible
    {R : Type u} [CommRing R] (h2 : Irreducible (2 : R))
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    (hrank : Module.finrank R H = 2) :
    Nonempty (H ≃ₐ[R] (Fin 2 → R)) ∨ Nonempty (H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod 2))) := by exact @_root_.P2MW.S_HopfAlgebra_nonempty_algEquiv_pi_or_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_irreducible.solution R _ h2 H _ _ _ _ hrank
