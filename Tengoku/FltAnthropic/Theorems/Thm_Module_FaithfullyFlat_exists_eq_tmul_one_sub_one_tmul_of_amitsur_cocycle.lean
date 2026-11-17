import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_FaithfullyFlat_exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_FaithfullyFlat_exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open TensorProduct

theorem Module.FaithfullyFlat.exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (c : S ⊗[R] S)
    (hc : Algebra.TensorProduct.map (AlgHom.id R S)
            (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) c +
          (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) c =
        Algebra.TensorProduct.map (AlgHom.id R S)
            (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) c) :
    ∃ s : S, c = s ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] s := by exact @_root_.P2MW.S_Module_FaithfullyFlat_exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle.solution R _ S _ _ _ c hc
