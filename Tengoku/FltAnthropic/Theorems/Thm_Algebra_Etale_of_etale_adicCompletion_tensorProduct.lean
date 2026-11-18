import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_Etale_of_etale_adicCompletion_tensorProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_Etale_of_etale_adicCompletion_tensorProduct.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open scoped TensorProduct in

/--
@isnad1 id=etale.1h2v.s9.fd1328794d90 from=translated src=- shape=31f1e9ab vocab=306c198c
-/
theorem Algebra.Etale.of_etale_adicCompletion_tensorProduct
    {R : Type u} {S : Type v} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    (h : Algebra.Etale (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      ((AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗[R] S)) :
    Algebra.Etale R S := by exact @_root_.P2MW.S_Algebra_Etale_of_etale_adicCompletion_tensorProduct.solution R S _ _ _ _ _ h
