import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ModularGroup_exists_mulEquiv_freeProduct_quotient_center

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularGroup_exists_mulEquiv_freeProduct_quotient_center.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
theorem ModularGroup.exists_mulEquiv_freeProduct_quotient_center :
    ∃ e : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2)))
        ≃* Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℤ),
      e (Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 0)
          (Multiplicative.ofAdd 1)) = QuotientGroup.mk ModularGroup.S ∧
      e (Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 1)
          (Multiplicative.ofAdd 1)) = QuotientGroup.mk (ModularGroup.S * ModularGroup.T) := by exact @_root_.P2MW.S_ModularGroup_exists_mulEquiv_freeProduct_quotient_center.solution
