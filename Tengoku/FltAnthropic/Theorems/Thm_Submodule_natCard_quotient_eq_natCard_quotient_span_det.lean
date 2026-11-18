import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Submodule_natCard_quotient_eq_natCard_quotient_span_det

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Submodule_natCard_quotient_eq_natCard_quotient_span_det.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Submodule.natCard_quotient_eq_natCard_quotient_span_det
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type} [AddCommGroup M] [Module R M]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (N : Submodule R M) (bN : Module.Basis ι R N) :
    Nat.card (M ⧸ N) = Nat.card (R ⧸ Ideal.span ({b.det (fun i => (bN i : M))} : Set R)) := by exact @_root_.P2MW.S_Submodule_natCard_quotient_eq_natCard_quotient_span_det.solution R _ _ _ M _ _ ι _ _ b N bN
