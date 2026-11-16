import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_exists_forall_dual_quotient_eq_trace_of_mem_comap_one_div_traceDual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_exists_forall_dual_quotient_eq_trace_of_mem_comap_one_div_traceDual.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

theorem Algebra.exists_forall_dual_quotient_eq_trace_of_mem_comap_one_div_traceDual
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (I : Ideal R) (s : S)
    (hs : s ∈ ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F))) :
    ∀ φ : Module.Dual (R ⧸ I) (S ⧸ I.map (algebraMap R S)),
      ∃ x : S ⧸ I.map (algebraMap R S), ∀ y : S ⧸ I.map (algebraMap R S),
        φ (Ideal.Quotient.mk (I.map (algebraMap R S)) s * y) =
          Algebra.trace (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (x * y) := by exact @_root_.P2MW.S_Algebra_exists_forall_dual_quotient_eq_trace_of_mem_comap_one_div_traceDual.solution R _ _ _ _ K _ _ _ S _ _ _ _ _ _ F _ _ _ _ _ _ _ _ I s hs
