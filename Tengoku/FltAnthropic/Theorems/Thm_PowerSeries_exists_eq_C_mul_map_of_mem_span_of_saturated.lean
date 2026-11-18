import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_PowerSeries_exists_eq_C_mul_map_of_mem_span_of_saturated

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_PowerSeries_exists_eq_C_mul_map_of_mem_span_of_saturated.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem PowerSeries.exists_eq_C_mul_map_of_mem_span_of_saturated
    {L : Type*} [Field L] (A : ValuationSubring L)
    (N : AddSubgroup (PowerSeries ℤ))
    (hN : ∀ (n : ℤ) (p : PowerSeries ℤ), n ≠ 0 → n • p ∈ N → p ∈ N)
    {V : PowerSeries L}
    (hV : V ∈ Submodule.span L
      ((fun p : PowerSeries ℤ => p.map (Int.castRingHom L)) '' (N : Set (PowerSeries ℤ))))
    (hV0 : V ≠ 0) :
    ∃ (c : L) (u : PowerSeries A), c ≠ 0 ∧
      V = PowerSeries.C c * u.map (A.subtype : A →+* L) ∧
      u.map (IsLocalRing.residue A) ≠ 0 ∧
      u.map (IsLocalRing.residue A) ∈
        Submodule.span (IsLocalRing.ResidueField A)
          ((fun p : PowerSeries ℤ => p.map (Int.castRingHom (IsLocalRing.ResidueField A))) ''
            (N : Set (PowerSeries ℤ))) := by exact @_root_.P2MW.S_PowerSeries_exists_eq_C_mul_map_of_mem_span_of_saturated.solution L _ A N hN V hV hV0
