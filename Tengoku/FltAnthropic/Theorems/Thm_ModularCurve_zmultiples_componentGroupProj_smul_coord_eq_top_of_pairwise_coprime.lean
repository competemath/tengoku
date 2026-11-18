import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ComponentGroup
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open ModularCurve

/--
@isnad1 id=eq.1h3v.s14.3c230d40e1f6 from=translated src=- shape=71b3c0ab vocab=bd113e4e
-/
theorem ModularCurve.zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (he : Pairwise fun s t => (e s).Coprime (e t))
    (s₀ : ι) :
    AddSubgroup.zmultiples (componentGroupProj e ((e s₀ : ℤ) •
      (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype)) = ⊤ := by exact @_root_.P2MW.S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime.solution ι _ e he s₀
