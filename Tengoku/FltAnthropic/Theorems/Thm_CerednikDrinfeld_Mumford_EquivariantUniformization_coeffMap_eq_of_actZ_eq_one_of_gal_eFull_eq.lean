import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq
import Tengoku.FltAnthropic.Definitions.Def_Compat_Mathlib430

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

local notation α "^+" M:51 => FixedPoints.addSubgroup M α

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

/--
@isnad1 id=eq.5h14v.s17.48cf72279415 from=translated src=- shape=d76332fe vocab=f02d0248
-/
theorem CerednikDrinfeld.Mumford.EquivariantUniformization.coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq
    {E V : Type} [Fintype E] [DecidableEq V]
    {r : ℕ} [Fact r.Prime] {D : DegeneracyData E V}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    {T : Type} [AddCommGroup T] {S : Type} [Group S]
    {scalar : S →* ↥(A.decompositionSubgroup ℚ)}
    {actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))} {gal : S →* AddAut T}
    (𝒰 : EquivariantUniformization r D A hA T S scalar actZ gal)
    (σ : S) (hσ : actZ σ = 1)
    (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion)
    (hs : ∀ c, s c = (scalar σ) • c)
    (hiso : ∀ c, Valued.v (s c) = Valued.v c)
    (u : 𝒰.P.TorusPoints) (hu : gal σ (𝒰.eFull u) = 𝒰.eFull u) :
    𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u := by exact @_root_.P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq.solution E V _ _ r _ D A hA T _ S _ scalar actZ gal 𝒰 σ hσ s hs hiso u hu
