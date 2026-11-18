import Tengoku.FltAnthropic.Definitions.Def_HeckeModule_IharaRungDatum
import Tengoku.FltAnthropic.P2M.Sol.S_IharaTower_RungAssembly_iharaClauseAt_rungDatumOfLegs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaTower_RungAssembly_iharaClauseAt_rungDatumOfLegs.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IharaTower in

theorem IharaTower.RungAssembly.iharaClauseAt_rungDatumOfLegs
    {𝒪 : Type} [CommRing 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] {T' : Type} [CommRing T'] [Algebra 𝒪 T']
    {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}
    {n : ℕ} (L : RungAssembly.LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) (πT : T →ₐ[𝒪] 𝒪)
    (hequiv : ∀ (t' : T') (m : M),
      (RungAssembly.rungDatumOfLegs L c res).i (res t' • m)
        = t' • (RungAssembly.rungDatumOfLegs L c res).i m)
    (hsurj : ∀ w' ∈ (Submodule.torsionBySet T' M'
        ↑(RingHom.ker (πT.comp res))).restrictScalars 𝒪,
      ∃ m ∈ (Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪,
        (RungAssembly.rungDatumOfLegs L c res).i m = w') :
    IharaClauseAt (RungAssembly.rungDatumOfLegs L c res) πT (πT.comp res) := by exact @_root_.P2MW.S_IharaTower_RungAssembly_iharaClauseAt_rungDatumOfLegs.solution 𝒪 _ T _ _ T' _ _ M _ _ _ _ M' _ _ _ _ P P' n L c res πT hequiv hsurj
