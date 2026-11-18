import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (φ : F →+* F') (w : ValuationSubring F')
    (hwK : ∀ a : K, φ (algebraMap K F a) ∈ w) (hwx : ∃ y : F, φ y ∉ w) :
    ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = w.comap φ := by exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable.solution K F F' _ _ _ _ x _ _ φ w hwK hwx
