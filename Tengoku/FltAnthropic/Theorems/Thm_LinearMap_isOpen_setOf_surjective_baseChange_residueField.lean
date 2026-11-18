import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LinearMap_isOpen_setOf_surjective_baseChange_residueField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LinearMap_isOpen_setOf_surjective_baseChange_residueField.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w

open TensorProduct

theorem LinearMap.isOpen_setOf_surjective_baseChange_residueField
    {A : Type u} [CommRing A] {P : Type v} {Q : Type w} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (d : P →ₗ[A] Q) [Module.Finite A (Q ⧸ LinearMap.range d)] :
    IsOpen {𝔭 : PrimeSpectrum A | Function.Surjective (d.baseChange 𝔭.asIdeal.ResidueField)} := by exact @_root_.P2MW.S_LinearMap_isOpen_setOf_surjective_baseChange_residueField.solution A _ P Q _ _ _ _ d _
