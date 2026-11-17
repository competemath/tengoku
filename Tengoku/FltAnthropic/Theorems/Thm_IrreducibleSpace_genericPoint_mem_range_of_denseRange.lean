import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IrreducibleSpace_genericPoint_mem_range_of_denseRange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IrreducibleSpace_genericPoint_mem_range_of_denseRange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

/--
@isnad1 id=mem.2h3v.s5.fa9ba7d63468 from=translated src=- shape=e99be96c vocab=06cc4c0c
-/
theorem IrreducibleSpace.genericPoint_mem_range_of_denseRange
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NoetherianSpace X] [QuasiSober X] [QuasiSober Y] [IrreducibleSpace Y] [T0Space Y]
    {f : X → Y} (hf : Continuous f) (hd : DenseRange f) :
    genericPoint Y ∈ Set.range f := by exact @_root_.P2MW.S_IrreducibleSpace_genericPoint_mem_range_of_denseRange.solution X Y _ _ _ _ _ _ _ f hf hd
