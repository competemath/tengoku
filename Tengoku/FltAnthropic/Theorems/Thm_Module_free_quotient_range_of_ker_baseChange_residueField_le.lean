import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_free_quotient_range_of_ker_baseChange_residueField_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_free_quotient_range_of_ker_baseChange_residueField_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v w

open scoped TensorProduct

/--
@isnad1 id=free.1h4v.s11.7510fb1dfe0d from=translated src=- shape=71b764dd vocab=0700dcc9
-/
theorem Module.free_quotient_range_of_ker_baseChange_residueField_le
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N)
    (h : LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R)) ≤
      LinearMap.range ((LinearMap.ker f).subtype.baseChange (IsLocalRing.ResidueField R))) :
    Module.Free R (N ⧸ LinearMap.range f) := by exact @_root_.P2MW.S_Module_free_quotient_range_of_ker_baseChange_residueField_le.solution R _ _ M N _ _ _ _ _ _ _ f h
