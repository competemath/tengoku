import Tengoku.Seed.RepresentationTheory.Basic
import Tengoku.Seed.LinearAlgebra.TensorProduct.Tower
import Tengoku.FltAnthropic.P2M.Sol.S_Representation_span_range_baseChange_eq_top_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Representation_span_range_baseChange_eq_top_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open Module LinearMap
/--
@isnad1 id=iff.0h5v.s12.5d6171459752 from=translated src=- shape=1af73d63 vocab=b556a4d6
-/
theorem Representation.span_range_baseChange_eq_top_iff
    {k K G V : Type*} [Field k] [Field K] [Algebra k K] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) :
    Submodule.span K (Set.range fun g => (ρ g).baseChange K) = ⊤ ↔
      Submodule.span k (Set.range ⇑ρ) = ⊤ := by exact @_root_.P2MW.S_Representation_span_range_baseChange_eq_top_iff.solution k K G V _ _ _ _ _ _ _ ρ
