import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

universe u v w

/--
@isnad1 id=faithful.1h4v.s11.008e0d06502a from=translated src=- shape=0f044a99 vocab=5a1582d4
-/
theorem Subalgebra.faithfullyFlat_of_faithfullyFlat_range_baseChange
    {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
    (k' : Type w) [Field k'] [Algebra k k']
    (hff : Module.FaithfullyFlat
      ↥((Algebra.TensorProduct.map (AlgHom.id k' k') K.val).range) (k' ⊗[k] H)) :
    Module.FaithfullyFlat ↥K H := by exact @_root_.P2MW.S_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange.solution k _ H _ _ K k' _ _ hff
