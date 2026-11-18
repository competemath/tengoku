import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

universe u v w

/--
@isnad1 id=faithful.4h5v.s9.df5220d95a74 from=translated src=- shape=ea633eb1 vocab=a03719ce
-/
theorem Subalgebra.faithfullyFlat_of_directed_of_forall_faithfullyFlat
    {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
    {ι : Type w} [Nonempty ι] (F : ι → Subalgebra k H) (hdir : Directed (· ≤ ·) F)
    (hle : ∀ i, F i ≤ K) (hcov : ∀ x ∈ K, ∃ i, x ∈ F i)
    (hff : ∀ i, Module.FaithfullyFlat ↥(F i) H) :
    Module.FaithfullyFlat ↥K H := by exact @_root_.P2MW.S_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat.solution k _ H _ _ K ι _ F hdir hle hcov hff
