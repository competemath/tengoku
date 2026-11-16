import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_RingTheory_AffineDilatation
import Tengoku.FltAnthropic.P2M.Sol.S_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

/--
@isnad1 id=and.2h4v.s9.1d9235ad6568 from=translated src=- shape=f8c849dc vocab=205e1cac
-/
theorem AffineDilatation.nonempty_algHom_and_subsingleton_of_isSMulRegular
    {A : Type u} [CommRing A] (I : Ideal A) (a : A)
    {C : Type v} [CommRing C] [Algebra A C] (hreg : IsSMulRegular C a)
    (hI : I.map (algebraMap A C) ≤ Ideal.span {algebraMap A C a}) :
    Nonempty (AffineDilatation.Ring I a →ₐ[A] C) ∧
      Subsingleton (AffineDilatation.Ring I a →ₐ[A] C) := by exact @_root_.P2MW.S_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular.solution A _ I a C _ _ hreg hI
