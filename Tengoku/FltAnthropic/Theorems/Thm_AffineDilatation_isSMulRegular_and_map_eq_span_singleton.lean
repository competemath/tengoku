import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_RingTheory_AffineDilatation
import Tengoku.FltAnthropic.P2M.Sol.S_AffineDilatation_isSMulRegular_and_map_eq_span_singleton

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AffineDilatation_isSMulRegular_and_map_eq_span_singleton.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

/--
@isnad1 id=and.1h3v.s10.b21067291ff4 from=translated src=- shape=e861c93c vocab=59c9080c
-/
theorem AffineDilatation.isSMulRegular_and_map_eq_span_singleton
    {A : Type u} [CommRing A] (I : Ideal A) (a : A) (ha : a ∈ I) :
    IsSMulRegular (AffineDilatation.Ring I a) a ∧
      I.map (algebraMap A (AffineDilatation.Ring I a)) =
        Ideal.span {algebraMap A (AffineDilatation.Ring I a) a} := by exact @_root_.P2MW.S_AffineDilatation_isSMulRegular_and_map_eq_span_singleton.solution A _ I a ha
