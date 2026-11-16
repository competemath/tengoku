import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_RingTheory_AffineDilatation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AffineDilatation_isSMulRegular_and_map_eq_span_singleton.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AffineDilatation_isSMulRegular_and_map_eq_span_singleton

set_option autoImplicit false

universe u

namespace AffineDilatation
export _root_.AffineDilatation (Ring divElem algebraMap_mul_divElem)
namespace BasicProps
open _root_.AffineDilatation

open scoped nonZeroDivisors

variable {A : Type u} [CommRing A]

theorem isSMulRegular (I : Ideal A) (a : A) : IsSMulRegular (Ring I a) a := by
  intro x y hxy
  apply Subtype.ext
  have h : algebraMap A (Localization.Away a) a * (x : Localization.Away a) =
      algebraMap A (Localization.Away a) a * (y : Localization.Away a) := by
    have := congrArg (fun z : Ring I a => (z : Localization.Away a)) hxy
    simpa [Algebra.smul_def] using this
  exact (IsLocalization.Away.algebraMap_isUnit a).mul_left_cancel h

theorem map_eq_span (I : Ideal A) (a : A) (ha : a ∈ I) :
    I.map (algebraMap A (Ring I a)) = Ideal.span {algebraMap A (Ring I a) a} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    exact ⟨divElem I a g hg, by rw [mul_comm, algebraMap_mul_divElem]⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ ha

end AffineDilatation.BasicProps

theorem solution
    {A : Type u} [CommRing A] (I : Ideal A) (a : A) (ha : a ∈ I) :
    IsSMulRegular (AffineDilatation.Ring I a) a ∧
      I.map (algebraMap A (AffineDilatation.Ring I a)) =
        Ideal.span {algebraMap A (AffineDilatation.Ring I a) a} :=
  ⟨AffineDilatation.BasicProps.isSMulRegular I a, AffineDilatation.BasicProps.map_eq_span I a ha⟩
