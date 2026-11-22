import Tengoku.Seed.NumberTheory.NumberField.InfiniteAdeleRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace

set_option autoImplicit false

open _root_.NumberField open _root_.NumberField.InfinitePlace open _root_.NumberField.InfinitePlace.Completion open _root_.NumberField.InfiniteAdeleRing

namespace P2mMixedHomeo

variable (K : Type) [Field K]

/--
@isnad1 id=continuo.0h1v.s9.abe7e68bd76d from=translated src=- shape=1251ce30 vocab=7bdfd003
-/
theorem continuous_ringEquiv_mixedSpace : Continuous (ringEquiv_mixedSpace K) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

/--
@isnad1 id=continuo.0h1v.s10.4d6642c60662 from=translated src=- shape=45767fe3 vocab=b5d7f621
-/
theorem continuous_ringEquiv_mixedSpace_symm : Continuous (ringEquiv_mixedSpace K).symm := by
  apply continuous_pi
  intro v
  by_cases hv : IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace K => (ringEquiv_mixedSpace K).symm y v)
        = fun y => (isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.1 ⟨v, hv⟩)
        ((ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : IsComplex v := not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace K => (ringEquiv_mixedSpace K).symm y v)
        = fun y => (isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨v, hc⟩) := by
      funext y
      apply (isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨v, hc⟩)
        ((ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

noncomputable def mixedHomeo : InfiniteAdeleRing K ≃ₜ mixedEmbedding.mixedSpace K where
  toEquiv := (ringEquiv_mixedSpace K).toEquiv
  continuous_toFun := continuous_ringEquiv_mixedSpace K
  continuous_invFun := continuous_ringEquiv_mixedSpace_symm K

/--
@isnad1 id=ishomeom.0h1v.s9.9b5641d9311d from=translated src=- shape=1251ce30 vocab=5aed3071
-/
theorem main : IsHomeomorph (ringEquiv_mixedSpace K) :=
  (mixedHomeo K).isHomeomorph

end P2mMixedHomeo

/--
@isnad1 id=ishomeom.0h1v.s9.9b5641d9311d from=translated src=- shape=1251ce30 vocab=5aed3071
-/
theorem solution (K : Type) [Field K] :
    IsHomeomorph (InfiniteAdeleRing.ringEquiv_mixedSpace K) :=
  P2mMixedHomeo.main K
