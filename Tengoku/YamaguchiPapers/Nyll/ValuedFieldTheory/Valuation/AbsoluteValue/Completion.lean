/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Extension
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean
import Tengoku.Seed.Analysis.Normed.Field.Instances
import Tengoku.Seed.Analysis.Normed.Module.Completion
import Tengoku.Seed.Analysis.Normed.Unbundled.RingSeminorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Completions of absolute-valued fields

This file supplies the canonical absolute value, completion maps, density,
and complete-target universal property for real-valued absolute values.  An
extension is expressed directly by AbsoluteValue.Extends; no extra
container is introduced.  The base-to-completion algebra instance is the
canonical one inherited from WithAbs; algebras between different completions
remain explicit.
-/

noncomputable section

open scoped Topology

namespace AbsoluteValue

universe u v w

/-- The norm absolute value on the completion attached to `vK`.-/
noncomputable def completionAbsoluteValue
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :
    AbsoluteValue vK.Completion ℝ :=
  NormedField.toAbsoluteValue vK.Completion

/-- The extended absolute value on the completion agrees with the original value
on embedded elements.
@isnad1 id=eq.0h3v.s8.ce87c5525c94 from=translated src=- shape=9e0f674f vocab=bd396c33
-/
@[simp]
theorem completionAbsoluteValue_coe
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) (x : K) :
    completionAbsoluteValue vK (x : vK.Completion) = vK x := by
  change ‖(x : vK.Completion)‖ = vK x
  rw [UniformSpace.Completion.norm_coe]
  rfl

/-- The field equipped with its completion absolute value is complete.
@isnad1 id=complete.0h2v.s9.63ae401e911d from=translated src=- shape=e9bd041b vocab=0e3addfa
-/
theorem completionAbsoluteValue_complete
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :
    CompleteSpace (WithAbs (completionAbsoluteValue vK)) := by
  let e := WithAbs.equiv (completionAbsoluteValue vK)
  have he : Isometry e :=
    AddMonoidHomClass.isometry_of_norm e.toRingHom fun _ ↦ rfl
  exact (completeSpace_congr (e := e.toEquiv) he.isUniformEmbedding).2 inferInstance

/-- Nontriviality passes to the completion absolute value.
@isnad1 id=isnontri.1h2v.s7.6482fe58e67e from=translated src=- shape=8e8e1bed vocab=5a4d674c
-/
theorem completionAbsoluteValue_isNontrivial
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial) :
    (completionAbsoluteValue vK).IsNontrivial := by
  rcases hvK with ⟨x, hx0, hx1⟩
  refine ⟨(x : vK.Completion), ?_, ?_⟩
  · intro hx
    have hx' : (WithAbs.equiv vK).symm x = 0 :=
      UniformSpace.Completion.coe_injective (α := WithAbs vK) hx
    exact hx0 (by simpa using congrArg (WithAbs.equiv vK) hx')
  · simpa using hx1

/-- The canonical embedding of an absolute-valued field in its completion.-/
noncomputable def toCompletion
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) :
    K →+* vK.Completion :=
  UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv vK).symm.toRingHom

/-- The canonical map into the completion sends an element to its constant Cauchy class.
@isnad1 id=eq.0h3v.s9.7e2240a2aa5c from=translated src=- shape=a0385b5a vocab=d39ec3c6
-/
@[simp]
theorem toCompletion_apply
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) (x : K) :
    toCompletion vK x = ((WithAbs.equiv vK).symm x : vK.Completion) :=
  rfl

/-- The canonical completion embedding agrees with the completion algebra map.
@isnad1 id=eq.0h3v.s10.dcf547758e55 from=translated src=- shape=985dee63 vocab=b57431d5
-/
@[simp]
theorem toCompletion_eq_algebraMap
    {K : Type u} [Field K] (vK : AbsoluteValue K ℝ) (x : K) :
    toCompletion vK x = algebraMap K vK.Completion x :=
  rfl

private noncomputable def baseToExtensionCompletion
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ) :
    WithAbs vK →+* wL.Completion :=
  UniformSpace.Completion.coeRingHom.comp
    (algebraMap (WithAbs vK) (WithAbs wL))

private theorem baseToExtensionCompletion_norm
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : WithAbs vK) :
    ‖baseToExtensionCompletion vK wL x‖ = ‖x‖ := by
  change
    ‖((algebraMap (WithAbs vK) (WithAbs wL)) x : wL.Completion)‖ = ‖x‖
  rw [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs,
    WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_algebraMap]
  exact hw x.ofAbs

private theorem baseToExtensionCompletion_isometry
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    Isometry (baseToExtensionCompletion vK wL) :=
  AddMonoidHomClass.isometry_of_norm _
    (baseToExtensionCompletion_norm vK wL hw)

/-- The isometric embedding between completions induced by an exact extension
of absolute values.-/
noncomputable def completionMap
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    vK.Completion →+* wL.Completion :=
  UniformSpace.Completion.extensionHom
    (baseToExtensionCompletion vK wL)
    (baseToExtensionCompletion_isometry vK wL hw).continuous

private theorem completionMap_withAbs_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : WithAbs vK) :
    completionMap vK wL hw (x : vK.Completion) =
      baseToExtensionCompletion vK wL x :=
  UniformSpace.Completion.extensionHom_coe
    (baseToExtensionCompletion vK wL)
    (baseToExtensionCompletion_isometry vK wL hw).continuous x

/-- On the canonical copy of the base field, the map between completions is
the original algebra map followed by the canonical completion map.
@isnad1 id=eq.1h5v.s10.f211b43e1f89 from=translated src=- shape=99daac97 vocab=935da176
-/
@[simp]
theorem completionMap_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : K) :
    completionMap vK wL hw (algebraMap K vK.Completion x) =
      toCompletion wL (algebraMap K L x) := by
  change completionMap vK wL hw
      (((WithAbs.equiv vK).symm x : WithAbs vK) : vK.Completion) =
    (((WithAbs.equiv wL).symm (algebraMap K L x) : WithAbs wL) :
      wL.Completion)
  rw [completionMap_withAbs_coe]
  rfl

/-- The map induced between completions is an isometry.
@isnad1 id=isometry.1h4v.s9.cb531cc96275 from=translated src=- shape=7ca9c8ba vocab=bf0115cb
-/
theorem completionMap_isometry
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    Isometry (completionMap vK wL hw) :=
  (baseToExtensionCompletion_isometry vK wL hw).completion_extension

/-- The algebra structure on the extension completion induced by the
completion map.  It is deliberately explicit rather than a global instance.-/
@[reducible] noncomputable def completionAlgebra
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    Algebra vK.Completion wL.Completion :=
  (completionMap vK wL hw).toAlgebra

/-- The algebra structure on the completion uses the canonical completion embedding.
@isnad1 id=eq.1h5v.s10.241a7badceaf from=translated src=- shape=49e86503 vocab=7796111b
-/
@[simp]
theorem completionAlgebra_algebraMap
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (x : vK.Completion) :
    @algebraMap vK.Completion wL.Completion _ _
        (completionAlgebra vK wL hw) x = completionMap vK wL hw x :=
  rfl

/-- The algebra structure on an extension completion induced by the dense
copy of the extension field.  It is deliberately explicit.-/
@[reducible] noncomputable def extensionCompletionAlgebra
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (wL : AbsoluteValue L ℝ) :
    Algebra K wL.Completion :=
  ((toCompletion wL).comp (algebraMap K L)).toAlgebra

/-- The canonical dense embedding as an algebra homomorphism.-/
noncomputable def toCompletionAlgHom
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (wL : AbsoluteValue L ℝ) :
    letI := extensionCompletionAlgebra (K := K) wL
    L →ₐ[K] wL.Completion := by
  letI := extensionCompletionAlgebra (K := K) wL
  exact
    { __ := toCompletion wL
      commutes' _ := rfl }

/-- The scalar tower `K → K_v → L_w` supplied by an exact extension.
@isnad1 id=isscalar.1h4v.s9.a5bbb941db75 from=translated src=- shape=0c914fe1 vocab=2c3e7a71
-/
theorem completion_isScalarTower
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) :
    letI hK := extensionCompletionAlgebra (K := K) wL
    letI : SMul K wL.Completion := hK.toSMul
    letI := completionAlgebra vK wL hw
    IsScalarTower K vK.Completion wL.Completion := by
  let hK := extensionCompletionAlgebra (K := K) wL
  let : SMul K wL.Completion := hK.toSMul
  let := completionAlgebra vK wL hw
  exact IsScalarTower.of_algebraMap_eq fun x ↦
    (completionMap_coe vK wL hw x).symm

section CompleteTarget

variable {K : Type u} {D : Type w} [Field K] [Field D]

private noncomputable def toCompleteTargetRingHom
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    (i : K →+* D) :
    WithAbs vK →+* WithAbs vD :=
  (WithAbs.equiv vD).symm.toRingHom.comp
    (i.comp (WithAbs.equiv vK).toRingHom)

private theorem toCompleteTargetRingHom_norm
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    (i : K →+* D) (hi : ∀ x : K, vD (i x) = vK x)
    (x : WithAbs vK) :
    ‖toCompleteTargetRingHom vK vD i x‖ = ‖x‖ := by
  change vD (i (WithAbs.equiv vK x)) = vK (WithAbs.equiv vK x)
  exact hi _

private theorem toCompleteTargetRingHom_isometry
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    (i : K →+* D) (hi : ∀ x : K, vD (i x) = vK x) :
    Isometry (toCompleteTargetRingHom vK vD i) :=
  AddMonoidHomClass.isometry_of_norm _
    (toCompleteTargetRingHom_norm vK vD i hi)

/-- A value-preserving embedding into a complete target extends uniquely from
the field to its metric completion.-/
noncomputable def completionMapToCompleteTarget
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    [CompleteSpace (WithAbs vD)]
    (i : K →+* D) (hi : ∀ x : K, vD (i x) = vK x) :
    vK.Completion →+* WithAbs vD :=
  UniformSpace.Completion.extensionHom
    (toCompleteTargetRingHom vK vD i)
    (toCompleteTargetRingHom_isometry vK vD i hi).continuous

private theorem completionMapToCompleteTarget_withAbs_coe
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    [CompleteSpace (WithAbs vD)]
    (i : K →+* D) (hi : ∀ x : K, vD (i x) = vK x)
    (x : WithAbs vK) :
    completionMapToCompleteTarget vK vD i hi
        (x : vK.Completion) =
      toCompleteTargetRingHom vK vD i x :=
  UniformSpace.Completion.extensionHom_coe
    (toCompleteTargetRingHom vK vD i)
    (toCompleteTargetRingHom_isometry vK vD i hi).continuous x

/-- The extension map to a complete target agrees with the original map on
embedded source elements.
@isnad1 id=eq.1h6v.s11.12997f544292 from=translated src=- shape=fd7939ac vocab=7172edee
-/
@[simp]
theorem completionMapToCompleteTarget_coe
    (vK : AbsoluteValue K ℝ) (vD : AbsoluteValue D ℝ)
    [CompleteSpace (WithAbs vD)]
    (i : K →+* D) (hi : ∀ x : K, vD (i x) = vK x)
    (x : K) :
    completionMapToCompleteTarget vK vD i hi
        (algebraMap K vK.Completion x) =
      (WithAbs.equiv vD).symm (i x) := by
  change completionMapToCompleteTarget vK vD i hi
      (((WithAbs.equiv vK).symm x : WithAbs vK) : vK.Completion) = _
  rw [completionMapToCompleteTarget_withAbs_coe]
  rfl

end CompleteTarget

section CompleteTargetTower

variable {K : Type u} {L : Type v} {D : Type w}
variable [Field K] [Field L] [Field D] [Algebra K L]

/-- Dense-point compatibility for extending `L → D` and first embedding the
completed base in the completion of `L`.
@isnad1 id=eq.2h8v.s11.7d02f09b1f54 from=translated src=- shape=faaaa808 vocab=5e249a5f
-/
@[simp]
theorem completionMapToCompleteTarget_comp_completionMap_coe
    (vK : AbsoluteValue K ℝ) (wL : AbsoluteValue L ℝ)
    (hw : Extends vK wL) (vD : AbsoluteValue D ℝ)
    [CompleteSpace (WithAbs vD)]
    (i : L →+* D) (hi : ∀ x : L, vD (i x) = wL x)
    (x : K) :
    completionMapToCompleteTarget wL vD i hi
        (completionMap vK wL hw (algebraMap K vK.Completion x)) =
      (WithAbs.equiv vD).symm (i (algebraMap K L x)) := by
  rw [completionMap_coe, toCompletion_eq_algebraMap,
    completionMapToCompleteTarget_coe]

end CompleteTargetTower

end AbsoluteValue

end
