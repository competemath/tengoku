/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.FieldTheory.KrullTopology
import Tengoku.Seed.FieldTheory.Galois.Basic
import Tengoku.Seed.FieldTheory.Galois.Infinite
import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Basic
import Tengoku.Seed.Topology.Algebra.Group.Basic
import Tengoku.Seed.Topology.Algebra.ContinuousMonoidHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The topology of a finite intermediate field's fixing subgroup

The usual algebraic identification of the fixing subgroup with the relative
Galois group is a homeomorphism for the Krull topologies. Finiteness of the
intermediate field suffices; no normality or algebraicity of the ambient
extension is needed.
-/

namespace KummerTheory

open scoped Topology

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
  (L : IntermediateField K Ω)

/-- The fixing subgroup equivalence preserves evaluation in the ambient field.
@isnad1 id=eq.0h5v.s12.ee7ddd0342bc from=translated src=- shape=131a0a30 vocab=fb7e5047
-/
theorem fixingSubgroupEquiv_apply (σ : L.fixingSubgroup) (x : Ω) :
    L.fixingSubgroupEquiv σ x = (σ : Gal(Ω/K)) x := by
  rfl

/-- The inverse fixing subgroup equivalence preserves ambient evaluation.
@isnad1 id=eq.0h5v.s12.25e513917aab from=translated src=- shape=bd62384d vocab=51105189
-/
theorem fixingSubgroupEquiv_symm_apply (σ : Gal(Ω/L)) (x : Ω) :
    (L.fixingSubgroupEquiv.symm σ : Gal(Ω/K)) x = σ x := by
  rfl

variable [FiniteDimensional K L]

/-- Reinterpreting an ambient fixing automorphism as an `L`-automorphism is continuous.
@isnad1 id=continuo.0h3v.s12.5bf975adc549 from=translated src=- shape=3c55d71f vocab=1e153818
-/
theorem fixingSubgroupEquiv_continuous : Continuous L.fixingSubgroupEquiv := by
  apply continuous_of_tendsto_nhds_one L.fixingSubgroupEquiv
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff L Ω U).mp hU
  have hEK : FiniteDimensional K (E.restrictScalars K) :=
    FiniteDimensional.trans K L E
  have hO : IsOpen ((Subtype.val : L.fixingSubgroup → Gal(Ω/K)) ⁻¹'
      ((E.restrictScalars K).fixingSubgroup : Set Gal(Ω/K))) :=
    (E.restrictScalars K).fixingSubgroup_isOpen.preimage continuous_subtype_val
  apply Filter.mem_of_superset (hO.mem_nhds (Subgroup.one_mem
    (E.restrictScalars K).fixingSubgroup))
  intro σ hσ
  apply hEU
  apply (IntermediateField.mem_fixingSubgroup_iff E (L.fixingSubgroupEquiv σ)).mpr
  intro x hx
  rw [fixingSubgroupEquiv_apply]
  exact (IntermediateField.mem_fixingSubgroup_iff (E.restrictScalars K) σ.val).mp hσ x hx

/-- Restricting scalars from `L` back to `K` is continuous into the fixing subgroup.
@isnad1 id=continuo.0h3v.s12.6717d1d93b96 from=translated src=- shape=37525341 vocab=9464677a
-/
theorem fixingSubgroupEquiv_symm_continuous : Continuous L.fixingSubgroupEquiv.symm := by
  apply Continuous.subtype_mk
  let r : Gal(Ω/L) →* Gal(Ω/K) :=
    L.fixingSubgroup.subtype.comp L.fixingSubgroupEquiv.symm.toMonoidHom
  change Continuous r
  apply continuous_of_tendsto_nhds_one r
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).mp hU
  let F : IntermediateField L Ω :=
    IntermediateField.extendScalars (show L ≤ L ⊔ E from le_sup_left)
  have hFK : FiniteDimensional K F := IntermediateField.finiteDimensional_sup L E
  have hF : FiniteDimensional L F := FiniteDimensional.right K L F
  apply (krullTopology_mem_nhds_one_iff L Ω (r ⁻¹' U)).mpr
  refine ⟨F, hF, ?_⟩
  intro σ hσ
  apply hEU
  apply (IntermediateField.mem_fixingSubgroup_iff E (r σ)).mpr
  intro x hx
  change σ x = x
  exact (IntermediateField.mem_fixingSubgroup_iff F σ).mp hσ x
    ((show E ≤ L ⊔ E from le_sup_right) hx)

/-- The finite intermediate field's fixing subgroup is its relative Galois group,
with the same Krull topology.-/
def fixingSubgroupContinuousEquiv : L.fixingSubgroup ≃ₜ* Gal(Ω/L) where
  toMulEquiv := L.fixingSubgroupEquiv
  continuous_toFun := fixingSubgroupEquiv_continuous L
  continuous_invFun := fixingSubgroupEquiv_symm_continuous L

/-- Evaluation of the continuous fixing subgroup equivalence.
@isnad1 id=eq.0h4v.s13.ecdbd6c24e26 from=translated src=- shape=fa1f03a9 vocab=525bd1f0
-/
theorem fixingSubgroupContinuousEquiv_apply (σ : L.fixingSubgroup) :
    fixingSubgroupContinuousEquiv L σ = L.fixingSubgroupEquiv σ := by
  rfl

/-- Evaluation of the inverse continuous fixing subgroup equivalence.
@isnad1 id=eq.0h4v.s13.d4588ff4f869 from=translated src=- shape=aa469d66 vocab=37ce9bcc
-/
theorem fixingSubgroupContinuousEquiv_symm_apply (σ : Gal(Ω/L)) :
    (fixingSubgroupContinuousEquiv L).symm σ = L.fixingSubgroupEquiv.symm σ := by
  rfl

/-- Every open subgroup of a Galois group is the relative Galois group
of a finite intermediate field, with its actual Krull topology.
@isnad1 id=ex.0h3v.s10.8d988cc414da from=translated src=- shape=ba2045d0 vocab=9b5e4776
-/
theorem exists_finiteIntermediateField_openSubgroup_equiv
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (H : OpenSubgroup Gal(Ω/K)) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      Nonempty ((H : Subgroup Gal(Ω/K)) ≃ₜ* Gal(Ω/E)) := by
  let E : IntermediateField K Ω :=
    IntermediateField.fixedField (H : Subgroup Gal(Ω/K))
  let closedH : ClosedSubgroup Gal(Ω/K) := ⟨H.toSubgroup, H.isClosed⟩
  have hfix : E.fixingSubgroup = (H : Subgroup Gal(Ω/K)) :=
    InfiniteGalois.fixingSubgroup_fixedField closedH
  have hE : FiniteDimensional K E :=
    (InfiniteGalois.isOpen_iff_finite E).mp (by
      rw [hfix]
      exact H.isOpen)
  have : FiniteDimensional K E := hE
  let e₀ : (H : Subgroup Gal(Ω/K)) ≃ₜ* E.fixingSubgroup :=
    { toMulEquiv := MulEquiv.subgroupCongr hfix.symm
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val
        (fun x => hfix.symm ▸ x.property)
      continuous_invFun := Continuous.subtype_mk continuous_subtype_val
        (fun x => hfix ▸ x.property) }
  exact ⟨E, hE, ⟨e₀.trans (fixingSubgroupContinuousEquiv E)⟩⟩

end KummerTheory
