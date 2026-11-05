/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.FiniteEtale.Henselian.CompleteOrthogonalIdempotents
import Tengoku.Seed.RingTheory.Etale.Field
import Tengoku.Seed.RingTheory.Localization.Away.Lemmas
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.IntegralClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local factors of finite étale algebras over complete local rings

Finite étale algebras over a complete local ring need not themselves be
local.  Their closed fibre is a finite product of fields.  The corresponding
complete orthogonal idempotents lift through the Henselian closed-fibre map,
and split the algebra into finite étale local factors.  This file establishes
that source decomposition; the later quotient-lifting assembly can use its
factors one at a time.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped TensorProduct

universe u

/-- If a maximal ideal is contained in the Jacobson radical, it is the unique
maximal ideal.
@isnad1 id=islocalr.2h2v.s6.2c598eabe141 from=translated src=- shape=30aad390 vocab=ec520072
-/
theorem isLocalRing_of_isMaximal_of_le_jacobson
    {S : Type u} [CommRing S] (J : Ideal S) (hJ : J.IsMaximal)
    (hjac : J ≤ Ideal.jacobson (⊥ : Ideal S)) :
    IsLocalRing S := by
  refine IsLocalRing.of_unique_max_ideal ⟨J, hJ, ?_⟩
  intro M hM
  symm
  apply hJ.eq_of_le hM.ne_top
  exact hjac.trans (sInf_le ⟨bot_le, hM⟩)

/-- An idempotent factor of a finite algebra is finite over the same base.
@isnad1 id=finite.0h3v.s8.7a02e12b3a3c from=translated src=- shape=8128a479 vocab=72f18a57
-/
theorem moduleFinite_quotient_span_one_sub
    {B D : Type u} [CommRing B] [CommRing D] [Algebra B D]
    [Module.Finite B D] (e : D) :
    Module.Finite B (D ⧸ Ideal.span {1 - e}) := by
  exact Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ B (Ideal.span {1 - e})).toLinearMap
    (Ideal.Quotient.mkₐ_surjective B (Ideal.span {1 - e}))

/-- An idempotent factor of an étale algebra is étale over the same base.
@isnad1 id=etale.1h3v.s7.67d4e97790b8 from=translated src=- shape=6905452a vocab=7443aad6
-/
theorem etale_quotient_span_one_sub_of_isIdempotentElem
    {B D : Type u} [CommRing B] [CommRing D] [Algebra B D]
    [Algebra.Etale B D] (e : D) (he : IsIdempotentElem e) :
    Algebra.Etale B (D ⧸ Ideal.span {1 - e}) := by
  let : IsLocalization.Away e (D ⧸ Ideal.span {1 - e}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem he
  let : Algebra.Etale D (D ⧸ Ideal.span {1 - e}) :=
    Algebra.Etale.of_isLocalizationAway e
  exact Algebra.Etale.comp B D (D ⧸ Ideal.span {1 - e})

/-- The kernel of a coordinate map in a product decomposition is the kernel
of the original map together with the complementary idempotent factor.
@isnad1 id=eq.1h8v.s9.89c6bad7b47d from=translated src=- shape=059567ff vocab=f0776114
-/
theorem ker_evalRingHom_comp_ringEquiv_comp_eq_sup_of_idempotent_lift
    {D F I : Type u} [CommRing D] [CommRing F]
    [Finite I] [DecidableEq I]
    (A : I → Type u) [∀ i, CommRing (A i)]
    (q : D →+* F) (E : F ≃+* ∀ i, A i) (e : I → D)
    (hmap : q ∘ e = E.symm ∘ fun i ↦ Pi.single i 1) (i : I) :
    RingHom.ker ((Pi.evalRingHom A i).comp E.toRingHom |>.comp q) =
      RingHom.ker q ⊔ Ideal.span {1 - e i} := by
  let f : D →+* A i := ((Pi.evalRingHom A i).comp E.toRingHom).comp q
  apply le_antisymm
  · intro d hd
    have hcoord : E (q d) i = 0 := by
      rw [RingHom.mem_ker] at hd
      exact hd
    have hmul : d * e i ∈ RingHom.ker q := by
      rw [RingHom.mem_ker, map_mul]
      apply E.injective
      rw [map_mul, map_zero]
      have hei : E (q (e i)) = Pi.single i 1 := by
        calc
          E (q (e i)) = E (E.symm (Pi.single i 1)) :=
            congrArg E (congrFun hmap i)
          _ = Pi.single i 1 := E.apply_symm_apply _
      rw [hei]
      ext j
      by_cases hji : j = i
      · subst j
        simp [hcoord]
      · simp [hji]
    have hrest : d * (1 - e i) ∈ Ideal.span {1 - e i} :=
      (Ideal.span {1 - e i}).mul_mem_left d
        (Ideal.subset_span (Set.mem_singleton (1 - e i)))
    have hadd : d * e i + d * (1 - e i) ∈
        RingHom.ker q ⊔ Ideal.span {1 - e i} :=
      add_mem
        ((le_sup_left : RingHom.ker q ≤
          RingHom.ker q ⊔ Ideal.span {1 - e i}) hmul)
        ((le_sup_right : Ideal.span {1 - e i} ≤
          RingHom.ker q ⊔ Ideal.span {1 - e i}) hrest)
    convert hadd using 1
    ring
  · apply sup_le
    · intro d hd
      rw [RingHom.mem_ker] at hd ⊢
      simp [hd]
    · apply Ideal.span_le.2
      intro d hd
      simp only [Set.mem_singleton_iff] at hd
      subst d
      change E (q (1 - e i)) i = 0
      have hei : E (q (e i)) = Pi.single i 1 := by
        calc
          E (q (e i)) = E (E.symm (Pi.single i 1)) :=
            congrArg E (congrFun hmap i)
          _ = Pi.single i 1 := E.apply_symm_apply _
      rw [map_sub, map_one, map_sub, map_one, hei]
      simp only [Pi.sub_apply, Pi.one_apply, Pi.single_eq_same, sub_self]

/-- The field factors of the closed fibre of a finite étale algebra over a
complete Noetherian local ring determine a complete orthogonal family of
idempotents upstairs.
@isnad1 id=other.0h2v.s10.1241264a0232 from=translated src=- shape=a751b0b6 vocab=dfad1f5a
-/
theorem exists_closedFiber_fieldFactors_and_idempotents_lift
    {B D : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal B) B]
    [CommRing D] [Algebra B D] [Module.Finite B D] [Algebra.Etale B D] :
    let k := ResidueField B
    let F := k ⊗[B] D
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I) (A : I → Type u)
      (_ : ∀ i, Field (A i)) (_ : ∀ i, Algebra k (A i))
      (E : F ≃ₐ[k] ∀ i, A i) (e : I → D),
      CompleteOrthogonalIdempotents e ∧
        (Algebra.TensorProduct.includeRight : D →ₐ[B] F) ∘ e =
          E.symm ∘ fun i ↦ Pi.single i 1 := by
  classical
  let k := ResidueField B
  let F := k ⊗[B] D
  let q : D →+* F :=
    (Algebra.TensorProduct.includeRight : D →ₐ[B] F)
  let : Module.Finite k F := inferInstance
  let : Algebra.Etale k F := Algebra.Etale.baseChange B D k
  obtain ⟨I, hI, A, hAfield, hAalg, E, -⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod k F).mp
      (inferInstance : Algebra.Etale k F)
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let (i : I) : Field (A i) := hAfield i
  let (i : I) : Algebra k (A i) := hAalg i
  let eFiber : I → F := fun i ↦ E.symm (Pi.single i 1)
  have heFiber : CompleteOrthogonalIdempotents eFiber := by
    change CompleteOrthogonalIdempotents
      (E.symm.toRingEquiv.toRingHom ∘ fun i ↦ Pi.single i 1)
    exact (CompleteOrthogonalIdempotents.single A).map E.symm.toRingHom
  have hqsurjective : Function.Surjective q := by
    have hresidue : Function.Surjective (algebraMap B k) := by
      change Function.Surjective
        (Ideal.Quotient.mk (maximalIdeal B))
      exact Ideal.Quotient.mk_surjective
    intro y
    obtain ⟨x, hx⟩ :=
      Algebra.TensorProduct.includeRight_surjective D hresidue y
    exact ⟨x, hx⟩
  let : HenselianRing D
      ((maximalIdeal B).map (algebraMap B D)) :=
    henselianRing_map_algebraMap_of_moduleFinite_of_isAdicComplete
  let : HenselianRing D (RingHom.ker q) := by
    have hker : RingHom.ker q =
        (maximalIdeal B).map (algebraMap B D) := by
      simpa only [q] using
        (residueField_tensor_includeRight_ker_eq_maximalIdeal_map
          (R := B) (S := D))
    rw [hker]
    infer_instance
  obtain ⟨e, he, hmap⟩ :=
    exists_completeOrthogonalIdempotents_lift_of_surjective_henselianRing_ker
      q hqsurjective eFiber heFiber
  exact ⟨I, inferInstance, Classical.decEq I, A, hAfield, hAalg, E, e, he, by
    funext i
    exact congrFun hmap i⟩

end EtaleFundamentalGroups

end
