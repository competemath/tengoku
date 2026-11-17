import Tengoku.Seed.NumberTheory.NumberField.AdeleRing
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms M4aP3B.Rows.DiscreteAdele.finite_setOf_algebraMap_mem_of_isCompact_impl` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms M4aP3B.Rows.DiscreteAdele.gate_univ_infinite` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.AdelicBox
open scoped Pointwise

noncomputable section

namespace M4aP3B
namespace Rows
namespace DiscreteAdele

variable (F : Type) [Field F] [NumberField F]

/--
@isnad1 id=eq.0h2v.s8.70332e47d30f from=translated src=- shape=d188da38 vocab=87444120
-/
theorem fst_algebraMap (ξ : F) :
    (algebraMap F (AdeleRing (𝓞 F) F) ξ).1 = algebraMap F (InfiniteAdeleRing F) ξ := rfl

/--
@isnad1 id=mem.0h1v.s7.139e47b6fa83 from=translated src=- shape=62dc9b7e vocab=9b03104f
-/
theorem zero_mem_integralFiniteAdeles' :
    (0 : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun _ => zero_mem _

/--
@isnad1 id=finite.1h2v.s8.8a14a556e5fb from=translated src=- shape=12dc3ea7 vocab=15ace594
-/
theorem finite_setOf_algebraMap_mem {C : Set (AdeleRing (𝓞 F) F)} (hC : IsCompact C) :
    {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C}.Finite := by
  classical

  have hO : IsOpen (integralFiniteAdeles (𝓞 F) F) := isOpen_integralFiniteAdeles F
  have hCf : IsCompact (Prod.snd '' C) := hC.image continuous_snd
  obtain ⟨t, -, hcover⟩ := hCf.elim_nhds_subcover
    (fun y => (fun z => z - y) ⁻¹' integralFiniteAdeles (𝓞 F) F) fun y _ =>
      (hO.preimage (continuous_id.sub continuous_const)).mem_nhds
        (by simpa only [Set.mem_preimage, Pi.sub_apply, id_eq, sub_self] using zero_mem_integralFiniteAdeles' F)

  have hCinf : IsCompact (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) :=
    (hC.image continuous_fst).image (continuous_ringEquiv_mixedSpace F)
  have hD : IsCompact ((fun p : mixedEmbedding.mixedSpace F × mixedEmbedding.mixedSpace F =>
      p.1 - p.2) '' ((InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) ×ˢ
        (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)))) :=
    (hCinf.prod hCinf).image (continuous_fst.sub continuous_snd)

  haveI : DiscreteTopology (mixedEmbedding.integerLattice F).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (mixedEmbedding.integerLattice F))
  have hL : ((fun p : mixedEmbedding.mixedSpace F × mixedEmbedding.mixedSpace F => p.1 - p.2) ''
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) ×ˢ
        (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C))) ∩
      (mixedEmbedding.integerLattice F : Set (mixedEmbedding.mixedSpace F))).Finite := by
    refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hD.isBounded ?_
    rw [← Submodule.coe_toAddSubgroup]
    exact AddSubgroup.isClosed_of_discrete

  have hT : ∀ y : FiniteAdeleRing (𝓞 F) F,
      {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C ∧
        (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - y ∈ integralFiniteAdeles (𝓞 F) F}.Finite := by
    intro y
    rcases Set.eq_empty_or_nonempty {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C ∧
        (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - y ∈ integralFiniteAdeles (𝓞 F) F} with h0 | ⟨ξ₀, hξ₀C, hξ₀y⟩
    · rw [h0]; exact Set.finite_empty
    refine (hL.preimage (f := fun ξ : F => mixedEmbedding F (ξ - ξ₀)) fun a _ b _ h =>
      sub_left_inj.1 (mixedEmbedding_injective F h)).subset ?_
    rintro ξ ⟨hξC, hξy⟩
    refine ⟨?_, ?_⟩
    ·
      refine ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ).1,
          InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1),
        ⟨⟨(algebraMap F (AdeleRing (𝓞 F) F) ξ).1, ⟨_, hξC, rfl⟩, rfl⟩,
          ⟨(algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1, ⟨_, hξ₀C, rfl⟩, rfl⟩⟩, ?_⟩
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ).1
          - InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1
        = mixedEmbedding F (ξ - ξ₀)
      rw [map_sub, fst_algebraMap, fst_algebraMap, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
        ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    ·
      have h2 : (algebraMap F (AdeleRing (𝓞 F) F) (ξ - ξ₀)).2
          = (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).2 := by
        rw [map_sub]; rfl
      have hdiff : (algebraMap F (AdeleRing (𝓞 F) F) (ξ - ξ₀)).2 ∈ integralFiniteAdeles (𝓞 F) F := by
        rw [h2, ← sub_sub_sub_cancel_right _ _ y]
        exact fun v => sub_mem (hξy v) (hξ₀y v)
      have hval : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (ξ - ξ₀) ≤ 1 := fun v => by
        have h := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (hdiff v)
        rwa [NumberField.AdeleRing.algebraMap_snd_apply,
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
      obtain ⟨o, ho⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (ξ - ξ₀) hval
      show mixedEmbedding F (ξ - ξ₀) ∈ (mixedEmbedding.integerLattice F : Set (mixedEmbedding.mixedSpace F))
      rw [← ho]
      exact ⟨o, rfl⟩

  refine (t.finite_toSet.biUnion fun y _ => hT y).subset fun ξ hξ => ?_
  have h2 : (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 ∈ Prod.snd '' C := ⟨_, hξ, rfl⟩
  obtain ⟨y, hy, hyO⟩ := Set.mem_iUnion₂.1 (hcover h2)
  exact Set.mem_iUnion₂.2 ⟨y, hy, hξ, hyO⟩

/--
@isnad1 id=finite.1h2v.s8.8a14a556e5fb from=translated src=- shape=12dc3ea7 vocab=15ace594
-/
theorem finite_setOf_algebraMap_mem_of_isCompact_impl (F : Type) [Field F] [NumberField F]
    {C : Set (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)} (hC : IsCompact C) :
    {ξ : F | algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ξ ∈ C}.Finite :=
  finite_setOf_algebraMap_mem F hC

/--
@isnad1 id=infinite.0h1v.s8.b64ab8cf2b77 from=translated src=- shape=f1c87979 vocab=f76d63e0
-/
theorem gate_univ_infinite (F : Type) [Field F] [NumberField F] :
    {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ (Set.univ : Set (AdeleRing (𝓞 F) F))}.Infinite := by
  simp only [Set.mem_univ, Set.ofPred_true]
  exact Set.infinite_univ

end M4aP3B.Rows.DiscreteAdele

end

/--
@isnad1 id=finite.1h2v.s8.8a14a556e5fb from=translated src=- shape=12dc3ea7 vocab=15ace594
-/
theorem solution
    (F : Type) [Field F] [NumberField F]
    {C : Set (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)} (hC : IsCompact C) :
    {ξ : F | algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ξ ∈ C}.Finite := by
  first
    | exact M4aP3B.Rows.DiscreteAdele.finite_setOf_algebraMap_mem_of_isCompact_impl F hC
    | (apply M4aP3B.Rows.DiscreteAdele.finite_setOf_algebraMap_mem_of_isCompact_impl <;> assumption)
