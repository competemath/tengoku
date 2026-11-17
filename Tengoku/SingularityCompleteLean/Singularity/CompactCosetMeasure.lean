import Tengoku.SingularityCompleteLean.Singularity.CompactFundamentalDomain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A common compactly supported transversal and quotient measures

Choose one geometric transversal, independent of the measure. It is a
fundamental domain for every measure. Locally finite measures therefore give
finite quotient measures; right lattice invariance makes the quotient
independent of the fundamental domain and preserves any left translation
which preserves the original measure.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Topology
open scoped Pointwise

namespace Singularity

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]

/-- A geometric measurable transversal with a compact bound, independent of any measure.
@isnad1 id=ex.0h2v.s7.19390071e02c from=translated src=- shape=df9bd8d6 vocab=af1e1e42
-/
theorem exists_compact_coset_transversal :
    ∃ S K : Set G, MeasurableSet S ∧ IsCompact K ∧ S ⊆ K ∧
      Set.InjOn (QuotientGroup.mk : G → G ⧸ Γ) S ∧
      (QuotientGroup.mk : G → G ⧸ Γ) '' S = univ := by
  have hc := (Γ.isQuotientCoveringMap ⟨inferInstance⟩).isCoveringMap.isLocalHomeomorph
  exact exists_compact_measurable_transversal (QuotientGroup.mk : G → G ⧸ Γ)
    hc QuotientGroup.mk_surjective

/-- The common transversal used for all measures on this coset quotient.-/
def compactCosetTransversal : Set G := (exists_compact_coset_transversal Γ).choose

/-- A compact set containing the chosen transversal.-/
def compactCosetTransversalBound : Set G := (exists_compact_coset_transversal Γ).choose_spec.choose

/--
@isnad1 id=measurab.0h2v.s6.b0f6c568cfdc from=translated src=- shape=3336c346 vocab=10ff8c73
-/
theorem compactCosetTransversal_measurable : MeasurableSet (compactCosetTransversal Γ) :=
  (exists_compact_coset_transversal Γ).choose_spec.choose_spec.1

/--
@isnad1 id=iscompac.0h2v.s6.73dd8949ec5b from=translated src=- shape=3336c346 vocab=629fd410
-/
theorem compactCosetTransversalBound_compact : IsCompact (compactCosetTransversalBound Γ) :=
  (exists_compact_coset_transversal Γ).choose_spec.choose_spec.2.1

/--
@isnad1 id=le.0h2v.s6.3fa416879bd4 from=translated src=- shape=e591cc53 vocab=6dc8b5b1
-/
theorem compactCosetTransversal_subset : compactCosetTransversal Γ ⊆ compactCosetTransversalBound Γ :=
  (exists_compact_coset_transversal Γ).choose_spec.choose_spec.2.2.1

/--
@isnad1 id=injon.0h2v.s6.2b8a8f9efa04 from=translated src=- shape=0689a707 vocab=fa6b5600
-/
theorem compactCosetTransversal_injective :
    Set.InjOn (QuotientGroup.mk : G → G ⧸ Γ) (compactCosetTransversal Γ) :=
  (exists_compact_coset_transversal Γ).choose_spec.choose_spec.2.2.2.1

/--
@isnad1 id=eq.0h2v.s7.69ccb626377f from=translated src=- shape=2608b29f vocab=fdeb444b
-/
theorem compactCosetTransversal_surjective :
    (QuotientGroup.mk : G → G ⧸ Γ) '' compactCosetTransversal Γ = univ :=
  (exists_compact_coset_transversal Γ).choose_spec.choose_spec.2.2.2.2

/-- The same geometric transversal is a fundamental domain for every measure.
@isnad1 id=isfundam.0h3v.s7.695ac56e7d1a from=translated src=- shape=3668877f vocab=ce3e709c
-/
theorem compactCosetTransversal_fundamental (m : Measure G) :
    IsFundamentalDomain Γ.op (compactCosetTransversal Γ) m :=
  isFundamentalDomain_of_quotient_transversal Γ m (compactCosetTransversal_measurable Γ)
    (compactCosetTransversal_injective Γ) (compactCosetTransversal_surjective Γ)

/-- Push the measure on the common transversal to the quotient.-/
def compactCosetQuotientMeasure (m : Measure G) : Measure (G ⧸ Γ) :=
  (m.restrict (compactCosetTransversal Γ)).map QuotientGroup.mk

/--
@isnad1 id=lt.0h3v.s7.b41bdfd6787a from=translated src=- shape=e1698848 vocab=9c2085f2
-/
theorem compactCosetTransversal_finite (m : Measure G) [IsLocallyFiniteMeasure m] :
    m (compactCosetTransversal Γ) < ⊤ :=
  (measure_mono (compactCosetTransversal_subset Γ)).trans_lt
    (compactCosetTransversalBound_compact Γ).measure_lt_top

/--
@isnad1 id=isfinite.0h3v.s7.f7929de0cecb from=translated src=- shape=1997f74b vocab=e1376c36
-/
theorem compactCosetQuotientMeasure_finite (m : Measure G) [IsLocallyFiniteMeasure m] :
    IsFiniteMeasure (compactCosetQuotientMeasure Γ m) := by
  let : Fact (m (compactCosetTransversal Γ) < ⊤) := ⟨compactCosetTransversal_finite Γ m⟩
  unfold compactCosetQuotientMeasure
  infer_instance

/--
@isnad1 id=eq.0h3v.s7.cc4ec1c981cb from=translated src=- shape=f4cda2d3 vocab=ecf826af
-/
theorem compactCosetQuotientMeasure_univ (m : Measure G) :
    compactCosetQuotientMeasure Γ m univ = m (compactCosetTransversal Γ) := by
  have hπ : Measurable (QuotientGroup.mk : G → G ⧸ Γ) := measurable_quotient_mk' (s := QuotientGroup.leftRel Γ)
  rw [compactCosetQuotientMeasure, Measure.map_apply hπ MeasurableSet.univ]
  simp

/-- A nonzero right lattice invariant measure descends to a nonzero quotient measure.
@isnad1 id=ne.1h3v.s7.c0f37e745e96 from=translated src=- shape=e3ff77fc vocab=083654e8
-/
theorem compactCosetQuotientMeasure_ne_zero (m : Measure G) [SMulInvariantMeasure Γ.op G m]
    (hm : m ≠ 0) : compactCosetQuotientMeasure Γ m ≠ 0 := by
  let : Countable Γ := countable_of_Lindelof_of_discrete
  have hpos := (compactCosetTransversal_fundamental Γ m).measure_ne_zero hm
  intro he
  apply hpos
  rw [← compactCosetQuotientMeasure_univ Γ m, he]
  rfl

/-- The quotient is invariant under any single left translation preserving the upstairs measure.
@isnad1 id=measurep.1h4v.s8.20365b5f5c85 from=translated src=- shape=7a1effa2 vocab=de6a6f1d
-/
theorem compactCosetQuotientMeasure_left_invariant (m : Measure G)
    [SMulInvariantMeasure Γ.op G m] (a : G)
    (ha : MeasurePreserving (fun x : G => a * x) m m) :
    MeasurePreserving (fun q : G ⧸ Γ => a • q)
      (compactCosetQuotientMeasure Γ m) (compactCosetQuotientMeasure Γ m) := by
  let : Countable Γ := countable_of_Lindelof_of_discrete
  let S := compactCosetTransversal Γ
  let π : G → G ⧸ Γ := QuotientGroup.mk
  have hπ : Measurable π := measurable_quotient_mk' (s := QuotientGroup.leftRel Γ)
  have hS := compactCosetTransversal_fundamental Γ m
  have hS' : IsFundamentalDomain Γ.op ((fun x : G => a * x) ⁻¹' S) m := by
    apply hS.preimage_of_equiv ha.quasiMeasurePreserving Function.bijective_id
    intro γ x
    change a * (x * MulOpposite.unop (γ : Gᵐᵒᵖ)) = (a * x) * MulOpposite.unop (γ : Gᵐᵒᵖ)
    exact (mul_assoc _ _ _).symm
  have he : compactCosetQuotientMeasure Γ m = (m.restrict ((fun x : G => a * x) ⁻¹' S)).map π :=
    hS.quotientMeasure_eq m hS'
  refine ⟨measurable_const_smul a, ?_⟩
  conv_lhs => rw [he]
  rw [Measure.map_map (measurable_const_smul a) hπ]
  have hcomm : (fun q : G ⧸ Γ => a • q) ∘ π = π ∘ (fun x : G => a * x) := rfl
  rw [hcomm, ← Measure.map_map hπ ha.measurable,
    (ha.restrict_preimage (compactCosetTransversal_measurable Γ)).map_eq]
  rfl

/-- Absolute continuity upstairs passes to the common quotient construction.
@isnad1 id=absolute.1h4v.s7.d8e2a2e48725 from=translated src=- shape=d99c7832 vocab=c579d2fd
-/
theorem compactCosetQuotientMeasure_absolutelyContinuous (m ρ : Measure G) (h : m ≪ ρ) :
    compactCosetQuotientMeasure Γ m ≪ compactCosetQuotientMeasure Γ ρ :=
  (h.restrict (compactCosetTransversal Γ)).map
    (show Measurable (QuotientGroup.mk : G → G ⧸ Γ) from measurable_quotient_mk' (s := QuotientGroup.leftRel Γ))

/-- Null quotient sets are exactly those whose full frame preimages are null.
@isnad1 id=iff.1h4v.s8.f52e43bbd866 from=translated src=- shape=45be86db vocab=329d5af0
-/
theorem compactCosetQuotientMeasure_null_iff (m : Measure G)
    [SMulInvariantMeasure Γ.op G m] {A : Set (G ⧸ Γ)} (hA : MeasurableSet A) :
    compactCosetQuotientMeasure Γ m A = 0 ↔ m (QuotientGroup.mk ⁻¹' A) = 0 := by
  let : Countable Γ := countable_of_Lindelof_of_discrete
  have hπ : Measurable (QuotientGroup.mk : G → G ⧸ Γ) :=
    measurable_quotient_mk' (s := QuotientGroup.leftRel Γ)
  rw [compactCosetQuotientMeasure, Measure.map_apply hπ hA, Measure.restrict_apply (hπ hA)]
  constructor
  · intro h
    apply (compactCosetTransversal_fundamental Γ m).measure_zero_of_invariant _ _ h
    intro γ
    ext x
    simp only [mem_smul_set_iff_inv_smul_mem, mem_preimage]
    have he : (QuotientGroup.mk (γ⁻¹ • x) : G ⧸ Γ) = QuotientGroup.mk x :=
      @Quotient.sound G (MulAction.orbitRel Γ.op G) _ _ ⟨γ⁻¹, rfl⟩
    exact he ▸ Iff.rfl
  · exact fun h => measure_mono_null inter_subset_left h

/-- For right lattice invariant measures, quotient absolute continuity is equivalent
 to absolute continuity upstairs.
@isnad1 id=iff.0h4v.s7.669b5ff9ca33 from=translated src=- shape=54445722 vocab=d58add83
-/
theorem compactCosetQuotientMeasure_absolutelyContinuous_iff (m ρ : Measure G)
    [SMulInvariantMeasure Γ.op G m] [SMulInvariantMeasure Γ.op G ρ] :
    compactCosetQuotientMeasure Γ m ≪ compactCosetQuotientMeasure Γ ρ ↔ m ≪ ρ := by
  let : Countable Γ := countable_of_Lindelof_of_discrete
  constructor
  · intro h
    apply AbsolutelyContinuous.mk
    intro A hA hρ
    have he : (QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' ((QuotientGroup.mk : G → G ⧸ Γ) '' A) =
        ⋃ γ : Γ.op, (fun x : G => γ • x) '' A :=
      MulAction.quotient_preimage_image_eq_union_mul A (G := Γ.op)
    have himage : MeasurableSet ((QuotientGroup.mk : G → G ⧸ Γ) '' A) := by
      apply measurableSet_quotient.mpr
      change MeasurableSet ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' ((QuotientGroup.mk : G → G ⧸ Γ) '' A))
      rw [he]
      exact MeasurableSet.iUnion fun γ => hA.const_smul γ
    have hpre : ρ ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' ((QuotientGroup.mk : G → G ⧸ Γ) '' A)) = 0 := by
      rw [he]
      apply measure_iUnion_null
      intro γ
      change ρ (γ • A) = 0
      rw [measure_smul, hρ]
    have hq := h ((compactCosetQuotientMeasure_null_iff Γ ρ himage).mpr hpre)
    exact measure_mono_null (Set.subset_preimage_image _ _)
      ((compactCosetQuotientMeasure_null_iff Γ m himage).mp hq)
  · exact compactCosetQuotientMeasure_absolutelyContinuous Γ m ρ

end Singularity
