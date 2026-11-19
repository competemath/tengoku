import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyActivePaperCutoff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Physical length tails versus regenerated minimal-layer prefixes

At a fixed point, the supporting intervals form an inclusion chain. Along
that chain the actual regenerated labels respect inclusion. Thus every
physical length tail is a full prefix minus one smaller prefix. Numerical
labels from a different family are never identified.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyGenerationLayers

open KrauseLaceyStoppingExtraction

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/--
@isnad1 id=le.1h2v.s4.26ece9602194 from=translated src=- shape=ee69e874 vocab=18da39c3
-/
theorem length_le_of_carrier_subset_physical {I J : RealInterval}
    (h : I.carrier ⊆ J.carrier) : I.length ≤ J.length := by
  have he := (Ioc_subset_Ioc_iff I.left_lt_right).mp h
  dsimp [RealInterval.length]
  linarith [he.1, he.2]

/--
@isnad1 id=le.6h4v.s7.035152240304 from=translated src=- shape=bd06ff9d vocab=7e37f6f5
-/
theorem carrier_subset_of_generationIndex_le_at_point
    {N : Finset RealInterval}
    (hlam : Set.Pairwise (↑N : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    {I J : RealInterval} (hI : I ∈ N) (hJ : J ∈ N) {x : ℝ}
    (hxI : x ∈ I.carrier) (hxJ : x ∈ J.carrier)
    (hidx : generationIndex N I ≤ generationIndex N J) : I.carrier ⊆ J.carrier := by
  by_cases heq : I = J
  · exact heq ▸ Subset.rfl
  rcases hlam hI hJ heq with hsub | hsub | hd
  · exact hsub
  · have hlt := generation_index_lt_of_proper_subset
      (generationIndex_spec hJ).2 (generationIndex_spec hI).2 hsub (Ne.symm heq)
    omega
  · exact (Set.disjoint_left.mp hd hxI hxJ).elim

/-- The actual covering chain determines a regenerated prefix cutoff
for every physical length threshold.
@isnad1 id=ex.1h3v.s6.b26c982846e9 from=translated src=- shape=3324f2fa vocab=7ff7e55f
-/
theorem exists_generation_cutoff_for_length
    (N : Finset RealInterval)
    (hlam : Set.Pairwise (↑N : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (t x : ℝ) : ∃ n ≤ N.card, ∀ I ∈ N, x ∈ I.carrier →
      (I.length < t ↔ generationIndex N I < n) := by
  let Q := N.filter fun I ↦ I.length < t ∧ x ∈ I.carrier
  let n := Q.sup fun I ↦ generationIndex N I + 1
  have hn : n ≤ N.card := Finset.sup_le fun I hI ↦
    (generationIndex_spec (Finset.mem_filter.mp hI).1).1
  refine ⟨n, hn, ?_⟩
  intro I hI hxI
  constructor
  · intro ht
    have h := Finset.le_sup (f := fun I ↦ generationIndex N I + 1)
      (Finset.mem_filter.mpr ⟨hI, ht, hxI⟩ : I ∈ Q)
    exact h
  · intro hi
    obtain ⟨J, hJ, hij⟩ := Finset.lt_sup_iff.mp hi
    have hj := Finset.mem_filter.mp hJ
    have hsub := carrier_subset_of_generationIndex_le_at_point hlam hI hj.1 hxI hj.2.2
      (by omega : generationIndex N I ≤ generationIndex N J)
    exact (length_le_of_carrier_subset_physical hsub).trans_lt hj.2.1

noncomputable def generationPrefixNormMax
    (N : Finset RealInterval) (v : RealInterval → ℂ) : ℝ :=
  ⨆ n : Fin (N.card + 1), ‖∑ i ∈ Finset.range n.val, ∑ I ∈ generation N i, v I‖

/--
@isnad1 id=le.2h4v.s7.4a29bc46486e from=translated src=- shape=83689941 vocab=98ee47f1
-/
theorem norm_lengthTail_le_two_generationPrefixNormMax
    (N : Finset RealInterval)
    (hlam : Set.Pairwise (↑N : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (v : RealInterval → ℂ) (t x : ℝ)
    (hsupport : ∀ I ∈ N, x ∉ I.carrier → v I = 0) :
    ‖∑ I ∈ N, if t ≤ I.length then v I else 0‖ ≤
      2 * generationPrefixNormMax N v := by
  obtain ⟨n, hn, hcut⟩ := exists_generation_cutoff_for_length N hlam t x
  have hpiece (I : RealInterval) (hI : I ∈ N) :
      (if t ≤ I.length then v I else 0) =
        v I - (if generationIndex N I < n then v I else 0) := by
    by_cases hxI : x ∈ I.carrier
    · by_cases ht : I.length < t
      · simp only [not_le_of_gt ht, ite_false, (hcut I hI hxI).mp ht, ite_true, sub_self]
      · have hi : ¬ generationIndex N I < n := mt (hcut I hI hxI).mpr ht
        simp only [le_of_not_gt ht, ite_true, hi, ite_false, sub_zero]
    · simp only [hsupport I hI hxI, ite_self, sub_self]
  have hfull : (∑ I ∈ N, v I) =
      ∑ i ∈ Finset.range N.card, ∑ I ∈ generation N i, v I := by
    simpa only [one_smul] using (sum_smul_generations_eq N v (fun _ ↦ (1 : ℝ))).symm
  have hprefix : (∑ I ∈ N, if generationIndex N I < n then v I else 0) =
      ∑ i ∈ Finset.range n, ∑ I ∈ generation N i, v I := by
    simpa only [one_smul, ite_smul, zero_smul] using
      (sum_smul_generations_range_eq N v (fun _ ↦ (1 : ℝ)) n).symm
  have hbound (m : ℕ) (hm : m ≤ N.card) :
      ‖∑ i ∈ Finset.range m, ∑ I ∈ generation N i, v I‖ ≤ generationPrefixNormMax N v :=
    le_ciSup (Set.finite_range (fun n : Fin (N.card + 1) ↦
      ‖∑ i ∈ Finset.range n.val, ∑ I ∈ generation N i, v I‖)).bddAbove
      ⟨m, by omega⟩
  rw [Finset.sum_congr rfl hpiece, Finset.sum_sub_distrib, hfull, hprefix]
  exact (norm_sub_le _ _).trans (by linarith [hbound N.card le_rfl, hbound n hn])

end KrauseLaceyGenerationLayers
end QuadraticCarleson
