import Tengoku.TunnellTwoToOneMap.TunnellMap.GloballyRankedExistence
import Tengoku.TunnellTwoToOneMap.TunnellMap.Parking

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Deferred-acceptance correctness contract

The source-proposing algorithm considers every target preceding a source's
final partner, and a target's held key can only decrease.  Its terminal
certificate therefore says that every such proposal is beaten by the final
held edge.  For globally ranked pairs this certificate is equivalent to
stability and hence identifies the unique stable perfect matching.
-/

namespace TunnellMap

namespace GloballyRanked

variable {K S T : Type*} [LinearOrder K]

/-- The transcript-free terminal certificate of source-proposing deferred
acceptance.-/
def DeferredAcceptanceCertificate (I : GloballyRanked K S T) (M : S ≃ T) : Prop :=
  ∀ s t, I.rank s t < I.rank s (M s) →
    I.rank (M.symm t) t < I.rank s t

/--
@isnad1 id=deferred.1h5v.s5.adcb2bcfbb21 from=translated src=- shape=826af070 vocab=b1b4552a
-/
theorem stable_deferredAcceptanceCertificate (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) : I.DeferredAcceptanceCertificate M := by
  intro s t hsource
  have htargetLe : I.rank (M.symm t) t ≤ I.rank s t := by
    apply le_of_not_gt
    intro htarget
    exact hM s t ⟨hsource, htarget⟩
  apply lt_of_le_of_ne htargetLe
  intro heq
  have hs : M.symm t = s := I.target_injective t heq
  have ht : t = M s := by
    rw [← hs]
    simp
  rw [ht] at hsource
  exact (lt_irrefl _) hsource

/--
@isnad1 id=stable.1h5v.s5.c3ce349f5ece from=translated src=- shape=826af070 vocab=b1b4552a
-/
theorem stable_of_deferredAcceptanceCertificate (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.DeferredAcceptanceCertificate M) : I.Stable M := by
  intro s t hblock
  have hfinal := hM s t hblock.1
  exact (not_lt_of_ge hfinal.le) hblock.2

/--
@isnad1 id=iff.0h5v.s5.030affcd2011 from=translated src=- shape=6e74e1e4 vocab=b1b4552a
-/
theorem stable_iff_deferredAcceptanceCertificate (I : GloballyRanked K S T)
    (M : S ≃ T) :
    I.Stable M ↔ I.DeferredAcceptanceCertificate M :=
  ⟨I.stable_deferredAcceptanceCertificate M,
    I.stable_of_deferredAcceptanceCertificate M⟩

section Finite

variable [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

/-- The targets to which source-proposing deferred acceptance sends a
proposal: all strictly preferred targets and then the final partner.-/
def proposalTargets (I : GloballyRanked K S T) (M : S ≃ T) (s : S) : Finset T :=
  insert (M s) (I.preferredTargets M s)

/--
@isnad1 id=mem.0h6v.s6.b2f6fa427da8 from=translated src=- shape=993b7c21 vocab=1d7f2680
-/
@[simp] theorem finalPartner_mem_proposalTargets (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) : M s ∈ I.proposalTargets M s := by
  simp [proposalTargets]

/--
@isnad1 id=not.0h6v.s6.582e8437fa11 from=translated src=- shape=24b3fe1c vocab=948a9fa7
-/
theorem finalPartner_not_mem_preferredTargets (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) : M s ∉ I.preferredTargets M s := by
  simp [preferredTargets]

/--
@isnad1 id=eq.0h6v.s5.847614e708e4 from=translated src=- shape=ea7f269f vocab=845a8243
-/
theorem proposalTargets_card (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) :
    (I.proposalTargets M s).card = I.proposalCount M s := by
  simp [proposalTargets, proposalCount, I.finalPartner_not_mem_preferredTargets M s]

/-- No source proposes twice to one target, and its total number of proposals
is at most the size of the target side.
@isnad1 id=le.0h6v.s5.6a33f8c54980 from=translated src=- shape=20e702e9 vocab=c47b3f21
-/
theorem proposalCount_le_card (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) : I.proposalCount M s ≤ Fintype.card T := by
  rw [← I.proposalTargets_card M s, ← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- The elementary `m²` termination bound before the parking improvement.
@isnad1 id=le.0h5v.s6.b64cd959b4ae from=translated src=- shape=a2f08c61 vocab=85788072
-/
theorem proposalCount_total_le_square (I : GloballyRanked K S T)
    (M : S ≃ T) :
    (∑ s : S, I.proposalCount M s) ≤ Fintype.card S * Fintype.card T := by
  calc
    (∑ s : S, I.proposalCount M s) ≤ ∑ _s : S, Fintype.card T :=
      Finset.sum_le_sum fun s _ => I.proposalCount_le_card M s
    _ = Fintype.card S * Fintype.card T := by simp

/-- Any perfect matching returned with the terminal deferred-acceptance
certificate is the unique stable matching.
@isnad1 id=eq.2h5v.s6.a20ee920d789 from=translated src=- shape=a1d1ee17 vocab=9f386090
-/
theorem deferredAcceptance_output_unique (I : GloballyRanked K S T)
    (hcard : Fintype.card S = Fintype.card T)
    (M : S ≃ T) (hM : I.DeferredAcceptanceCertificate M) :
    M = Classical.choose (I.exists_unique_stable hcard) := by
  classical
  exact (Classical.choose_spec (I.exists_unique_stable hcard)).2 M
    (I.stable_of_deferredAcceptanceCertificate M hM)

end Finite

end GloballyRanked

end TunnellMap
