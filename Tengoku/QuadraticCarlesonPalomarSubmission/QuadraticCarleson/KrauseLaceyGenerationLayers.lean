import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyStoppingExtraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual finite minimal-generation decomposition

These are the successive inclusion-minimal layers used in KL18. Their
disjointness and finite exhaustion are proved from laminarity and finiteness.
No relative scale gap is inferred merely from a gap between layer labels.
-/

open Function Set

namespace QuadraticCarleson
namespace KrauseLaceyGenerationLayers

open KrauseLaceyStoppingExtraction

set_option autoImplicit false

/-- The literal inclusion-minimal intervals of a finite collection.-/
noncomputable def minimalLayer (S : Finset RealInterval) : Finset RealInterval := by
  classical
  exact S.filter fun I ↦ ∀ J ∈ S, J.carrier ⊆ I.carrier → J = I

/--
@isnad1 id=iff.0h2v.s5.16510a4b034b from=translated src=- shape=1d0fe556 vocab=82315c65
-/
theorem mem_minimalLayer_iff {S : Finset RealInterval} {I : RealInterval} :
    I ∈ minimalLayer S ↔ I ∈ S ∧ ∀ J ∈ S, J.carrier ⊆ I.carrier → J = I := by
  classical
  simp [minimalLayer]

/--
@isnad1 id=le.0h1v.s4.5852ac7901da from=translated src=- shape=76c97b8b vocab=8b3ca904
-/
theorem minimalLayer_subset (S : Finset RealInterval) : minimalLayer S ⊆ S := by
  intro I hI
  exact (mem_minimalLayer_iff.mp hI).1

/--
@isnad1 id=nonempty.1h1v.s3.ff273b96889c from=translated src=- shape=6b9120e2 vocab=cc9bc41c
-/
theorem minimalLayer_nonempty {S : Finset RealInterval} (hS : S.Nonempty) :
    (minimalLayer S).Nonempty := by
  obtain ⟨I, hI, hmin⟩ := S.exists_min_image RealInterval.length hS
  refine ⟨I, mem_minimalLayer_iff.mpr ⟨hI, ?_⟩⟩
  intro J hJ hsub
  exact interval_eq_of_carrier_subset_of_length_le hsub (hmin J hJ)

/-- Each actual minimal layer consists of disjoint parent intervals.
@isnad1 id=pairwise.1h1v.s6.dabb5e74b327 from=translated src=- shape=98d8f4fe vocab=a0bb63a0
-/
theorem minimalLayer_pairwiseDisjoint {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier) :
    Set.Pairwise (↑(minimalLayer S)) (Disjoint on RealInterval.carrier) := by
  intro I hI J hJ hne
  have hi := mem_minimalLayer_iff.mp hI
  have hj := mem_minimalLayer_iff.mp hJ
  rcases hlam hi.1 hj.1 hne with hsub | hsub | hd
  · exact (hne (hj.2 I hi.1 hsub)).elim
  · exact (hne (hi.2 J hj.1 hsub).symm).elim
  · exact hd

/-- Remove one actual minimal layer at each step.-/
noncomputable def remainingIntervals (S : Finset RealInterval) : ℕ → Finset RealInterval
  | 0 => S
  | n + 1 => by classical exact remainingIntervals S n \ minimalLayer (remainingIntervals S n)

noncomputable def generation (S : Finset RealInterval) (n : ℕ) : Finset RealInterval :=
  minimalLayer (remainingIntervals S n)

/--
@isnad1 id=le.0h2v.s5.c1ebf232ae06 from=translated src=- shape=88e64e8f vocab=fc191c7d
-/
theorem remainingIntervals_succ_subset (S : Finset RealInterval) (n : ℕ) :
    remainingIntervals S (n + 1) ⊆ remainingIntervals S n := by
  classical
  exact Finset.sdiff_subset

/--
@isnad1 id=antitone.0h1v.s3.550cb5a96e6b from=translated src=- shape=134d4dcd vocab=1d7549b4
-/
theorem remainingIntervals_antitone (S : Finset RealInterval) :
    Antitone (remainingIntervals S) :=
  antitone_nat_of_succ_le (remainingIntervals_succ_subset S)

/--
@isnad1 id=le.0h2v.s4.9aa40bef76bd from=translated src=- shape=c77b2321 vocab=48b5fd95
-/
theorem remainingIntervals_subset (S : Finset RealInterval) (n : ℕ) :
    remainingIntervals S n ⊆ S :=
  remainingIntervals_antitone S (Nat.zero_le n)

/--
@isnad1 id=le.0h2v.s4.ffcdb8614c17 from=translated src=- shape=c77b2321 vocab=eab0f4b1
-/
theorem generation_subset (S : Finset RealInterval) (n : ℕ) : generation S n ⊆ S :=
  (minimalLayer_subset _).trans (remainingIntervals_subset S n)

/--
@isnad1 id=pairwise.1h2v.s6.9dac7c2c5c28 from=translated src=- shape=24ef9f59 vocab=f4bd552f
-/
theorem generation_pairwiseDisjoint {S : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (n : ℕ) : Set.Pairwise (↑(generation S n)) (Disjoint on RealInterval.carrier) := by
  apply minimalLayer_pairwiseDisjoint
  intro I hI J hJ hne
  exact hlam (remainingIntervals_subset S n hI) (remainingIntervals_subset S n hJ) hne

/-- No interval is counted in two different generations.
@isnad1 id=disjoint.1h3v.s4.ef83a0947b4b from=translated src=- shape=3c2d0d77 vocab=1b3d6c03
-/
theorem generations_disjoint (S : Finset RealInterval) {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (generation S m) (generation S n) := by
  classical
  wlog hlt : m < n generalizing m n
  · exact (this hmn.symm (by omega)).symm
  apply Finset.disjoint_left.mpr
  intro I hIm hIn
  have hrem : I ∈ remainingIntervals S (m + 1) :=
    remainingIntervals_antitone S (by omega : m + 1 ≤ n) (minimalLayer_subset _ hIn)
  exact (Finset.mem_sdiff.mp hrem).2 hIm

/--
@isnad1 id=le.0h2v.s4.bf6b4c9e7690 from=translated src=- shape=019c3eff vocab=0c863110
-/
theorem card_remainingIntervals_le (S : Finset RealInterval) (n : ℕ) :
    (remainingIntervals S n).card ≤ S.card - n := by
  classical
  induction n with
  | zero => simp [remainingIntervals]
  | succ n ih =>
    by_cases hnone : remainingIntervals S n = ∅
    · simp [remainingIntervals, hnone, minimalLayer]
    · have hpos := Finset.card_pos.mpr (minimalLayer_nonempty
        (Finset.nonempty_iff_ne_empty.mpr hnone))
      rw [remainingIntervals, Finset.card_sdiff_of_subset (minimalLayer_subset _)]
      omega

/--
@isnad1 id=eq.0h1v.s4.f165a64422ae from=translated src=- shape=61399901 vocab=97a266cb
-/
theorem remainingIntervals_card_eq_empty (S : Finset RealInterval) :
    remainingIntervals S S.card = ∅ := by
  have h := card_remainingIntervals_le S S.card
  exact Finset.card_eq_zero.mp (by omega)

/-- The finite minimal-generation construction exhausts the input
collection, with an explicit bound on the number of layers.
@isnad1 id=ex.1h2v.s5.3df169fc7082 from=translated src=- shape=7f3cf271 vocab=0e6213ff
-/
theorem exists_generation_of_mem {S : Finset RealInterval} {I : RealInterval}
    (hI : I ∈ S) : ∃ n < S.card, I ∈ generation S n := by
  classical
  by_contra hn
  push_neg at hn
  have hremain : ∀ n ≤ S.card, I ∈ remainingIntervals S n := by
    intro n
    induction n with
    | zero => intro _; exact hI
    | succ n ih =>
      intro hncard
      exact Finset.mem_sdiff.mpr ⟨ih (by omega), hn n (by omega)⟩
  have h := hremain S.card le_rfl
  rw [remainingIntervals_card_eq_empty] at h
  exact Finset.notMem_empty I h

/-- On a containment chain, the actual minimal-generation labels are
strictly ordered. This is the valid ordering used for maximal prefixes.
@isnad1 id=lt.4h5v.s5.021e4cf2ff37 from=translated src=- shape=0c2c74bd vocab=3b138319
-/
theorem generation_index_lt_of_proper_subset
    {S : Finset RealInterval} {I J : RealInterval} {m n : ℕ}
    (hI : I ∈ generation S m) (hJ : J ∈ generation S n)
    (hsub : I.carrier ⊆ J.carrier) (hne : I ≠ J) : m < n := by
  by_contra hnot
  have hrem : I ∈ remainingIntervals S n :=
    remainingIntervals_antitone S (by omega : n ≤ m) (minimalLayer_subset _ hI)
  exact hne ((mem_minimalLayer_iff.mp hJ).2 I hrem hsub)

end KrauseLaceyGenerationLayers
end QuadraticCarleson
