import Tengoku.PaperCLean.PaperC.Affine.RelationalPrimeAssignment
import Tengoku.PaperCLean.PaperC.Arithmetic.CRT
import Tengoku.PaperCLean.PaperC.Arithmetic.IntervalCongruence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 1200000

/-!
# Counting opposite starts for one large-kernel assignment

For a selected integer `n`, an assignment chooses one offset in the opposite
start block for each prime of the large odd kernel `𝒦_{L+1}(n)`.  All opposite
starts realizing one fixed assignment lie in a single residue class modulo
that kernel.  Hence there are at most `N / 𝒦_{L+1}(n) + 1` of them in
`[N,2N)`, and there are exactly `(L+1)^ω(𝒦_{L+1}(n))` possible assignments.

This is the finite CRT counting component of Lemma 4.2.
-/

namespace PaperC
namespace LargeKernelAssignments

open scoped BigOperators Function
open Finset
open Affine

noncomputable section

/-- Prime indices of the selected integer, packaged as a finite type.-/
abbrev LargePrimeIndex (L n : ℕ) :=
  {p : ℕ //
    p ∈ LargeOddKernel.largeOddPrimeSupport (L + 1) n}

/-- One opposite-block offset for every large odd prime of `n`.-/
abbrev LargePrimeAssignment (L n : ℕ) :=
  LargePrimeIndex L n → Fin (L + 1)

/-- The finite set of all large-prime assignments.-/
def allAssignments (L n : ℕ) :
    Finset (LargePrimeAssignment L n) :=
  Finset.univ

/--
@isnad1 id=eq.0h2v.s5.5edae69252ce from=translated src=- shape=5975e4ab vocab=42f22ec5
-/
@[simp]
theorem card_allAssignments (L n : ℕ) :
    (allAssignments L n).card =
      (L + 1) ^
        (LargeOddKernel.largeOddPrimeSupport (L + 1) n).card := by
  classical
  simp [allAssignments, LargePrimeAssignment, LargePrimeIndex,
    Fintype.card_congr (Equiv.refl (LargePrimeIndex L n))]

/--
Starts in the dyadic block realizing a fixed assignment through nonzero
parity coordinates.-/
def startsForAssignment
    (N L n : ℕ) (assignment : LargePrimeAssignment L n) :
    Finset ℕ := by
  classical
  exact (dyadicBlock N).filter fun y ↦
    ∀ p : LargePrimeIndex L n,
      parityVec
          (startCompleteVertexLabel y L (assignment p))
          p.1 ≠
        0

/--
@isnad1 id=iff.0h5v.s7.e8e6fc199c1e from=translated src=- shape=18517225 vocab=795949bb
-/
@[simp]
theorem mem_startsForAssignment
    {N L n y : ℕ} {assignment : LargePrimeAssignment L n} :
    y ∈ startsForAssignment N L n assignment ↔
      y ∈ dyadicBlock N ∧
        ∀ p : LargePrimeIndex L n,
          parityVec
              (startCompleteVertexLabel y L (assignment p))
              p.1 ≠
            0 := by
  classical
  simp [startsForAssignment]

/--
If the same fixed offset has a prime divisor in two start blocks, their
starts are congruent modulo that prime.
@isnad1 id=modeq.4h5v.s6.54a16735017b from=translated src=- shape=13e2d6ee vocab=7cc095be
-/
theorem start_modEq_of_assigned_labels_dvd
    {y z L p : ℕ} (hy : 1 ≤ y) (hz : 1 ≤ z)
    (w : Fin (L + 1))
    (hyDvd : p ∣ startCompleteVertexLabel y L w)
    (hzDvd : p ∣ startCompleteVertexLabel z L w) :
    y ≡ z [MOD p] := by
  have hlabel :
      startCompleteVertexLabel y L w ≡
        startCompleteVertexLabel z L w [MOD p] :=
    hyDvd.modEq_zero_nat.trans hzDvd.zero_modEq_nat
  by_cases hw0 : w.1 = 0
  · simp only [startCompleteVertexLabel, hw0, ite_eq_left] at hlabel
    have hadd := hlabel.add_right 1
    simpa [Nat.sub_add_cancel hy, Nat.sub_add_cancel hz] using hadd
  · simp only [startCompleteVertexLabel, hw0, ite_eq_right] at hlabel
    exact Nat.ModEq.add_right_cancel' (w.1 - 1) hlabel

private theorem pairwise_coprime_of_nodup_primes
    {indices : List ℕ}
    (hnodup : indices.Nodup)
    (hprime : ∀ p ∈ indices, p.Prime) :
    indices.Pairwise Nat.Coprime := by
  induction indices with
  | nil => simp
  | cons p indices ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.pairwise_cons]
      constructor
      · intro q hq
        exact (Nat.coprime_primes
          (hprime p (by simp))
          (hprime q (by simp [hq]))).mpr
            (by
              intro hpq
              apply hnodup.1
              simpa [hpq] using hq)
      · apply ih hnodup.2
        intro q hq
        exact hprime q (by simp [hq])

/-- The prime list of the large support is pairwise coprime.
@isnad1 id=pairwise.0h2v.s4.c592f3a29be8 from=translated src=- shape=0be6aec7 vocab=c508cace
-/
theorem largeSupport_toList_pairwise_coprime (L n : ℕ) :
    (LargeOddKernel.largeOddPrimeSupport (L + 1) n).toList.Pairwise
      Nat.Coprime := by
  classical
  apply pairwise_coprime_of_nodup_primes
    (LargeOddKernel.largeOddPrimeSupport (L + 1) n).nodup_toList
  intro p hp
  exact
    (LargeOddKernel.prime_and_large_of_mem_largeOddPrimeSupport
      (by simpa using hp)).1

/--
Any two starts realizing a fixed assignment are congruent modulo the complete
large odd kernel.
@isnad1 id=modeq.3h6v.s6.ede40eab27f5 from=translated src=- shape=cfee2cc0 vocab=fb88339a
-/
theorem pairwise_modEq_largeOddKernel
    {N L n : ℕ} (hN : 1 ≤ N)
    (assignment : LargePrimeAssignment L n)
    {y z : ℕ}
    (hy : y ∈ startsForAssignment N L n assignment)
    (hz : z ∈ startsForAssignment N L n assignment) :
    y ≡ z [MOD LargeOddKernel.largeOddKernel (L + 1) n] := by
  classical
  have hyBlock := (mem_startsForAssignment.mp hy).1
  have hzBlock := (mem_startsForAssignment.mp hz).1
  have hyOne : 1 ≤ y := by
    have := (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hyBlock)).1
    exact hN.trans this
  have hzOne : 1 ≤ z := by
    have := (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hzBlock)).1
    exact hN.trans this
  have hperPrime :
      ∀ p ∈
          (LargeOddKernel.largeOddPrimeSupport (L + 1) n).toList,
        y ≡ z [MOD p] := by
    intro p hp
    let pIndex : LargePrimeIndex L n :=
      ⟨p, by simpa using hp⟩
    have hyParity :=
      (mem_startsForAssignment.mp hy).2 pIndex
    have hzParity :=
      (mem_startsForAssignment.mp hz).2 pIndex
    exact start_modEq_of_assigned_labels_dvd hyOne hzOne
      (assignment pIndex)
      (Affine.RelationalPrimeAssignment.dvd_of_parityVec_ne_zero
        hyParity)
      (Affine.RelationalPrimeAssignment.dvd_of_parityVec_ne_zero
        hzParity)
  have hcrt :=
    (Nat.modEq_list_prod_iff
      (largeSupport_toList_pairwise_coprime L n)).mpr
      (fun i ↦ hperPrime
        ((LargeOddKernel.largeOddPrimeSupport (L + 1) n).toList.get i)
        ((LargeOddKernel.largeOddPrimeSupport (L + 1) n).toList.get_mem i))
  simpa [LargeOddKernel.largeOddKernel] using hcrt

/--
One fixed assignment contributes at most one residue class modulo the kernel
inside `[N,2N)`.
@isnad1 id=le.1h4v.s6.065dfb19aaed from=translated src=- shape=9fdf4153 vocab=a4dea25f
-/
theorem card_startsForAssignment_cast_le
    {N L n : ℕ} (hN : 1 ≤ N)
    (assignment : LargePrimeAssignment L n) :
    ((startsForAssignment N L n assignment).card : ℚ) ≤
      (N : ℚ) /
          (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
        1 := by
  classical
  by_cases hempty : startsForAssignment N L n assignment = ∅
  · simp [hempty]
    positivity
  · have hnonempty :
        (startsForAssignment N L n assignment).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let z : ℕ := (startsForAssignment N L n assignment).min' hnonempty
    have hz : z ∈ startsForAssignment N L n assignment :=
      Finset.min'_mem _ _
    have hsubset :
        startsForAssignment N L n assignment ⊆
          {y ∈ Finset.Ico N (2 * N) |
            y ≡ z [MOD
              LargeOddKernel.largeOddKernel (L + 1) n]} := by
      intro y hy
      have hyBlock := (mem_startsForAssignment.mp hy).1
      simp only [Finset.mem_filter]
      exact ⟨by simpa [dyadicBlock] using hyBlock,
        pairwise_modEq_largeOddKernel hN assignment hy hz⟩
    have hcard :
        ((startsForAssignment N L n assignment).card : ℚ) ≤
          ((#{y ∈ Finset.Ico N (2 * N) |
              y ≡ z [MOD
                LargeOddKernel.largeOddKernel (L + 1) n]} : ℕ) : ℚ) := by
      exact_mod_cast Finset.card_le_card hsubset
    refine hcard.trans ?_
    have hinterval :=
      card_nat_Ico_modEq_cast_le_div_add_one
        N (2 * N) z
        (LargeOddKernel.largeOddKernel (L + 1) n)
        (Nat.pos_of_ne_zero
          (LargeOddKernel.largeOddKernel_ne_zero (L + 1) n))
        (by omega)
    have hlength :
        (((2 * N : ℕ) : ℤ) - (N : ℤ)) = (N : ℤ) := by
      push_cast
      ring
    have hlengthQ : (2 * (N : ℚ) - (N : ℚ)) = (N : ℚ) := by
      ring
    norm_num [hlength] at hinterval
    rw [hlengthQ] at hinterval
    simpa using hinterval

/-- Union over all possible assignments.-/
def startsForSomeAssignment (N L n : ℕ) : Finset ℕ :=
  (allAssignments L n).biUnion
    (startsForAssignment N L n)

/--
@isnad1 id=iff.0h4v.s5.001d994e8546 from=translated src=- shape=b88ff4b0 vocab=6055a902
-/
@[simp]
theorem mem_startsForSomeAssignment
    {N L n y : ℕ} :
    y ∈ startsForSomeAssignment N L n ↔
      ∃ assignment : LargePrimeAssignment L n,
        y ∈ startsForAssignment N L n assignment := by
  classical
  simp [startsForSomeAssignment, allAssignments]

/--
After summing over the `(L+1)^ω` assignments, the number of possible opposite
starts is bounded by the assignment count times the one-class estimate.
@isnad1 id=le.1h3v.s6.9f1f3762be11 from=translated src=- shape=06e91d25 vocab=317a2ff3
-/
theorem card_startsForSomeAssignment_cast_le
    {N L n : ℕ} (hN : 1 ≤ N) :
    ((startsForSomeAssignment N L n).card : ℚ) ≤
      ((L + 1 : ℕ) ^
          (LargeOddKernel.largeOddPrimeSupport (L + 1) n).card : ℚ) *
        ((N : ℚ) /
            (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
          1) := by
  classical
  calc
    ((startsForSomeAssignment N L n).card : ℚ)
        ≤ (∑ assignment ∈ allAssignments L n,
            (startsForAssignment N L n assignment).card : ℕ) := by
          exact_mod_cast Finset.card_biUnion_le
    _ = ∑ assignment ∈ allAssignments L n,
          ((startsForAssignment N L n assignment).card : ℚ) := by
      norm_cast
    _ ≤ ∑ _assignment ∈ allAssignments L n,
          ((N : ℚ) /
              (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
            1) := by
      exact Finset.sum_le_sum fun assignment _ ↦
        card_startsForAssignment_cast_le hN assignment
    _ = ((allAssignments L n).card : ℚ) *
          ((N : ℚ) /
              (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
            1) := by
      simp
      ring
    _ = ((L + 1 : ℕ) ^
          (LargeOddKernel.largeOddPrimeSupport (L + 1) n).card : ℚ) *
        ((N : ℚ) /
            (LargeOddKernel.largeOddKernel (L + 1) n : ℚ) +
          1) := by
      rw [card_allAssignments]
      norm_cast

/-- Every complete start label in the dyadic block is covered by the cutoff.
@isnad1 id=le.1h4v.s5.0140308328ef from=translated src=- shape=75e5f221 vocab=b4e50d5f
-/
theorem startCompleteVertexLabel_le_dyadicCutoff
    {N L x : ℕ} (hx : x ∈ dyadicBlock N)
    (v : Fin (L + 1)) :
    startCompleteVertexLabel x L v ≤ dyadicCutoff N L := by
  have hxData :
      N ≤ x ∧ x < 2 * N :=
    Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)
  simp only [startCompleteVertexLabel]
  split_ifs <;> unfold dyadicCutoff <;> omega

/--
A selected left occurrence of a relation forces the right start into the
union of all large-kernel assignment classes attached to the selected label.
@isnad1 id=mem.4h6v.s10.1f13acdbd2ec from=translated src=- shape=4a25b74e vocab=2471a6ac
-/
theorem right_mem_startsForSomeAssignment_of_selected_left
    {N L x y : ℕ} (hN : 2 ≤ N)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N)
    (u : RelationSpace
      (twoStartSystem (dyadicCutoff N L) x y L))
    (v : Fin (L + 1))
    (hvSelected :
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) (Sum.inl v) ≠
        0) :
    y ∈ startsForSomeAssignment N L
      (startCompleteVertexLabel x L v) := by
  classical
  have hxTwo := two_le_of_mem_dyadicBlock hN hx
  have hyTwo := two_le_of_mem_dyadicBlock hN hy
  let assignment :
      LargePrimeAssignment L (startCompleteVertexLabel x L v) :=
    fun p ↦ Classical.choose
      (Affine.RelationalPrimeAssignment.existsUnique_opposite_for_largeKernel_of_left
          hxTwo hyTwo u v hvSelected
          (startCompleteVertexLabel_le_dyadicCutoff hx v)
          p.2)
  rw [mem_startsForSomeAssignment]
  refine ⟨assignment, ?_⟩
  rw [mem_startsForAssignment]
  refine ⟨hy, ?_⟩
  intro p
  exact (Classical.choose_spec
    (Affine.RelationalPrimeAssignment.existsUnique_opposite_for_largeKernel_of_left
        hxTwo hyTwo u v hvSelected
        (startCompleteVertexLabel_le_dyadicCutoff hx v)
        p.2)).1.2

/-- Symmetric right-selected version.
@isnad1 id=mem.4h6v.s10.49edc199a36f from=translated src=- shape=be3e900b vocab=d88fea37
-/
theorem left_mem_startsForSomeAssignment_of_selected_right
    {N L x y : ℕ} (hN : 2 ≤ N)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N)
    (u : RelationSpace
      (twoStartSystem (dyadicCutoff N L) x y L))
    (v : Fin (L + 1))
    (hvSelected :
      twoStartCompleteBoundary L
          (u : Sum (Fin L) (Fin L) → F₂) (Sum.inr v) ≠
        0) :
    x ∈ startsForSomeAssignment N L
      (startCompleteVertexLabel y L v) := by
  classical
  have hxTwo := two_le_of_mem_dyadicBlock hN hx
  have hyTwo := two_le_of_mem_dyadicBlock hN hy
  let assignment :
      LargePrimeAssignment L (startCompleteVertexLabel y L v) :=
    fun p ↦ Classical.choose
      (Affine.RelationalPrimeAssignment.existsUnique_opposite_for_largeKernel_of_right
          hxTwo hyTwo u v hvSelected
          (startCompleteVertexLabel_le_dyadicCutoff hy v)
          p.2)
  rw [mem_startsForSomeAssignment]
  refine ⟨assignment, ?_⟩
  rw [mem_startsForAssignment]
  refine ⟨hx, ?_⟩
  intro p
  exact (Classical.choose_spec
    (Affine.RelationalPrimeAssignment.existsUnique_opposite_for_largeKernel_of_right
        hxTwo hyTwo u v hvSelected
        (startCompleteVertexLabel_le_dyadicCutoff hy v)
        p.2)).1.2

end

end LargeKernelAssignments
end PaperC
