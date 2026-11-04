import Tengoku.GeneralStochToDet.stoch_to_det.Seed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite interface for the all-label shared-race theorem

This file contains only the discrete source/posterior definitions and the
shared Gumbel race.  The analytic clock proof and the application to the
duplicate-grouped race live in later modules.
-/

namespace stoch_to_det
namespace SharedRace

open Finset MeasureTheory

universe u

variable {Ω : Type u} {κ : Type} [Fintype Ω] [Fintype κ]

/-- The joint law of a source atom and one categorical draw from its
posterior vector.-/
noncomputable def posteriorJoint (μ : Ω → ℝ) (r : Ω → κ → ℝ) :
    Ω × κ → ℝ :=
  fun zi => μ zi.1 * r zi.1 zi.2

/-- The mean categorical posterior.-/
noncomputable def posteriorMean (μ : Ω → ℝ) (r : Ω → κ → ℝ) : κ → ℝ :=
  fun i => ∑ z, μ z * r z i

/-- The conditional mismatch probability of two iid categorical draws.-/
noncomputable def categoricalMismatch (μ : Ω → ℝ) (r : Ω → κ → ℝ) : ℝ :=
  ∑ z, μ z * (1 - ∑ i, (r z i) ^ 2)

/-- Measurable tie-breaking version of the Gumbel-max race with weights `t`.-/
noncomputable def weightedLexWinner [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (G : κ → ℝ) : κ :=
  lexMax (fun G i => Real.log (t i) + G i) G

/-- Winner map for a source-indexed posterior family.-/
noncomputable def sharedWinner [DecidableEq κ] [Nonempty κ]
    (r : Ω → κ → ℝ) (G : κ → ℝ) (z : Ω) : κ :=
  weightedLexWinner (r z) G

/-- Average fixed-seed entropy of the shared-race winner, in bits.-/
noncomputable def sharedRaceEntropy [DecidableEq κ] [Nonempty κ]
    (μ : Ω → ℝ) (r : Ω → κ → ℝ) : ℝ :=
  ∫ G, H (push (sharedWinner r G) μ) ∂(seedLaw κ)

/-- The categorical joint is a PMF whenever the source and every posterior
row are PMFs.
@isnad1 id=ispmf.2h4v.s5.3aa117969a89 from=translated src=- shape=ef2ceb08 vocab=20a41007
-/
lemma posteriorJoint_isPMF {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ) (hr : ∀ z, IsPMF (r z)) :
    IsPMF (posteriorJoint μ r) := by
  constructor
  · intro zi
    exact mul_nonneg (hμ.nonneg zi.1) ((hr zi.1).nonneg zi.2)
  · unfold mass posteriorJoint
    rw [Fintype.sum_prod_type]
    calc
      (∑ z, ∑ i, μ z * r z i) = ∑ z, μ z * ∑ i, r z i := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
      _ = ∑ z, μ z := by
        apply Finset.sum_congr rfl
        intro z _
        rw [show (∑ i, r z i) = 1 by simpa [mass] using (hr z).total, mul_one]
      _ = 1 := by simpa [mass] using hμ.total

/-- Support-local version: posterior rows outside the support of `μ` are
irrelevant and need not be normalized.
@isnad1 id=ispmf.2h4v.s5.e1275516d87f from=translated src=- shape=6db758a9 vocab=20a41007
-/
lemma posteriorJoint_isPMF_of_support {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ) (hr : ∀ z, μ z ≠ 0 → IsPMF (r z)) :
    IsPMF (posteriorJoint μ r) := by
  constructor
  · intro zi
    by_cases hz : μ zi.1 = 0
    · simp [posteriorJoint, hz]
    · exact mul_nonneg (hμ.nonneg zi.1) ((hr zi.1 hz).nonneg zi.2)
  · unfold mass posteriorJoint
    rw [Fintype.sum_prod_type]
    calc
      (∑ z, ∑ i, μ z * r z i) = ∑ z, μ z * ∑ i, r z i := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
      _ = ∑ z, μ z := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : μ z = 0
        · simp [hz]
        · rw [show (∑ i, r z i) = 1 by
            simpa [mass] using (hr z hz).total, mul_one]
      _ = 1 := by simpa [mass] using hμ.total

/-- The mean posterior is a PMF.
@isnad1 id=ispmf.2h4v.s5.abd7997c69c5 from=translated src=- shape=b7c9cffe vocab=574c3dce
-/
lemma posteriorMean_isPMF {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ) (hr : ∀ z, IsPMF (r z)) :
    IsPMF (posteriorMean μ r) := by
  constructor
  · intro i
    exact Finset.sum_nonneg fun z _ =>
      mul_nonneg (hμ.nonneg z) ((hr z).nonneg i)
  · unfold mass posteriorMean
    calc
      (∑ i, ∑ z, μ z * r z i) = ∑ z, ∑ i, μ z * r z i :=
        Finset.sum_comm
      _ = ∑ z, μ z * ∑ i, r z i := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
      _ = ∑ z, μ z := by
        apply Finset.sum_congr rfl
        intro z _
        rw [show (∑ i, r z i) = 1 by simpa [mass] using (hr z).total, mul_one]
      _ = 1 := by simpa [mass] using hμ.total

/-- Support-local version of `posteriorMean_isPMF`.
@isnad1 id=ispmf.2h4v.s5.39d8724b5989 from=translated src=- shape=fb539d25 vocab=574c3dce
-/
lemma posteriorMean_isPMF_of_support {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ) (hr : ∀ z, μ z ≠ 0 → IsPMF (r z)) :
    IsPMF (posteriorMean μ r) := by
  constructor
  · intro i
    apply Finset.sum_nonneg
    intro z _
    by_cases hz : μ z = 0
    · simp [hz]
    · exact mul_nonneg (hμ.nonneg z) ((hr z hz).nonneg i)
  · unfold mass posteriorMean
    calc
      (∑ i, ∑ z, μ z * r z i) = ∑ z, ∑ i, μ z * r z i :=
        Finset.sum_comm
      _ = ∑ z, μ z * ∑ i, r z i := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
      _ = ∑ z, μ z := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : μ z = 0
        · simp [hz]
        · rw [show (∑ i, r z i) = 1 by
            simpa [mass] using (hr z hz).total, mul_one]
      _ = 1 := by simpa [mass] using hμ.total

omit [Fintype κ] in
/-- Strictly positive posterior rows on the support give a strictly positive
mean posterior.
@isnad1 id=lt.2h5v.s6.ca5a4d86aa2e from=translated src=- shape=42d7efa6 vocab=683845c3
-/
lemma posteriorMean_pos_of_support {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) :
    ∀ i, 0 < posteriorMean μ r i := by
  have hsum : 0 < ∑ z, μ z := by
    have htotal : ∑ z, μ z = 1 := by simpa [mass] using hμ.total
    rw [htotal]
    norm_num
  obtain ⟨z, _hzmem, hzpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (s := (Finset.univ : Finset Ω))
      (fun z _ => hμ.nonneg z)).mp hsum
  intro i
  unfold posteriorMean
  apply Finset.sum_pos'
  · intro x _
    by_cases hx : μ x = 0
    · simp [hx]
    · exact mul_nonneg (hμ.nonneg x) (hrpos x hx i).le
  · exact ⟨z, Finset.mem_univ z,
      mul_pos hzpos (hrpos z hzpos.ne' i)⟩

/-- Every coordinate of a finite PMF is at most one.
@isnad1 id=le.1h3v.s4.b1a7820a65ce from=translated src=- shape=5193ede0 vocab=97151dff
-/
lemma pmf_apply_le_one {m : κ → ℝ} (hm : IsPMF m) (i : κ) :
    m i ≤ 1 := by
  calc
    m i ≤ ∑ j, m j :=
      Finset.single_le_sum (fun j _ => hm.nonneg j) (Finset.mem_univ i)
    _ = 1 := by simpa [mass] using hm.total

/-- Collision probability of a finite PMF is at most one.
@isnad1 id=le.1h2v.s5.23fc8f9d9317 from=translated src=- shape=f786341b vocab=0f518da3
-/
lemma pmf_sum_sq_le_one {m : κ → ℝ} (hm : IsPMF m) :
    ∑ i, m i ^ 2 ≤ 1 := by
  calc
    (∑ i, m i ^ 2) ≤ ∑ i, m i := by
      apply Finset.sum_le_sum
      intro i _
      have hi0 := hm.nonneg i
      have hi1 := pmf_apply_le_one hm i
      nlinarith
    _ = 1 := by simpa [mass] using hm.total

/-- The categorical mismatch charge is nonnegative under support-local PMF
assumptions.
@isnad1 id=le.2h4v.s5.2dfd0e2b832c from=translated src=- shape=edb94080 vocab=e875e27e
-/
lemma categoricalMismatch_nonneg_of_support
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ) (hr : ∀ z, μ z ≠ 0 → IsPMF (r z)) :
    0 ≤ categoricalMismatch μ r := by
  unfold categoricalMismatch
  apply Finset.sum_nonneg
  intro z _
  by_cases hz : μ z = 0
  · simp [hz]
  · exact mul_nonneg (hμ.nonneg z) (sub_nonneg.mpr (pmf_sum_sq_le_one (hr z hz)))

/-- The source marginal of the categorical joint.
@isnad1 id=eq.1h4v.s6.f2875a8c4693 from=translated src=- shape=083ec129 vocab=2f5e433b
-/
lemma push_posteriorJoint_fst [DecidableEq Ω]
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z)) :
    push Prod.fst (posteriorJoint μ r) = μ := by
  funext z
  unfold push posteriorJoint
  simp_rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  by_cases hz : μ z = 0
  · simp [hz]
  · calc
      (∑ x, ∑ i, if x = z then μ x * r x i else 0) =
          ∑ x, if x = z then ∑ i, μ x * r x i else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = z <;> simp [hx]
      _ = ∑ i, μ z * r z i := by simp
      _ = μ z * ∑ i, r z i := by rw [Finset.mul_sum]
      _ = μ z := by
        rw [show (∑ i, r z i) = 1 by simpa [mass] using (hr z hz).total,
          mul_one]

/-- The categorical marginal of the joint is the mean posterior.
@isnad1 id=eq.0h4v.s5.ae22d5a37c5e from=translated src=- shape=e11fca6b vocab=9e39049c
-/
lemma push_posteriorJoint_snd [DecidableEq κ]
    {μ : Ω → ℝ} {r : Ω → κ → ℝ} :
    push Prod.snd (posteriorJoint μ r) = posteriorMean μ r := by
  funext i
  unfold push posteriorJoint posteriorMean
  simp_rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp

/-- The exact support-positive shared-race statement needed by the `C < 96`
bridge. It is in bits, so the natural-log mismatch coefficient `log 2` becomes
`1`.-/
def HasSharedRaceBound (Ω : Type u) (κ : Type)
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ]
    [Nonempty κ] : Prop :=
  ∀ (μ : Ω → ℝ) (r : Ω → κ → ℝ),
    IsPMF μ →
      (∀ z, μ z ≠ 0 → IsPMF (r z)) →
      (∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) →
      sharedRaceEntropy μ r ≤
        2 * MI Prod.fst Prod.snd (posteriorJoint μ r) +
          categoricalMismatch μ r

/-- The universal shared-race statement is immediate for a singleton label
alphabet.
@isnad1 id=hasshare.0h2v.s4.17b92ae407ed from=translated src=- shape=6e211c33 vocab=87fb340f
-/
theorem hasSharedRaceBound_of_subsingleton
    [DecidableEq Ω] [DecidableEq κ] [Nonempty κ] [Subsingleton κ] :
    HasSharedRaceBound Ω κ := by
  intro μ r hμ hr _hrpos
  have hjoint := posteriorJoint_isPMF_of_support hμ hr
  have hzero (G : κ → ℝ) : H (push (sharedWinner r G) μ) = 0 := by
    have hpush : IsPMF (push (sharedWinner r G) μ) := isPMF_push hμ
    apply le_antisymm
    · calc
        H (push (sharedWinner r G) μ) ≤ lg (Fintype.card κ) := H_le_card hpush
        _ = 0 := by
          have hcard : Fintype.card κ = 1 :=
            Fintype.card_eq_one_iff.mpr
              ⟨Classical.choice inferInstance,
                fun y => Subsingleton.elim y (Classical.choice inferInstance)⟩
          simp [hcard]
    · exact H_nonneg_of_isPMF hpush
  have hshared : sharedRaceEntropy μ r = 0 := by
    unfold sharedRaceEntropy
    simp_rw [hzero]
    simp
  rw [hshared]
  exact add_nonneg
    (mul_nonneg (by norm_num) (MI_nonneg hjoint Prod.fst Prod.snd))
    (categoricalMismatch_nonneg_of_support hμ hr)

end SharedRace
end stoch_to_det
