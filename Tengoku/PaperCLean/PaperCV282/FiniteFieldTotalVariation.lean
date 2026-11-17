import Tengoku.PaperCLean.PaperC.Probability.SectionThirteenFiniteBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Half-L1 variation and finite pushforwards for finite fields

The target type is arbitrary, in particular a finite vector of natural counts.
Every application to probability laws supplies exact mass one and summability.
The notation does not equip the infinite state space with a fictitious Fintype.
-/

namespace PaperC.V282.FiniteFieldTotalVariation

open ArratiaGoldsteinGordonInput
open scoped BigOperators

noncomputable section

variable {α : Type*}

@[reducible]
local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- Half-`ℓ¹` total variation for two real mass functions on `α`.-/
def massTotalVariation
    (p q : α → ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * ∑' k : α, |p k - q k|

/-- The absolute difference of two summable nonnegative mass functions is
summable.
@isnad1 id=summable.4h3v.s6.1c90119c81d8 from=translated src=- shape=08495abe vocab=732bba7d
-/
theorem summable_abs_sub_of_nonneg
    {p q : α → ℝ}
    (hp : Summable p) (hq : Summable q)
    (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) :
    Summable fun k ↦ |p k - q k| := by
  apply (hp.add hq).of_nonneg_of_le
  · intro k
    exact abs_nonneg _
  · intro k
    exact abs_sub_le_iff.mpr
      ⟨by linarith [hp0 k, hq0 k], by linarith [hp0 k, hq0 k]⟩

/-- Total variation is nonnegative whenever its defining series is summable.
@isnad1 id=le.0h3v.s4.da3a865ec365 from=translated src=- shape=c0aa7a93 vocab=0fb6e1c9
-/
theorem massTotalVariation_nonneg
    (p q : α → ℝ) :
    0 ≤ massTotalVariation p q := by
  unfold massTotalVariation
  exact mul_nonneg (by positivity)
    (tsum_nonneg fun _ ↦ abs_nonneg _)

/-- Symmetry of half-`ℓ¹` total variation.
@isnad1 id=eq.0h3v.s4.79130e20e22a from=translated src=- shape=a2b97482 vocab=9ed4be06
-/
theorem massTotalVariation_comm
    (p q : α → ℝ) :
    massTotalVariation p q = massTotalVariation q p := by
  unfold massTotalVariation
  congr 1
  apply tsum_congr
  intro k
  exact abs_sub_comm _ _

/-- Triangle inequality for discrete total variation.
@isnad1 id=le.6h4v.s6.bd16a84ac96d from=translated src=- shape=79176cfb vocab=7ed97258
-/
theorem massTotalVariation_triangle
    {p q r : α → ℝ}
    (hp : Summable p) (hq : Summable q) (hr : Summable r)
    (hp0 : ∀ k, 0 ≤ p k)
    (hq0 : ∀ k, 0 ≤ q k)
    (hr0 : ∀ k, 0 ≤ r k) :
    massTotalVariation p r ≤
      massTotalVariation p q + massTotalVariation q r := by
  have hpq :
      Summable fun k ↦ |p k - q k| :=
    summable_abs_sub_of_nonneg hp hq hp0 hq0
  have hqr :
      Summable fun k ↦ |q k - r k| :=
    summable_abs_sub_of_nonneg hq hr hq0 hr0
  have hpr :
      Summable fun k ↦ |p k - r k| :=
    summable_abs_sub_of_nonneg hp hr hp0 hr0
  have hsum :
      (∑' k : α, |p k - r k|) ≤
        ∑' k : α, (|p k - q k| + |q k - r k|) := by
    exact hpr.tsum_le_tsum
      (fun k ↦ by
        calc
          |p k - r k| =
              |(p k - q k) + (q k - r k)| := by ring_nf
          _ ≤ |p k - q k| + |q k - r k| := abs_add_le _ _)
      (hpq.add hqr)
  unfold massTotalVariation
  calc
    (2 : ℝ)⁻¹ * ∑' k : α, |p k - r k| ≤
        (2 : ℝ)⁻¹ *
          ∑' k : α, (|p k - q k| + |q k - r k|) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ =
        (2 : ℝ)⁻¹ * ∑' k : α, |p k - q k| +
          (2 : ℝ)⁻¹ * ∑' k : α, |q k - r k| := by
      rw [hpq.tsum_add hqr]
      ring

/-! ## Uniform finite mixtures -/

/-- Uniform average of a finite family of real numbers.-/
def uniformAverage
    {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  (∑ i, f i) / (Fintype.card ι : ℝ)

/--
Convexity of total variation under a finite uniform mixture.  The reference
mass `q` is the same in every component.
@isnad1 id=le.1h4v.s6.7118c0988774 from=translated src=- shape=c7ab597f vocab=03bd0392
-/
theorem massTotalVariation_uniformMixture_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → α → ℝ) (q : α → ℝ)
    (hsummable :
      ∀ i, Summable fun k ↦ |p i k - q k|) :
    massTotalVariation
        (fun k ↦ uniformAverage (fun i ↦ p i k)) q ≤
      uniformAverage
        (fun i ↦ massTotalVariation (p i) q) := by
  classical
  let d : ℝ := Fintype.card ι
  have hdNat : 0 < Fintype.card ι := Fintype.card_pos
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast hdNat
  have hsumAbs :
      Summable fun k : α ↦
        ∑ i : ι, |p i k - q k| :=
    (hasSum_sum (s := Finset.univ)
      (fun i _hi ↦ (hsummable i).hasSum)).summable
  have hpoint :
      ∀ k : α,
        |uniformAverage (fun i ↦ p i k) - q k| ≤
          uniformAverage (fun i ↦ |p i k - q k|) := by
    intro k
    unfold uniformAverage
    have hsumq :
        (∑ _i : ι, q k) = (Fintype.card ι : ℝ) * q k := by
      simp
    rw [show (∑ i, p i k) / (Fintype.card ι : ℝ) - q k =
        (∑ i, (p i k - q k)) / (Fintype.card ι : ℝ) by
      rw [Finset.sum_sub_distrib, hsumq]
      field_simp]
    rw [abs_div, abs_of_pos hd]
    apply div_le_div_of_nonneg_right
    · exact Finset.abs_sum_le_sum_abs _ _
    · exact hd.le
  have hleftSummable :
      Summable fun k ↦
        |uniformAverage (fun i ↦ p i k) - q k| := by
    have hrightSummable :
        Summable fun k ↦
          uniformAverage (fun i ↦ |p i k - q k|) := by
      unfold uniformAverage
      exact hsumAbs.div_const _
    exact hrightSummable.of_nonneg_of_le
      (fun k ↦ abs_nonneg _) hpoint
  have hrightSummable :
      Summable fun k ↦
        uniformAverage (fun i ↦ |p i k - q k|) := by
    unfold uniformAverage
    exact hsumAbs.div_const _
  have htsum :
      (∑' k : α,
          |uniformAverage (fun i ↦ p i k) - q k|) ≤
        ∑' k : α,
          uniformAverage (fun i ↦ |p i k - q k|) :=
    hleftSummable.tsum_le_tsum hpoint hrightSummable
  have hinterchange :
      (∑' k : α,
          uniformAverage (fun i ↦ |p i k - q k|)) =
        uniformAverage
          (fun i ↦ ∑' k : α, |p i k - q k|) := by
    unfold uniformAverage
    rw [tsum_div_const]
    congr 1
    exact Summable.tsum_finsetSum
      (s := Finset.univ) (fun i _hi ↦ hsummable i)
  unfold massTotalVariation
  calc
    (2 : ℝ)⁻¹ *
          ∑' k : α,
            |uniformAverage (fun i ↦ p i k) - q k| ≤
        (2 : ℝ)⁻¹ *
          ∑' k : α,
            uniformAverage (fun i ↦ |p i k - q k|) :=
      mul_le_mul_of_nonneg_left htsum (by positivity)
    _ =
        (2 : ℝ)⁻¹ *
          uniformAverage
            (fun i ↦ ∑' k : α, |p i k - q k|) := by
      rw [hinterchange]
    _ =
        uniformAverage
          (fun i ↦
            (2 : ℝ)⁻¹ * ∑' k : α, |p i k - q k|) := by
      unfold uniformAverage
      rw [← Finset.mul_sum]
      ring

/-! ## Pushforward laws and the coupling inequality -/

/-- Law of an discrete-valued function on a finite probability space.-/
def finiteFieldLaw
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → α) (k : α) : ℝ := by
  classical
  exact ∑ ω, if Z ω = k then μ.prob ω else 0

/-- The pushforward law is nonnegative.
@isnad1 id=le.0h5v.s5.f1c20c9f84c1 from=translated src=- shape=9fcb66d0 vocab=4b02ba26
-/
theorem finiteFieldLaw_nonneg
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → α) (k : α) :
    0 ≤ finiteFieldLaw μ Z k := by
  classical
  unfold finiteFieldLaw
  exact Finset.sum_nonneg fun ω _ ↦ by
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl

/-- The pushforward mass function has total mass one.
@isnad1 id=hassum.0h4v.s5.f9ff523db1a2 from=translated src=- shape=5da8b152 vocab=0e99635a
-/
theorem hasSum_finiteFieldLaw
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → α) :
    HasSum (finiteFieldLaw μ Z) 1 := by
  classical
  let support : Finset α := Finset.univ.image Z
  have hout :
      ∀ k ∉ support, finiteFieldLaw μ Z k = 0 := by
    intro k hk
    unfold finiteFieldLaw
    apply Finset.sum_eq_zero
    intro ω _hω
    rw [ite_eq_right]
    intro hZ
    apply hk
    exact Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, hZ⟩
  have hsum :
      ∑ k ∈ support, finiteFieldLaw μ Z k = 1 := by
    unfold finiteFieldLaw
    rw [Finset.sum_comm]
    calc
      (∑ ω, ∑ k ∈ support, if Z ω = k then μ.prob ω else 0) =
          ∑ ω, μ.prob ω := by
        apply Finset.sum_congr rfl
        intro ω _hω
        have hmem : Z ω ∈ support :=
          Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩
        simp [hmem]
      _ = 1 := μ.sum_prob
  have hfinite :
      HasSum (finiteFieldLaw μ Z)
        (∑ k ∈ support, finiteFieldLaw μ Z k) :=
    hasSum_sum_of_ne_finset_zero hout
  rw [hsum] at hfinite
  exact hfinite

/-- The pushforward mass function is summable.
@isnad1 id=summable.0h4v.s5.faae03de91e2 from=translated src=- shape=6d40a95f vocab=4c7fc834
-/
theorem summable_finiteFieldLaw
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → α) :
    Summable (finiteFieldLaw μ Z) :=
  (hasSum_finiteFieldLaw μ Z).summable

/-- Restricting a summable nonnegative mass to an arbitrary set remains summable.
@isnad1 id=summable.2h3v.s6.818b9ba7eac1 from=translated src=- shape=40b47131 vocab=bd0c11a7
-/
theorem summable_restricted_mass {p : α → ℝ} (hp : Summable p)
    (hp0 : ∀ k, 0 ≤ p k) (A : Set α) :
    Summable (fun k => if k ∈ A then p k else 0) := by
  classical
  apply hp.of_nonneg_of_le
  · intro k
    split_ifs <;> simp [hp0]
  · intro k
    split_ifs <;> simp [hp0]

/-- The positive part of the mass difference is an exact maximizing test set.
@isnad1 id=eq.4h3v.s7.048ef52b8a38 from=translated src=- shape=d344c6b9 vocab=9a698af2
-/
theorem massTotalVariation_eq_positive_set {p q : α → ℝ}
    (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) :
    massTotalVariation p q =
      (∑' k, if q k ≤ p k then p k else 0) -
        ∑' k, if q k ≤ p k then q k else 0 := by
  classical
  have hpa : Summable (fun k => if q k ≤ p k then p k else 0) := by
    apply hp.summable.of_nonneg_of_le
    · intro k; split_ifs <;> simp [hp0]
    · intro k; split_ifs <;> simp [hp0]
  have hqa : Summable (fun k => if q k ≤ p k then q k else 0) := by
    apply hq.summable.of_nonneg_of_le
    · intro k; split_ifs <;> simp [hq0]
    · intro k; split_ifs <;> simp [hq0]
  have hpoint (k : α) : |p k - q k| =
      2 * ((if q k ≤ p k then p k else 0) - (if q k ≤ p k then q k else 0)) - (p k - q k) := by
    by_cases h : q k ≤ p k
    · rw [ite_eq_left h, ite_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · rw [ite_eq_right h, ite_eq_right h, abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))]
      ring
  unfold massTotalVariation
  simp_rw [hpoint]
  rw [((hpa.sub hqa).mul_left 2).tsum_sub (hp.summable.sub hq.summable),
    tsum_mul_left, hpa.tsum_sub hqa, hp.summable.tsum_sub hq.summable,
    hp.tsum_eq, hq.tsum_eq]
  ring

/-- A uniform bound for all test-set discrepancies bounds the exact half-L1 distance.
@isnad1 id=le.5h4v.s7.61843215feb9 from=translated src=- shape=5c41cb9f vocab=5c118042
-/
theorem massTotalVariation_le_of_test_sets {p q : α → ℝ}
    (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) {r : ℝ}
    (h : ∀ A : Set α,
      |(∑' k, if k ∈ A then p k else 0) - ∑' k, if k ∈ A then q k else 0| ≤ r) :
    massTotalVariation p q ≤ r := by
  rw [massTotalVariation_eq_positive_set hp hq hp0 hq0]
  exact (le_abs_self _).trans (h {k | q k ≤ p k})

/-- A finite pushforward assigns the same mass as its original event.
@isnad1 id=eq.0h5v.s6.4fd8f38b5963 from=translated src=- shape=040d2b74 vocab=9e7ffc51
-/
theorem restricted_finiteFieldLaw_eq_eventProbability {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (W : Ω → α) (A : Set α) :
    (∑' k, if k ∈ A then finiteFieldLaw μ W k else 0) =
      eventProbability μ (fun ω => W ω ∈ A) := by
  classical
  let s : Finset α := Finset.univ.image W
  have hout (k : α) (hk : k ∉ s) : finiteFieldLaw μ W k = 0 := by
    unfold finiteFieldLaw
    apply Finset.sum_eq_zero
    intro ω _
    have hne : W ω ≠ k := fun h => hk (Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, h⟩)
    simp [hne]
  rw [tsum_eq_sum (s := s) (fun k hk => by simp [hout k hk])]
  unfold finiteFieldLaw eventProbability
  calc
    _ = ∑ k ∈ s, ∑ ω, if W ω = k then (if k ∈ A then μ.prob ω else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k ∈ A
      · simp only [hk, ite_true]
      · simp [hk]
    _ = ∑ ω, ∑ k ∈ s, if W ω = k then (if k ∈ A then μ.prob ω else 0) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ω _
      have hmem : W ω ∈ s := Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩
      simp [hmem]

/--
@isnad1 id=le.4h3v.s6.84afab9f0198 from=translated src=- shape=e41864ce vocab=f7df0499
-/
theorem massTotalVariation_le_one {p q : α → ℝ}
    (hp : HasSum p 1) (hq : HasSum q 1)
    (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) :
    massTotalVariation p q ≤ 1 := by
  have hsum := (summable_abs_sub_of_nonneg hp.summable hq.summable hp0 hq0).tsum_le_tsum
    (fun k => abs_sub_le_iff.2 ⟨by linarith [hp0 k, hq0 k], by linarith [hp0 k, hq0 k]⟩)
    (hp.summable.add hq.summable)
  rw [hp.summable.tsum_add hq.summable, hp.tsum_eq, hq.tsum_eq] at hsum
  unfold massTotalVariation
  linarith

/--
@isnad1 id=hassum.1h3v.s6.c4fa2661ab5a from=translated src=- shape=8b0daf02 vocab=5160b552
-/
theorem hasSum_uniformMixture {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → α → ℝ) (hp : ∀ i, HasSum (p i) 1) :
    HasSum (fun k => uniformAverage (fun i => p i k)) 1 := by
  have h := (hasSum_sum (s := Finset.univ) (fun i _ => hp i)).div_const (Fintype.card ι : ℝ)
  simpa [uniformAverage, Fintype.card_ne_zero] using h

/--
@isnad1 id=le.1h4v.s5.dc5c5e68dc08 from=translated src=- shape=b3b7e03a vocab=b3df313d
-/
theorem uniformMixture_nonneg {ι : Type*} [Fintype ι]
    (p : ι → α → ℝ) (hp : ∀ i k, 0 ≤ p i k) (k : α) :
    0 ≤ uniformAverage (fun i => p i k) := by
  unfold uniformAverage
  exact div_nonneg (Finset.sum_nonneg (fun i _ => hp i k)) (by positivity)

/--
@isnad1 id=le.0h6v.s6.e0ac6eb01b76 from=translated src=- shape=f047e86a vocab=48a4d7b8
-/
theorem event_discrepancy_le_disagreement {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z W : Ω → α) (A : Set α) :
    |eventProbability μ (fun ω => Z ω ∈ A) - eventProbability μ (fun ω => W ω ∈ A)| ≤
      eventProbability μ (fun ω => Z ω ≠ W ω) := by
  classical
  unfold eventProbability
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ ω, |(if Z ω ∈ A then μ.prob ω else 0) -
      (if W ω ∈ A then μ.prob ω else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases heq : Z ω = W ω
      · simp [heq]
      · by_cases hz : Z ω ∈ A <;> by_cases hw : W ω ∈ A <;>
          simp [heq, hz, hw, abs_of_nonneg (μ.nonneg ω), μ.nonneg ω]

/--
@isnad1 id=le.0h5v.s5.dfdc8b443796 from=translated src=- shape=010a5260 vocab=476f87c8
-/
theorem massTotalVariation_finiteFieldLaw_le_disagreement {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z W : Ω → α) :
    massTotalVariation (finiteFieldLaw μ Z) (finiteFieldLaw μ W) ≤
      eventProbability μ (fun ω => Z ω ≠ W ω) := by
  apply massTotalVariation_le_of_test_sets (hasSum_finiteFieldLaw μ Z) (hasSum_finiteFieldLaw μ W)
    (finiteFieldLaw_nonneg μ Z) (finiteFieldLaw_nonneg μ W)
  intro A
  rw [restricted_finiteFieldLaw_eq_eventProbability, restricted_finiteFieldLaw_eq_eventProbability]
  exact event_discrepancy_le_disagreement μ Z W A

/--
@isnad1 id=le.0h5v.s6.8ce3c16f62b5 from=translated src=- shape=add12a7a vocab=b31fa636
-/
theorem disagreement_le_sum_coordinate_disagreements {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] (μ : FinitePMF Ω) (Z W : Ω → ι → ℕ) :
    eventProbability μ (fun ω => Z ω ≠ W ω) ≤
      ∑ i, eventProbability μ (fun ω => Z ω i ≠ W ω i) := by
  classical
  unfold eventProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases heq : Z ω = W ω
  · simp only [heq, ne_eq, not_true_eq_false, ite_false]
    positivity
  · rw [ite_eq_left heq]
    obtain ⟨i, hi⟩ : ∃ i, Z ω i ≠ W ω i := by
      by_contra h
      apply heq
      funext i
      exact not_ne_iff.mp (not_exists.mp h i)
    calc
      μ.prob ω = if Z ω i ≠ W ω i then μ.prob ω else 0 := by simp [hi]
      _ ≤ ∑ j, if Z ω j ≠ W ω j then μ.prob ω else 0 :=
        Finset.single_le_sum (f := fun j => if Z ω j ≠ W ω j then μ.prob ω else 0)
          (fun j _ => by split_ifs <;> simp [μ.nonneg ω]) (Finset.mem_univ i)
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : Z ω j ≠ W ω j <;> simp [hj]

/--
@isnad1 id=le.0h5v.s6.008805f0acd1 from=translated src=- shape=61846985 vocab=24643671
-/
theorem massTotalVariation_finiteFieldLaw_le_coordinate_disagreements {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] (μ : FinitePMF Ω) (Z W : Ω → ι → ℕ) :
    massTotalVariation (finiteFieldLaw μ Z) (finiteFieldLaw μ W) ≤
      ∑ i, eventProbability μ (fun ω => Z ω i ≠ W ω i) :=
  (massTotalVariation_finiteFieldLaw_le_disagreement μ Z W).trans
    (disagreement_le_sum_coordinate_disagreements μ Z W)

def retainedField {Ω ι : Type*} (good : Finset ι) (W : Ω → ι → ℕ) (ω : Ω) (i : ι) : ℕ := by
  classical
  exact if i ∈ good then W ω i else 0

def badFieldSites {ι : Type*} [Fintype ι] (good : Finset ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => i ∉ good)

/--
@isnad1 id=iff.0h3v.s5.504101d0f316 from=translated src=- shape=59869106 vocab=566de319
-/
theorem mem_badFieldSites {ι : Type*} [Fintype ι] (good : Finset ι) (i : ι) :
    i ∈ badFieldSites good ↔ i ∉ good := by
  classical
  simp [badFieldSites]

/--
@isnad1 id=le.0h5v.s6.917ca8baebde from=translated src=- shape=1fd9d68d vocab=2c3aa0d5
-/
theorem massTotalVariation_retainedField_le_bad_sites {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] (μ : FinitePMF Ω) (good : Finset ι) (W : Ω → ι → ℕ) :
    massTotalVariation (finiteFieldLaw μ W) (finiteFieldLaw μ (retainedField good W)) ≤
      ∑ i ∈ badFieldSites good, eventProbability μ (fun ω => W ω i ≠ 0) := by
  classical
  apply (massTotalVariation_finiteFieldLaw_le_coordinate_disagreements μ W (retainedField good W)).trans_eq
  rw [badFieldSites, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ good <;> simp [retainedField, hi, eventProbability]
  all_goals
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : W ω i = 0 <;> simp [hω]

end
end PaperC.V282.FiniteFieldTotalVariation
