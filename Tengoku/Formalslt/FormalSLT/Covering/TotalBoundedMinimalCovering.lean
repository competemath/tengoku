import Tengoku.Formalslt.FormalSLT.Covering.TotalBoundedDudleyCovering
import Tengoku.Formalslt.FormalSLT.Covering.UnitIntervalDudley

/-!
# Genuine minimal covering numbers for totally bounded index spaces

This module defines the genuine finite metric covering number of a nonempty
totally bounded metric index space at a positive radius, then compares it with
the selected dyadic finite-net counts used by the total-bounded Dudley bridge.

The comparison proved here has the mathematically valid orientation: the
minimal covering number is bounded above by every selected finite cover count.
The reverse inequality needed to replace selected counts by minimal counts in
the current upper-bound Dudley wrapper would require the selected covers to be
chosen cardinal-minimal, or an added minimality hypothesis.
-/

namespace FormalSLT.Covering.TotalBoundedMinimalCovering

open scoped BigOperators Interval
open FormalSLT.Covering.FiniteSubGaussianChaining
open FormalSLT.Covering.TotalBoundedDudley
open FormalSLT.Covering.TotalBoundedDudleyCovering

noncomputable section

universe u

variable {T : Type u}

/-- There is a finite metric `ε`-cover of the whole index space using at most
`n` centers. This is the predicate minimized by
`minimalMetricCoveringNumber`. -/
def MetricCoverCardinalityLe [PseudoMetricSpace T] (ε : ℝ) (n : ℕ) : Prop :=
  ∃ C : Finset T, C.card ≤ n ∧ ∀ t : T, ∃ c ∈ C, dist t c ≤ ε

private theorem metricCoverCardinalityLe_exists_of_totallyBoundedUniv
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, MetricCoverCardinalityLe (T := T) ε n := by
  classical
  rcases finiteMetricCoverOfTotallyBoundedUniv (T := T) hT hε with
    ⟨C, hCfinite, hcover⟩
  let F : Finset T := hCfinite.toFinset
  refine ⟨F.card, F, le_rfl, ?_⟩
  intro t
  rcases hcover t with ⟨c, hc, hdist⟩
  exact ⟨c, by simpa [F] using (hCfinite.mem_toFinset.mpr hc), hdist⟩

/-- The genuine minimal metric covering number of a nonempty totally bounded
index space at a positive radius. -/
def minimalMetricCoveringNumber [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) : ℕ := by
  classical
  exact Nat.find
    (metricCoverCardinalityLe_exists_of_totallyBoundedUniv (T := T) hT hε)

/-- The minimal covering number is realized by an explicit finite metric cover.
@isnad1 id=metricco.2h2v.s5.916f45f0181c from=translated src=- shape=a5af5997 vocab=a994b2b2
-/
theorem minimalMetricCoveringNumber_spec
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) :
    MetricCoverCardinalityLe (T := T) ε
      (minimalMetricCoveringNumber (T := T) hT hε) := by
  classical
  unfold minimalMetricCoveringNumber
  exact Nat.find_spec
    (metricCoverCardinalityLe_exists_of_totallyBoundedUniv (T := T) hT hε)

/-- Minimality: any finite metric `ε`-cover with at most `n` centers bounds the
genuine minimal covering number by `n`.
@isnad1 id=le.3h3v.s5.ba70e24debc6 from=translated src=- shape=c1b61b0c vocab=4125e241
-/
theorem minimalMetricCoveringNumber_le_of_metricCoverCardinalityLe
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (hcover : MetricCoverCardinalityLe (T := T) ε n) :
    minimalMetricCoveringNumber (T := T) hT hε ≤ n := by
  classical
  unfold minimalMetricCoveringNumber
  exact Nat.find_min'
    (metricCoverCardinalityLe_exists_of_totallyBoundedUniv (T := T) hT hε)
    hcover

/-- A nonempty index space has positive genuine minimal covering number at any
positive radius.
@isnad1 id=lt.2h2v.s5.f369d81b89f5 from=translated src=- shape=2523e5d6 vocab=51641571
-/
theorem minimalMetricCoveringNumber_pos
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) :
    0 < minimalMetricCoveringNumber (T := T) hT hε := by
  by_contra hnot
  have hzero :
      minimalMetricCoveringNumber (T := T) hT hε = 0 :=
    Nat.eq_zero_of_not_pos hnot
  rcases minimalMetricCoveringNumber_spec (T := T) hT hε with
    ⟨C, hcard, hcover⟩
  have hcard_zero : C.card = 0 := by
    exact Nat.eq_zero_of_le_zero (by simpa [hzero] using hcard)
  have hC_empty : C = ∅ := Finset.card_eq_zero.mp hcard_zero
  obtain ⟨t⟩ := (inferInstance : Nonempty T)
  rcases hcover t with ⟨c, hc, _hdist⟩
  simp [hC_empty] at hc

/-- A cardinal-minimal finite metric `ε`-cover of the whole index space.

This is the selected-cover construction needed for the genuine-minimal route:
the cover is chosen from the `Nat.find` witness for
`minimalMetricCoveringNumber`, not supplied as an extra hypothesis. -/
def minimalMetricCoverOfTotallyBoundedUniv
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) :
    Finset T :=
  Classical.choose (minimalMetricCoveringNumber_spec (T := T) hT hε)

/-- The chosen minimal cover covers every index point within radius `ε`.
@isnad1 id=ex.2h3v.s6.bac66ccd467b from=translated src=- shape=84f5a79a vocab=dbfbbd28
-/
theorem minimalMetricCoverOfTotallyBoundedUniv_cover
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε)
    (t : T) :
    ∃ c ∈ minimalMetricCoverOfTotallyBoundedUniv (T := T) hT hε,
      dist t c ≤ ε := by
  classical
  exact (Classical.choose_spec
    (minimalMetricCoveringNumber_spec (T := T) hT hε)).2 t

/-- The chosen minimal cover has at most the genuine minimal covering number
many centers.
@isnad1 id=le.2h2v.s5.f30b1f1194cf from=translated src=- shape=5c826eb7 vocab=88d74c5f
-/
theorem minimalMetricCoverOfTotallyBoundedUniv_card_le
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) :
    (minimalMetricCoverOfTotallyBoundedUniv (T := T) hT hε).card ≤
      minimalMetricCoveringNumber (T := T) hT hε := by
  classical
  exact (Classical.choose_spec
    (minimalMetricCoveringNumber_spec (T := T) hT hε)).1

/-- The chosen minimal cover has exactly the genuine minimal covering number
of centers.
@isnad1 id=eq.2h2v.s5.85968b5cbbc9 from=translated src=- shape=5c826eb7 vocab=ebe946d9
-/
theorem minimalMetricCoverOfTotallyBoundedUniv_card_eq
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) :
    (minimalMetricCoverOfTotallyBoundedUniv (T := T) hT hε).card =
      minimalMetricCoveringNumber (T := T) hT hε := by
  classical
  apply le_antisymm
  · exact minimalMetricCoverOfTotallyBoundedUniv_card_le (T := T) hT hε
  · exact minimalMetricCoveringNumber_le_of_metricCoverCardinalityLe
      (T := T) hT hε
      ⟨minimalMetricCoverOfTotallyBoundedUniv (T := T) hT hε, le_rfl,
        minimalMetricCoverOfTotallyBoundedUniv_cover (T := T) hT hε⟩

/-- Cardinal minimality of the chosen finite metric cover: every finite
`ε`-cover has at least as many centers.
@isnad1 id=le.3h3v.s6.9430d0e721ac from=translated src=- shape=c22c5f17 vocab=c8a09e88
-/
theorem minimalMetricCoverOfTotallyBoundedUniv_card_minimal
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε)
    (C : Finset T) (hcover : ∀ t : T, ∃ c ∈ C, dist t c ≤ ε) :
    (minimalMetricCoverOfTotallyBoundedUniv (T := T) hT hε).card ≤ C.card := by
  rw [minimalMetricCoverOfTotallyBoundedUniv_card_eq (T := T) hT hε]
  exact minimalMetricCoveringNumber_le_of_metricCoverCardinalityLe
    (T := T) hT hε ⟨C, le_rfl, hcover⟩

/-- Convert the cardinal-minimal finite cover into the finite-net record used
by the chaining layer. -/
def minimalFiniteNetOfTotallyBoundedUniv
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) (hε : 0 < ε) :
    BundledFiniteNet T := by
  classical
  let F := minimalMetricCoverOfTotallyBoundedUniv (T := T) hT hε
  exact finiteNetOfCoverSet
    (F : Set T)
    (by exact F.finite_toSet)
    ε hε.le
    (by
      intro t
      rcases minimalMetricCoverOfTotallyBoundedUniv_cover
          (T := T) hT hε t with
        ⟨c, hc, hdist⟩
      exact ⟨c, by simpa [F] using hc, hdist⟩)

/-- The minimal finite-net extractor uses the requested radius.
@isnad1 id=eq.2h2v.s5.90942d30454d from=translated src=- shape=3aedba70 vocab=f373c74f
-/
@[simp] theorem minimalFiniteNetOfTotallyBoundedUniv_radius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) (hε : 0 < ε) :
    (minimalFiniteNetOfTotallyBoundedUniv (T := T) hT ε hε).net.radius = ε := by
  rfl

/-- The minimal finite-net extractor uses the ambient metric distance.
@isnad1 id=eq.2h2v.s6.d59a206e9e8c from=translated src=- shape=de8144fc vocab=95499679
-/
@[simp] theorem minimalFiniteNetOfTotallyBoundedUniv_dist
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) (ε : ℝ) (hε : 0 < ε) :
    (minimalFiniteNetOfTotallyBoundedUniv (T := T) hT ε hε).net.dist =
      fun s t => dist s t := by
  rfl

/-- The bundled minimal finite net carries exactly the genuine minimal covering
number of centers.
@isnad1 id=eq.2h2v.s5.bfd1feee28d6 from=translated src=- shape=5c826eb7 vocab=05bfe14f
-/
theorem minimalFiniteNetOfTotallyBoundedUniv_coveringNumber_eq
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T)) {ε : ℝ} (hε : 0 < ε) :
    (minimalFiniteNetOfTotallyBoundedUniv (T := T) hT ε hε).coveringNumber =
      minimalMetricCoveringNumber (T := T) hT hε := by
  classical
  unfold minimalFiniteNetOfTotallyBoundedUniv BundledFiniteNet.coveringNumber
    FiniteNet.coveringNumber finiteNetOfCoverSet
  simp [minimalMetricCoverOfTotallyBoundedUniv_card_eq (T := T) hT hε]

/-- Dyadic finite-net schedule whose cover at each scale is cardinal-minimal. -/
def minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    BundledFiniteNet T :=
  minimalFiniteNetOfTotallyBoundedUniv
    (T := T) hT (dyadicChainingNetRadius radiusScale j)
    (dyadicChainingNetRadius_pos hradiusScale j)

/-- The minimal dyadic finite-net schedule has the expected radius.
@isnad1 id=eq.2h3v.s6.d3d37a1d734f from=translated src=- shape=ca4f7769 vocab=c72286e1
-/
@[simp] theorem minimalDyadicChainingFiniteNetOfTotallyBoundedUniv_radius
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net.radius =
      dyadicChainingNetRadius radiusScale j := by
  rfl

/-- The minimal dyadic finite-net schedule uses the ambient metric distance.
@isnad1 id=eq.2h3v.s6.b0468f11eb47 from=translated src=- shape=87184d35 vocab=8c8f73e6
-/
@[simp] theorem minimalDyadicChainingFiniteNetOfTotallyBoundedUniv_dist
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).net.dist = fun s t => dist s t := by
  rfl

/-- At each dyadic radius, the minimal dyadic finite net has cardinality equal
to the genuine minimal covering number.
@isnad1 id=eq.2h3v.s5.b878076c715b from=translated src=- shape=cd94b566 vocab=38887fac
-/
theorem minimalDyadicChainingFiniteNetOfTotallyBoundedUniv_coveringNumber_eq
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    (minimalDyadicChainingFiniteNetOfTotallyBoundedUniv
      (T := T) hT hradiusScale j).coveringNumber =
      minimalMetricCoveringNumber
        (T := T) hT (dyadicChainingNetRadius_pos hradiusScale j) := by
  exact minimalFiniteNetOfTotallyBoundedUniv_coveringNumber_eq
    (T := T) hT (dyadicChainingNetRadius_pos hradiusScale j)

/-- A bundled finite net using the ambient metric distance gives a finite metric
cover with at most its selected covering count.
@isnad1 id=metricco.1h2v.s5.aad93cd52709 from=translated src=- shape=f76c5107 vocab=97db8f09
-/
theorem metricCoverCardinalityLe_of_bundledFiniteNet
    [PseudoMetricSpace T] [Nonempty T]
    (B : BundledFiniteNet T)
    (hdist : B.net.dist = fun s t => dist s t) :
    MetricCoverCardinalityLe (T := T) B.net.radius B.coveringNumber := by
  classical
  letI : Fintype B.A := B.instFintype
  let C : Finset T := Finset.univ.image B.net.center
  refine ⟨C, ?_, ?_⟩
  · have hcard : C.card ≤ (Finset.univ : Finset B.A).card :=
      Finset.card_image_le
    simpa [C, BundledFiniteNet.coveringNumber, FiniteNet.coveringNumber] using hcard
  · intro t
    refine ⟨B.net.center (B.net.project t), ?_, ?_⟩
    · simp [C]
    · simpa [hdist] using B.net.covers t

/-- Any ambient-metric bundled finite net bounds the genuine minimal covering
number at its radius.
@isnad1 id=le.3h2v.s6.6b01a6b85eae from=translated src=- shape=26dfd16d vocab=4ddad246
-/
theorem minimalMetricCoveringNumber_le_bundledFiniteNet_coveringNumber
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    (B : BundledFiniteNet T)
    (hdist : B.net.dist = fun s t => dist s t)
    (hradius : 0 < B.net.radius) :
    minimalMetricCoveringNumber (T := T) hT hradius ≤ B.coveringNumber :=
  minimalMetricCoveringNumber_le_of_metricCoverCardinalityLe
    (T := T) hT hradius
    (metricCoverCardinalityLe_of_bundledFiniteNet (T := T) B hdist)

/-- At each dyadic radius, the genuine minimal covering number is bounded by
the selected total-bounded dyadic net cardinality.
@isnad1 id=le.2h3v.s6.c1b7ed929505 from=translated src=- shape=7fc94c78 vocab=ea4964d6
-/
theorem minimalMetricCoveringNumber_le_dyadicSelectedCoveringNumber
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    minimalMetricCoveringNumber (T := T) hT
        (dyadicChainingNetRadius_pos hradiusScale j) ≤
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.coveringNumber := by
  have hdist :
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.dist = fun s t => dist s t := by
    simp
  have hle :=
    minimalMetricCoveringNumber_le_bundledFiniteNet_coveringNumber
      (T := T) hT
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j)
      hdist
      (by simp [dyadicChainingNetRadius_pos hradiusScale j])
  simpa [BundledFiniteNet.coveringNumber] using hle

/-- The selected dyadic envelope dominates the genuine minimal covering number
at each sampled dyadic net radius. This is the true bridge from minimal
covering numbers to the currently selected-count staircase.
@isnad1 id=le.2h3v.s5.128d68a18547 from=translated src=- shape=60c44c40 vocab=81ac8858
-/
theorem minimalMetricCoveringNumber_le_totalBoundedDyadicCoverCountEnvelope
    [PseudoMetricSpace T] [Nonempty T]
    (hT : TotallyBounded (Set.univ : Set T))
    {radiusScale : ℝ} (hradiusScale : 0 < radiusScale) (j : ℕ) :
    minimalMetricCoveringNumber (T := T) hT
        (dyadicChainingNetRadius_pos hradiusScale j) ≤
      totalBoundedDyadicCoverCountEnvelope (T := T) hT hradiusScale j := by
  have hminimal :=
    minimalMetricCoveringNumber_le_dyadicSelectedCoveringNumber
      (T := T) hT hradiusScale j
  have hsucc_pos :
      0 <
        (dyadicChainingFiniteNetOfTotallyBoundedUniv
          (T := T) hT hradiusScale (j + 1)).net.coveringNumber :=
    FiniteNet.coveringNumber_pos
      ((dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale (j + 1)).net)
  have hnet_le_product :
      (dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.coveringNumber ≤
        dyadicChainingCoverCount (T := T) hT hradiusScale j := by
    unfold dyadicChainingCoverCount
    exact Nat.le_mul_of_pos_right
      ((dyadicChainingFiniteNetOfTotallyBoundedUniv
        (T := T) hT hradiusScale j).net.coveringNumber)
      hsucc_pos
  exact hminimal.trans
    (hnet_le_product.trans
      (dyadicChainingCoverCount_le_envelope (T := T) hT hradiusScale j))

/-- Non-vacuity witness: the genuine minimal covering number is positive on the
mechanized unit interval at a concrete positive radius.
@isnad1 id=lt.0h0v.s5.c1a505a20f17 from=translated src=- shape=af2c19b7 vocab=11aec84d
-/
theorem unitInterval_minimalMetricCoveringNumber_sample_positive :
    0 <
      minimalMetricCoveringNumber
        (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
        FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
        (by norm_num : (0 : ℝ) < (1 : ℝ) / 2) :=
  minimalMetricCoveringNumber_pos
    (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
    FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
    (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)

/-- Non-vacuity witness: the chosen cardinal-minimal finite cover of the
mechanized unit interval has positive cardinality at a concrete radius.
@isnad1 id=lt.0h0v.s6.9ad60196ec6c from=translated src=- shape=76c08603 vocab=7df8b4a1
-/
theorem unitInterval_minimalMetricCoverOfTotallyBoundedUniv_sample_card_positive :
    0 <
      (minimalMetricCoverOfTotallyBoundedUniv
        (T := FormalSLT.Covering.UnitIntervalDudley.UnitInterval)
        FormalSLT.Covering.UnitIntervalDudley.unitInterval_totallyBounded_univ
        (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).card := by
  rw [minimalMetricCoverOfTotallyBoundedUniv_card_eq]
  exact unitInterval_minimalMetricCoveringNumber_sample_positive

end

end FormalSLT.Covering.TotalBoundedMinimalCovering
