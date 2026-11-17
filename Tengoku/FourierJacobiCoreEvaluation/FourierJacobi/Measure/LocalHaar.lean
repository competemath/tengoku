import Tengoku.Seed.NumberTheory.LocalField.Basic
import Tengoku.Seed.MeasureTheory.Measure.Haar.Basic
import Tengoku.Seed.RingTheory.Ideal.Norm.AbsNorm
import Tengoku.Seed.MeasureTheory.Measure.Real
import Tengoku.FourierJacobiCoreEvaluation.FourierJacobi.Measure.NullSets

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Concrete normalized local-field Haar measure

The field is an arbitrary nonarchimedean local field in mathlib's sense.
The residue cardinality is the cardinality of its actual residue field.
No primality, characteristic-zero, or oddness restriction is needed here.

The measure is constructed by Haar's theorem, normalized on the actual
valuation ring. Ideal-power volumes are deduced from finite additive indices;
they are not supplied as assumptions. These are ingredients of `exp:haar-shells`
and `expanded:collision` in the expanded Section 2.
-/

noncomputable section

open MeasureTheory ValuativeRel
open scoped ENNReal NNReal

namespace FourierJacobi.Measure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/--
@isnad1 id=t2space.0h1v.s4.7e1ccb55d0cf from=translated src=- shape=7ddc04c7 vocab=d124730f
-/
local instance localField_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

variable [MeasurableSpace K] [BorelSpace K]

/-- The compact open valuation ring, as a normalization set for Haar measure.-/
def integersCompact : TopologicalSpace.PositiveCompacts K :=
  ⟨⟨𝒪[K], IsNonarchimedeanLocalField.isCompact_closedBall K 1⟩,
    by
      rw [(valuation K).isOpen_integer.interior_eq]
      exact ⟨0, by simp⟩⟩

/-- Additive Haar measure on the local field, with valuation-ring volume one.-/
def additiveHaar : MeasureTheory.Measure K :=
  MeasureTheory.Measure.addHaarMeasure (integersCompact K)

/--
@isnad1 id=isaddhaa.0h1v.s5.5c2a09d9380e from=translated src=- shape=21c02aa3 vocab=9ceed8db
-/
instance additiveHaar_isAddHaarMeasure : (additiveHaar K).IsAddHaarMeasure := by
  unfold additiveHaar
  infer_instance

/--
@isnad1 id=eq.0h1v.s6.48d065ff14f6 from=translated src=- shape=49bb49cf vocab=f5e43de9
-/
theorem additiveHaar_integers : additiveHaar K (𝒪[K] : Set K) = 1 :=
  MeasureTheory.Measure.addHaarMeasure_self

/-- The actual cardinality of the residue field; it is not assumed prime.-/
def residueCardinality : ℕ := Nat.card 𝓀[K]

omit [MeasurableSpace K] [BorelSpace K] in
/--
@isnad1 id=lt.0h1v.s5.ca0b47ea1fc0 from=translated src=- shape=41309794 vocab=573039cb
-/
theorem residueCardinality_pos : 0 < residueCardinality K := Nat.card_pos

omit [MeasurableSpace K] [BorelSpace K] in
/--
@isnad1 id=isprimep.0h1v.s5.8279542281e0 from=translated src=- shape=58163b13 vocab=7bbeac12
-/
theorem residueCardinality_isPrimePow : IsPrimePow (residueCardinality K) := by
  let := Fintype.ofFinite 𝓀[K]
  simpa [residueCardinality, Nat.card_eq_fintype_card] using
    (FiniteField.isPrimePow_card (K := 𝓀[K]))

omit [MeasurableSpace K] [BorelSpace K] in
/--
@isnad1 id=lt.0h1v.s5.c0003d6b0709 from=translated src=- shape=41309794 vocab=573039cb
-/
theorem residueCardinality_one_lt : 1 < residueCardinality K := by
  have h := (residueCardinality_isPrimePow K).two_le
  omega

/--
@isnad1 id=measurab.0h1v.s8.4954c69924b0 from=translated src=- shape=41cc921b vocab=0cbf2d61
-/
theorem integers_measurableEmbedding :
    MeasurableEmbedding (fun x : 𝒪[K] => (x : K)) :=
  MeasurableEmbedding.subtype_coe (valuation K).isOpen_integer.measurableSet

/-- The pullback of ambient additive Haar measure to its compact valuation ring.-/
def integersHaar : MeasureTheory.Measure 𝒪[K] :=
  (additiveHaar K).comap (fun x : 𝒪[K] => (x : K))

/--
@isnad1 id=isaddlef.0h1v.s8.861dc17f7fed from=translated src=- shape=3d1c311b vocab=9e39e005
-/
instance integersHaar_isAddLeftInvariant : (integersHaar K).IsAddLeftInvariant :=
  MeasureTheory.Measure.IsAddLeftInvariant.comap (additiveHaar K)
    (f := (𝒪[K]).subtype.toAddMonoidHom) (integers_measurableEmbedding K)

/--
@isnad1 id=eq.0h2v.s9.fdf431cd1e7b from=translated src=- shape=30934dad vocab=4fc9e81c
-/
theorem integersHaar_apply (s : Set 𝒪[K]) :
    integersHaar K s = additiveHaar K ((fun x : 𝒪[K] => (x : K)) '' s) :=
  (integers_measurableEmbedding K).comap_apply (additiveHaar K) s

/--
@isnad1 id=eq.0h1v.s9.432d2897927a from=translated src=- shape=a549bc19 vocab=6dfb40aa
-/
theorem integersHaar_univ : integersHaar K Set.univ = 1 := by
  rw [integersHaar_apply]
  simpa using additiveHaar_integers K

/--
@isnad1 id=isprobab.0h1v.s7.ae0e45c10fe9 from=translated src=- shape=1b67010a vocab=f0a3ac47
-/
instance integersHaar_isProbabilityMeasure : IsProbabilityMeasure (integersHaar K) :=
  ⟨integersHaar_univ K⟩

omit [MeasurableSpace K] [BorelSpace K] in
/--
@isnad1 id=ne.0h1v.s10.75a9abf55e8b from=translated src=- shape=2b1f4312 vocab=73e529b4
-/
theorem maximalIdeal_ne_bot : 𝓂[K] ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field 𝒪[K]

omit [MeasurableSpace K] [BorelSpace K] in
/-- The finite additive index of the nth maximal-ideal power is q^n.
@isnad1 id=eq.0h2v.s11.5487bd6c80f9 from=translated src=- shape=25e41e5a vocab=3b8ef486
-/
theorem maximalIdeal_pow_index (n : ℕ) :
    (𝓂[K] ^ n).toAddSubgroup.index = residueCardinality K ^ n := by
  exact cardQuot_pow_of_prime (maximalIdeal_ne_bot K)

/--
@isnad1 id=finitein.0h2v.s11.63850ef04cdd from=translated src=- shape=a953f395 vocab=3e4600df
-/
instance maximalIdeal_pow_finiteIndex (n : ℕ) : (𝓂[K] ^ n).toAddSubgroup.FiniteIndex :=
  ⟨by rw [maximalIdeal_pow_index]; exact pow_ne_zero n (residueCardinality_pos K).ne'⟩

/-- Every nonnegative valuation ball has its expected volume, using actual Haar measure.
@isnad1 id=eq.0h2v.s11.0fbd6f97eea9 from=translated src=- shape=4701b71e vocab=c9f94e77
-/
theorem integersHaar_maximalIdeal_pow (n : ℕ) :
    integersHaar K ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) = (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  have h := (𝓂[K] ^ n).toAddSubgroup.index_mul_measure
    (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ n)).measurableSet (integersHaar K)
  rw [maximalIdeal_pow_index, integersHaar_univ, Nat.cast_pow] at h
  rw [← ENNReal.inv_pow, ← one_div]
  exact (ENNReal.eq_div_iff (pow_ne_zero n (by exact_mod_cast
    (residueCardinality_pos K).ne')) (by finiteness)).mpr h

/-- Ambient local-field volume of the image of the nth maximal-ideal power.
@isnad1 id=eq.0h2v.s11.cf7327b60558 from=translated src=- shape=fb35052b vocab=b9ed365d
-/
theorem additiveHaar_maximalIdeal_pow (n : ℕ) :
    additiveHaar K ((fun x : 𝒪[K] => (x : K)) '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) =
      (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  rw [← integersHaar_apply, integersHaar_maximalIdeal_pow]

omit [MeasurableSpace K] [BorelSpace K] in
/-- A chosen generator of the maximal ideal realizes its powers as actual valuation balls.
This includes zero, whose multiplicative valuation is zero (additive valuation infinity).
@isnad1 id=iff.1h4v.s11.7bc3f5edc281 from=translated src=- shape=af843562 vocab=3a9fdc8d
-/
theorem mem_maximalIdeal_pow_iff_valuation_le (π : 𝒪[K])
    (hπ : 𝓂[K] = Ideal.span {π}) (n : ℕ) (x : 𝒪[K]) :
    x ∈ 𝓂[K] ^ n ↔ valuation K (x : K) ≤ valuation K (π : K) ^ n := by
  rw [hπ, Ideal.span_singleton_pow]
  change x ∈ (Ideal.span {π ^ n} : Set 𝒪[K]) ↔ _
  rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
  simp

/-- Nonnegative uniformizer balls in the ambient field have volume q^-n.
@isnad1 id=eq.1h3v.s10.2a4cd3c18dfb from=translated src=- shape=568d81f8 vocab=e7a8148a
-/
theorem additiveHaar_uniformizer_pow (π : 𝒪[K])
    (hπ : 𝓂[K] = Ideal.span {π}) (n : ℕ) :
    additiveHaar K ((fun u : 𝒪[K] => (π : K) ^ n * (u : K)) '' Set.univ) =
      (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  have heq : (fun u : 𝒪[K] => (π : K) ^ n * (u : K)) '' Set.univ =
      (fun x : 𝒪[K] => (x : K)) '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := by
    rw [hπ, Ideal.span_singleton_pow]
    ext x
    constructor
    · rintro ⟨u, _, rfl⟩
      exact ⟨π ^ n * u, Ideal.mem_span_singleton.mpr ⟨u, rfl⟩, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hy
      exact ⟨u, Set.mem_univ _, by simp⟩
  rw [heq, additiveHaar_maximalIdeal_pow]

/-- Unit elements inside the valuation ring, kept as a measurable subset of the ring.-/
def integralUnits : Set 𝒪[K] := (𝓂[K] : Set 𝒪[K])ᶜ

omit [MeasurableSpace K] [BorelSpace K] in
/--
@isnad1 id=iff.0h2v.s9.20e74dd897b2 from=translated src=- shape=e228d26a vocab=e521f061
-/
theorem mem_integralUnits_iff (x : 𝒪[K]) : x ∈ integralUnits K ↔ IsUnit x := by
  simp [integralUnits, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/--
@isnad1 id=measurab.0h1v.s7.7bc1bbb22167 from=translated src=- shape=3d1c311b vocab=9bff7dcd
-/
theorem integralUnits_measurableSet : MeasurableSet (integralUnits K) :=
  (IsNoetherianRing.isClosed_ideal 𝓂[K]).measurableSet.compl

/-- Additive volume of the units, with precisely the manuscript's normalization.
@isnad1 id=eq.0h1v.s9.e406f5f4c688 from=translated src=- shape=4bb19861 vocab=d15451c7
-/
theorem integersHaar_integralUnits :
    integersHaar K (integralUnits K) = 1 - (residueCardinality K : ℝ≥0∞)⁻¹ := by
  rw [integralUnits, measure_compl (IsNoetherianRing.isClosed_ideal 𝓂[K]).measurableSet
    (measure_ne_top _ _)]
  simpa using congrArg (fun x : ℝ≥0∞ => 1 - x) (integersHaar_maximalIdeal_pow K 1)

/-- The additive valuation shell of depth n in the valuation ring.-/
def integralShell (n : ℕ) : Set 𝒪[K] :=
  ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) \ ((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Set 𝒪[K])

/--
@isnad1 id=eq.0h2v.s9.7fa09e083e0f from=translated src=- shape=3fbf6ecb vocab=e4636c0e
-/
theorem integersHaar_integralShell (n : ℕ) :
    integersHaar K (integralShell K n) =
      (residueCardinality K : ℝ≥0∞)⁻¹ ^ n -
        (residueCardinality K : ℝ≥0∞)⁻¹ ^ (n + 1) := by
  rw [integralShell, measure_sdiff
    (show ((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) from
      Ideal.pow_le_pow_right (Nat.le_succ n))
    (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ (n + 1))).measurableSet.nullMeasurableSet
    (measure_ne_top _ _), integersHaar_maximalIdeal_pow, integersHaar_maximalIdeal_pow]

/-- The event that a unit differs from one by an element of the nth ideal power.
The definition itself is on the whole valuation ring; for positive n the event
is proved to consist of units. The point one is retained at every finite depth.-/
def collisionTail (n : ℕ) : Set 𝒪[K] :=
  (fun x : 𝒪[K] => x - 1) ⁻¹' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])

/--
@isnad1 id=measurab.0h2v.s7.76003e90226f from=translated src=- shape=0cc30f15 vocab=7b294759
-/
theorem collisionTail_measurableSet (n : ℕ) : MeasurableSet (collisionTail K n) :=
  (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ n)).measurableSet.preimage
    (by fun_prop)

omit [MeasurableSpace K] [BorelSpace K] in
/--
@isnad1 id=le.0h2v.s7.61560ecec22d from=translated src=- shape=312cc9b5 vocab=e672c8fe
-/
theorem collisionTail_succ_subset (n : ℕ) :
    collisionTail K (n + 1) ⊆ collisionTail K n :=
  Set.preimage_mono (Ideal.pow_le_pow_right (Nat.le_succ n))

omit [MeasurableSpace K] [BorelSpace K] in
/--
@isnad1 id=le.1h2v.s7.9fe2284623a6 from=translated src=- shape=bc9d11ce vocab=31e39d33
-/
theorem collisionTail_subset_units {n : ℕ} (hn : 0 < n) :
    collisionTail K n ⊆ integralUnits K := by
  intro x hx
  have hm : x - 1 ∈ 𝓂[K] :=
    (show 𝓂[K] ^ n ≤ 𝓂[K] from by simpa using
      (Ideal.pow_le_pow_right (I := 𝓂[K]) hn)) hx
  intro hx'
  have h1 := (𝓂[K]).sub_mem hx' hm
  simp only [sub_sub_cancel] at h1
  exact Ideal.one_notMem 𝓂[K] h1

/--
@isnad1 id=eq.0h2v.s9.103972a129c8 from=translated src=- shape=a2347389 vocab=e010a64b
-/
theorem integersHaar_collisionTail (n : ℕ) :
    integersHaar K (collisionTail K n) = (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  simp only [collisionTail, sub_eq_add_neg, measure_preimage_add_right]
  exact integersHaar_maximalIdeal_pow K n

/--
@isnad1 id=eq.0h2v.s11.7e7a85716cd9 from=translated src=- shape=eadfcf69 vocab=dc2576de
-/
theorem integersHaar_real_maximalIdeal_pow (n : ℕ) :
    (integersHaar K).real ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) =
      (residueCardinality K : ℝ)⁻¹ ^ n := by
  simp [measureReal_def, integersHaar_maximalIdeal_pow]

/-- The ordinary real-valued shell volume in product form.
@isnad1 id=eq.0h2v.s7.c54c3176795b from=translated src=- shape=80d22805 vocab=cd904a3a
-/
theorem integersHaar_real_integralShell (n : ℕ) :
    (integersHaar K).real (integralShell K n) =
      (1 - (residueCardinality K : ℝ)⁻¹) * (residueCardinality K : ℝ)⁻¹ ^ n := by
  rw [integralShell, measureReal_sdiff
    (show ((𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) : Set 𝒪[K]) ⊆
      ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) from
      Ideal.pow_le_pow_right (Nat.le_succ n))
    (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ (n + 1))).measurableSet,
    integersHaar_real_maximalIdeal_pow, integersHaar_real_maximalIdeal_pow, pow_succ]
  ring

/--
@isnad1 id=eq.0h2v.s7.3052c2087790 from=translated src=- shape=1a43d467 vocab=c4b3e48c
-/
theorem integersHaar_real_collisionTail (n : ℕ) :
    (integersHaar K).real (collisionTail K n) = (residueCardinality K : ℝ)⁻¹ ^ n := by
  simp [measureReal_def, integersHaar_collisionTail]

/--
@isnad1 id=eq.0h1v.s7.99c95ab11469 from=translated src=- shape=df57f8b7 vocab=d1349d9b
-/
theorem integersHaar_real_integralUnits :
    (integersHaar K).real (integralUnits K) = 1 - (residueCardinality K : ℝ)⁻¹ := by
  rw [integralUnits, measureReal_compl
    (IsNoetherianRing.isClosed_ideal 𝓂[K]).measurableSet]
  simpa using congrArg (fun x : ℝ => 1 - x) (integersHaar_real_maximalIdeal_pow K 1)

/-- The conditional Haar mass of a measurable event, conditioned on being a unit.
This is a ratio of actual Haar measures, not a stipulated distribution.-/
def unitConditionalMass (s : Set 𝒪[K]) : ℝ :=
  (integersHaar K).real (s ∩ integralUnits K) /
    (integersHaar K).real (integralUnits K)

/--
@isnad1 id=eq.1h2v.s8.97e865fba13a from=translated src=- shape=6b02b83f vocab=9ff3b08e
-/
theorem unitConditionalMass_of_subset (s : Set 𝒪[K]) (hs : s ⊆ integralUnits K) :
    unitConditionalMass K s = (integersHaar K).real s /
      (1 - (residueCardinality K : ℝ)⁻¹) := by
  rw [unitConditionalMass, Set.inter_eq_self_of_subset_left hs,
    integersHaar_real_integralUnits]

/-- Cancellation tail law: depth at least n+1 has probability q^-n/(q-1).
@isnad1 id=eq.0h2v.s6.9d7bee771ea5 from=translated src=- shape=c1afe3e2 vocab=ea5eb858
-/
theorem unitConditionalMass_collisionTail (n : ℕ) :
    unitConditionalMass K (collisionTail K (n + 1)) =
      (residueCardinality K : ℝ)⁻¹ ^ n / (residueCardinality K - 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by
    exact_mod_cast residueCardinality_one_lt K
  rw [unitConditionalMass_of_subset _ _ (collisionTail_subset_units K (Nat.succ_pos n)),
    integersHaar_real_collisionTail, pow_succ]
  field_simp

/-- Cancellation mass at positive depth: the difference of successive actual tails.
@isnad1 id=eq.0h2v.s8.95b4f8d07633 from=translated src=- shape=533294ce vocab=caa668ac
-/
theorem unitConditionalMass_collisionDepth (n : ℕ) :
    unitConditionalMass K (collisionTail K (n + 1) \ collisionTail K (n + 2)) =
      (residueCardinality K : ℝ)⁻¹ ^ (n + 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by
    exact_mod_cast residueCardinality_one_lt K
  rw [unitConditionalMass_of_subset _ _
    (Set.Subset.trans Set.sdiff_subset (collisionTail_subset_units K (Nat.succ_pos n))),
    measureReal_sdiff (collisionTail_succ_subset K (n + 1))
      (collisionTail_measurableSet K (n + 2)),
    integersHaar_real_collisionTail, integersHaar_real_collisionTail]
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  have hd : 1 - (residueCardinality K : ℝ)⁻¹ ≠ 0 := by
    have hq0 : (residueCardinality K : ℝ) ≠ 0 := (lt_trans zero_lt_one hq).ne'
    have heq : 1 - (residueCardinality K : ℝ)⁻¹ =
        (residueCardinality K - 1) / residueCardinality K := by field_simp
    rw [heq]
    exact div_ne_zero (sub_ne_zero.mpr hq.ne') hq0
  calc
    _ = (residueCardinality K : ℝ)⁻¹ ^ (n + 1) *
        (1 - (residueCardinality K : ℝ)⁻¹) /
        (1 - (residueCardinality K : ℝ)⁻¹) := by congr 1; ring
    _ = _ := mul_div_cancel_right₀ _ hd

/-- Cancellation mass at depth zero, inside the unit group.
@isnad1 id=eq.0h1v.s8.02e7b72f474a from=translated src=- shape=89394ab9 vocab=2b26266d
-/
theorem unitConditionalMass_collisionDepth_zero :
    unitConditionalMass K (integralUnits K \ collisionTail K 1) =
      (residueCardinality K - 2) / (residueCardinality K - 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by
    exact_mod_cast residueCardinality_one_lt K
  rw [unitConditionalMass_of_subset _ _ Set.sdiff_subset,
    measureReal_sdiff (collisionTail_subset_units K (by omega))
      (collisionTail_measurableSet K 1),
    integersHaar_real_collisionTail, integersHaar_real_integralUnits, pow_one]
  field_simp
  ring

/-- The corresponding congruence ball centered at an arbitrary integral unit.-/
def unitCenteredTail (a : 𝒪[K]ˣ) (n : ℕ) : Set 𝒪[K] :=
  (fun x : 𝒪[K] => x - (a : 𝒪[K])) ⁻¹'
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])

omit [MeasurableSpace K] [BorelSpace K] in
/--
@isnad1 id=le.1h3v.s8.6d1f7128ec88 from=translated src=- shape=b1d6e52b vocab=93c96d36
-/
theorem unitCenteredTail_subset_units (a : 𝒪[K]ˣ) {n : ℕ} (hn : 0 < n) :
    unitCenteredTail K a n ⊆ integralUnits K := by
  intro x hx hx'
  have hm : x - (a : 𝒪[K]) ∈ 𝓂[K] :=
    (show 𝓂[K] ^ n ≤ 𝓂[K] from by simpa using
      (Ideal.pow_le_pow_right (I := 𝓂[K]) hn)) hx
  have ha : (a : 𝒪[K]) ∈ integralUnits K :=
    (mem_integralUnits_iff K _).mpr a.isUnit
  apply ha
  simpa using (𝓂[K]).sub_mem hx' hm

/--
@isnad1 id=eq.0h3v.s9.3bf78e29a1cd from=translated src=- shape=6bc35e2f vocab=0cbe59fa
-/
theorem integersHaar_unitCenteredTail (a : 𝒪[K]ˣ) (n : ℕ) :
    integersHaar K (unitCenteredTail K a n) = (residueCardinality K : ℝ≥0∞)⁻¹ ^ n := by
  simp only [unitCenteredTail, sub_eq_add_neg, measure_preimage_add_right]
  exact integersHaar_maximalIdeal_pow K n

/--
@isnad1 id=eq.0h3v.s8.aa50d6475f9f from=translated src=- shape=bba94ca2 vocab=7a537076
-/
theorem unitConditionalMass_unitCenteredTail (a : 𝒪[K]ˣ) (n : ℕ) :
    unitConditionalMass K (unitCenteredTail K a (n + 1)) =
      (residueCardinality K : ℝ)⁻¹ ^ n / (residueCardinality K - 1) := by
  have hq : (1 : ℝ) < residueCardinality K := by
    exact_mod_cast residueCardinality_one_lt K
  rw [unitConditionalMass_of_subset _ _
    (unitCenteredTail_subset_units K a (Nat.succ_pos n))]
  have hv : (integersHaar K).real (unitCenteredTail K a (n + 1)) =
      (residueCardinality K : ℝ)⁻¹ ^ (n + 1) := by
    simp [measureReal_def, integersHaar_unitCenteredTail]
  rw [hv, pow_succ]
  field_simp

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K] in
/-- For an integral unit denominator, the ratio's cancellation depth is the depth
of the difference. This is the key elementary step for a fixed unit numerator.
@isnad1 id=eq.1h3v.s9.762f4c92c412 from=translated src=- shape=05bdaa2d vocab=e7eb0205
-/
theorem valuation_ratio_sub_one (a x : 𝒪[K]) (hx : IsUnit x) :
    valuation K ((a : K) / (x : K) - 1) = valuation K ((x : K) - (a : K)) := by
  have hvx : valuation K (x : K) = 1 := by
    change valuation K ((algebraMap 𝒪[K] K) x) = 1
    exact (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp hx
  have hx0 : (x : K) ≠ 0 := by
    intro h
    simp [h] at hvx
  have heq : (a : K) / (x : K) - 1 = ((a : K) - (x : K)) / (x : K) := by
    field_simp
  rw [heq, map_div₀, hvx, div_one, (valuation K).map_sub_swap]

/-- Actual ratio-cancellation tails for a unit numerator and Haar-uniform integral
units. The valuation inequality includes the infinite-depth point, with no
incorrect finite value assigned to it.
@isnad1 id=eq.1h4v.s11.4e86fc7b6150 from=translated src=- shape=3af77913 vocab=bf8e640a
-/
theorem unitConditionalMass_ratio_tail (π : 𝒪[K]) (hπ : 𝓂[K] = Ideal.span {π})
    (a : 𝒪[K]ˣ) (n : ℕ) :
    unitConditionalMass K {x : 𝒪[K] | x ∈ integralUnits K ∧
      valuation K (((a : 𝒪[K]) : K) / (x : K) - 1) ≤
        valuation K (π : K) ^ (n + 1)} =
      (residueCardinality K : ℝ)⁻¹ ^ n / (residueCardinality K - 1) := by
  have heq : {x : 𝒪[K] | x ∈ integralUnits K ∧
      valuation K (((a : 𝒪[K]) : K) / (x : K) - 1) ≤
        valuation K (π : K) ^ (n + 1)} = unitCenteredTail K a (n + 1) := by
    ext x
    constructor
    · rintro ⟨hx, hv⟩
      rw [valuation_ratio_sub_one K _ _ ((mem_integralUnits_iff K _).mp hx)] at hv
      exact (mem_maximalIdeal_pow_iff_valuation_le K π hπ _ (x - a)).mpr hv
    · intro hx
      have hu := unitCenteredTail_subset_units K a (Nat.succ_pos n) hx
      refine ⟨hu, ?_⟩
      rw [valuation_ratio_sub_one K _ _ ((mem_integralUnits_iff K _).mp hu)]
      exact (mem_maximalIdeal_pow_iff_valuation_le K π hπ _ (x - a)).mp hx
  rw [heq, unitConditionalMass_unitCenteredTail]

/-- Ambient additive Haar has no atoms, by the separately proved local-field
non-isolation theorem; atomlessness is not an extra hypothesis.
@isnad1 id=nullsing.0h1v.s5.a02970767a6b from=translated src=- shape=de699033 vocab=42f4d5dd
-/
instance additiveHaar_nullSingletonClass : NullSingletonClass (additiveHaar K) :=
  localField_haar_nullSingletonClass K (additiveHaar K)

/-- In particular every point of the valuation ring has zero pulled-back Haar mass.
@isnad1 id=eq.0h2v.s9.41d535af5e87 from=translated src=- shape=d1f887a5 vocab=fd51ece4
-/
theorem integersHaar_singleton (x : 𝒪[K]) : integersHaar K {x} = 0 := by
  rw [integersHaar_apply]
  simp

/-- The infinite-cancellation point has no extra probability mass.
@isnad1 id=eq.0h2v.s8.8fc05f57081c from=translated src=- shape=42411126 vocab=82d147c1
-/
theorem unitConditionalMass_singleton (x : 𝒪[K]) : unitConditionalMass K {x} = 0 := by
  have h : integersHaar K ({x} ∩ integralUnits K) = 0 :=
    measure_mono_null Set.inter_subset_left (integersHaar_singleton K x)
  simp [unitConditionalMass, measureReal_def, h]

end FourierJacobi.Measure
