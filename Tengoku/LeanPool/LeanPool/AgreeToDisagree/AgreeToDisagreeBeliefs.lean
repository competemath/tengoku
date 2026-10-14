/-
Copyright (c) 2026 Axiom Math contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AgreeToDisagree contributors
-/
module

public import Tengoku.LeanPool.LeanPool.AgreeToDisagree.AgreeToDisagree
public import Tengoku

/-!
# Approximate agreement under common belief

This file proves the `p`-belief version of Aumann's agreement theorem.
-/

@[expose] public section

namespace AgreeToDisagree

open Set MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The set of states where the posterior probability of `E` is at least `p`. -/
abbrev Partition.belief (P : Partition Ω) (μ : Measure Ω)
    (p : ENNReal) (E : Set Ω) : Set Ω :=
  {ω | p ≤ P.probabilityAt μ E ω}

/-- A set is `p`-evident for a partition if membership implies `p`-belief in itself. -/
abbrev Partition.IsEvidentBelief (P : Partition Ω) (μ : Measure Ω)
    (p : ENNReal) (E : Set Ω) : Prop :=
  E ⊆ P.belief μ p E

/-- Common `p`-belief at a state, represented by an evident event containing that state. -/
abbrev IsCommonBeliefAt {ι : Type*} (P : ι → Partition Ω) (μ : Measure Ω)
    (p : ENNReal) (C : Set Ω) (ω : Ω) : Prop :=
  ∃ E : Set Ω, ω ∈ E ∧ (∀ i, (P i).IsEvidentBelief μ p E) ∧ ∀ i, E ⊆ (P i).belief μ p C

/-- Monotonicity of belief: `X ⊆ Y` implies `P.belief μ p X ⊆ P.belief μ p Y`.
@isnad1 id=le.1h6v.s5.276440c40879 from=translated src=- shape=6086879c vocab=b625c41f
-/
lemma Partition.belief_mono (P : Partition Ω) (μ : Measure Ω)
    (p : ENNReal) {X Y : Set Ω} (hXY : X ⊆ Y) :
    P.belief μ p X ⊆ P.belief μ p Y := fun _ hω ↦
  hω.trans (ENNReal.div_le_div_right (measure_mono (inter_subset_inter_left _ hXY)) _)

/-- The belief set equals a union over partition atoms with sufficient conditional probability.
@isnad1 id=eq.0h5v.s7.d3b3b64f41ad from=translated src=- shape=a6807617 vocab=bd94f377
-/
lemma Partition.belief_eq_biUnion {P : Partition Ω}
    (μ : Measure Ω)
    (p : ENNReal) (X : Set Ω) :
    P.belief μ p X = ⋃ s ∈ {s : Set Ω | s ∈ P ∧ p ≤ μ (X ∩ s) / μ s}, s := by
  ext ω
  simp only [Partition.belief, Partition.probabilityAt, Set.mem_ofPred_eq,
    Set.mem_iUnion, exists_prop]
  refine ⟨fun hω ↦ ⟨P.class ω, ⟨P.class_mem ω, hω⟩, P.mem_class ω⟩, ?_⟩
  rintro ⟨s, ⟨hs, hps⟩, hωs⟩
  rw [Partition.class_eq_of_mem hs hωs]
  exact hps

/-- For a measurable countable partition `P`, the belief set `P.belief μ p X` is measurable.
@isnad1 id=measurab.2h5v.s5.78d0ddf0dde8 from=translated src=- shape=9a8c804f vocab=3a44e810
-/
lemma Partition.measurableSet_belief {P : Partition Ω} (hP : P.Measurable)
    (hPc : P.val.Countable) (μ : Measure Ω)
    (p : ENNReal) (X : Set Ω) :
    MeasurableSet (P.belief μ p X) := by
  rw [Partition.belief_eq_biUnion]
  exact MeasurableSet.biUnion (hPc.mono fun _ hs ↦ hs.1) (fun s hs ↦ hP s hs.1)

omit [IsProbabilityMeasure μ] in
/-- The downward step of belief idempotence.
@isnad1 id=le.1h5v.s5.7200af7441a1 from=translated src=- shape=ca9a8fa3 vocab=a63e4775
-/
lemma Partition.belief_belief_subset {P : Partition Ω}
    {p : ENNReal} (hp : 0 < p) (X : Set Ω) :
    P.belief μ p (P.belief μ p X) ⊆ P.belief μ p X := by
  intro ω hω
  rw [Partition.belief_eq_biUnion] at hω ⊢
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hω ⊢
  obtain ⟨s, ⟨hsP, hs_prob⟩, hωs⟩ := hω
  refine ⟨s, ⟨hsP, ?_⟩, hωs⟩
  by_contra h_not
  push Not at h_not
  have h_empty : P.belief μ p X ∩ s = ∅ := by
    ext ω'
    refine ⟨fun ⟨hω'bel, hω's⟩ ↦ ?_, fun hω'empty ↦ False.elim hω'empty⟩
    have hbel : p ≤ μ (X ∩ P.class ω') / μ (P.class ω') := hω'bel
    rw [Partition.class_eq_of_mem hsP hω's] at hbel
    exact (not_le.mpr h_not) hbel
  rw [h_empty] at hs_prob
  have h_zero : p ≤ 0 := by
    simpa only [measure_empty, ENNReal.zero_div] using hs_prob
  exact (not_le.mpr hp) h_zero

/-- If `0 < p ≤ a / b`, then `0 < a`.
@isnad1 id=lt.2h3v.s5.8427245eeae7 from=translated src=- shape=492bb2e2 vocab=f01e2841
-/
lemma ennreal_num_pos_of_ratio_ge {p a b : ENNReal} (hp : 0 < p)
    (h : p ≤ a / b) : 0 < a := by
  by_contra h₁
  push Not at h₁
  rw [le_antisymm h₁ zero_le, ENNReal.zero_div] at h
  exact absurd (h.trans_lt hp) (lt_irrefl _)

omit [IsProbabilityMeasure μ] in
/-- If `A` is `p`-evident with `0 < p`, then `μ A > 0`.
@isnad1 id=lt.3h6v.s6.1e83efb3b629 from=translated src=- shape=a9352a76 vocab=04936e99
-/
lemma measure_pos_of_evident_belief {P : Partition Ω}
    {p : ENNReal} (hp : 0 < p) {A : Set Ω} {ω : Ω}
    (hω : ω ∈ A) (hev : A ⊆ P.belief μ p A) :
    0 < μ A :=
  (ennreal_num_pos_of_ratio_ge hp (hev hω)).trans_le (measure_mono Set.inter_subset_left)

omit [IsProbabilityMeasure μ] in
/-- A set of positive measure is nonempty.
@isnad1 id=nonempty.1h3v.s5.7aa67d39b903 from=translated src=- shape=52432392 vocab=4876a42c
-/
lemma nonempty_of_measure_pos {s : Set Ω} (h : 0 < μ s) : s.Nonempty :=
  Set.nonempty_iff_ne_empty.mpr fun he ↦ by simp [he] at h

omit [IsProbabilityMeasure μ] in
/-- If `A ⊆ P.belief μ p {ω | P.probabilityAt μ E ω = r}`, then probability equals r on A.
@isnad1 id=eq.3h8v.s6.1a46ae86bcaf from=translated src=- shape=ae547c73 vocab=089fe8fc
-/
lemma probabilityAt_eq_of_belief_const
    {P : Partition Ω} {p : ENNReal} (hp : 0 < p) {E A : Set Ω} {r : ENNReal}
    (hA : A ⊆ P.belief μ p {ω | P.probabilityAt μ E ω = r}) :
    ∀ ω ∈ A, P.probabilityAt μ E ω = r := by
  intro ω hω
  have hbel := hA hω
  rw [Partition.belief_eq_biUnion] at hbel
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hbel
  obtain ⟨s, ⟨hsP, hps⟩, hωs⟩ := hbel
  obtain ⟨ω₀, hω₀S, hω₀s⟩ := nonempty_of_measure_pos (ennreal_num_pos_of_ratio_ge hp hps)
  change μ (E ∩ P.class ω) / μ (P.class ω) = r
  rw [← Partition.class_eq_class_of_mem
    (Partition.class_eq_of_mem hsP hωs ▸ hω₀s : ω₀ ∈ P.class ω)]
  exact hω₀S

/-! ## Helpers for `core_bound` -/

/--
@isnad1 id=eq.4h8v.s7.712fb5f9ea8c from=translated src=- shape=544c6d8d vocab=6138731d
-/
lemma core_bound.atom_E_eq {P : Partition Ω} (hP' : ∀ s ∈ P, μ s > 0)
    {A E : Set Ω} {r : ENNReal}
    (hAR : ∀ ω ∈ A, P.probabilityAt μ E ω = r)
    {s : Set Ω} (hs : s ∈ P) {ω : Ω} (hω : ω ∈ A ∩ s) :
    μ (E ∩ s) = r * μ s := by
  have h : μ (E ∩ s) / μ s = r := by
    simpa [Partition.probabilityAt, Partition.class_eq_of_mem hs hω.2] using hAR ω hω.1
  rw [← h, ENNReal.div_mul_cancel (hP' s hs).ne' (measure_ne_top μ s)]

/--
@isnad1 id=le.4h7v.s7.5803bfcc82a0 from=translated src=- shape=975cf19d vocab=ee03a52a
-/
lemma core_bound.atom_evidence {P : Partition Ω} (hP' : ∀ s ∈ P, μ s > 0)
    {p : ENNReal} {A : Set Ω} (hAev : A ⊆ P.belief μ p A)
    {s : Set Ω} (hs : s ∈ P) {ω : Ω} (hω : ω ∈ A ∩ s) :
    p * μ s ≤ μ (A ∩ s) := by
  have hbelief : p ≤ μ (A ∩ s) / μ s := by
    rw [← Partition.class_eq_of_mem hs hω.2]; exact hAev hω.1
  have hμs_top : μ s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  exact (ENNReal.le_div_iff_mul_le (Or.inl (hP' s hs).ne') (Or.inl hμs_top)).mp hbelief

private lemma atom_real_arith {x αr r p δ : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hα_le_1 : αr ≤ 1) (hp_le_α : p ≤ αr)
    (hδ0 : 0 ≤ δ) (hδ_ub : δ ≤ 1 - αr) (heq : r = x * αr + δ) :
    |x - r| ≤ 1 - p := by
  have h1 : (0 : ℝ) ≤ 1 - αr := by linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> nlinarith [mul_le_mul_of_nonneg_right hx1 h1, mul_nonneg hx0 h1]

/--
@isnad1 id=le.6h8v.s8.5bff6c9bd973 from=translated src=- shape=5a7779e2 vocab=e2bbcafb
-/
lemma core_bound.atom_real_bound {P : Partition Ω} (hP' : ∀ s ∈ P, μ s > 0)
    {p : ENNReal} {A E : Set Ω} (hA : MeasurableSet A)
    {r : ENNReal} {s : Set Ω} (hs : s ∈ P) (hAsmu : 0 < μ (A ∩ s))
    (hEs : μ (E ∩ s) = r * μ s) (hαs : p * μ s ≤ μ (A ∩ s)) :
    |(μ (E ∩ A ∩ s) / μ (A ∩ s)).toReal - r.toReal| ≤ 1 - p.toReal := by
  have hms_pos : 0 < μ s := hP' s hs
  have hAs_le_s : μ (A ∩ s) ≤ μ s := measure_mono Set.inter_subset_right
  have hAs_ne_top : μ (A ∩ s) ≠ ⊤ := (hAs_le_s.trans_lt (measure_lt_top μ s)).ne
  have hEAs_le_As : μ (E ∩ A ∩ s) ≤ μ (A ∩ s) :=
    measure_mono fun _ hω ↦ ⟨hω.1.2, hω.2⟩
  have hEAs_ne_top : μ (E ∩ A ∩ s) ≠ ⊤ :=
    (hEAs_le_As.trans_lt hAs_ne_top.lt_top).ne
  have hsdA_ne_top : μ (s \ A) ≠ ⊤ :=
    ((measure_mono Set.sdiff_subset).trans_lt (measure_lt_top μ s)).ne
  have hEsdA_le_sdA : μ ((E ∩ s) \ A) ≤ μ (s \ A) :=
    measure_mono fun _ hω ↦ ⟨hω.1.2, hω.2⟩
  have hEsdA_ne_top : μ ((E ∩ s) \ A) ≠ ⊤ :=
    (hEsdA_le_sdA.trans_lt hsdA_ne_top.lt_top).ne
  have hdecE : μ (E ∩ A ∩ s) + μ ((E ∩ s) \ A) = μ (E ∩ s) := by
    rw [show E ∩ A ∩ s = (E ∩ s) ∩ A by ext x; simp [and_assoc, and_comm]]
    exact measure_inter_add_sdiff (E ∩ s) hA
  have hdecS : μ (A ∩ s) + μ (s \ A) = μ s := by
    rw [inter_comm]
    exact measure_inter_add_sdiff s hA
  set ms := (μ s).toReal
  set mAs := (μ (A ∩ s)).toReal
  set mEAs := (μ (E ∩ A ∩ s)).toReal
  set msdA := (μ (s \ A)).toReal
  set mEsdA := (μ ((E ∩ s) \ A)).toReal
  have hms_pos_R : 0 < ms := ENNReal.toReal_pos hms_pos.ne' (measure_lt_top μ s).ne
  have hmAs_pos_R : 0 < mAs := ENNReal.toReal_pos hAsmu.ne' hAs_ne_top
  have hmAs_le_ms : mAs ≤ ms := ENNReal.toReal_mono (measure_lt_top μ s).ne hAs_le_s
  have hmEAs_le_mAs : mEAs ≤ mAs := ENNReal.toReal_mono hAs_ne_top hEAs_le_As
  have hdecS_R : mAs + msdA = ms := by
    rw [← ENNReal.toReal_add hAs_ne_top hsdA_ne_top, hdecS]
  have hdecE_R : mEAs + mEsdA = (μ (E ∩ s)).toReal := by
    rw [← ENNReal.toReal_add hEAs_ne_top hEsdA_ne_top, hdecE]
  have hEs_R : (μ (E ∩ s)).toReal = r.toReal * ms := by rw [hEs, ENNReal.toReal_mul]
  have hp_ev_R : p.toReal * ms ≤ mAs := by
    have := ENNReal.toReal_mono hAs_ne_top hαs
    rwa [ENNReal.toReal_mul] at this
  set αr := mAs / ms with hαr_def
  set xr := mEAs / mAs with hxr_def
  set δ := mEsdA / ms with hδ_def
  have hδ_ub : δ ≤ 1 - αr := by
    have h2 : δ ≤ msdA / ms :=
      div_le_div_of_nonneg_right (ENNReal.toReal_mono hsdA_ne_top hEsdA_le_sdA) hms_pos_R.le
    have h3 : msdA / ms = 1 - αr := by
      rw [show msdA = ms - mAs by linarith, hαr_def]; field_simp
    linarith
  have hp_le_α : p.toReal ≤ αr := by rw [hαr_def, le_div_iff₀ hms_pos_R]; linarith
  have heq : r.toReal = xr * αr + δ := by
    have key : r.toReal * ms = mEAs + mEsdA := by rw [← hEs_R, ← hdecE_R]
    have : r.toReal = (mEAs + mEsdA) / ms := by field_simp at key ⊢; linarith
    rw [this, hxr_def, hαr_def, hδ_def]; field_simp
  rw [show (μ (E ∩ A ∩ s) / μ (A ∩ s)).toReal = xr from ENNReal.toReal_div ..]
  exact atom_real_arith (div_nonneg ENNReal.toReal_nonneg hmAs_pos_R.le)
    ((div_le_one hmAs_pos_R).mpr hmEAs_le_mAs)
    ((div_le_one hms_pos_R).mpr hmAs_le_ms) hp_le_α
    (div_nonneg ENNReal.toReal_nonneg hms_pos_R.le) hδ_ub heq

/--
@isnad1 id=eq.3h4v.s7.400615b63299 from=translated src=- shape=030db648 vocab=15580d74
-/
lemma core_bound.tsum_decomp_A {P : Partition Ω} (hP : P.Measurable)
    (hP' : ∀ s ∈ P, μ s > 0) {A : Set Ω} (hA : MeasurableSet A) :
    μ A = ∑' (s : P.val), μ (A ∩ s.1) := by
  have : Countable P.val := (Partition.countable_of_measure_pos hP hP').to_subtype
  have hUnion : A = ⋃ (s : P.val), A ∩ s.1 := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff]
    refine ⟨fun hA ↦ ?_, fun ⟨_, hA, _⟩ ↦ hA⟩
    obtain ⟨s, hs, hωs⟩ : ω ∈ ⋃₀ P.val := by rw [P.2.sUnion_eq_univ]; trivial
    exact ⟨⟨s, hs⟩, hA, hωs⟩
  conv_lhs => rw [hUnion]
  exact measure_iUnion
    (fun s t hst ↦ (P.2.pairwiseDisjoint s.2 t.2 (fun h ↦ hst (Subtype.ext h))).mono
      inter_subset_right inter_subset_right)
    (fun s ↦ hA.inter (hP s.1 s.2))

/--
@isnad1 id=le.2h4v.s6.55b7776e6c5d from=translated src=- shape=31209b52 vocab=d0265399
-/
lemma core_bound.abs_sub_div_le_of_mul {T q r b : ℝ} (hT : 0 < T)
    (h : |r * T - q| ≤ T * b) : |r - q / T| ≤ b := by
  rw [show r - q / T = (r * T - q) / T by field_simp, abs_div, abs_of_pos hT, div_le_iff₀ hT]
  linarith

/--
@isnad1 id=le.1h8v.s8.75609a10b9cf from=translated src=- shape=2aa742e9 vocab=9f1c9864
-/
lemma core_bound.weighted_atom_bound
    {P : Partition Ω} {A E : Set Ω} {p r : ENNReal}
    (hAtom : ∀ (s : P.val), 0 < μ (A ∩ s.1) →
        |(μ (E ∩ A ∩ s.1) / μ (A ∩ s.1)).toReal - r.toReal| ≤ 1 - p.toReal)
    (s : P.val) :
    |(μ (A ∩ s.1)).toReal * r.toReal - (μ (E ∩ A ∩ s.1)).toReal|
      ≤ (μ (A ∩ s.1)).toReal * (1 - p.toReal) := by
  by_cases hpos : 0 < μ (A ∩ s.1)
  · have ha : 0 < (μ (A ∩ s.1)).toReal :=
      ENNReal.toReal_pos hpos.ne' (measure_ne_top μ _)
    have h := hAtom s hpos
    rw [ENNReal.toReal_div] at h
    rw [show (μ (A ∩ s.1)).toReal * r.toReal - (μ (E ∩ A ∩ s.1)).toReal =
      (μ (A ∩ s.1)).toReal * (r.toReal - (μ (E ∩ A ∩ s.1)).toReal / (μ (A ∩ s.1)).toReal)
      by field_simp, abs_mul, abs_of_pos ha, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left h ha.le
  · push Not at hpos
    have hμA_zero : μ (A ∩ s.1) = 0 := le_antisymm hpos zero_le
    have hμEA_zero : μ (E ∩ A ∩ s.1) = 0 :=
      le_antisymm (hμA_zero ▸ measure_mono fun _ ⟨⟨_, h⟩, h'⟩ ↦ ⟨h, h'⟩) zero_le
    simp [hμA_zero, hμEA_zero]

/--
@isnad1 id=le.3h7v.s9.7b9739af3f97 from=translated src=- shape=d9b78cb2 vocab=f2cf0561
-/
lemma core_bound.weighted_sum_bound
    {P : Partition Ω}
    {p : ENNReal} {A E : Set Ω} {r : ENNReal}
    (hμA : μ A = ∑' (s : P.val), μ (A ∩ s.1))
    (hμEA : μ (E ∩ A) = ∑' (s : P.val), μ (E ∩ A ∩ s.1))
    (hAtom : ∀ (s : P.val), 0 < μ (A ∩ s.1) →
        |(μ (E ∩ A ∩ s.1) / μ (A ∩ s.1)).toReal - r.toReal| ≤ 1 - p.toReal) :
    |r.toReal * (μ A).toReal - (μ (E ∩ A)).toReal|
      ≤ (μ A).toReal * (1 - p.toReal) := by
  have hSumA : Summable (fun s : P.val ↦ (μ (A ∩ s.1)).toReal) :=
    ENNReal.summable_toReal (hμA ▸ measure_ne_top μ A)
  have hSumEA : Summable (fun s : P.val ↦ (μ (E ∩ A ∩ s.1)).toReal) :=
    ENNReal.summable_toReal (hμEA ▸ measure_ne_top μ _)
  have hAtsum : (μ A).toReal = ∑' s : P.val, (μ (A ∩ s.1)).toReal := by
    rw [hμA, ENNReal.tsum_toReal_eq (fun _ ↦ measure_ne_top μ _)]
  have hEAtsum : (μ (E ∩ A)).toReal = ∑' s : P.val, (μ (E ∩ A ∩ s.1)).toReal := by
    rw [hμEA, ENNReal.tsum_toReal_eq (fun _ ↦ measure_ne_top μ _)]
  rw [hAtsum, hEAtsum]
  have hSumRA := hSumA.mul_left r.toReal
  rw [← tsum_mul_left, ← Summable.tsum_sub hSumRA hSumEA]
  have hterm : ∀ s : P.val,
      ‖r.toReal * (μ (A ∩ s.1)).toReal - (μ (E ∩ A ∩ s.1)).toReal‖
        ≤ (μ (A ∩ s.1)).toReal * (1 - p.toReal) := fun s ↦ by
    simpa [Real.norm_eq_abs, mul_comm] using core_bound.weighted_atom_bound (μ := μ) hAtom s
  refine (tsum_of_norm_bounded (hSumA.mul_right _).hasSum hterm).trans ?_
  rw [tsum_mul_right, ← hAtsum]

/-- Core bound (Step 4 of the informal proof).
@isnad1 id=le.7h7v.s7.46e5fc332e0f from=translated src=- shape=293c4492 vocab=82add17d
-/
lemma core_bound {P : Partition Ω} (hP : P.Measurable) (hP' : ∀ s ∈ P, μ s > 0)
    {p : ENNReal} {A E : Set Ω}
    (hA : MeasurableSet A) (hAmu : 0 < μ A) (hAev : A ⊆ P.belief μ p A)
    (hE : MeasurableSet E) {r : ENNReal}
    (hAR : ∀ ω ∈ A, P.probabilityAt μ E ω = r) :
    |r.toReal - (μ (E ∩ A) / μ A).toReal| ≤ 1 - p.toReal := by
  have hμA : μ A = ∑' (s : P.val), μ (A ∩ s.1) := core_bound.tsum_decomp_A hP hP' hA
  have hμEA : μ (E ∩ A) = ∑' (s : P.val), μ (E ∩ A ∩ s.1) :=
    core_bound.tsum_decomp_A hP hP' (hE.inter hA)
  have hAtom : ∀ (s : P.val), 0 < μ (A ∩ s.1) →
      |(μ (E ∩ A ∩ s.1) / μ (A ∩ s.1)).toReal - r.toReal| ≤ 1 - p.toReal := fun s hAs ↦ by
    obtain ⟨ω, hω⟩ : (A ∩ s.1).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr (fun h ↦ by simp [h] at hAs)
    exact core_bound.atom_real_bound hP' hA s.2 hAs
      (core_bound.atom_E_eq hP' hAR s.2 hω) (core_bound.atom_evidence hP' hAev s.2 hω)
  rw [ENNReal.toReal_div]
  exact core_bound.abs_sub_div_le_of_mul
    (ENNReal.toReal_pos hAmu.ne' (measure_lt_top μ A).ne)
    (core_bound.weighted_sum_bound hμA hμEA hAtom)

/--
@isnad1 id=le.5h10v.s7.fd27829348f7 from=translated src=- shape=da5dedfb vocab=a60ce3d7
-/
lemma agreeToDisagree_beliefs {ι : Type*} {P : ι → Partition Ω}
    (hP : ∀ i, (P i).Measurable) (hP' : ∀ i, ∀ s ∈ P i, μ s > 0)
    {E : Set Ω} (hE : MeasurableSet E) (ω : Ω) {p : ENNReal} (hp : 0 < p) {r : ι → ENNReal}
    (h : IsCommonBeliefAt P μ p {ω | ∀ i, (P i).probabilityAt μ E ω = r i} ω) :
    ∀ i j, |(r i).toReal - (r j).toReal| ≤ 2 * (1 - p.toReal) := by
  intro i j
  obtain ⟨A₀, hωA₀, hev, hbel⟩ := h
  -- A is the measurable witness: intersection of belief sets for players i, j
  set A : Set Ω := (P i).belief μ p A₀ ∩ (P j).belief μ p A₀
  have hAmeas : MeasurableSet A :=
    (Partition.measurableSet_belief (hP i)
        (Partition.countable_of_measure_pos (hP i) (hP' i)) μ p A₀).inter
      (Partition.measurableSet_belief (hP j)
        (Partition.countable_of_measure_pos (hP j) (hP' j)) μ p A₀)
  have hA₀A : A₀ ⊆ A := fun _ hω' ↦ ⟨hev i hω', hev j hω'⟩
  have hevi : A ⊆ (P i).belief μ p A := fun _ hω' ↦ (P i).belief_mono μ p hA₀A hω'.1
  have hevj : A ⊆ (P j).belief μ p A := fun _ hω' ↦ (P j).belief_mono μ p hA₀A hω'.2
  set C : Set Ω := {ω | ∀ k, (P k).probabilityAt μ E ω = r k}
  have hbCi : A ⊆ (P i).belief μ p C := fun _ hω' ↦
    Partition.belief_belief_subset hp _ ((P i).belief_mono μ p (hbel i) hω'.1)
  have hbCj : A ⊆ (P j).belief μ p C := fun _ hω' ↦
    Partition.belief_belief_subset hp _ ((P j).belief_mono μ p (hbel j) hω'.2)
  have hPRi : ∀ ω' ∈ A, (P i).probabilityAt μ E ω' = r i :=
    probabilityAt_eq_of_belief_const hp
      (hbCi.trans ((P i).belief_mono μ p fun _ hω' ↦ hω' i))
  have hPRj : ∀ ω' ∈ A, (P j).probabilityAt μ E ω' = r j :=
    probabilityAt_eq_of_belief_const hp
      (hbCj.trans ((P j).belief_mono μ p fun _ hω' ↦ hω' j))
  have hAmu : 0 < μ A := measure_pos_of_evident_belief hp (hA₀A hωA₀) hevi
  have boundi := core_bound (hP i) (hP' i) hAmeas hAmu hevi hE hPRi
  have boundj := core_bound (hP j) (hP' j) hAmeas hAmu hevj hE hPRj
  have tri := abs_sub_le (r i).toReal (μ (E ∩ A) / μ A).toReal (r j).toReal
  rw [abs_sub_comm] at boundj
  linarith

end AgreeToDisagree
