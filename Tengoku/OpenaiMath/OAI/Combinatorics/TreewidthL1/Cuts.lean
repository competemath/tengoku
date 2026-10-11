import Tengoku.OpenaiMath.OAI.Combinatorics.TreewidthL1.WeightedPaths

namespace OAI

universe treewidthLevel1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal

variable {V : Type*} [Fintype V]

noncomputable def thresholdLabels (F : V → ℝ) (t : ℝ) : V → Bool :=
  fun v => decide (t < F v)

noncomputable def sweep (M : ℝ) (F : V → ℝ) : Measure (V → Bool) :=
  (volume.restrict (Icc (-M) M)).map (thresholdLabels F)

def complementCut (ω : V → Bool) : V → Bool := fun v => !(ω v)

noncomputable def symmetrizeCut (μ : Measure (V → Bool)) : Measure (V → Bool) :=
  (1 / 2 : ℝ≥0∞) • (μ + μ.map complementCut)

def cutEvent (P : Finset V) (z : V) (b : P → Bool) (q : Bool) : Set (V → Bool) :=
  {ω | (∀ s : P, ω s = b s) ∧ ω z = q}

noncomputable def cutUncertainty (μ : Measure (V → Bool)) (P : Finset V) (z : V) : ℝ := by
  classical
  exact ∑ b : P → Bool, min (μ.real (cutEvent P z b false)) (μ.real (cutEvent P z b true))

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

lemma measurable_thresholdLabels
    {V : Type treewidthLevel1} [Fintype V]
    (F : V → ℝ) : Measurable (thresholdLabels F) := by
  apply Measurable.of_eval
  intro v
  have h : Measurable (fun t : ℝ => if t < F v then true else false) :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const
  convert h using 1
  ext t
  simp [thresholdLabels]

instance sweep_finite (M : ℝ) (F : V → ℝ) : IsFiniteMeasure (sweep M F) := by
  unfold sweep
  infer_instance

lemma cutEvent_measurable (P : Finset V) (z : V) (b : P → Bool) (q : Bool) :
    MeasurableSet (cutEvent P z b q) := (Set.toFinite _).measurableSet

lemma measurable_complementCut : Measurable (complementCut (V := V)) :=
  measurable_of_finite _

instance symmetrizeCut_finite (μ : Measure (V → Bool)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (symmetrizeCut μ) := by
  constructor
  change (1 / 2 : ℝ≥0∞) * (μ + μ.map complementCut) Set.univ < ⊤
  finiteness

lemma complementCut_involutive
    {V : Type treewidthLevel1} [Fintype V] : Function.Involutive (complementCut (V := V)) := by
  intro ω
  funext v
  simp [complementCut]

def complementEquiv (V : Type*) : (V → Bool) ≃ (V → Bool) where
  toFun := complementCut
  invFun := complementCut
  left_inv := by intro ω; funext v; simp [complementCut]
  right_inv := by intro ω; funext v; simp [complementCut]

lemma complement_preimage_event
    {V : Type treewidthLevel1} [Fintype V]
    (P : Finset V) (z : V) (b : P → Bool) (q : Bool) :
    complementCut ⁻¹' cutEvent P z b q =
      cutEvent P z (complementCut b) (!q) := by
  ext ω
  simp only [Set.mem_preimage, cutEvent, Set.mem_ofPred_eq, complementCut]
  constructor
  · rintro ⟨h, hz⟩
    constructor
    · intro s
      have := congrArg Bool.not (h s)
      simpa using this
    · have := congrArg Bool.not hz
      simpa using this
  · rintro ⟨h, hz⟩
    constructor
    · intro s
      have := congrArg Bool.not (h s)
      simpa using this
    · have := congrArg Bool.not hz
      simpa using this

lemma uncertainty_nonneg
    {V : Type treewidthLevel1} [Fintype V]
    (μ : Measure (V → Bool)) (P : Finset V) (z : V) :
    0 ≤ cutUncertainty μ P z :=
  Finset.sum_nonneg (fun _ _ => le_min measureReal_nonneg measureReal_nonneg)

lemma uncertainty_add
    {V : Type treewidthLevel1} [Fintype V]
    (μ ν : Measure (V → Bool)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (P : Finset V) (z : V) :
    cutUncertainty μ P z + cutUncertainty ν P z ≤ cutUncertainty (μ + ν) P z := by
  classical
  simp only [cutUncertainty, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _
  rw [measureReal_add_apply (by finiteness) (by finiteness),
    measureReal_add_apply (by finiteness) (by finiteness)]
  exact min_add_min_le_min_add_add

lemma uncertainty_complement (μ : Measure (V → Bool)) (P : Finset V) (z : V) :
    cutUncertainty (μ.map complementCut) P z = cutUncertainty μ P z := by
  classical
  simp only [cutUncertainty, map_measureReal_apply measurable_complementCut
    (cutEvent_measurable _ _ _ _), complement_preimage_event, Bool.not_false,
    Bool.not_true]
  simp_rw [min_comm]
  simpa only [complementEquiv, Equiv.coe_fn_mk] using (complementEquiv P).sum_comp
    (fun b : P → Bool => min (μ.real (cutEvent P z b false))
      (μ.real (cutEvent P z b true)))

lemma uncertainty_symmetrize (μ : Measure (V → Bool)) [IsFiniteMeasure μ]
    (P : Finset V) (z : V) :
    cutUncertainty μ P z ≤ cutUncertainty (symmetrizeCut μ) P z := by
  classical
  have h := uncertainty_add μ (μ.map complementCut) P z
  rw [uncertainty_complement] at h
  have heq : cutUncertainty (symmetrizeCut μ) P z =
      cutUncertainty (μ + μ.map complementCut) P z / 2 := by
    simp only [cutUncertainty, symmetrizeCut, measureReal_ennreal_smul_apply]
    norm_num
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    simp only [one_div_mul_eq_div, min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
  rw [heq]
  linarith

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

lemma thresholdLabels_constant_gap
    {V : Type treewidthLevel1} [Fintype V]
    (F : V → ℝ) (z s : V) (t a : ℝ)
    (_ : 0 < t) (hs : t ≤ |F z - F s|)
    (ha : F z - t < a ∧ a < F z + t) :
    thresholdLabels F a s = thresholdLabels F (F z) s := by
  by_cases h : F z < F s
  · rw [abs_of_neg (sub_neg.mpr h)] at hs
    have h' : a < F s := by linarith
    simp [thresholdLabels, h, h']
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt h))] at hs
    have h' : ¬a < F s := by linarith
    simp [thresholdLabels, h, h']

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

lemma symmetrizeCut_add (μ ν : Measure (V → Bool)) :
    symmetrizeCut (μ + ν) = symmetrizeCut μ + symmetrizeCut ν := by
  simp only [symmetrizeCut, Measure.map_add _ _ measurable_complementCut, smul_add]
  ac_rfl

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

noncomputable def cutTrace (μ : Measure (V → Bool)) (P : Finset V) : Measure (P → Bool) :=
  μ.map (fun ω s => ω s)

noncomputable def cutSeparation (μ : Measure (V → Bool)) (u v : V) : ℝ :=
  μ.real {ω | ω u ≠ ω v}

def CommonWeakOrder (P : Finset V) (F H : V → ℝ) : Prop :=
  ∃ e : Fin P.card ≃ P,
    Monotone (fun i => F (e i)) ∧ Monotone (fun i => H (e i))

def partialCutEvent (P Q : Finset V) : Set (V → Bool) :=
  {ω | (∀ p ∈ P, ω p = true) ∧ ∀ q ∈ Q, ω q = false}

/-- On a finite Boolean cube, all-true conjunctions determine a finite measure.
The proof retains the total mass (the conjunction over the empty set). -/
lemma cutMeasure_ext_all_true (μ ν : Measure (V → Bool)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (heq : ∀ P : Finset V, μ.real {ω | ∀ p ∈ P, ω p = true} =
      ν.real {ω | ∀ p ∈ P, ω p = true}) : μ = ν := by
  classical
  have hpartial (Q : Finset V) : ∀ P : Finset V,
      μ.real (partialCutEvent P Q) = ν.real (partialCutEvent P Q) := by
    induction Q using Finset.induction_on with
    | empty =>
      intro P
      simpa [partialCutEvent] using heq P
    | @insert a Q ha ih =>
      intro P
      have hpart : partialCutEvent P Q =
          partialCutEvent (insert a P) Q ∪ partialCutEvent P (insert a Q) := by
        ext ω
        simp only [partialCutEvent, Set.mem_ofPred_eq, Finset.mem_insert,
          forall_eq_or_imp, Set.mem_union]
        cases h : ω a <;> simp
      have hdis : Disjoint (partialCutEvent (insert a P) Q)
          (partialCutEvent P (insert a Q)) := by
        apply Set.disjoint_left.mpr
        intro ω h₁ h₂
        have ht := h₁.1 a (Finset.mem_insert_self a P)
        have hf := h₂.2 a (Finset.mem_insert_self a Q)
        simp_all
      have hμ := measureReal_union hdis
        (Set.toFinite (partialCutEvent P (insert a Q))).measurableSet
        (μ := μ)
      have hν := measureReal_union hdis
        (Set.toFinite (partialCutEvent P (insert a Q))).measurableSet
        (μ := ν)
      rw [← hpart] at hμ hν
      linarith [ih P, ih (insert a P)]
  apply Measure.ext_of_singleton
  intro ω
  have hs : ({ω} : Set (V → Bool)) = partialCutEvent
      (Finset.univ.filter fun v => ω v = true)
      (Finset.univ.filter fun v => ω v = false) := by
    ext η
    simp only [Set.mem_singleton_iff, partialCutEvent, Set.mem_ofPred_eq,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl
      exact ⟨fun _ h => h, fun _ h => h⟩
    · rintro ⟨h₁, h₂⟩
      funext v
      cases h : ω v
      · exact h₂ v h
      · exact h₁ v h
  apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
  rw [hs]
  exact hpartial _ _

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

lemma cutTrace_add (μ ν : Measure (V → Bool)) (P : Finset V) :
    cutTrace (μ + ν) P = cutTrace μ P + cutTrace ν P := by
  exact Measure.map_add _ _ (measurable_of_finite _)

lemma sweep_separation_ordered (M : ℝ) (F : V → ℝ) (u v : V)
    (h : F u ≤ F v) (hm : -M ≤ F u ∧ F v ≤ M) :
    cutSeparation (sweep M F) u v = F v - F u := by
  rw [cutSeparation, sweep, map_measureReal_apply (measurable_thresholdLabels F)
    (Set.toFinite _).measurableSet,
    measureReal_restrict_apply ((measurable_thresholdLabels F) (Set.toFinite _).measurableSet)]
  have hset : (thresholdLabels F ⁻¹' {ω | ω u ≠ ω v}) ∩ Icc (-M) M =
      Ico (F u) (F v) := by
    ext t
    constructor
    · rintro ⟨hne, _⟩
      by_cases hu : t < F u
      · have hv : t < F v := hu.trans_le h
        simp [thresholdLabels, hu, hv] at hne
      · have hv : t < F v := by
          by_contra hv
          simp [thresholdLabels, hu, hv] at hne
        exact ⟨le_of_not_gt hu, hv⟩
    · rintro ⟨hu, hv⟩
      refine ⟨?_, ⟨hm.1.trans hu, hv.le.trans hm.2⟩⟩
      simp [thresholdLabels, show ¬t < F u from not_lt.mpr hu, hv]
  rw [hset, Real.volume_real_Ico_of_le h]

theorem sweep_separation (M : ℝ) (F : V → ℝ) (hF : ∀ v, |F v| ≤ M) (u v : V) :
    cutSeparation (sweep M F) u v = |F u - F v| := by
  rcases le_total (F u) (F v) with h | h
  · rw [sweep_separation_ordered M F u v h
      ⟨(abs_le.mp (hF u)).1, (abs_le.mp (hF v)).2⟩,
      abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · have he : cutSeparation (sweep M F) u v = cutSeparation (sweep M F) v u := by
      unfold cutSeparation
      congr 1
      ext ω
      exact ne_comm
    rw [he, sweep_separation_ordered M F v u h
      ⟨(abs_le.mp (hF v)).1, (abs_le.mp (hF u)).2⟩,
      abs_of_nonneg (sub_nonneg.mpr h)]

end BoundedTreewidthL1

end OAI
