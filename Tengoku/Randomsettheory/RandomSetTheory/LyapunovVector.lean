/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.LyapunovRangeCompactness
import Tengoku.Seed.Analysis.Convex.KreinMilman
import Tengoku.Seed.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

noncomputable section

namespace RandomSetTheory

/-! This file is intentionally developed independently from the conditional
bridges in `LyapunovRangeCompactness`. -/

section SetwiseContents

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The index type of measurable subsets.-/
abbrev MeasurableSubset (Omega : Type*) [MeasurableSpace Omega] :=
  {s : Set Omega // MeasurableSet s}

/-- The empty measurable subset, bundled as an index.-/
def emptyMeasurableSubset : MeasurableSubset Omega :=
  ⟨∅, MeasurableSet.empty⟩

/-- Union of two bundled measurable subsets.-/
def unionMeasurableSubset (s t : MeasurableSubset Omega) :
    MeasurableSubset Omega :=
  ⟨(s : Set Omega) ∪ t, s.property.union t.property⟩

/-- Real-valued, finitely additive contents dominated by a fixed finite
measure.  Domination by a countably additive finite measure will force these
contents to be countably additive.-/
def dominatedContents (mu : Measure Omega) :
    Set (MeasurableSubset Omega → ℝ) :=
  {m | m emptyMeasurableSubset = 0 ∧
    (∀ s, 0 ≤ m s ∧ m s ≤ mu.real (s : Set Omega)) ∧
    ∀ (s t : MeasurableSubset Omega),
      Disjoint (s : Set Omega) (t : Set Omega) →
      m (unionMeasurableSubset s t) = m s + m t}

theorem isClosed_dominatedContents (mu : Measure Omega) :
    IsClosed (dominatedContents mu) := by
  rw [dominatedContents]
  apply IsClosed.inter
  · exact isClosed_eq
      (show Continuous (fun m : MeasurableSubset Omega → ℝ ↦
        m emptyMeasurableSubset) from continuous_apply _)
      (show Continuous (fun _ : MeasurableSubset Omega → ℝ ↦ (0 : ℝ)) from
        continuous_const)
  apply IsClosed.inter
  · change IsClosed ({m : MeasurableSubset Omega → ℝ |
      ∀ s, 0 ≤ m s ∧ m s ≤ mu.real (s : Set Omega)} :
        Set (MeasurableSubset Omega → ℝ))
    rw [show {m : MeasurableSubset Omega → ℝ |
        ∀ s, 0 ≤ m s ∧ m s ≤ mu.real (s : Set Omega)} =
        ⋂ s : MeasurableSubset Omega,
          {m | 0 ≤ m s} ∩ {m | m s ≤ mu.real (s : Set Omega)} by
      ext m
      simp]
    exact isClosed_iInter fun (s : MeasurableSubset Omega) ↦
      (isClosed_le
        (show Continuous (fun _ : MeasurableSubset Omega → ℝ ↦ (0 : ℝ)) from
          continuous_const)
        (show Continuous (fun m : MeasurableSubset Omega → ℝ ↦ m s) from
          continuous_apply s)).inter
      (isClosed_le
        (show Continuous (fun m : MeasurableSubset Omega → ℝ ↦ m s) from
          continuous_apply s)
        (show Continuous (fun _ : MeasurableSubset Omega → ℝ ↦
          mu.real (s : Set Omega)) from continuous_const))
  · change IsClosed ({m : MeasurableSubset Omega → ℝ |
      ∀ (s t : MeasurableSubset Omega),
        Disjoint (s : Set Omega) (t : Set Omega) →
          m (unionMeasurableSubset s t) = m s + m t} :
        Set (MeasurableSubset Omega → ℝ))
    rw [show {m : MeasurableSubset Omega → ℝ |
        ∀ (s t : MeasurableSubset Omega),
          Disjoint (s : Set Omega) (t : Set Omega) →
          m (unionMeasurableSubset s t) = m s + m t} =
        ⋂ (s : MeasurableSubset Omega) (t : MeasurableSubset Omega)
          (_h : Disjoint (s : Set Omega) (t : Set Omega)),
          {m | m (unionMeasurableSubset s t) = m s + m t} by
      ext m
      simp]
    exact isClosed_iInter fun (s : MeasurableSubset Omega) ↦
      isClosed_iInter fun (t : MeasurableSubset Omega) ↦
      isClosed_iInter fun _h : Disjoint (s : Set Omega) (t : Set Omega) ↦
        isClosed_eq
          (show Continuous (fun m : MeasurableSubset Omega → ℝ ↦
            m (unionMeasurableSubset s t)) from continuous_apply _)
          (show Continuous (fun m : MeasurableSubset Omega → ℝ ↦ m s + m t) from
            (continuous_apply s).add (continuous_apply t))

theorem isCompact_dominatedContents (mu : Measure Omega) :
    IsCompact (dominatedContents mu) := by
  let box : Set (MeasurableSubset Omega → ℝ) :=
    Set.univ.pi fun s ↦ Set.Icc 0 (mu.real (s : Set Omega))
  have hbox : IsCompact box := isCompact_univ_pi fun _ ↦ isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_dominatedContents mu)
  intro m hm s _hs
  exact hm.2.1 s

theorem convex_dominatedContents (mu : Measure Omega) :
    Convex ℝ (dominatedContents mu) := by
  intro m hm n hn a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm.1, hn.1,
      mul_zero, add_zero]
  · intro s
    constructor
    · exact add_nonneg (smul_nonneg ha (hm.2.1 s).1)
        (smul_nonneg hb (hn.2.1 s).1)
    · change a * m s + b * n s ≤ mu.real (s : Set Omega)
      calc
        a * m s + b * n s ≤
            a * mu.real (s : Set Omega) +
              b * mu.real (s : Set Omega) := by
          gcongr
          exact (hm.2.1 s).2
          exact (hn.2.1 s).2
        _ = mu.real (s : Set Omega) := by rw [← add_mul, hab, one_mul]
  · intro s t hst
    simp only [Pi.add_apply, Pi.smul_apply, hm.2.2 s t hst,
      hn.2.2 s t hst]
    module

/-! ## From dominated contents to measures -/

theorem dominatedContent_finsetRange_union
    {mu : Measure Omega} {m : MeasurableSubset Omega → ℝ}
    (hm : m ∈ dominatedContents mu)
    (f : ℕ → Set Omega) (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise fun i j : ℕ ↦ Disjoint (f i) (f j)) (n : ℕ) :
    m ⟨⋃ i ∈ Finset.range n, f i,
      Finset.measurableSet_biUnion _ (fun i _ ↦ hf i)⟩ =
      ∑ i ∈ Finset.range n, m ⟨f i, hf i⟩ := by
  induction n with
  | zero => simpa [emptyMeasurableSubset] using hm.1
  | succ n ihn =>
      let P : Set Omega := ⋃ i ∈ Finset.range n, f i
      have hP : MeasurableSet P :=
        Finset.measurableSet_biUnion _ (fun i _ ↦ hf i)
      have hPdisj : Disjoint P (f n) := by
        rw [Set.disjoint_left]
        intro x hxP hxn
        rcases Set.mem_iUnion.mp hxP with ⟨i, hxP⟩
        rcases Set.mem_iUnion.mp hxP with ⟨hi, hxi⟩
        have hin : i < n := Finset.mem_range.mp hi
        exact Set.disjoint_left.mp (hd (Nat.ne_of_lt hin)) hxi hxn
      have hUnion :
          (⋃ i ∈ Finset.range (n + 1), f i) = P ∪ f n := by
        ext x
        simp [Finset.range_add_one, P, or_comm]
      rw [show m ⟨⋃ i ∈ Finset.range (n + 1), f i,
          Finset.measurableSet_biUnion _ (fun i _ ↦ hf i)⟩ =
          m (unionMeasurableSubset ⟨P, hP⟩ ⟨f n, hf n⟩) by
        congr 1
        exact Subtype.ext hUnion]
      rw [hm.2.2 ⟨P, hP⟩ ⟨f n, hf n⟩ hPdisj, ihn]
      rw [Finset.sum_range_succ]

/-- A nonnegative finitely additive content dominated by a finite measure is
countably additive.-/
theorem dominatedContent_hasSum_iUnion
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {m : MeasurableSubset Omega → ℝ}
    (hm : m ∈ dominatedContents mu)
    (f : ℕ → Set Omega) (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise fun i j : ℕ ↦ Disjoint (f i) (f j)) :
    HasSum (fun i ↦ m ⟨f i, hf i⟩)
      (m ⟨⋃ i, f i, MeasurableSet.iUnion hf⟩) := by
  let U : Set Omega := ⋃ i, f i
  let P : ℕ → Set Omega := fun n ↦ ⋃ i ∈ Finset.range n, f i
  have hU : MeasurableSet U := MeasurableSet.iUnion hf
  have hP : ∀ n, MeasurableSet (P n) := fun n ↦
    Finset.measurableSet_biUnion _ (fun i _ ↦ hf i)
  have hPU : ∀ n, P n ⊆ U := by
    intro n x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨_hi, hxi⟩
    exact Set.mem_iUnion_of_mem i hxi
  have hmono : Monotone P := by
    intro n k hnk x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hi, hxi⟩
    exact Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem
      (Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hnk)) hxi
  have hiUnionP : (⋃ n, P n) = U := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset hPU
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      exact Set.mem_iUnion_of_mem (i + 1) <|
        Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem
          (Finset.mem_range.mpr (by omega)) hxi
  have hmuP_enn : Tendsto (fun n ↦ mu (P n)) atTop (nhds (mu U)) := by
    have h := tendsto_measure_iUnion_atTop (μ := mu) hmono
    change Tendsto (fun n ↦ mu (P n)) atTop
      (nhds (mu (⋃ n, P n))) at h
    rwa [hiUnionP] at h
  have hmuP : Tendsto (fun n ↦ mu.real (P n)) atTop
      (nhds (mu.real U)) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top mu U)).comp hmuP_enn
  have hmuTail : Tendsto (fun n ↦ mu.real (U \ P n)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ mu.real U) atTop
        (nhds (mu.real U)) := tendsto_const_nhds
    have hsub : Tendsto (fun n ↦ mu.real U - mu.real (P n)) atTop
        (nhds (mu.real U - mu.real U)) := hconst.sub hmuP
    convert hsub using 1
    · funext n
      exact measureReal_sdiff (hPU n) (hP n)
    · simp
  have hmTail : Tendsto
      (fun n ↦ m ⟨U \ P n, hU.diff (hP n)⟩) atTop (nhds 0) := by
    exact squeeze_zero'
      (Filter.Eventually.of_forall fun n ↦
        (hm.2.1 ⟨U \ P n, hU.diff (hP n)⟩).1)
      (Filter.Eventually.of_forall fun n ↦
        (hm.2.1 ⟨U \ P n, hU.diff (hP n)⟩).2) hmuTail
  have hsplit : ∀ n,
      m ⟨U, hU⟩ = m ⟨P n, hP n⟩ +
        m ⟨U \ P n, hU.diff (hP n)⟩ := by
    intro n
    have hdisj : Disjoint (P n) (U \ P n) := Set.disjoint_sdiff_right
    have hunion : P n ∪ (U \ P n) = U := by
      apply Set.Subset.antisymm
      · exact union_subset (hPU n) sdiff_subset
      · intro x hxU
        by_cases hxP : x ∈ P n
        · exact Or.inl hxP
        · exact Or.inr ⟨hxU, hxP⟩
    rw [← hm.2.2 ⟨P n, hP n⟩ ⟨U \ P n, hU.diff (hP n)⟩ hdisj]
    congr 1
    exact Subtype.ext hunion.symm
  have hmP : Tendsto (fun n ↦ m ⟨P n, hP n⟩) atTop
      (nhds (m ⟨U, hU⟩)) := by
    have hEq : (fun n ↦ m ⟨P n, hP n⟩) =
        fun n ↦ m ⟨U, hU⟩ - m ⟨U \ P n, hU.diff (hP n)⟩ := by
      funext n
      linarith [hsplit n]
    rw [hEq]
    simpa using tendsto_const_nhds.sub hmTail
  have hpartial : Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, m ⟨f i, hf i⟩) atTop
      (nhds (m ⟨U, hU⟩)) := by
    apply hmP.congr'
    exact Filter.Eventually.of_forall fun n ↦
      dominatedContent_finsetRange_union hm f hf hd n
  have hsum : HasSum (fun i ↦ m ⟨f i, hf i⟩) (m ⟨U, hU⟩) :=
    (hasSum_iff_tendsto_nat_of_nonneg
      (fun i ↦ (hm.2.1 ⟨f i, hf i⟩).1) _).mpr hpartial
  exact hsum

theorem dominatedContent_iUnion
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {m : MeasurableSubset Omega → ℝ}
    (hm : m ∈ dominatedContents mu)
    (f : ℕ → Set Omega) (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise fun i j : ℕ ↦ Disjoint (f i) (f j)) :
    m ⟨⋃ i, f i, MeasurableSet.iUnion hf⟩ =
      ∑' i, m ⟨f i, hf i⟩ :=
  (dominatedContent_hasSum_iUnion hm f hf hd).tsum_eq.symm

/-- The measure canonically represented by a dominated content.-/
def dominatedContentToMeasure
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (m : MeasurableSubset Omega → ℝ)
    (hm : m ∈ dominatedContents mu) : Measure Omega :=
  Measure.ofMeasurable
    (fun s hs ↦ ENNReal.ofReal (m ⟨s, hs⟩))
    (by
      have hempty : m ⟨∅, MeasurableSet.empty⟩ = 0 := by
        simpa only [emptyMeasurableSubset] using hm.1
      rw [hempty, ENNReal.ofReal_zero])
    (by
      intro f hf hd
      have hs := dominatedContent_hasSum_iUnion hm f hf hd
      have hnonneg : ∀ i, 0 ≤ m ⟨f i, hf i⟩ := fun i ↦
        (hm.2.1 ⟨f i, hf i⟩).1
      rw [← hs.tsum_eq]
      exact ENNReal.ofReal_tsum_of_nonneg hnonneg hs.summable)

@[simp]
theorem dominatedContentToMeasure_apply
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (m : MeasurableSubset Omega → ℝ)
    (hm : m ∈ dominatedContents mu)
    (s : Set Omega) (hs : MeasurableSet s) :
    dominatedContentToMeasure mu m hm s = ENNReal.ofReal (m ⟨s, hs⟩) := by
  exact Measure.ofMeasurable_apply s hs

@[simp]
theorem dominatedContentToMeasure_real_apply
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (m : MeasurableSubset Omega → ℝ)
    (hm : m ∈ dominatedContents mu)
    (s : Set Omega) (hs : MeasurableSet s) :
    (dominatedContentToMeasure mu m hm).real s = m ⟨s, hs⟩ := by
  rw [Measure.real, dominatedContentToMeasure_apply]
  exact ENNReal.toReal_ofReal (hm.2.1 ⟨s, hs⟩).1

theorem dominatedContentToMeasure_le
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (m : MeasurableSubset Omega → ℝ)
    (hm : m ∈ dominatedContents mu) :
    dominatedContentToMeasure mu m hm ≤ mu := by
  rw [Measure.le_iff]
  intro s hs
  rw [dominatedContentToMeasure_apply mu m hm s hs]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top mu s)).mpr
    (hm.2.1 ⟨s, hs⟩).2

/-- Setwise real coordinates of a finite measure.-/
def measureContent (nu : Measure Omega) : MeasurableSubset Omega → ℝ :=
  fun s ↦ nu.real (s : Set Omega)

theorem measureContent_mem_dominatedContents
    (mu nu : Measure Omega) [IsFiniteMeasure mu]
    (hnu : nu ≤ mu) : measureContent nu ∈ dominatedContents mu := by
  letI : IsFiniteMeasure nu := isFiniteMeasure_of_le mu hnu
  refine ⟨?_, ?_, ?_⟩
  · simp [measureContent, emptyMeasurableSubset]
  · intro s
    refine ⟨measureReal_nonneg, ?_⟩
    exact (ENNReal.toReal_le_toReal (measure_ne_top nu (s : Set Omega))
      (measure_ne_top mu (s : Set Omega))).mpr (hnu (s : Set Omega))
  · intro s t hst
    change nu.real ((s : Set Omega) ∪ (t : Set Omega)) =
      nu.real (s : Set Omega) + nu.real (t : Set Omega)
    exact measureReal_union hst t.property

@[simp]
theorem dominatedContentToMeasure_measureContent
    (mu nu : Measure Omega) [IsFiniteMeasure mu]
    (hnu : nu ≤ mu) :
    dominatedContentToMeasure mu (measureContent nu)
      (measureContent_mem_dominatedContents mu nu hnu) = nu := by
  letI : IsFiniteMeasure nu := isFiniteMeasure_of_le mu hnu
  apply Measure.ext
  intro s hs
  rw [dominatedContentToMeasure_apply mu (measureContent nu)
    (measureContent_mem_dominatedContents mu nu hnu) s hs]
  simp [measureContent, Measure.real, ENNReal.ofReal_toReal (measure_ne_top nu s)]

@[simp]
theorem measureContent_dominatedContentToMeasure
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (m : MeasurableSubset Omega → ℝ)
    (hm : m ∈ dominatedContents mu) :
    measureContent (dominatedContentToMeasure mu m hm) = m := by
  funext s
  exact dominatedContentToMeasure_real_apply mu m hm s s.property

/-- Setwise coordinates of a measurable restriction.-/
def restrictionContent (mu : Measure Omega) (A : Set Omega) :
    MeasurableSubset Omega → ℝ :=
  measureContent (mu.restrict A)

theorem restrictionContent_mem_dominatedContents
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (A : Set Omega) : restrictionContent mu A ∈ dominatedContents mu :=
  measureContent_mem_dominatedContents mu (mu.restrict A) Measure.restrict_le_self

end SetwiseContents

/-! ## Continuity of integration for setwise dominated convergence -/

section IntegralContinuity

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Integration against the measure represented by a dominated content.-/
def dominatedContentIntegral (mu : Measure Omega) [IsFiniteMeasure mu]
    (f : Omega → E) (m : dominatedContents mu) : E :=
  ∫ omega, f omega ∂(dominatedContentToMeasure mu m.1 m.2)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem dominatedContentIntegral_simple_eq
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (g : SimpleFunc Omega E) (m : dominatedContents mu) :
    dominatedContentIntegral mu (fun omega ↦ g omega) m =
      ∑ y ∈ g.range,
        m.1 ⟨g ⁻¹' {y}, g.measurableSet_fiber y⟩ • y := by
  let nu := dominatedContentToMeasure mu m.1 m.2
  have hnu : nu ≤ mu := dominatedContentToMeasure_le mu m.1 m.2
  letI : IsFiniteMeasure nu := isFiniteMeasure_of_le mu hnu
  rw [dominatedContentIntegral, g.integral_eq_sum g.integrable_of_isFiniteMeasure]
  apply Finset.sum_congr rfl
  intro y hy
  rw [dominatedContentToMeasure_real_apply mu m.1 m.2
    (g ⁻¹' {y}) (g.measurableSet_fiber y)]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- A simple-function integral is a finite linear combination of coordinate
evaluations, hence continuous for the setwise topology.-/
theorem continuous_dominatedContentIntegral_simple
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (g : SimpleFunc Omega E) :
    Continuous (dominatedContentIntegral mu (fun omega ↦ g omega)) := by
  rw [show dominatedContentIntegral mu (fun omega ↦ g omega) =
      fun m : dominatedContents mu ↦
        ∑ y ∈ g.range, m.1 ⟨g ⁻¹' {y}, g.measurableSet_fiber y⟩ • y by
    funext m
    exact dominatedContentIntegral_simple_eq mu g m]
  apply continuous_finsetSum
  intro y hy
  exact ((continuous_apply
    (⟨g ⁻¹' {y}, g.measurableSet_fiber y⟩ : MeasurableSubset Omega)).comp
    continuous_subtype_val).smul continuous_const

/-- Setwise integration is continuous on the compact space of submeasures
dominated by `mu`, for every `mu`-integrable measurable vector function.
The proof is uniform simple-function approximation in `L¹(mu)`.-/
theorem continuous_dominatedContentIntegral
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {f : Omega → E} (hf : Integrable f mu) (hfm : Measurable f) :
    Continuous (dominatedContentIntegral mu f) := by
  let F : ℕ → SimpleFunc Omega E := fun n ↦
    SimpleFunc.approxOn f hfm (Set.range f ∪ {0}) 0 (by simp) n
  have hFint : ∀ n, Integrable (fun omega ↦ F n omega) mu := fun n ↦
    SimpleFunc.integrable_approxOn_range hfm hf n
  let err : ℕ → ℝ := fun n ↦ ∫ omega, ‖F n omega - f omega‖ ∂mu
  have herr : Tendsto err atTop (nhds 0) := by
    simpa only [err, F] using
      (MeasureTheory.tendsto_integral_norm_approxOn_sub hfm hf)
  have hunif : TendstoUniformly
      (fun n ↦ dominatedContentIntegral mu (fun omega ↦ F n omega))
      (dominatedContentIntegral mu f) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro eps heps
    have hev : ∀ᶠ n in atTop, err n < eps :=
      (tendsto_order.1 herr).2 eps heps
    filter_upwards [hev] with n hn
    intro m
    let nu := dominatedContentToMeasure mu m.1 m.2
    have hnu : nu ≤ mu := dominatedContentToMeasure_le mu m.1 m.2
    have hfnu : Integrable f nu := hf.mono_measure hnu
    have hFnu : Integrable (fun omega ↦ F n omega) nu :=
      (hFint n).mono_measure hnu
    calc
      dist (dominatedContentIntegral mu f m)
          (dominatedContentIntegral mu (fun omega ↦ F n omega) m) =
          ‖(∫ omega, f omega ∂nu) - ∫ omega, F n omega ∂nu‖ := by
        rw [dist_eq_norm]
        rfl
      _ = ‖∫ omega, (f omega - F n omega) ∂nu‖ := by
        rw [integral_sub hfnu hFnu]
      _ ≤ ∫ omega, ‖f omega - F n omega‖ ∂nu :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ omega, ‖f omega - F n omega‖ ∂mu := by
        exact integral_mono_measure hnu
          (Filter.Eventually.of_forall fun omega ↦ norm_nonneg _)
          (hf.sub (hFint n)).norm
      _ = err n := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega ↦ norm_sub_rev _ _
      _ < eps := hn
  exact hunif.continuous
    (Filter.Frequently.of_forall fun n ↦
      continuous_dominatedContentIntegral_simple mu (F n))

end IntegralContinuity

/-! ## Contents represented by bounded real densities -/

section DensityContents

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Setwise coordinates of the measure whose (nonnegative) real density is
`g`.  Using `ENNReal.ofReal` keeps the definition meaningful without a
separate nonnegativity argument.-/
def densityContent (mu : Measure Omega) (g : Omega → ℝ) :
    MeasurableSubset Omega → ℝ :=
  measureContent (mu.withDensity fun omega ↦ ENNReal.ofReal (g omega))

/-- Pointwise truncation to the unit interval.-/
def unitClip (g : Omega → ℝ) (omega : Omega) : ℝ :=
  max 0 (min 1 (g omega))

theorem measurable_unitClip {g : Omega → ℝ} (hg : Measurable g) :
    Measurable (unitClip g) :=
  measurable_const.max (measurable_const.min hg)

omit [MeasurableSpace Omega] in
theorem unitClip_nonneg (g : Omega → ℝ) (omega : Omega) :
    0 ≤ unitClip g omega :=
  le_max_left _ _

omit [MeasurableSpace Omega] in
theorem unitClip_le_one (g : Omega → ℝ) (omega : Omega) :
    unitClip g omega ≤ 1 := by
  exact max_le zero_le_one (min_le_left _ _)

omit [MeasurableSpace Omega] in
theorem unitClip_eq_self {g : Omega → ℝ} {omega : Omega}
    (hg0 : 0 ≤ g omega) (hg1 : g omega ≤ 1) :
    unitClip g omega = g omega := by
  simp [unitClip, min_eq_right hg1, max_eq_right hg0]

/-- The dominated content associated with a real density after harmless
pointwise truncation to `[0,1]`.-/
def clippedDensityContent (mu : Measure Omega) (g : Omega → ℝ) :
    MeasurableSubset Omega → ℝ :=
  densityContent mu (unitClip g)

theorem densityMeasure_le
    (mu : Measure Omega) {g : Omega → ℝ}
    (hg1 : ∀ omega, g omega ≤ 1) :
    mu.withDensity (fun omega ↦ ENNReal.ofReal (g omega)) ≤ mu := by
  calc
    mu.withDensity (fun omega ↦ ENNReal.ofReal (g omega)) ≤
        mu.withDensity (fun _ ↦ (1 : ℝ≥0∞)) :=
      withDensity_mono <| Filter.Eventually.of_forall fun omega ↦
        ENNReal.ofReal_le_one.mpr (hg1 omega)
    _ = mu := withDensity_one

theorem densityContent_mem_dominatedContents
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {g : Omega → ℝ} (hg1 : ∀ omega, g omega ≤ 1) :
    densityContent mu g ∈ dominatedContents mu :=
  measureContent_mem_dominatedContents mu _ (densityMeasure_le mu hg1)

theorem clippedDensityContent_mem_dominatedContents
    (mu : Measure Omega) [IsFiniteMeasure mu] (g : Omega → ℝ) :
    clippedDensityContent mu g ∈ dominatedContents mu :=
  densityContent_mem_dominatedContents mu (unitClip_le_one g)

@[simp]
theorem densityContent_apply
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {g : Omega → ℝ} (hg : Measurable g) (hg0 : ∀ omega, 0 ≤ g omega)
    (s : MeasurableSubset Omega) :
    densityContent mu g s = ∫ omega in (s : Set Omega), g omega ∂mu := by
  rw [densityContent, measureContent, ← setIntegral_one_eq_measureReal]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    hg.ennreal_ofReal (Filter.Eventually.of_forall fun _ ↦ by simp)
    (fun _ ↦ (1 : ℝ)) s.property]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun omega ↦ by
    simp [ENNReal.toReal_ofReal (hg0 omega)]

theorem dominatedContentIntegral_densityContent
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (f : Omega → E) {g : Omega → ℝ}
    (hg : Measurable g) (hg0 : ∀ omega, 0 ≤ g omega)
    (hg1 : ∀ omega, g omega ≤ 1) :
    dominatedContentIntegral mu f
      ⟨densityContent mu g, densityContent_mem_dominatedContents mu hg1⟩ =
      ∫ omega, g omega • f omega ∂mu := by
  let nu := mu.withDensity fun omega ↦ ENNReal.ofReal (g omega)
  have hnu : nu ≤ mu := densityMeasure_le mu hg1
  change (∫ omega, f omega ∂(dominatedContentToMeasure mu
    (measureContent nu) _)) = _
  rw [dominatedContentToMeasure_measureContent mu nu hnu]
  rw [integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ by simp)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun omega ↦ by
    change (ENNReal.ofReal (g omega)).toReal • f omega =
      g omega • f omega
    rw [ENNReal.toReal_ofReal (hg0 omega)]

theorem clippedDensityContent_apply
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {g : Omega → ℝ} (hg : Measurable g)
    (hg0 : ∀ᵐ omega ∂mu, 0 ≤ g omega)
    (hg1 : ∀ᵐ omega ∂mu, g omega ≤ 1)
    (s : MeasurableSubset Omega) :
    clippedDensityContent mu g s =
      ∫ omega in (s : Set Omega), g omega ∂mu := by
  rw [clippedDensityContent, densityContent_apply mu
    (measurable_unitClip hg) (unitClip_nonneg g) s]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hg0, ae_restrict_of_ae hg1] with omega h0 h1
  exact unitClip_eq_self h0 h1

theorem dominatedContentIntegral_clippedDensityContent
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (f : Omega → E) {g : Omega → ℝ} (hg : Measurable g)
    (hg0 : ∀ᵐ omega ∂mu, 0 ≤ g omega)
    (hg1 : ∀ᵐ omega ∂mu, g omega ≤ 1) :
    dominatedContentIntegral mu f
      ⟨clippedDensityContent mu g,
        clippedDensityContent_mem_dominatedContents mu g⟩ =
      ∫ omega, g omega • f omega ∂mu := by
  change dominatedContentIntegral mu f
    ⟨densityContent mu (unitClip g), _⟩ = _
  rw [dominatedContentIntegral_densityContent mu f
    (measurable_unitClip hg) (unitClip_nonneg g) (unitClip_le_one g)]
  apply integral_congr_ae
  filter_upwards [hg0, hg1] with omega h0 h1
  rw [unitClip_eq_self h0 h1]

end DensityContents

/-! ## Compact relaxed ranges and compact fibers -/

section RelaxedRange

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Range of the integral over all positive measures dominated by `mu`.-/
def relaxedIntegralRange (mu : Measure Omega) [IsFiniteMeasure mu]
    (f : Omega → E) : Set E :=
  Set.range (dominatedContentIntegral mu f)

theorem isCompact_relaxedIntegralRange
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {f : Omega → E} (hf : Integrable f mu) (hfm : Measurable f) :
    IsCompact (relaxedIntegralRange mu f) := by
  letI : CompactSpace (dominatedContents mu) :=
    isCompact_iff_compactSpace.mp (isCompact_dominatedContents mu)
  rw [relaxedIntegralRange, ← Set.image_univ]
  exact isCompact_univ.image (continuous_dominatedContentIntegral mu hf hfm)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] in
theorem dominatedContentIntegral_restrictionContent
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (f : Omega → E) (A : Set Omega) :
    dominatedContentIntegral mu f
      ⟨restrictionContent mu A,
        restrictionContent_mem_dominatedContents mu A⟩ =
      ∫ omega in A, f omega ∂mu := by
  change (∫ omega, f omega ∂(dominatedContentToMeasure mu
    (measureContent (mu.restrict A)) _)) = ∫ omega in A, f omega ∂mu
  rw [dominatedContentToMeasure_measureContent mu (mu.restrict A)
    Measure.restrict_le_self]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] in
theorem measurableSetIntegralRange_subset_relaxedIntegralRange
    (mu : Measure Omega) [IsFiniteMeasure mu] (f : Omega → E) :
    measurableSetIntegralRange mu f ⊆ relaxedIntegralRange mu f := by
  rintro z ⟨A, hA, rfl⟩
  refine ⟨⟨restrictionContent mu A,
    restrictionContent_mem_dominatedContents mu A⟩, ?_⟩
  exact dominatedContentIntegral_restrictionContent mu f A

/-- Every point in the closure of the raw range is attained by a dominated
submeasure.  The remaining purification step will show that an extreme
attainer is actually a restriction.-/
theorem exists_dominatedContentIntegral_eq_of_mem_closure
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {f : Omega → E} (hf : Integrable f mu) (hfm : Measurable f)
    {z : E} (hz : z ∈ closure (measurableSetIntegralRange mu f)) :
    ∃ m : dominatedContents mu, dominatedContentIntegral mu f m = z := by
  have hrelClosed : IsClosed (relaxedIntegralRange mu f) :=
    (isCompact_relaxedIntegralRange mu hf hfm).isClosed
  have hclosure : closure (measurableSetIntegralRange mu f) ⊆
      relaxedIntegralRange mu f :=
    closure_minimal (measurableSetIntegralRange_subset_relaxedIntegralRange mu f)
      hrelClosed
  exact hclosure hz

/-- The ambient set of all dominated contents integrating `f` to `z`.-/
def dominatedIntegralFiber (mu : Measure Omega) [IsFiniteMeasure mu]
    (f : Omega → E) (z : E) : Set (MeasurableSubset Omega → ℝ) :=
  Subtype.val '' {m : dominatedContents mu |
    dominatedContentIntegral mu f m = z}

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] in
theorem mem_dominatedIntegralFiber_iff
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (f : Omega → E) (z : E) (m : MeasurableSubset Omega → ℝ) :
    m ∈ dominatedIntegralFiber mu f z ↔
      ∃ hm : m ∈ dominatedContents mu,
        dominatedContentIntegral mu f ⟨m, hm⟩ = z := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.property, hn⟩
  · rintro ⟨hm, hint⟩
    exact ⟨⟨m, hm⟩, hint, rfl⟩

theorem isCompact_dominatedIntegralFiber
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {f : Omega → E} (hf : Integrable f mu) (hfm : Measurable f)
    (z : E) : IsCompact (dominatedIntegralFiber mu f z) := by
  letI : CompactSpace (dominatedContents mu) :=
    isCompact_iff_compactSpace.mp (isCompact_dominatedContents mu)
  have hclosed : IsClosed {m : dominatedContents mu |
      dominatedContentIntegral mu f m = z} :=
    isClosed_eq (continuous_dominatedContentIntegral mu hf hfm) continuous_const
  exact hclosed.isCompact.image continuous_subtype_val

theorem dominatedIntegralFiber_nonempty_of_mem_closure
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {f : Omega → E} (hf : Integrable f mu) (hfm : Measurable f)
    {z : E} (hz : z ∈ closure (measurableSetIntegralRange mu f)) :
    (dominatedIntegralFiber mu f z).Nonempty := by
  obtain ⟨m, hm⟩ :=
    exists_dominatedContentIntegral_eq_of_mem_closure mu hf hfm hz
  exact ⟨m.1, (mem_dominatedIntegralFiber_iff mu f z m.1).2
    ⟨m.2, hm⟩⟩

/-- A compact nonempty moment fiber has an extreme point.  Notice that this
does not require proving convexity of the fiber: the version of
Krein--Milman used here produces an extreme point of every nonempty compact
subset of a locally convex space.-/
theorem exists_extreme_dominatedIntegralFiber_of_mem_closure
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {f : Omega → E} (hf : Integrable f mu) (hfm : Measurable f)
    {z : E} (hz : z ∈ closure (measurableSetIntegralRange mu f)) :
    ∃ m : MeasurableSubset Omega → ℝ,
      m ∈ (dominatedIntegralFiber mu f z).extremePoints ℝ := by
  exact (isCompact_dominatedIntegralFiber mu hf hfm z).extremePoints_nonempty
    (dominatedIntegralFiber_nonempty_of_mem_closure mu hf hfm hz)

end RelaxedRange

/-! ## The bang--bang perturbation -/

section BangBang

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A finite scalar step function supported on the pieces `A i`.-/
def finpartitionStep {ι : Type*} [Fintype ι]
    (A : ι → Set Omega) (c : ι → ℝ) (omega : Omega) : ℝ :=
  ∑ i, (A i).indicator (fun _ ↦ c i) omega

theorem measurable_finpartitionStep {ι : Type*} [Fintype ι]
    {A : ι → Set Omega} (hA : ∀ i, MeasurableSet (A i)) (c : ι → ℝ) :
    Measurable (finpartitionStep A c) := by
  exact Finset.measurable_sum Finset.univ fun i _ ↦
    measurable_const.indicator (hA i)

omit [MeasurableSpace Omega] in
theorem finpartitionStep_eq_on_piece {ι : Type*} [Fintype ι]
    {A : ι → Set Omega}
    (hAdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (c : ι → ℝ) {i : ι} {omega : Omega} (homega : omega ∈ A i) :
    finpartitionStep A c omega = c i := by
  rw [finpartitionStep, Finset.sum_eq_single i]
  · exact Set.indicator_of_mem homega (fun _ ↦ c i)
  · intro j _hj hji
    have hnot : omega ∉ A j := fun hj ↦
      Set.disjoint_left.mp (hAdisj j i hji) hj homega
    exact Set.indicator_of_notMem hnot (fun _ ↦ c j)
  · simp

omit [MeasurableSpace Omega] in
theorem finpartitionStep_eq_zero_of_not_mem {ι : Type*} [Fintype ι]
    (A : ι → Set Omega) (c : ι → ℝ) {omega : Omega}
    (homega : ∀ i, omega ∉ A i) :
    finpartitionStep A c omega = 0 := by
  simp [finpartitionStep, Set.indicator_of_notMem, homega]

omit [MeasurableSpace Omega] in
theorem abs_finpartitionStep_le_sum {ι : Type*} [Fintype ι]
    (A : ι → Set Omega) (c : ι → ℝ) (omega : Omega) :
    |finpartitionStep A c omega| ≤ ∑ i, |c i| := by
  calc
    |finpartitionStep A c omega| ≤
        ∑ i, |(A i).indicator (fun _ ↦ c i) omega| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| := by
      apply Finset.sum_le_sum
      intro i _hi
      by_cases hi : omega ∈ A i
      · simp [Set.indicator_of_mem hi]
      · simp [Set.indicator_of_notMem hi]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] in
theorem integral_finpartitionStep_smul {ι : Type*} [Fintype ι]
    (mu : Measure Omega)
    {A : ι → Set Omega} (hA : ∀ i, MeasurableSet (A i))
    (c : ι → ℝ) {f : Omega → E} (hf : Integrable f mu) :
    ∫ omega, finpartitionStep A c omega • f omega ∂mu =
      ∑ i, c i • ∫ omega in A i, f omega ∂mu := by
  have hfun : (fun omega ↦ finpartitionStep A c omega • f omega) =
      fun omega ↦ ∑ i, (A i).indicator (fun omega ↦ c i • f omega) omega := by
    funext omega
    rw [finpartitionStep, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : omega ∈ A i
    · simp [Set.indicator_of_mem hi]
    · simp [Set.indicator_of_notMem hi]
  rw [hfun, integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [integral_indicator (hA i), integral_smul]
  · intro i _hi
    exact (hf.fun_smul (c i)).indicator (hA i)

/-- If a measurable unit-interval-valued density is not almost everywhere
`0` or `1`, it is uniformly separated from both endpoints on a measurable
set of positive measure.-/
theorem exists_fractional_density_strip
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (h : Omega → ℝ) (hh : Measurable h)
    (h_nonneg : ∀ᵐ omega ∂mu, 0 ≤ h omega)
    (h_le_one : ∀ᵐ omega ∂mu, h omega ≤ 1)
    (h_not_extreme : ¬ ∀ᵐ omega ∂mu, h omega = 0 ∨ h omega = 1) :
    ∃ n : ℕ,
      MeasurableSet {omega | (1 / (n + 1 : ℝ)) ≤ h omega ∧
        h omega ≤ 1 - 1 / (n + 1 : ℝ)} ∧
      0 < mu.real {omega | (1 / (n + 1 : ℝ)) ≤ h omega ∧
        h omega ≤ 1 - 1 / (n + 1 : ℝ)} := by
  let B : ℕ → Set Omega := fun n ↦
    {omega | (1 / (n + 1 : ℝ)) ≤ h omega ∧
      h omega ≤ 1 - 1 / (n + 1 : ℝ)}
  have hBmeas : ∀ n, MeasurableSet (B n) := by
    intro n
    exact (measurableSet_le measurable_const hh).inter
      (measurableSet_le hh measurable_const)
  let F : Set Omega := {omega | 0 < h omega ∧ h omega < 1}
  have hFeq : F = ⋃ n, B n := by
    ext omega
    simp only [F, B, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨h0, h1⟩
      have hmin : 0 < min (h omega) (1 - h omega) :=
        lt_min h0 (sub_pos.mpr h1)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hmin
      refine ⟨n, (hn.trans_le (min_le_left _ _)).le, ?_⟩
      have hn' : 1 / (n + 1 : ℝ) < 1 - h omega :=
        hn.trans_le (min_le_right _ _)
      linarith
    · rintro ⟨n, hn0, hn1⟩
      have heps : 0 < (1 / (n + 1 : ℝ)) := by positivity
      exact ⟨heps.trans_le hn0,
        lt_of_le_of_lt hn1 (sub_lt_self 1 heps)⟩
  have hFne : mu F ≠ 0 := by
    intro hFzero
    apply h_not_extreme
    have hnotF : ∀ᵐ omega ∂mu, omega ∉ F := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hFzero
    filter_upwards [h_nonneg, h_le_one, hnotF] with omega h0 h1 hF
    by_cases hz : h omega = 0
    · exact Or.inl hz
    · right
      have hpos : 0 < h omega := lt_of_le_of_ne h0 (Ne.symm hz)
      have hnlt : ¬ h omega < 1 := fun hlt ↦ hF ⟨hpos, hlt⟩
      exact le_antisymm h1 (not_lt.mp hnlt)
  have hUne : mu (⋃ n, B n) ≠ 0 := by rwa [← hFeq]
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hUne
  exact ⟨n, hBmeas n, ENNReal.toReal_pos hn.ne' (by finiteness)⟩

/-- Equal positive measurable partition into `d + 1` pieces.-/
theorem IsAtomlessMeasure.exists_positive_equal_finpartition
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hmu : IsAtomlessMeasure mu) (d : ℕ)
    {B : Set Omega} (hB : MeasurableSet B) (hBpos : 0 < mu.real B) :
    ∃ A : Fin (d + 1) → Set Omega,
      IsMeasurableFinpartition Finset.univ B A ∧
        ∀ i, 0 < mu.real (A i) := by
  obtain ⟨A, hApart, hmass⟩ :=
    hmu.exists_isMeasurableFinpartition_measureReal_eq
      (Finset.univ : Finset (Fin (d + 1))) B hB
      (fun _ ↦ (1 / (d + 1 : ℝ)))
      (by intro i hi; positivity)
      (by simp; field_simp)
  refine ⟨A, hApart, fun i ↦ ?_⟩
  rw [hmass i (Finset.mem_univ i)]
  positivity

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] in
/-- An extreme point of a fixed finite-dimensional moment fiber is a
measurable restriction of the reference measure.  This is the purification
(or bang--bang) step in Lyapunov's theorem.-/
theorem extreme_dominatedIntegralFiber_is_restriction
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hmu : IsAtomlessMeasure mu) [FiniteDimensional ℝ E]
    {f : Omega → E} (hf : Integrable f mu)
    {z : E} {m : MeasurableSubset Omega → ℝ}
    (hmext : m ∈ (dominatedIntegralFiber mu f z).extremePoints ℝ) :
    ∃ A : Set Omega, MeasurableSet A ∧ m = restrictionContent mu A := by
  have hmfiber : m ∈ dominatedIntegralFiber mu f z :=
    (mem_extremePoints_iff_left.mp hmext).1
  obtain ⟨hm, hmInt⟩ :=
    (mem_dominatedIntegralFiber_iff mu f z m).mp hmfiber
  let nu : Measure Omega := dominatedContentToMeasure mu m hm
  have hnu : nu ≤ mu := dominatedContentToMeasure_le mu m hm
  letI : IsFiniteMeasure nu := isFiniteMeasure_of_le mu hnu
  let g : Omega → ℝ := fun omega ↦ (nu.rnDeriv mu omega).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv nu mu).ennreal_toReal
  have hg0 : ∀ᵐ omega ∂mu, 0 ≤ g omega :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg
  have hg1 : ∀ᵐ omega ∂mu, g omega ≤ 1 := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hnu] with omega homega
    have homega' : nu.rnDeriv mu omega ≤ (1 : ℝ≥0∞) := by
      simpa using homega
    change (nu.rnDeriv mu omega).toReal ≤ 1
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by simp) homega'
  have hmRN (s : MeasurableSubset Omega) :
      m s = ∫ omega in (s : Set Omega), g omega ∂mu := by
    calc
      m s = measureContent nu s := by
        rw [measureContent_dominatedContentToMeasure mu m hm]
      _ = nu.real (s : Set Omega) := rfl
      _ = ∫ omega in (s : Set Omega), g omega ∂mu := by
        symm
        exact Measure.setIntegral_toReal_rnDeriv
          hnu.absolutelyContinuous (s : Set Omega)
  by_contra hnoA
  have hgNotExtreme : ¬ ∀ᵐ omega ∂mu, g omega = 0 ∨ g omega = 1 := by
    intro hgExtreme
    let A0 : Set Omega := {omega | g omega = 1}
    have hA0 : MeasurableSet A0 :=
      measurableSet_eq_fun hg measurable_const
    have hrnIndicator : nu.rnDeriv mu =ᵐ[mu]
        A0.indicator (1 : Omega → ℝ≥0∞) := by
      filter_upwards [hgExtreme, Measure.rnDeriv_lt_top nu mu] with omega hext hfinite
      rcases hext with hzero | hone
      · have hrzero : nu.rnDeriv mu omega = 0 := by
          rcases (ENNReal.toReal_eq_zero_iff _).mp hzero with hrzero | htop
          · exact hrzero
          · exact (ne_of_lt hfinite htop).elim
        have hnotA : omega ∉ A0 := by
          intro hmem
          have : g omega = 1 := hmem
          linarith
        rw [Set.indicator_of_notMem hnotA, hrzero]
      · have hrone : nu.rnDeriv mu omega = 1 :=
          (ENNReal.toReal_eq_one_iff _).mp hone
        have hmem : omega ∈ A0 := hone
        rw [Set.indicator_of_mem hmem, hrone]
        simp
    have hnuRestrict : nu = mu.restrict A0 := by
      calc
        nu = mu.withDensity (nu.rnDeriv mu) :=
          (Measure.withDensity_rnDeriv_eq nu mu
            hnu.absolutelyContinuous).symm
        _ = mu.withDensity (A0.indicator (1 : Omega → ℝ≥0∞)) :=
          withDensity_congr_ae hrnIndicator
        _ = mu.restrict A0 := withDensity_indicator_one hA0
    apply hnoA
    refine ⟨A0, hA0, ?_⟩
    rw [restrictionContent, ← hnuRestrict]
    exact (measureContent_dominatedContentToMeasure mu m hm).symm
  obtain ⟨n, hBmeas, hBpos⟩ :=
    exists_fractional_density_strip mu g hg hg0 hg1 hgNotExtreme
  let eps : ℝ := 1 / (n + 1 : ℝ)
  let B : Set Omega := {omega | eps ≤ g omega ∧ g omega ≤ 1 - eps}
  have heps : 0 < eps := by simp only [eps]; positivity
  have hBmeas' : MeasurableSet B := by simpa only [B, eps] using hBmeas
  have hBpos' : 0 < mu.real B := by simpa only [B, eps] using hBpos
  let d := Module.finrank ℝ E
  obtain ⟨A, hApart, hApos⟩ :=
    hmu.exists_positive_equal_finpartition mu d hBmeas' hBpos'
  rcases hApart with ⟨hAmeas0, hAsub0, hAdisj0, _hAunion⟩
  have hAmeas : ∀ i, MeasurableSet (A i) := fun i ↦
    hAmeas0 i (Finset.mem_univ i)
  have hAsub : ∀ i, A i ⊆ B := fun i ↦
    hAsub0 i (Finset.mem_univ i)
  have hAdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j) :=
    fun i j hij ↦ hAdisj0 i (Finset.mem_univ i) j (Finset.mem_univ j) hij
  let v : Fin (d + 1) → E := fun i ↦ ∫ omega in A i, f omega ∂mu
  have hvdep : ¬ LinearIndependent ℝ v := by
    intro hv
    have hcard := hv.fintype_card_le_finrank
    have : d + 1 ≤ d := by simpa only [Fintype.card_fin, d] using hcard
    omega
  obtain ⟨c, hcMoment, i0, hi0⟩ :=
    Fintype.not_linearIndependent_iff.mp hvdep
  let C : ℝ := ∑ i, |c i|
  have hCpos : 0 < C := by
    have hiabs : 0 < |c i0| := abs_pos.mpr hi0
    exact hiabs.trans_le <| by
      exact Finset.single_le_sum (fun i _ ↦ abs_nonneg (c i))
        (Finset.mem_univ i0)
  let eta : ℝ := eps / C
  have heta : 0 < eta := div_pos heps hCpos
  let delta : Omega → ℝ := finpartitionStep A c
  have hdeltaMeas : Measurable delta := measurable_finpartitionStep hAmeas c
  have hdeltaBound : ∀ omega, |delta omega| ≤ C :=
    abs_finpartitionStep_le_sum A c
  have hperturbBound : ∀ omega, |eta * delta omega| ≤ eps := by
    intro omega
    calc
      |eta * delta omega| = eta * |delta omega| := by
        rw [abs_mul, abs_of_pos heta]
      _ ≤ eta * C := mul_le_mul_of_nonneg_left
        (hdeltaBound omega) heta.le
      _ = eps := by simp [eta, ne_of_gt hCpos]
  have hdeltaMoment : ∫ omega, delta omega • f omega ∂mu = 0 := by
    rw [show (∫ omega, delta omega • f omega ∂mu) =
        ∑ i, c i • ∫ omega in A i, f omega ∂mu from
      integral_finpartitionStep_smul mu hAmeas c hf]
    exact hcMoment
  have hdeltaZeroOutside {omega : Omega} (homega : omega ∉ B) :
      delta omega = 0 := by
    exact finpartitionStep_eq_zero_of_not_mem A c fun i hi ↦
      homega (hAsub i hi)
  let gp : Omega → ℝ := fun omega ↦ g omega + eta * delta omega
  let gm : Omega → ℝ := fun omega ↦ g omega - eta * delta omega
  have hetaDeltaMeas : Measurable (fun omega ↦ eta * delta omega) :=
    measurable_const.mul hdeltaMeas
  have hgpMeas : Measurable gp := hg.add hetaDeltaMeas
  have hgmMeas : Measurable gm := hg.sub hetaDeltaMeas
  have hgp0 : ∀ᵐ omega ∂mu, 0 ≤ gp omega := by
    filter_upwards [hg0, hg1] with omega hg0' hg1'
    by_cases homega : omega ∈ B
    · have hstrip : eps ≤ g omega ∧ g omega ≤ 1 - eps := by
        simpa only [B, mem_ofPred_eq] using homega
      have hbounds := abs_le.mp (hperturbBound omega)
      dsimp only [gp]
      linarith
    · simp only [gp, hdeltaZeroOutside homega, mul_zero, add_zero]
      exact hg0'
  have hgp1 : ∀ᵐ omega ∂mu, gp omega ≤ 1 := by
    filter_upwards [hg0, hg1] with omega hg0' hg1'
    by_cases homega : omega ∈ B
    · have hstrip : eps ≤ g omega ∧ g omega ≤ 1 - eps := by
        simpa only [B, mem_ofPred_eq] using homega
      have hbounds := abs_le.mp (hperturbBound omega)
      dsimp only [gp]
      linarith
    · simp only [gp, hdeltaZeroOutside homega, mul_zero, add_zero]
      exact hg1'
  have hgm0 : ∀ᵐ omega ∂mu, 0 ≤ gm omega := by
    filter_upwards [hg0, hg1] with omega hg0' hg1'
    by_cases homega : omega ∈ B
    · have hstrip : eps ≤ g omega ∧ g omega ≤ 1 - eps := by
        simpa only [B, mem_ofPred_eq] using homega
      have hbounds := abs_le.mp (hperturbBound omega)
      dsimp only [gm]
      linarith
    · simp only [gm, hdeltaZeroOutside homega, mul_zero, sub_zero]
      exact hg0'
  have hgm1 : ∀ᵐ omega ∂mu, gm omega ≤ 1 := by
    filter_upwards [hg0, hg1] with omega hg0' hg1'
    by_cases homega : omega ∈ B
    · have hstrip : eps ≤ g omega ∧ g omega ≤ 1 - eps := by
        simpa only [B, mem_ofPred_eq] using homega
      have hbounds := abs_le.mp (hperturbBound omega)
      dsimp only [gm]
      linarith
    · simp only [gm, hdeltaZeroOutside homega, mul_zero, sub_zero]
      exact hg1'
  have hgfInt : Integrable (fun omega ↦ g omega • f omega) mu := by
    apply hf.bdd_smul 1 hg.aestronglyMeasurable
    filter_upwards [hg0, hg1] with omega h0 h1
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have hdeltafInt : Integrable
      (fun omega ↦ delta omega • f omega) mu := by
    apply hf.bdd_smul C hdeltaMeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun omega ↦ by
      simpa only [Real.norm_eq_abs] using hdeltaBound omega
  have hgInt : Integrable g mu := by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    filter_upwards [hg0, hg1] with omega h0 h1
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have hdeltaInt : Integrable delta mu := by
    apply Integrable.of_bound hdeltaMeas.aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun omega ↦ by
      simpa only [Real.norm_eq_abs] using hdeltaBound omega
  have hetaDeltaInt : Integrable (fun omega ↦ eta * delta omega) mu := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hdeltaInt.fun_smul eta
  have hgpMoment :
      ∫ omega, gp omega • f omega ∂mu =
        ∫ omega, g omega • f omega ∂mu := by
    calc
      ∫ omega, gp omega • f omega ∂mu =
          ∫ omega, (g omega • f omega) +
            eta • (delta omega • f omega) ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega ↦ by
          simp only [gp, add_smul, mul_smul]
      _ = (∫ omega, g omega • f omega ∂mu) +
          ∫ omega, eta • (delta omega • f omega) ∂mu :=
        integral_add hgfInt (hdeltafInt.fun_smul eta)
      _ = ∫ omega, g omega • f omega ∂mu := by
        rw [integral_smul, hdeltaMoment, smul_zero, add_zero]
  have hgmMoment :
      ∫ omega, gm omega • f omega ∂mu =
        ∫ omega, g omega • f omega ∂mu := by
    calc
      ∫ omega, gm omega • f omega ∂mu =
          ∫ omega, (g omega • f omega) -
            eta • (delta omega • f omega) ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega ↦ by
          simp only [gm, sub_smul, mul_smul]
      _ = (∫ omega, g omega • f omega ∂mu) -
          ∫ omega, eta • (delta omega • f omega) ∂mu :=
        integral_sub hgfInt (hdeltafInt.fun_smul eta)
      _ = ∫ omega, g omega • f omega ∂mu := by
        rw [integral_smul, hdeltaMoment, smul_zero, sub_zero]
  have hgMoment : ∫ omega, g omega • f omega ∂mu = z := by
    calc
      ∫ omega, g omega • f omega ∂mu =
          ∫ omega, f omega ∂nu :=
        integral_rnDeriv_smul hnu.absolutelyContinuous
      _ = dominatedContentIntegral mu f ⟨m, hm⟩ := rfl
      _ = z := hmInt
  let p : MeasurableSubset Omega → ℝ := clippedDensityContent mu gp
  let q : MeasurableSubset Omega → ℝ := clippedDensityContent mu gm
  have hpdom : p ∈ dominatedContents mu :=
    clippedDensityContent_mem_dominatedContents mu gp
  have hqdom : q ∈ dominatedContents mu :=
    clippedDensityContent_mem_dominatedContents mu gm
  have hpMoment : dominatedContentIntegral mu f ⟨p, hpdom⟩ = z := by
    calc
      dominatedContentIntegral mu f ⟨p, hpdom⟩ =
          ∫ omega, gp omega • f omega ∂mu := by
        exact dominatedContentIntegral_clippedDensityContent
          mu f hgpMeas hgp0 hgp1
      _ = ∫ omega, g omega • f omega ∂mu := hgpMoment
      _ = z := hgMoment
  have hqMoment : dominatedContentIntegral mu f ⟨q, hqdom⟩ = z := by
    calc
      dominatedContentIntegral mu f ⟨q, hqdom⟩ =
          ∫ omega, gm omega • f omega ∂mu := by
        exact dominatedContentIntegral_clippedDensityContent
          mu f hgmMeas hgm0 hgm1
      _ = ∫ omega, g omega • f omega ∂mu := hgmMoment
      _ = z := hgMoment
  have hpFiber : p ∈ dominatedIntegralFiber mu f z :=
    (mem_dominatedIntegralFiber_iff mu f z p).2 ⟨hpdom, hpMoment⟩
  have hqFiber : q ∈ dominatedIntegralFiber mu f z :=
    (mem_dominatedIntegralFiber_iff mu f z q).2 ⟨hqdom, hqMoment⟩
  let r : MeasurableSubset Omega → ℝ := fun s ↦
    eta * ∫ omega in (s : Set Omega), delta omega ∂mu
  have hpEq : p = m + r := by
    funext s
    change clippedDensityContent mu gp s =
      m s + eta * ∫ omega in (s : Set Omega), delta omega ∂mu
    rw [clippedDensityContent_apply mu hgpMeas hgp0 hgp1 s, hmRN s]
    change (∫ omega in (s : Set Omega),
      g omega + eta * delta omega ∂mu) = _
    rw [integral_add hgInt.integrableOn hetaDeltaInt.integrableOn,
      integral_const_mul]
  have hqEq : q = m - r := by
    funext s
    change clippedDensityContent mu gm s =
      m s - eta * ∫ omega in (s : Set Omega), delta omega ∂mu
    rw [clippedDensityContent_apply mu hgmMeas hgm0 hgm1 s, hmRN s]
    change (∫ omega in (s : Set Omega),
      g omega - eta * delta omega ∂mu) = _
    rw [integral_sub hgInt.integrableOn hetaDeltaInt.integrableOn,
      integral_const_mul]
  have hmOpen : m ∈ openSegment ℝ q p := by
    rw [hqEq, hpEq]
    exact mem_openSegment_sub_add m r
  have hqEqM : q = m :=
    (mem_extremePoints_iff_left.mp hmext).2 q hqFiber p hpFiber hmOpen
  have hrZero : r = 0 := by
    apply sub_eq_self.mp
    exact hqEq.symm.trans hqEqM
  have hdeltaAi :
      ∫ omega in A i0, delta omega ∂mu =
        mu.real (A i0) * c i0 := by
    calc
      ∫ omega in A i0, delta omega ∂mu =
          ∫ _omega in A i0, c i0 ∂mu := by
        apply integral_congr_ae
        exact ae_restrict_of_forall_mem (hAmeas i0) fun omega homega ↦
          finpartitionStep_eq_on_piece hAdisj c homega
      _ = mu.real (A i0) * c i0 := by
        simpa only [smul_eq_mul] using
          (setIntegral_const (μ := mu) (s := A i0) (c i0))
  have hrCoord : eta * ∫ omega in A i0, delta omega ∂mu = 0 := by
    have := congrFun hrZero
      (⟨A i0, hAmeas i0⟩ : MeasurableSubset Omega)
    simpa only [r, Pi.zero_apply] using this
  rw [hdeltaAi] at hrCoord
  exact (mul_ne_zero heta.ne'
    (mul_ne_zero (ne_of_gt (hApos i0)) hi0)) hrCoord

/-! ## Unconditional finite-dimensional Lyapunov theorem -/

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] in
theorem measurableSetIntegralRange_congr_ae
    (mu : Measure Omega) {f g : Omega → E} (hfg : f =ᵐ[mu] g) :
    measurableSetIntegralRange mu f = measurableSetIntegralRange mu g := by
  ext z
  constructor
  · rintro ⟨A, hA, hInt⟩
    refine ⟨A, hA, ?_⟩
    calc
      ∫ omega in A, g omega ∂mu = ∫ omega in A, f omega ∂mu :=
        integral_congr_ae (ae_restrict_of_ae hfg.symm)
      _ = z := hInt
  · rintro ⟨A, hA, hInt⟩
    refine ⟨A, hA, ?_⟩
    calc
      ∫ omega in A, f omega ∂mu = ∫ omega in A, g omega ∂mu :=
        integral_congr_ae (ae_restrict_of_ae hfg)
      _ = z := hInt

/-- For a measurable integrable density, every point in the closure of the
raw vector-measure range is already represented by a measurable set.-/
theorem exists_measurable_setIntegral_eq_of_mem_closure_of_atomless
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hmu : IsAtomlessMeasure mu) [FiniteDimensional ℝ E]
    {f : Omega → E} (hf : Integrable f mu) (hfm : Measurable f)
    {z : E} (hz : z ∈ closure (measurableSetIntegralRange mu f)) :
    ∃ A : Set Omega, MeasurableSet A ∧ ∫ omega in A, f omega ∂mu = z := by
  obtain ⟨m, hmext⟩ :=
    exists_extreme_dominatedIntegralFiber_of_mem_closure mu hf hfm hz
  obtain ⟨A, hA, hmA⟩ :=
    extreme_dominatedIntegralFiber_is_restriction mu hmu hf hmext
  have hmfiber : m ∈ dominatedIntegralFiber mu f z :=
    (mem_extremePoints_iff_left.mp hmext).1
  obtain ⟨hm, hmz⟩ := (mem_dominatedIntegralFiber_iff mu f z m).mp hmfiber
  subst m
  refine ⟨A, hA, ?_⟩
  rw [← dominatedContentIntegral_restrictionContent mu f A]
  exact hmz

/-- Closedness of the raw range for a measurable integrable vector
function on a finite atomless base.-/
theorem isClosed_measurableSetIntegralRange_of_atomless_integrable_measurable
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hmu : IsAtomlessMeasure mu) [FiniteDimensional ℝ E]
    {f : Omega → E} (hf : Integrable f mu) (hfm : Measurable f) :
    IsClosed (measurableSetIntegralRange mu f) := by
  rw [← closure_eq_iff_isClosed]
  apply Subset.antisymm
  · intro z hz
    obtain ⟨A, hA, hAz⟩ :=
      exists_measurable_setIntegral_eq_of_mem_closure_of_atomless
        mu hmu hf hfm hz
    exact ⟨A, hA, hAz⟩
  · exact subset_closure

/-- The raw range is closed for every integrable vector function; a
measurable representative removes the inessential pointwise measurability
assumption.-/
theorem isClosed_measurableSetIntegralRange_of_atomless_integrable
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hmu : IsAtomlessMeasure mu) [FiniteDimensional ℝ E]
    {f : Omega → E} (hf : Integrable f mu) :
    IsClosed (measurableSetIntegralRange mu f) := by
  let g : Omega → E := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[mu] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g mu := hf.congr hfg
  have hgm : Measurable g := hf.aestronglyMeasurable.measurable_mk
  rw [measurableSetIntegralRange_congr_ae mu hfg]
  exact isClosed_measurableSetIntegralRange_of_atomless_integrable_measurable
    mu hmu hg hgm

/-- The finite-dimensional vector-measure range is compact.-/
theorem isCompact_measurableSetIntegralRange_of_atomless_integrable
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hmu : IsAtomlessMeasure mu) [FiniteDimensional ℝ E]
    {f : Omega → E} (hf : Integrable f mu) :
    IsCompact (measurableSetIntegralRange mu f) :=
  (isCompact_measurableSetIntegralRange_iff_isClosed hf).mpr
    (isClosed_measurableSetIntegralRange_of_atomless_integrable mu hmu hf)

/-- Compactness and convexity of the raw range, i.e. the classical
finite-dimensional Lyapunov conclusion in set form.-/
theorem isCompact_convex_measurableSetIntegralRange_of_atomless
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hmu : IsAtomlessMeasure mu) [FiniteDimensional ℝ E]
    {f : Omega → E} (hf : Integrable f mu) :
    IsCompact (measurableSetIntegralRange mu f) ∧
      Convex ℝ (measurableSetIntegralRange mu f) := by
  have hclosed :=
    isClosed_measurableSetIntegralRange_of_atomless_integrable mu hmu hf
  have hclosure :=
    isCompact_convex_closure_measurableSetIntegralRange_of_atomless
      mu hmu hf
  rw [hclosed.closure_eq] at hclosure
  exact hclosure

/-- Sequential attainment of limits of measurable set integrals on every
finite atomless base in finite dimension.-/
theorem hasSequentialSetIntegralAttainment_of_atomless_finiteDimensional
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hmu : IsAtomlessMeasure mu) [FiniteDimensional ℝ E] :
    HasSequentialSetIntegralAttainment mu E := by
  rw [hasSequentialSetIntegralAttainment_iff_isClosedRange]
  intro f hf
  exact isClosed_measurableSetIntegralRange_of_atomless_integrable mu hmu hf

/-- **Finite-dimensional Lyapunov convexity theorem.** Every integrable
vector function on a finite atomless measurable space has a convex raw
set-integral range.-/
theorem hasLyapunovConvexity_of_atomless_finiteDimensional
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (hmu : IsAtomlessMeasure mu) [FiniteDimensional ℝ E] :
    HasLyapunovConvexity mu E := by
  intro f hf
  exact (isCompact_convex_measurableSetIntegralRange_of_atomless
    mu hmu hf).2

end BangBang

end RandomSetTheory
