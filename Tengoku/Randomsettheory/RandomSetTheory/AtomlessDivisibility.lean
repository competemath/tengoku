/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.ExactDivisibility

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sierpiński divisibility for atomless finite measures

This module closes the gap between the elementary nonatomicity predicate
`IsAtomlessMeasure` and exact scalar divisibility.  No standard-Borel or
countable-generation hypothesis is used.

The first ingredient is the classical infimum argument: a positive measurable
set contains positive measurable subsets of arbitrarily small mass.  If the
positive attainable masses had a positive infimum, splitting a set whose mass
is less than twice this infimum would produce a smaller positive mass.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace RandomSetTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Arbitrarily small positive pieces -/

/-- In an atomless finite measure space, every positive measurable set contains
a positive measurable subset of arbitrarily small prescribed upper mass.

This is the key local lemma in the proof of Sierpiński's exact divisibility
theorem.  It holds on an arbitrary measurable space.-/
theorem IsAtomlessMeasure.exists_subset_measureReal_pos_le
    {μ : Measure Ω} [IsFiniteMeasure μ] (hμ : IsAtomlessMeasure μ)
    {s : Set Ω} (hs : MeasurableSet s) (hspos : 0 < μ s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧
      0 < μ.real t ∧ μ.real t ≤ ε := by
  let P : Set ℝ :=
    {x | ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧
      0 < μ.real t ∧ μ.real t = x}
  have hsreal : 0 < μ.real s :=
    ENNReal.toReal_pos hspos.ne' (measure_ne_top μ s)
  have hPne : P.Nonempty := by
    refine ⟨μ.real s, s, Subset.rfl, hs, hsreal, rfl⟩
  have hPbelow : BddBelow P := by
    refine ⟨0, ?_⟩
    rintro x ⟨t, -, -, htpos, rfl⟩
    exact htpos.le
  have hInf : sInf P = 0 := by
    apply le_antisymm
    · by_contra hnot
      have hInfPos : 0 < sInf P := lt_of_not_ge hnot
      have hInfTwo : sInf P < 2 * sInf P := by linarith
      obtain ⟨x, hxP, hxTwo⟩ :=
        exists_lt_of_csInf_lt hPne hInfTwo
      rcases hxP with ⟨t, hts, ht, htposReal, htx⟩
      have htpos : 0 < μ t :=
        (ENNReal.toReal_pos_iff.mp htposReal).1
      obtain ⟨u, hut, hu, hupos, hvpos⟩ :=
        hμ.exists_measurable_split ht htpos
      let v : Set Ω := t \ u
      have hv : MeasurableSet v := ht.diff hu
      have hus : u ⊆ s := hut.trans hts
      have hvs : v ⊆ s := Set.sdiff_subset.trans hts
      have huposReal : 0 < μ.real u :=
        ENNReal.toReal_pos hupos.ne' (measure_ne_top μ u)
      have hvposReal : 0 < μ.real v :=
        ENNReal.toReal_pos hvpos.ne' (measure_ne_top μ v)
      have hvMeasure : μ.real v = μ.real t - μ.real u := by
        exact measureReal_sdiff hut hu
      have hxMeasure : μ.real t = x := htx
      by_cases huHalf : μ.real u ≤ x / 2
      · have huP : μ.real u ∈ P :=
          ⟨u, hus, hu, huposReal, rfl⟩
        have hInfLe : sInf P ≤ μ.real u := csInf_le hPbelow huP
        have hxHalfLt : x / 2 < sInf P := by linarith [hxTwo]
        linarith
      · have hvHalf : μ.real v ≤ x / 2 := by
          rw [hvMeasure, hxMeasure]
          linarith
        have hvP : μ.real v ∈ P :=
          ⟨v, hvs, hv, hvposReal, rfl⟩
        have hInfLe : sInf P ≤ μ.real v := csInf_le hPbelow hvP
        have hxHalfLt : x / 2 < sInf P := by linarith [hxTwo]
        linarith
    · exact le_csInf hPne fun x hx ↦ by
        rcases hx with ⟨t, -, -, htpos, rfl⟩
        exact htpos.le
  have hInfLt : sInf P < ε := by simpa [hInf] using hε
  obtain ⟨x, hxP, hxε⟩ := exists_lt_of_csInf_lt hPne hInfLt
  rcases hxP with ⟨t, hts, ht, htpos, htx⟩
  refine ⟨t, hts, ht, htpos, ?_⟩
  rw [htx]
  exact hxε.le

/-- Among the positive subsets of `s` whose mass is at most `b`, one can
choose a subset whose mass dominates every other admissible mass up to the
factor `2`.  This harmless factor is what makes the subsequent greedy
construction quantitative enough to force exhaustion of the target gap.-/
theorem IsAtomlessMeasure.exists_subset_measureReal_quasiMax
    {μ : Measure Ω} [IsFiniteMeasure μ] (hμ : IsAtomlessMeasure μ)
    {s : Set Ω} (hs : MeasurableSet s) (hspos : 0 < μ s)
    {b : ℝ} (hb : 0 < b) :
    ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧
      0 < μ.real t ∧ μ.real t ≤ b ∧
      ∀ u : Set Ω, u ⊆ s → MeasurableSet u →
        0 < μ.real u → μ.real u ≤ b →
        μ.real u ≤ 2 * μ.real t := by
  let P : Set ℝ :=
    {x | ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧
      0 < μ.real t ∧ μ.real t ≤ b ∧ μ.real t = x}
  obtain ⟨t₀, ht₀s, ht₀, ht₀pos, ht₀b⟩ :=
    hμ.exists_subset_measureReal_pos_le hs hspos hb
  have hPne : P.Nonempty := by
    exact ⟨μ.real t₀, t₀, ht₀s, ht₀, ht₀pos, ht₀b, rfl⟩
  have hPabove : BddAbove P := by
    refine ⟨b, ?_⟩
    rintro x ⟨t, -, -, -, htb, rfl⟩
    exact htb
  have hSupPos : 0 < sSup P :=
    lt_of_lt_of_le ht₀pos
      (le_csSup hPabove
        ⟨t₀, ht₀s, ht₀, ht₀pos, ht₀b, rfl⟩)
  have hHalf : sSup P / 2 < sSup P := by linarith
  obtain ⟨x, hxP, hxHalf⟩ := exists_lt_of_lt_csSup hPne hHalf
  rcases hxP with ⟨t, hts, ht, htpos, htb, htx⟩
  refine ⟨t, hts, ht, htpos, htb, ?_⟩
  intro u hus hu hupos hub
  have huP : μ.real u ∈ P :=
    ⟨u, hus, hu, hupos, hub, rfl⟩
  have huSup : μ.real u ≤ sSup P := le_csSup hPabove huP
  linarith [htx]

/-! ## Exact prescribed masses -/

/-- **Sierpiński's exact divisibility theorem, target-mass form.**

For a finite atomless measure on an arbitrary measurable space, every real
mass between `0` and the mass of a measurable set is attained by one of its
measurable subsets.-/
theorem IsAtomlessMeasure.exists_subset_measureReal_eq
    {μ : Measure Ω} [IsFiniteMeasure μ] (hμ : IsAtomlessMeasure μ)
    {s : Set Ω} (hs : MeasurableSet s)
    {b : ℝ} (hb0 : 0 ≤ b) (hbs : b ≤ μ.real s) :
    ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧ μ.real t = b := by
  classical
  by_cases hbzero : b = 0
  · exact ⟨∅, empty_subset s, MeasurableSet.empty, by simp [hbzero]⟩
  have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hbzero)
  let Good : Set Ω → Set Ω → Prop := fun A t ↦
    t ⊆ s \ A ∧ MeasurableSet t ∧
      0 < μ.real t ∧ μ.real t ≤ b - μ.real A ∧
      ∀ u : Set Ω, u ⊆ s \ A → MeasurableSet u →
        0 < μ.real u → μ.real u ≤ b - μ.real A →
        μ.real u ≤ 2 * μ.real t
  have exists_good (A : Set Ω) (hA : MeasurableSet A)
      (hAs : A ⊆ s) (hAb : μ.real A < b) :
      ∃ t : Set Ω, Good A t := by
    have hremReal : μ.real (s \ A) = μ.real s - μ.real A :=
      measureReal_sdiff hAs hA
    have hremRealPos : 0 < μ.real (s \ A) := by
      rw [hremReal]
      linarith
    have hremPos : 0 < μ (s \ A) :=
      (ENNReal.toReal_pos_iff.mp hremRealPos).1
    have hgap : 0 < b - μ.real A := sub_pos.mpr hAb
    obtain ⟨t, htr, ht, htpos, htle, htdom⟩ :=
      hμ.exists_subset_measureReal_quasiMax (hs.diff hA) hremPos hgap
    exact ⟨t, htr, ht, htpos, htle, htdom⟩
  let Admissible : Set Ω → Prop := fun A ↦
    MeasurableSet A ∧ A ⊆ s ∧ μ.real A < b
  let piece : Set Ω → Set Ω := fun A ↦
    if h : Admissible A then
      Classical.choose (exists_good A h.1 h.2.1 h.2.2)
    else ∅
  have piece_spec (A : Set Ω) (hA : Admissible A) :
      Good A (piece A) := by
    rw [show piece A = Classical.choose
      (exists_good A hA.1 hA.2.1 hA.2.2) by simp [piece, hA]]
    exact Classical.choose_spec (exists_good A hA.1 hA.2.1 hA.2.2)
  have piece_eq_empty (A : Set Ω) (hA : ¬ Admissible A) :
      piece A = ∅ := by simp [piece, hA]
  let A : ℕ → Set Ω := fun n ↦
    Nat.rec ∅ (fun _ C ↦ C ∪ piece C) n
  have A_zero : A 0 = ∅ := rfl
  have A_succ (n : ℕ) : A (n + 1) = A n ∪ piece (A n) := rfl
  have A_invariant (n : ℕ) :
      MeasurableSet (A n) ∧ A n ⊆ s ∧ μ.real (A n) ≤ b := by
    induction n with
    | zero => simp [A, hb0]
    | succ n ih =>
        rw [show A (n + 1) = A n ∪ piece (A n) from A_succ n]
        by_cases hlt : μ.real (A n) < b
        · have hAdm : Admissible (A n) := ⟨ih.1, ih.2.1, hlt⟩
          have hp := piece_spec (A n) hAdm
          have hpSub : piece (A n) ⊆ s \ A n := hp.1
          have hpMeas : MeasurableSet (piece (A n)) := hp.2.1
          have hpLe : μ.real (piece (A n)) ≤ b - μ.real (A n) :=
            hp.2.2.2.1
          have hdisj : Disjoint (A n) (piece (A n)) := by
            rw [Set.disjoint_left]
            intro x hxA hxp
            exact (hpSub hxp).2 hxA
          refine ⟨ih.1.union hpMeas,
            union_subset ih.2.1 (hpSub.trans Set.sdiff_subset), ?_⟩
          rw [measureReal_union hdisj hpMeas]
          linarith
        · have hNotAdm : ¬ Admissible (A n) := by
            intro hAdm
            exact hlt hAdm.2.2
          rw [piece_eq_empty (A n) hNotAdm, union_empty]
          exact ih
  have A_step (n : ℕ) : A n ⊆ A (n + 1) := by
    rw [A_succ]
    exact subset_union_left
  have A_mono : Monotone A := monotone_nat_of_le_succ A_step
  let U : Set Ω := ⋃ n, A n
  have hUmeas : MeasurableSet U :=
    MeasurableSet.iUnion fun n ↦ (A_invariant n).1
  have hUs : U ⊆ s :=
    iUnion_subset fun n ↦ (A_invariant n).2.1
  have hlimReal :
      Filter.Tendsto (fun n ↦ μ.real (A n)) Filter.atTop
        (nhds (μ.real U)) := by
    have hlim := tendsto_measure_iUnion_atTop (μ := μ) A_mono
    have htoReal := ENNReal.tendsto_toReal (measure_ne_top μ U)
    convert htoReal.comp hlim using 1 <;>
      simp [Measure.real, Function.comp_def, U]
  have hUb : μ.real U ≤ b :=
    le_of_tendsto hlimReal
      (Filter.Eventually.of_forall fun n ↦ (A_invariant n).2.2)
  refine ⟨U, hUs, hUmeas, ?_⟩
  apply le_antisymm hUb
  by_contra hnot
  have hUlt : μ.real U < b := lt_of_not_ge hnot
  have hremReal : μ.real (s \ U) = μ.real s - μ.real U :=
    measureReal_sdiff hUs hUmeas
  have hremRealPos : 0 < μ.real (s \ U) := by
    rw [hremReal]
    linarith
  have hremPos : 0 < μ (s \ U) :=
    (ENNReal.toReal_pos_iff.mp hremRealPos).1
  have hgapPos : 0 < b - μ.real U := sub_pos.mpr hUlt
  obtain ⟨t, htRem, htMeas, htPos, htGap⟩ :=
    hμ.exists_subset_measureReal_pos_le (hs.diff hUmeas) hremPos hgapPos
  have A_subset_U (n : ℕ) : A n ⊆ U := by
    exact subset_iUnion A n
  have A_real_le_U (n : ℕ) : μ.real (A n) ≤ μ.real U :=
    measureReal_mono (A_subset_U n)
  have A_admissible (n : ℕ) : Admissible (A n) := by
    refine ⟨(A_invariant n).1, (A_invariant n).2.1, ?_⟩
    exact (A_real_le_U n).trans_lt hUlt
  have piece_good (n : ℕ) : Good (A n) (piece (A n)) :=
    piece_spec (A n) (A_admissible n)
  have t_subset_remainder (n : ℕ) : t ⊆ s \ A n := by
    intro x hxt
    refine ⟨(htRem hxt).1, ?_⟩
    intro hxA
    exact (htRem hxt).2 (A_subset_U n hxA)
  have htGap_n (n : ℕ) : μ.real t ≤ b - μ.real (A n) := by
    calc
      μ.real t ≤ b - μ.real U := htGap
      _ ≤ b - μ.real (A n) := sub_le_sub_left (A_real_le_U n) b
  have piece_lower (n : ℕ) : μ.real t / 2 ≤ μ.real (piece (A n)) := by
    have hdom := (piece_good n).2.2.2.2
      t (t_subset_remainder n) htMeas htPos (htGap_n n)
    linarith
  have A_measure_succ (n : ℕ) :
      μ.real (A (n + 1)) =
        μ.real (A n) + μ.real (piece (A n)) := by
    rw [A_succ]
    have hpSub : piece (A n) ⊆ s \ A n := (piece_good n).1
    have hpMeas : MeasurableSet (piece (A n)) := (piece_good n).2.1
    have hdisj : Disjoint (A n) (piece (A n)) := by
      rw [Set.disjoint_left]
      intro x hxA hxp
      exact (hpSub hxp).2 hxA
    exact measureReal_union hdisj hpMeas
  let δ : ℝ := μ.real t / 2
  have hδpos : 0 < δ := by simp only [δ]; linarith
  have A_growth (n : ℕ) : (n : ℝ) * δ ≤ μ.real (A n) := by
    induction n with
    | zero => simp [A_zero]
    | succ n ih =>
        rw [show μ.real (A (n + 1)) =
          μ.real (A n) + μ.real (piece (A n)) from A_measure_succ n]
        have hp := piece_lower n
        simp only [Nat.cast_add, Nat.cast_one]
        simp only [δ] at ih ⊢
        nlinarith
  obtain ⟨n, hn⟩ := Archimedean.arch (b + 1) hδpos
  have hn' : b + 1 ≤ (n : ℝ) * δ := by
    simpa [nsmul_eq_mul] using hn
  have hnb := (A_invariant n).2.2
  have hng := A_growth n
  linarith

/-- ENNReal form of Sierpiński's theorem: every extended-real target below
the finite mass of `s` is attained exactly.-/
theorem IsAtomlessMeasure.exists_subset_measure_eq
    {μ : Measure Ω} [IsFiniteMeasure μ] (hμ : IsAtomlessMeasure μ)
    {s : Set Ω} (hs : MeasurableSet s)
    {c : ℝ≥0∞} (hcs : c ≤ μ s) :
    ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧ μ t = c := by
  have hcTop : c ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ s) hcs
  have hcRealLe : c.toReal ≤ μ.real s := by
    exact (ENNReal.toReal_le_toReal hcTop (measure_ne_top μ s)).mpr hcs
  obtain ⟨t, hts, ht, htMeasure⟩ :=
    hμ.exists_subset_measureReal_eq hs ENNReal.toReal_nonneg hcRealLe
  refine ⟨t, hts, ht, ?_⟩
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top μ t) hcTop).mp
  simpa [Measure.real] using htMeasure

/-- **General Sierpiński divisibility theorem.** Every finite atomless measure
on an arbitrary measurable space is exactly divisible.-/
theorem hasExactDivisibility_of_atomless
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (hμ : IsAtomlessMeasure μ) :
    HasExactDivisibility μ := by
  intro s hs a ha0 ha1
  have hs0 : 0 ≤ μ.real s := ENNReal.toReal_nonneg
  have hab0 : 0 ≤ a * μ.real s := mul_nonneg ha0 hs0
  have habs : a * μ.real s ≤ μ.real s := by
    nlinarith
  obtain ⟨A, hAs, hA, hmeasure⟩ :=
    hμ.exists_subset_measureReal_eq hs hab0 habs
  exact ⟨A, hAs, hA, hmeasure⟩

/-- For finite measures, the project's elementary atomlessness predicate is
equivalent to exact measurable divisibility.-/
theorem hasExactDivisibility_iff_isAtomlessMeasure
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    HasExactDivisibility μ ↔ IsAtomlessMeasure μ := by
  exact ⟨HasExactDivisibility.isAtomlessMeasure,
    hasExactDivisibility_of_atomless⟩

/-- Every finite atomless measure admits finite measurable partitions with
arbitrary prescribed nonnegative real weights.-/
theorem IsAtomlessMeasure.exists_isMeasurableFinpartition_measureReal_eq
    {ι : Type*} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hμ : IsAtomlessMeasure μ)
    (s : Finset ι) (B : Set Ω) (hB : MeasurableSet B)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsum : ∑ i ∈ s, w i = 1) :
    ∃ A : ι → Set Ω, IsMeasurableFinpartition s B A ∧
      ∀ i ∈ s, μ.real (A i) = w i * μ.real B := by
  exact (hasExactDivisibility_of_atomless hμ)
    |>.exists_isMeasurableFinpartition_measureReal_eq
      s B hB w hw hsum

end RandomSetTheory
