import Tengoku.Seed.MeasureTheory.Measure.Prod
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Measurable selection from positive-measure closed real sections

A concrete essential-left-endpoint construction used in `pshd-vibe`, Lemma 1.3.
-/

open Set MeasureTheory

namespace PshLines.PSHD

/-- Rational upper cutoffs below which a real set has positive measure.-/
def positiveMeasureCuts (K : Set ℝ) : Set ℝ :=
  {t | ∃ r : ℚ, t = r ∧ 0 < volume (K ∩ Iio (r : ℝ))}

/-- The essential left endpoint, expressed using countably many cutoffs.-/
noncomputable def positiveMeasureEndpoint (K : Set ℝ) : ℝ :=
  sInf (positiveMeasureCuts K)

private theorem cuts_bddBelow {K : Set ℝ} {a : ℝ} (hK : K ⊆ Ici a) :
    BddBelow (positiveMeasureCuts K) := by
  refine ⟨a, ?_⟩
  rintro t ⟨r, rfl, hr⟩
  by_contra h
  have hempty : K ∩ Iio (r : ℝ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxr⟩
    exact (not_le_of_gt (lt_trans hxr (lt_of_not_ge h))) (hK hx)
  simp [hempty] at hr

private theorem cuts_nonempty {K : Set ℝ} {b : ℝ} (hK : K ⊆ Iic b)
    (hpos : 0 < volume K) : (positiveMeasureCuts K).Nonempty := by
  obtain ⟨r, hr⟩ := exists_rat_gt b
  refine ⟨r, r, rfl, ?_⟩
  have heq : K ∩ Iio (r : ℝ) = K := inter_eq_left.mpr fun x hx => lt_of_le_of_lt (hK hx) hr
  simpa [heq] using hpos

/-- The essential endpoint belongs to every closed bounded positive-measure set.-/
theorem positiveMeasureEndpoint_mem {K : Set ℝ} {a b : ℝ}
    (hclosed : IsClosed K) (hK : K ⊆ Icc a b) (hpos : 0 < volume K) :
    positiveMeasureEndpoint K ∈ K := by
  have hbelow := cuts_bddBelow (fun x hx => (hK hx).1)
  have hnonempty := cuts_nonempty (fun x hx => (hK hx).2) hpos
  let q := positiveMeasureEndpoint K
  by_contra hq
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl q hq
  obtain ⟨l, hl₁, hl₂⟩ := exists_rat_btwn (sub_lt_self q hε)
  obtain ⟨t, ht, htq⟩ := (csInf_lt_iff hbelow hnonempty).mp (show sInf (positiveMeasureCuts K) < q + ε by dsimp [q, positiveMeasureEndpoint]; linarith)
  obtain ⟨r, rfl, hr⟩ := ht
  have hlzero : volume (K ∩ Iio (l : ℝ)) = 0 := by
    by_contra hz
    have hm : (l : ℝ) ∈ positiveMeasureCuts K := ⟨l, rfl, lt_of_le_of_ne bot_le (Ne.symm hz)⟩
    have := csInf_le hbelow hm
    change q ≤ (l : ℝ) at this
    linarith
  have hsub : K ∩ Iio (r : ℝ) ⊆ K ∩ Iio (l : ℝ) := by
    rintro x ⟨hx, hxr⟩
    refine ⟨hx, ?_⟩
    by_contra hxl
    change ¬ x < (l : ℝ) at hxl
    change x < (r : ℝ) at hxr
    have hdist : dist x q < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact hball hdist hx
  have hm : volume (K ∩ Iio (r : ℝ)) ≤ volume (K ∩ Iio (l : ℝ)) := measure_mono hsub
  rw [hlzero] at hm
  exact (not_lt_of_ge hm) hr

/-- Positive-measure closed sections of a Borel relation in a fixed compact real
interval admit a measurable selector.-/
theorem exists_measurable_mem_of_closed_positive_sections
    {S : Type*} [MeasurableSpace S] {K : Set (S × ℝ)} {a b : ℝ}
    (hK : MeasurableSet K)
    (hclosed : ∀ s, IsClosed (Prod.mk s ⁻¹' K))
    (hbound : ∀ s, Prod.mk s ⁻¹' K ⊆ Icc a b)
    (hpos : ∀ s, 0 < volume (Prod.mk s ⁻¹' K)) :
    ∃ q : S → ℝ, Measurable q ∧ ∀ s, (s, q s) ∈ K := by
  refine ⟨fun s => positiveMeasureEndpoint (Prod.mk s ⁻¹' K), ?_, ?_⟩
  · apply measurable_of_Iio
    intro t
    have heq : {s | positiveMeasureEndpoint (Prod.mk s ⁻¹' K) < t} =
        ⋃ r : ℚ, {s | (r : ℝ) < t ∧ 0 < volume ((Prod.mk s ⁻¹' K) ∩ Iio (r : ℝ))} := by
      ext s
      simp only [mem_ofPred_eq, mem_iUnion]
      rw [positiveMeasureEndpoint, csInf_lt_iff
        (cuts_bddBelow (fun x hx => (hbound s hx).1))
        (cuts_nonempty (fun x hx => (hbound s hx).2) (hpos s))]
      constructor
      · rintro ⟨x, ⟨r, rfl, hr⟩, hrt⟩
        exact ⟨r, hrt, hr⟩
      · rintro ⟨r, hrt, hr⟩
        exact ⟨r, ⟨r, rfl, hr⟩, hrt⟩
    change MeasurableSet {s | positiveMeasureEndpoint (Prod.mk s ⁻¹' K) < t}
    rw [heq]
    apply MeasurableSet.iUnion
    intro r
    have hm : Measurable (fun s => volume ((Prod.mk s ⁻¹' K) ∩ Iio (r : ℝ))) := by
      exact measurable_measure_prodMk_left (hK.inter (measurable_snd measurableSet_Iio))
    exact (MeasurableSet.const _).inter (measurableSet_lt measurable_const hm)
  · intro s
    exact positiveMeasureEndpoint_mem (hclosed s) (hbound s) (hpos s)

end PshLines.PSHD
