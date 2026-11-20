import Tengoku.PshdLean.PshLines.PSHD.LineSections
import Tengoku.PshdLean.PshLines.DeficitConvolution
import Tengoku.PshdLean.PshLines.DeficitLocalization
import Tengoku.PshdLean.PshLines.TestLeviPairing
import Tengoku.PshdLean.PshLines.CompactDiscLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Distributional Levi positivity from line sections

Step 3 of Proposition 2.1 of `pshd-vibe`, first half. A Borel function which is
locally bounded above, nonnegative, and subharmonic on every affine complex-line
section of an open set is locally integrable there, and each of its
constant-direction Levi distributions is positive. Positivity comes from the
disc submean inequality on the complex lines: averaging the localized deficit
over circles in a fixed direction and pairing with a test function shows that
the pairing is superharmonic along that direction.
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions ContDiff

namespace PshLines.PSHD

/-- A function which is locally bounded above on an open set is bounded above
on each compact subset.
@isnad1 id=ex.3h4v.s6.4be894db8486 from=translated src=- shape=5197e22f vocab=f85932de
-/
theorem exists_upper_bound_of_isCompact {X : Type*} [PseudoMetricSpace X] {u : X → ℝ}
    {D K : Set X}
    (hbdd : ∀ p ∈ D, ∃ r > 0, BddAbove (u '' ball p r)) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ C : ℝ, ∀ x ∈ K, u x ≤ C := by
  refine hK.induction_on (p := fun s => ∃ C : ℝ, ∀ x ∈ s, u x ≤ C) ⟨0, by simp⟩
    (fun s t hst ⟨C, hC⟩ => ⟨C, fun x hx => hC x (hst hx)⟩)
    (fun s t ⟨C, hC⟩ ⟨C', hC'⟩ => ⟨max C C', fun x hx => hx.elim
      (fun hx => (hC x hx).trans (le_max_left _ _))
      (fun hx => (hC' x hx).trans (le_max_right _ _))⟩) ?_
  intro p hp
  obtain ⟨r, hr, C, hC⟩ := hbdd p (hKD hp)
  exact ⟨ball p r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds p hr),
    C, fun x hx => hC ⟨x, hx, rfl⟩⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A Borel function which is nonnegative and locally bounded above on an open
set is locally integrable there.
@isnad1 id=locallyi.4h4v.s7.a59eed4335aa from=translated src=- shape=96f97623 vocab=f50ed9af
-/
theorem locallyIntegrableOn_of_bddAbove {u : E → ℝ} {D : Set E} (hD : IsOpen D)
    (hu : Measurable u) (hpos : ∀ x ∈ D, 0 ≤ u x)
    (hbdd : ∀ p ∈ D, ∃ r > 0, BddAbove (u '' ball p r))
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ] :
    LocallyIntegrableOn u D μ := by
  rw [locallyIntegrableOn_iff hD.isLocallyClosed]
  intro K hKD hK
  obtain ⟨C, hC⟩ := exists_upper_bound_of_isCompact hbdd hK hKD
  refine Measure.integrableOn_of_bounded hK.measure_lt_top.ne
    hu.aestronglyMeasurable (M := C) ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  rw [Real.norm_of_nonneg (hpos x (hKD hx))]
  exact hC x hx

/-- **Distributional Levi positivity from line sections** (Step 3 of
Proposition 2.1). For a Borel function which is locally integrable, locally
bounded above and subharmonic on every connected component of every affine
complex-line section of an open set, every constant-direction Levi
distribution is positive.
@isnad1 id=hasnonne.4h4v.s8.d677148e9dc1 from=translated src=- shape=4d74c480 vocab=675c8068
-/
theorem LineSubharmonicOn.hasNonnegativeDistributionalLevi {Ω : Opens E} {u : E → ℝ}
    (hl : LineSubharmonicOn u Ω) (hu : Measurable u)
    (hbdd : ∀ p ∈ Ω, ∃ r > 0, BddAbove (u '' ball p r))
    (μ : Measure E) [μ.IsAddHaarMeasure] (huL : LocallyIntegrableOn u Ω μ) :
    HasNonnegativeDistributionalLevi (regularDistribution μ u huL) := by
  intro v φ hφn
  obtain ⟨R, hR, K, hK, hKΩ, hφK, hdiscs⟩ :=
    exists_compact_affineClosedDisc_family φ.hasCompactSupport Ω.isOpen φ.tsupport_subset v
  obtain ⟨C, hC⟩ := exists_upper_bound_of_isCompact hbdd hK hKΩ
  let f : E → ℝ := K.indicator (fun x => C - u x)
  have hf : LocallyIntegrable f μ := by
    simpa only [EReal.toReal_coe] using
      locallyIntegrable_indicator_realDeficit_of_isCompact (u := fun x => (u x : EReal))
        hK hKΩ (by simpa only [EReal.toReal_coe] using huL) C
  have hfn : ∀ x, 0 ≤ f x := fun x => by
    by_cases hx : x ∈ K
    · simpa [f, hx] using hC x hx
    · simp [f, hx]
  have hD : K.indicator (fun y => ((C : EReal) - (u y : EReal)).toENNReal) =
      fun y => ENNReal.ofReal (f y) := by
    funext y
    by_cases hy : y ∈ K
    · simp only [f, indicator_of_mem hy, ← EReal.coe_sub, EReal.real_coe_toENNReal]
    · simp [f, hy]
  have hDm : Measurable (K.indicator (fun y => ((C : EReal) - (u y : EReal)).toENNReal)) := by
    rw [hD]
    exact ((measurable_const.sub hu).indicator hK.measurableSet).ennreal_ofReal
  have hφ2 : ContDiff ℝ 2 (φ : E → ℝ) :=
    φ.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hpair := (hl.hasDiscSubmeanOn.mono hKΩ).integral_deficit_mul_leviForm_nonpos
    subset_rfl C (fun y hy => EReal.coe_le_coe_iff.mpr (hC y hy)) hDm
    (Filter.EventuallyEq.of_eq hD) hf hfn φ.hasCompactSupport hφ2 hφn v hR (by
      intro r hr x hx
      exact hdiscs x (subset_closure hx) r hr.2.le)
  change (∫ x, K.indicator (fun y => C - u y) x * leviForm φ x v ∂μ) ≤ 0 at hpair
  rw [integral_indicator_deficit_mul_leviForm_testFunction huL φ hφK C v] at hpair
  exact neg_nonpos.mp hpair

end PshLines.PSHD
