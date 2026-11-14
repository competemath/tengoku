import Tengoku.Piirrationalitymeasure.Formalization.ParameterSavingSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The four actual endpoint families of (6.17) and constancy between them. -/

namespace PiIrrationality

open MeasureTheory Set Filter
open scoped Topology

inductive SavingEndpointType
  | A | B | C | Q
  deriving DecidableEq

instance : Fintype SavingEndpointType :=
  ⟨{.A, .B, .C, .Q}, by intro T; cases T <;> simp⟩

noncomputable def savingEndpointSlope (a b c : ℝ) : SavingEndpointType → ℝ
  | .A => a
  | .B => b
  | .C => c
  | .Q => a + 2 * b - c

noncomputable def savingEndpointShift (z : ℝ × ℝ) : SavingEndpointType → ℝ
  | .A => 1 / 2 + z.1
  | .B => z.2
  | .C => 0
  | .Q => 1 / 2 + z.1 + 2 * z.2

noncomputable def savingEndpoint (a b c : ℝ) (z : ℝ × ℝ)
    (T : SavingEndpointType) (j : ℤ) : ℝ :=
  ((j : ℝ) - savingEndpointShift z T) / savingEndpointSlope a b c T

noncomputable def translatedSavingChi (a b c : ℝ) (z : ℝ × ℝ) (u : ℝ) : ℝ :=
  savingChi (a * u + z.1) (b * u + z.2) (c * u)

noncomputable def translatedSavingMeasure (a b c : ℝ) (z : ℝ × ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, translatedSavingChi a b c z u

theorem savingEndpoint_eq_iff {a b c : ℝ} {z : ℝ × ℝ} {T : SavingEndpointType}
    {j : ℤ} {u : ℝ} (hT : savingEndpointSlope a b c T ≠ 0) :
    u = savingEndpoint a b c z T j ↔
      savingEndpointSlope a b c T * u + savingEndpointShift z T = (j : ℝ) := by
  rw [savingEndpoint, eq_div_iff hT]
  constructor <;> intro h <;> linarith

theorem savingEndpoint_candidate_formulas (z : ℝ × ℝ) (j : ℤ) :
    savingEndpoint 1857 3714 5570 z .A j = ((j : ℝ) - 1 / 2 - z.1) / 1857 ∧
    savingEndpoint 1857 3714 5570 z .B j = ((j : ℝ) - z.2) / 3714 ∧
    savingEndpoint 1857 3714 5570 z .C j = (j : ℝ) / 5570 ∧
    savingEndpoint 1857 3714 5570 z .Q j =
      ((j : ℝ) - 1 / 2 - z.1 - 2 * z.2) / 3715 := by
  dsimp only [savingEndpoint, savingEndpointSlope, savingEndpointShift]
  exact ⟨by ring, rfl, by ring, by ring⟩

theorem savingChi_eventuallyEq_of_continuousAt {ι : Type*} [TopologicalSpace ι]
    {X Y Z : ι → ℝ} {u : ι} (hX : ContinuousAt X u) (hY : ContinuousAt Y u)
    (hZ : ContinuousAt Z u)
    (hA : X u + 1 / 2 ≠ (⌊X u + 1 / 2⌋ : ℝ))
    (hB : Y u ≠ (⌊Y u⌋ : ℝ)) (hC : Z u ≠ (⌊Z u⌋ : ℝ))
    (hneq : Int.fract (X u + 1 / 2) + 2 * Int.fract (Y u) ≠ Int.fract (Z u)) :
    (fun v => savingChi (X v) (Y v) (Z v)) =ᶠ[𝓝 u]
      (fun _ => savingChi (X u) (Y u) (Z u)) := by
  have hAcont := (continuousAt_fract hA).comp (f := fun v => X v + 1 / 2) (hX.add_const _)
  have hBcont := (continuousAt_fract hB).comp (f := Y) hY
  have hCcont := (continuousAt_fract hC).comp (f := Z) hZ
  have hcont := hAcont.add (hBcont.const_mul 2)
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · filter_upwards [hcont.eventually_lt hCcont hlt] with v hv
    exact (ite_eq_left hv).trans (ite_eq_left hlt).symm
  · filter_upwards [hCcont.eventually_lt hcont hgt] with v hv
    exact (ite_eq_right hv.not_gt).trans (ite_eq_right hgt.not_gt).symm

theorem translatedSavingChi_locally_constant {a b c : ℝ} {z : ℝ × ℝ} {u : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hq : a + 2 * b - c ≠ 0)
    (hu : ∀ T j, u ≠ savingEndpoint a b c z T j) :
    translatedSavingChi a b c z =ᶠ[𝓝 u] (fun _ => translatedSavingChi a b c z u) := by
  have hne (T : SavingEndpointType) (j : ℤ) :
      savingEndpointSlope a b c T * u + savingEndpointShift z T ≠ (j : ℝ) := by
    have hT : savingEndpointSlope a b c T ≠ 0 := by cases T <;> assumption
    exact fun he => hu T j ((savingEndpoint_eq_iff hT).mpr he)
  have hA : a * u + z.1 + 1 / 2 ≠ (⌊a * u + z.1 + 1 / 2⌋ : ℝ) := by
    simpa only [savingEndpointSlope, savingEndpointShift, add_left_comm, add_comm, add_assoc]
      using hne .A ⌊a * u + z.1 + 1 / 2⌋
  have hB : b * u + z.2 ≠ (⌊b * u + z.2⌋ : ℝ) := hne .B _
  have hC : c * u ≠ (⌊c * u⌋ : ℝ) := by
    simpa only [savingEndpointSlope, savingEndpointShift, add_zero] using hne .C ⌊c * u⌋
  have hneq : Int.fract (a * u + z.1 + 1 / 2) + 2 * Int.fract (b * u + z.2) ≠
      Int.fract (c * u) := by
    intro he
    apply hne .Q (⌊a * u + z.1 + 1 / 2⌋ + 2 * ⌊b * u + z.2⌋ - ⌊c * u⌋)
    dsimp [savingEndpointSlope, savingEndpointShift]
    simp only [Int.fract] at he
    push_cast
    nlinarith only [he]
  exact savingChi_eventuallyEq_of_continuousAt (by fun_prop) (by fun_prop)
    (by fun_prop) hA hB hC hneq

theorem savingEndpoint_affine (a b c : ℝ) (T : SavingEndpointType) (j : ℤ)
    (z v : ℝ × ℝ) (s : ℝ) :
    savingEndpoint a b c (z + s • v) T j = savingEndpoint a b c z T j -
      s * (savingEndpointShift v T - savingEndpointShift 0 T) / savingEndpointSlope a b c T := by
  cases T <;> dsimp [savingEndpoint, savingEndpointShift, savingEndpointSlope] <;> ring

theorem translatedSavingChi_constantOn_interval {a b c l r : ℝ} {z : ℝ × ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hq : a + 2 * b - c ≠ 0)
    (hend : ∀ u ∈ Ioo l r, ∀ T j, u ≠ savingEndpoint a b c z T j)
    {x y : ℝ} (hx : x ∈ Ioo l r) (hy : y ∈ Ioo l r) :
    translatedSavingChi a b c z x = translatedSavingChi a b c z y := by
  have hi : ContinuousOn (translatedSavingChi a b c z) (Ioo l r) := by
    intro u hu
    exact (continuousAt_const.congr_of_eventuallyEq
      (translatedSavingChi_locally_constant ha hb hc hq (hend u hu))).continuousWithinAt
  apply isPreconnected_Ioo.constant_of_mapsTo
    (T := ({0, 1} : Set ℝ)) (Set.toFinite _).isDiscrete hi ?_ hx hy
  intro u _
  unfold translatedSavingChi savingChi
  split_ifs <;> simp

theorem savingEndpoint_finite_on_interval {a b c : ℝ} (z : ℝ × ℝ)
    (T : SavingEndpointType) (hT : 0 < savingEndpointSlope a b c T) (l r : ℝ) :
    (Set.range (savingEndpoint a b c z T) ∩ Icc l r).Finite := by
  let m := savingEndpointSlope a b c T
  let d := savingEndpointShift z T
  apply ((finite_Icc ⌈m * l + d⌉ ⌊m * r + d⌋).image
    (savingEndpoint a b c z T)).subset
  rintro u ⟨⟨j, rfl⟩, hu⟩
  refine ⟨j, ⟨?_, ?_⟩, rfl⟩
  · apply Int.ceil_le.mpr
    have he := (savingEndpoint_eq_iff hT.ne').mp (rfl :
      savingEndpoint a b c z T j = savingEndpoint a b c z T j)
    have hl := mul_le_mul_of_nonneg_left hu.1 hT.le
    dsimp [m, d]
    linarith
  · apply Int.le_floor.mpr
    have he := (savingEndpoint_eq_iff hT.ne').mp (rfl :
      savingEndpoint a b c z T j = savingEndpoint a b c z T j)
    have hr := mul_le_mul_of_nonneg_left hu.2 hT.le
    dsimp [m, d]
    linarith

theorem savingEndpoints_finite_on_interval {a b c : ℝ} (z : ℝ × ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hq : 0 < a + 2 * b - c) (l r : ℝ) :
    (⋃ T, Set.range (savingEndpoint a b c z T) ∩ Icc l r).Finite := by
  apply Set.finite_iUnion
  intro T
  apply savingEndpoint_finite_on_interval
  cases T <;> assumption

theorem translatedSavingMeasure_candidate_zero :
    translatedSavingMeasure 1857 3714 5570 0 = (1724689 : ℝ) / 13797510 := by
  have hm : MeasurableSet primeSavingSet := by
    rw [primeSavingSet_eq_intervals]
    exact activeSavingCells.measurableSet_biUnion (fun _ _ => measurableSet_Ico)
  have hsub : primeSavingSet ⊆ Ico (0 : ℝ) 1 := fun _ hu => ⟨hu.1, hu.2.1⟩
  calc
    _ = ∫ u in Ico (0 : ℝ) 1, primeSavingSet.indicator (fun _ => (1 : ℝ)) u := by
      unfold translatedSavingMeasure
      rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Ico_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Ico
      intro u hu
      simpa only [translatedSavingChi, Prod.fst_zero, Prod.snd_zero, add_zero] using
        savingChi_candidate_indicator hu
    _ = ∫ u in primeSavingSet, (1 : ℝ) := by
      rw [setIntegral_indicator hm, inter_eq_right.mpr hsub]
    _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_one, primeSavingSet_volume_real]

end PiIrrationality
