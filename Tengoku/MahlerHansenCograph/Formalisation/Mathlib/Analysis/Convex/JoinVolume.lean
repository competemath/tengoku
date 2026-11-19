/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.Seed.Analysis.Convex.Join
import Tengoku.Seed.Analysis.Convex.Measure
import Tengoku.Seed.Analysis.Convex.EGauge
import Tengoku.Seed.Analysis.Convex.Topology
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Integral
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta
import Tengoku.Seed.MeasureTheory.Constructions.Pi
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Pointwise ENNReal
open Set MeasureTheory

universe u v

namespace MeasureTheory

/-!
## Coordinate-axis embeddings
-/

private def productAxisLeft (V : Type u) (W : Type v) :
    (V → ℝ) →ₗ[ℝ] ((V → ℝ) × (W → ℝ)) where
  toFun x := (x, 0)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro c x
    ext <;> simp

private def productAxisRight (V : Type u) (W : Type v) :
    (W → ℝ) →ₗ[ℝ] ((V → ℝ) × (W → ℝ)) where
  toFun y := (0, y)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro c x
    ext <;> simp

lemma convex_productAxisLeft_image
    {V : Type u} {W : Type v}
    (s : Set (V → ℝ)) (hs : Convex ℝ s) :
    Convex ℝ ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s) := by
  simpa [productAxisLeft] using
    hs.linear_image (productAxisLeft V W)

lemma convex_productAxisRight_image
    {V : Type u} {W : Type v}
    (t : Set (W → ℝ)) (ht : Convex ℝ t) :
    Convex ℝ ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t) := by
  simpa [productAxisRight] using
    ht.linear_image (productAxisRight V W)

lemma convex_convexJoin_productAxis
    {V : Type u} {W : Type v}
    (s : Set (V → ℝ)) (t : Set (W → ℝ))
    (hs : Convex ℝ s) (ht : Convex ℝ t) :
    Convex ℝ
      (convexJoin ℝ
        ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s)
        ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t)) := by
  exact
    (convex_productAxisLeft_image s hs).convexJoin
      (convex_productAxisRight_image t ht)

lemma nullMeasurableSet_convexJoin_productAxis
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (s : Set (V → ℝ)) (t : Set (W → ℝ))
    (hs : Convex ℝ s) (ht : Convex ℝ t) :
    NullMeasurableSet
      (convexJoin ℝ
        ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s)
        ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t))
      volume := by
  classical
  let μ : Measure ((V → ℝ) × (W → ℝ)) :=
    (volume : Measure (V → ℝ)).prod (volume : Measure (W → ℝ))
  let _ : μ.IsAddHaarMeasure := by
    dsimp [μ]
    exact Measure.prod.instIsAddHaarMeasure _ _
  have hμ := (convex_convexJoin_productAxis s t hs ht).nullMeasurableSet μ
  simpa only [μ, ← Measure.volume_eq_prod (V → ℝ) (W → ℝ)] using hμ

/-!
## Exact geometry of the coordinate-axis join
-/

lemma mem_convexJoin_productAxis_iff
    {V : Type u} {W : Type v}
    {s : Set (V → ℝ)} {t : Set (W → ℝ)}
    {z : (V → ℝ) × (W → ℝ)} :
    z ∈
        convexJoin ℝ
          ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s)
          ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t) ↔
      ∃ a b : ℝ,
        0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
          ∃ x ∈ s, ∃ y ∈ t, z = (a • x, b • y) := by
  rw [mem_convexJoin]
  constructor
  · rintro ⟨p, hp, q, hq, hz⟩
    rcases hp with ⟨x, hx, rfl⟩
    rcases hq with ⟨y, hy, rfl⟩
    change
      ∃ a b : ℝ,
        0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
          a • (x, (0 : W → ℝ)) +
              b • ((0 : V → ℝ), y) = z at hz
    rcases hz with ⟨a, b, ha, hb, hab, hz⟩
    refine ⟨a, b, ha, hb, hab, x, hx, y, hy, ?_⟩
    simpa using hz.symm
  · rintro ⟨a, b, ha, hb, hab, x, hx, y, hy, rfl⟩
    refine
      ⟨(x, (0 : W → ℝ)), ⟨x, hx, rfl⟩,
       ((0 : V → ℝ), y), ⟨y, hy, rfl⟩, ?_⟩
    change
      ∃ c d : ℝ,
        0 ≤ c ∧ 0 ≤ d ∧ c + d = 1 ∧
          c • (x, (0 : W → ℝ)) +
              d • ((0 : V → ℝ), y) =
            (a • x, b • y)
    refine ⟨a, b, ha, hb, hab, ?_⟩
    simp

lemma mem_convexJoin_productAxis_iff_exists_Icc
    {V : Type u} {W : Type v}
    {s : Set (V → ℝ)} {t : Set (W → ℝ)}
    {z : (V → ℝ) × (W → ℝ)} :
    z ∈
        convexJoin ℝ
          ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s)
          ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t) ↔
      ∃ r ∈ Set.Icc (0 : ℝ) 1,
        ∃ x ∈ s, ∃ y ∈ t, z = ((1 - r) • x, r • y) := by
  rw [mem_convexJoin_productAxis_iff]
  constructor
  · rintro ⟨a, b, ha, hb, hab, x, hx, y, hy, hz⟩
    refine ⟨b, ⟨hb, ?_⟩, x, hx, y, hy, ?_⟩
    · linarith
    · have ha' : a = 1 - b := by linarith
      simpa [ha'] using hz
  · rintro ⟨r, ⟨hr0, hr1⟩, x, hx, y, hy, hz⟩
    exact
      ⟨1 - r, r, sub_nonneg.mpr hr1, hr0, by ring,
       x, hx, y, hy, hz⟩

/-!
## Nested homothetic copies of a convex set containing zero
-/

private lemma smul_set_mono_of_convex_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E}
    (hs : Convex ℝ s) (h0s : (0 : E) ∈ s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a • s ⊆ b • s := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  by_cases hb : b = 0
  · have ha0 : a = 0 := by
      apply le_antisymm
      · simpa [hb] using hab
      · exact ha
    subst a
    subst b
    exact ⟨x, hx, by simp⟩
  · have hbpos : 0 < b := lt_of_le_of_ne (ha.trans hab) (Ne.symm hb)
    have hratio : a / b ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg ha hbpos.le
      · exact (div_le_one hbpos).2 hab
    refine ⟨(a / b) • x, hs.smul_mem_of_zero_mem h0s hx hratio, ?_⟩
    change b • ((a / b) • x) = a • x
    rw [smul_smul]
    field_simp

private lemma exists_smul_lt_of_mem_interior_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (h0s : (0 : E) ∈ s)
    {r : ℝ} (hr : 0 < r) {x : E} (hx : x ∈ interior (r • s)) :
    ∃ c : ℝ, 0 ≤ c ∧ c < r ∧ x ∈ c • s := by
  rw [interior_smul₀ (ne_of_gt hr)] at hx
  rcases hx with ⟨z, hz, rfl⟩
  by_cases hz0 : z = 0
  · subst z
    exact ⟨0, le_rfl, hr, ⟨0, h0s, by simp⟩⟩
  · rcases (Metric.isOpen_iff.mp isOpen_interior z hz) with
      ⟨ε, hε, hball⟩
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    let δ : ℝ := ε / (2 * ‖z‖)
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    let w : E := (1 + δ) • z
    have hwball : w ∈ Metric.ball z ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      change ‖(1 + δ) • z - z‖ < ε
      rw [add_smul, one_smul, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos hδ]
      dsimp [δ]
      have hn0 : ‖z‖ ≠ 0 := ne_of_gt hn
      calc
        ε / (2 * ‖z‖) * ‖z‖ = ε / 2 := by field_simp
        _ < ε := by linarith
    have hw : w ∈ s := interior_subset (hball hwball)
    refine ⟨r / (1 + δ), ?_, ?_, ⟨w, hw, ?_⟩⟩
    · positivity
    · exact (div_lt_iff₀ (by linarith : 0 < 1 + δ)).2 (by nlinarith)
    · dsimp [w]
      rw [smul_smul]
      field_simp

/-!
## The coefficient
-/

noncomputable def freeSumVolumeCoeff (a b : ℕ) : ℝ :=
  (a.factorial : ℝ) * (b.factorial : ℝ) /
    ((a + b).factorial : ℝ)

lemma freeSumVolumeCoeff_nonneg (a b : ℕ) :
    0 ≤ freeSumVolumeCoeff a b := by
  unfold freeSumVolumeCoeff
  positivity

lemma freeSumVolumeCoeff_pos (a b : ℕ) :
    0 < freeSumVolumeCoeff a b := by
  unfold freeSumVolumeCoeff
  positivity

@[simp] lemma freeSumVolumeCoeff_zero_right (a : ℕ) :
    freeSumVolumeCoeff a 0 = 1 := by
  simp [freeSumVolumeCoeff, Nat.factorial_ne_zero]

@[simp] lemma freeSumVolumeCoeff_zero_left (b : ℕ) :
    freeSumVolumeCoeff 0 b = 1 := by
  simp [freeSumVolumeCoeff, Nat.factorial_ne_zero]

/-!
## Fubini for a null-measurable subset of a Euclidean product

`Measure.prod_apply` asks for a measurable set.  A convex join is generally only
available to us as `NullMeasurableSet`, so replace it by `toMeasurable`, use
`prod_apply`, and transfer the a.e. equality to sections.
-/

private lemma measurable_measure_prodMk_preimage
    {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [SFinite ν] {s : Set (α × β)}
    (hs : MeasurableSet s) :
    Measurable (fun x : α => ν (Prod.mk x ⁻¹' s)) := by
  have hi : Measurable (s.indicator (fun _ => (1 : ENNReal))) :=
    Measurable.indicator measurable_const hs
  have hlin := hi.lintegral_prod_right' (ν := ν)
  convert hlin using 1
  funext x
  rw [← setLIntegral_one]
  rw [← lintegral_indicator
    (hs.preimage (measurable_prodMk_left (x := x)))]
  congr 1

private lemma ae_measure_prodMk_preimage_eq_zero_of_measure_eq_zero
    {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    {s : Set (α × β)} (hs : (μ.prod ν) s = 0) :
    ∀ᵐ x : α ∂μ, ν (Prod.mk x ⁻¹' s) = 0 := by
  let M : Set (α × β) := toMeasurable (μ.prod ν) s
  have hM : MeasurableSet M := measurableSet_toMeasurable _ _
  have hMzero : (μ.prod ν) M = 0 := by
    dsimp [M]
    rw [measure_toMeasurable]
    exact hs
  have hlin : ∫⁻ x : α, ν (Prod.mk x ⁻¹' M) ∂μ = 0 := by
    rw [← Measure.prod_apply hM, hMzero]
  have hmeas : Measurable (fun x : α => ν (Prod.mk x ⁻¹' M)) :=
    measurable_measure_prodMk_preimage ν hM
  have haeM := (lintegral_eq_zero_iff hmeas).mp hlin
  filter_upwards [haeM] with x hx
  apply measure_mono_null _ hx
  exact Set.preimage_mono (subset_toMeasurable (μ.prod ν) s)

/-- Fubini's formula for a null-measurable subset of a product measure.-/
lemma Measure.prod_apply_nullMeasurableSet
    {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    {s : Set (α × β)} (hs : NullMeasurableSet s (μ.prod ν)) :
    (μ.prod ν) s = ∫⁻ x : α, ν {y : β | (x, y) ∈ s} ∂μ := by
  let M : Set (α × β) := toMeasurable (μ.prod ν) s
  have hM : MeasurableSet M := measurableSet_toMeasurable _ _
  have hsM : s =ᵐ[μ.prod ν] M := by
    simpa [M] using hs.toMeasurable_ae_eq.symm
  have hsec :
      ∀ᵐ x : α ∂μ, (Prod.mk x ⁻¹' s) =ᵐ[ν] (Prod.mk x ⁻¹' M) := by
    rcases ae_eq_set.mp hsM with ⟨hsM, hMs⟩
    have hsMsec :=
      ae_measure_prodMk_preimage_eq_zero_of_measure_eq_zero μ ν hsM
    have hMssec :=
      ae_measure_prodMk_preimage_eq_zero_of_measure_eq_zero μ ν hMs
    filter_upwards [hsMsec, hMssec] with x hxsM hxMs
    apply ae_eq_set.mpr
    simpa only [Set.preimage_sdiff] using And.intro hxsM hxMs
  calc
    (μ.prod ν) s = (μ.prod ν) M := by
      dsimp [M]
      exact (measure_toMeasurable s).symm
    _ = ∫⁻ x : α, ν (Prod.mk x ⁻¹' M) ∂μ := Measure.prod_apply hM
    _ = ∫⁻ x : α, ν (Prod.mk x ⁻¹' s) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hsec] with x hx
      exact measure_congr hx.symm
    _ = ∫⁻ x : α, ν {y : β | (x, y) ∈ s} ∂μ := by rfl

lemma volume_eq_lintegral_fiber_of_nullMeasurableSet
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {J : Set ((V → ℝ) × (W → ℝ))}
    (hJ : NullMeasurableSet J volume) :
    volume J =
      ∫⁻ x : V → ℝ, volume {y : W → ℝ | (x, y) ∈ J} := by
  let M : Set ((V → ℝ) × (W → ℝ)) := toMeasurable volume J
  have hM : MeasurableSet M := by
    dsimp [M]
    exact measurableSet_toMeasurable _ _
  have hJM : J =ᵐ[volume] M := by
    simpa [M] using hJ.toMeasurable_ae_eq.symm
  have hJMprod := hJM
  rw [Measure.volume_eq_prod (V → ℝ) (W → ℝ)] at hJMprod
  have hsec :
      ∀ᵐ x : V → ℝ,
        (Prod.mk x ⁻¹' J) =ᵐ[volume] (Prod.mk x ⁻¹' M) := by
    rcases ae_eq_set.mp hJMprod with ⟨hJM, hMJ⟩
    have hJMsec :=
      ae_measure_prodMk_preimage_eq_zero_of_measure_eq_zero
        (volume : Measure (V → ℝ)) (volume : Measure (W → ℝ)) hJM
    have hMJsec :=
      ae_measure_prodMk_preimage_eq_zero_of_measure_eq_zero
        (volume : Measure (V → ℝ)) (volume : Measure (W → ℝ)) hMJ
    filter_upwards [hJMsec, hMJsec] with x hxJM hxMJ
    apply ae_eq_set.mpr
    simpa only [Set.preimage_sdiff] using And.intro hxJM hxMJ
  calc
    volume J = volume M := by
      dsimp [M]
      exact (measure_toMeasurable J).symm
    _ =
        ((volume : Measure (V → ℝ)).prod
          (volume : Measure (W → ℝ))) M := by
      rw [← Measure.volume_eq_prod (V → ℝ) (W → ℝ)]
    _ =
        ∫⁻ x : V → ℝ,
          volume (Prod.mk x ⁻¹' M) := by
      exact Measure.prod_apply hM
    _ =
        ∫⁻ x : V → ℝ,
          volume (Prod.mk x ⁻¹' J) := by
      apply lintegral_congr_ae
      filter_upwards [hsec] with x hx
      exact measure_congr hx.symm
    _ =
        ∫⁻ x : V → ℝ,
          volume {y : W → ℝ | (x, y) ∈ J} := by
      rfl

/-!
## A one-sided radial coordinate

For a convex body which need not absorb all directions, `egauge NNReal` is the
appropriate radial functional.  The `if` is essential: `ENNReal.top.toReal = 0`,
so without it points outside the positive cone would incorrectly get radius 1.
-/

private noncomputable def remainingRadius
    {V : Type u} [Fintype V]
    (s : Set (V → ℝ)) (x : V → ℝ) : ℝ :=
  if egauge NNReal s x < 1 then
    1 - (egauge NNReal s x).toReal
  else
    0

private lemma remainingRadius_nonneg
    {V : Type u} [Fintype V]
    (s : Set (V → ℝ)) (x : V → ℝ) :
    0 ≤ remainingRadius s x := by
  unfold remainingRadius
  split_ifs with h
  · have hle : (egauge NNReal s x).toReal ≤ (1 : ℝ) := by
      exact ENNReal.toReal_mono (by simp) (le_of_lt h)
    linarith
  · exact le_rfl

private lemma remainingRadius_le_one
    {V : Type u} [Fintype V]
    (s : Set (V → ℝ)) (x : V → ℝ) :
    remainingRadius s x ≤ 1 := by
  unfold remainingRadius
  split_ifs
  · have hnn : 0 ≤ (egauge NNReal s x).toReal :=
      ENNReal.toReal_nonneg
    linarith
  · norm_num

/-!
### Strict one-sided egauge sublevels

Mathematically:
  {x | egauge NNReal s x < r}
is the increasing union of `c • s` for `0 ≤ c < r`.  Convexity plus `0 ∈ s`
makes these homothetic copies nested.  Haar scaling gives the measure.

A practical formal proof can either:
  * exhaust `r` by a monotone rational/natural sequence `c_n ↑ r`, or
  * sandwich the strict sublevel between `interior (r • s)` and `r • s`
    and use `Convex.addHaar_frontier`.

The second route is shorter if the needed interior/homothety rewrites elaborate
smoothly; the first route is more elementary and robust.
-/

private lemma egauge_lt_ae_eq_smul
    {V : Type u} [Fintype V]
    (s : Set (V → ℝ))
    (hs : Convex ℝ s)
    (h0s : (0 : V → ℝ) ∈ s)
    {r : ℝ} (hr : 0 < r) :
    {x : V → ℝ | egauge NNReal s x < ENNReal.ofReal r} =ᵐ[volume]
      r • s := by
  classical
  let A : Set (V → ℝ) :=
    {x | egauge NNReal s x < ENNReal.ofReal r}
  let B : Set (V → ℝ) := r • s
  have hupper : A ⊆ B := by
    intro x hx
    rcases egauge_lt_iff.mp hx with ⟨c, hxc, hc⟩
    have hcr : (c : ℝ) < r := by
      change (c : ENNReal) < ENNReal.ofReal r at hc
      exact ENNReal.coe_lt_ofReal.mp hc
    apply smul_set_mono_of_convex_zero hs h0s c.property hcr.le
    simpa [NNReal.smul_def] using hxc
  have hlower : interior B ⊆ A := by
    intro x hx
    rcases exists_smul_lt_of_mem_interior_smul h0s hr hx with
      ⟨c, hc0, hcr, hxc⟩
    let cn : NNReal := ⟨c, hc0⟩
    apply egauge_lt_iff.mpr
    refine ⟨cn, ?_, ?_⟩
    · rcases hxc with ⟨z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      change (cn : ℝ) • z = c • z
      rfl
    · change (cn : ENNReal) < ENNReal.ofReal r
      rw [ENNReal.coe_lt_ofReal]
      exact hcr
  have hfront : volume (frontier B) = 0 := by
    exact (hs.smul r).addHaar_frontier volume
  have hBA : volume (B \ A) = 0 := by
    apply measure_mono_null _ hfront
    intro x hx
    rw [frontier]
    exact ⟨subset_closure hx.1, fun hxi => hx.2 (hlower hxi)⟩
  have hAB : volume (A \ B) = 0 := by
    rw [Set.sdiff_eq_empty.mpr hupper]
    simp
  exact ae_eq_set.mpr ⟨hAB, hBA⟩

private lemma nullMeasurableSet_egauge_lt
    {V : Type u} [Fintype V]
    (s : Set (V → ℝ))
    (hs : Convex ℝ s)
    (h0s : (0 : V → ℝ) ∈ s)
    {r : ℝ} (hr : 0 < r) :
    NullMeasurableSet
      {x : V → ℝ | egauge NNReal s x < ENNReal.ofReal r} volume := by
  have hscaled : NullMeasurableSet (r • s) volume :=
    (hs.smul r).nullMeasurableSet volume
  exact hscaled.congr (egauge_lt_ae_eq_smul s hs h0s hr).symm

private lemma volume_egauge_lt
    {V : Type u} [Fintype V]
    (s : Set (V → ℝ))
    (hs : Convex ℝ s)
    (h0s : (0 : V → ℝ) ∈ s)
    {r : ℝ} (hr : 0 < r) :
    volume
        {x : V → ℝ |
          egauge NNReal s x < ENNReal.ofReal r} =
      ENNReal.ofReal (r ^ Fintype.card V) * volume s := by
  have hae := egauge_lt_ae_eq_smul s hs h0s hr
  calc
    volume {x : V → ℝ | egauge NNReal s x < ENNReal.ofReal r} =
        volume (r • s) := measure_congr hae
    _ = ENNReal.ofReal (r ^ Module.finrank ℝ (V → ℝ)) * volume s := by
      exact Measure.addHaar_smul_of_nonneg volume hr.le s
    _ = ENNReal.ofReal (r ^ Fintype.card V) * volume s := by
      simp

/-!
## Tail distribution of the remaining radius

This is intentionally proved from `volume_egauge_lt`; it is the bridge from
one-sided convex geometry to the one-dimensional layer-cake integral.
-/

private lemma remainingRadius_gt_set
    {V : Type u} [Fintype V]
    (s : Set (V → ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    {x : V → ℝ | r < remainingRadius s x} =
      {x : V → ℝ |
        egauge NNReal s x < ENNReal.ofReal (1 - r)} := by
  have hpos : 0 < 1 - r := sub_pos.mpr hr1
  ext x
  unfold remainingRadius
  change
    (r < if egauge NNReal s x < 1 then
        1 - (egauge NNReal s x).toReal else 0) ↔ _
  split_ifs with hx
  · have hx_top : egauge NNReal s x ≠ ⊤ := ne_top_of_lt hx
    constructor
    · intro h
      have hreal : (egauge NNReal s x).toReal < 1 - r := by linarith
      exact
        (ENNReal.toReal_lt_toReal
          hx_top ENNReal.ofReal_ne_top).mp <| by
            simpa [ENNReal.toReal_ofReal hpos.le] using hreal
    · intro h
      have hreal : (egauge NNReal s x).toReal < 1 - r := by
        have h' :=
          (ENNReal.toReal_lt_toReal
            hx_top ENNReal.ofReal_ne_top).mpr h
        simpa [ENNReal.toReal_ofReal hpos.le] using h'
      linarith
  · constructor
    · intro h
      linarith
    · intro h
      exfalso
      apply hx
      have hle : ENNReal.ofReal (1 - r) ≤ 1 := by
        rw [ENNReal.ofReal_le_one]
        linarith
      exact lt_of_lt_of_le h hle

private lemma volume_remainingRadius_gt
    {V : Type u} [Fintype V]
    (s : Set (V → ℝ))
    (hs : Convex ℝ s)
    (h0s : (0 : V → ℝ) ∈ s)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    volume {x : V → ℝ | r < remainingRadius s x} =
      ENNReal.ofReal ((1 - r) ^ Fintype.card V) * volume s := by
  have hpos : 0 < 1 - r := sub_pos.mpr hr1
  rw [remainingRadius_gt_set s hr0 hr1]
  exact volume_egauge_lt s hs h0s hpos

private lemma volume_remainingRadius_gt_of_one_le
    {V : Type u} [Fintype V]
    (s : Set (V → ℝ))
    {r : ℝ} (hr : 1 ≤ r) :
    volume {x : V → ℝ | r < remainingRadius s x} = 0 := by
  have hempty :
      {x : V → ℝ | r < remainingRadius s x} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact not_lt_of_ge (le_trans (remainingRadius_le_one s x) hr)
  simp [hempty]

/-!
## Fibre volume

For fixed x, the free-sum fibre in W is squeezed between the strict and closed
one-sided radial sublevels of t at radius `remainingRadius s x`.

The upper inclusion follows immediately from the join representation and
`egauge_le_of_mem_smul`.

For the lower inclusion, strictness gives a little coefficient slack:
choose homothety coefficients for x and y whose sum is < 1, and absorb the
unused coefficient into the zero points of s/t.  Boundaries have zero volume.

The positive-dimensional assumption on W is only needed at radius zero, where
the fibre is at most `{0}` and hence has volume zero.
-/

private lemma volume_convexJoin_productAxis_fiber
    {V : Type u} {W : Type v}
    [Fintype V] [Fintype W]
    (s : Set (V → ℝ)) (t : Set (W → ℝ))
    (hs : Convex ℝ s) (ht : Convex ℝ t)
    (h0s : (0 : V → ℝ) ∈ s)
    (h0t : (0 : W → ℝ) ∈ t)
    (hb : 0 < Fintype.card W)
    (x : V → ℝ) :
    volume
        {y : W → ℝ |
          (x, y) ∈
            convexJoin ℝ
              ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s)
              ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t)} =
      ENNReal.ofReal
          ((remainingRadius s x) ^ Fintype.card W) *
        volume t := by
  classical
  let F : Set (W → ℝ) :=
    {y | (x, y) ∈
      convexJoin ℝ
        ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s)
        ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t)}
  by_cases hp : egauge NNReal s x < 1
  · let R : ℝ := 1 - (egauge NNReal s x).toReal
    have hp_top : egauge NNReal s x ≠ ⊤ := ne_top_of_lt hp
    have hp_real : (egauge NNReal s x).toReal < 1 := by
      have h' :=
        (ENNReal.toReal_lt_toReal hp_top (by simp)).mpr hp
      simpa using h'
    have hR : 0 < R := by
      dsimp [R]
      linarith
    have hupper : F ⊆ R • t := by
      intro y hy
      rcases mem_convexJoin_productAxis_iff.mp hy with
        ⟨a, b, ha, hb0, hab, sx, hsx, ty, hty, hxy⟩
      have hxas : x ∈ a • s :=
        ⟨sx, hsx, by simpa using (congrArg Prod.fst hxy).symm⟩
      let an : NNReal := ⟨a, ha⟩
      have hxan : x ∈ an • s := by
        rcases hxas with ⟨z, hz, rfl⟩
        refine ⟨z, hz, ?_⟩
        change (an : ℝ) • z = a • z
        rfl
      have hp_le : egauge NNReal s x ≤ (an : ENNReal) := by
        have h := egauge_le_of_mem_smul hxan
        change egauge NNReal s x ≤ (an : ENNReal) at h
        exact h
      have hp_real_le : (egauge NNReal s x).toReal ≤ a := by
        have h := ENNReal.toReal_mono (by simp) hp_le
        rw [ENNReal.coe_toReal] at h
        change (egauge NNReal s x).toReal ≤ a at h
        exact h
      have hbR : b ≤ R := by
        dsimp [R]
        linarith
      apply smul_set_mono_of_convex_zero ht h0t hb0 hbR
      exact ⟨ty, hty, by simpa using (congrArg Prod.snd hxy).symm⟩
    have hlower : interior (R • t) ⊆ F := by
      intro y hy
      rcases exists_smul_lt_of_mem_interior_smul h0t hR hy with
        ⟨c, hc0, hcR, hyc⟩
      have hc1 : c ≤ 1 := by
        have hp_nn := ENNReal.toReal_nonneg (a := egauge NNReal s x)
        dsimp [R] at hcR
        linarith
      have hpg :
          egauge NNReal s x < ENNReal.ofReal (1 - c) := by
        apply (ENNReal.toReal_lt_toReal hp_top ENNReal.ofReal_ne_top).mp
        rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hc1)]
        dsimp [R] at hcR
        linarith
      rcases egauge_lt_iff.mp hpg with ⟨a, hxa, ha⟩
      have haR : (a : ℝ) < 1 - c := by
        change (a : ENNReal) < ENNReal.ofReal (1 - c) at ha
        exact ENNReal.coe_lt_ofReal.mp ha
      have hxa_real : x ∈ (a : ℝ) • s := by
        simpa [NNReal.smul_def] using hxa
      have hxa_big : x ∈ (1 - c) • s :=
        smul_set_mono_of_convex_zero hs h0s a.property haR.le hxa_real
      rcases hxa_big with ⟨sx, hsx, hxsx⟩
      rcases hyc with ⟨ty, hty, hyty⟩
      apply mem_convexJoin_productAxis_iff.mpr
      refine ⟨1 - c, c, sub_nonneg.mpr hc1, hc0, by ring,
        sx, hsx, ty, hty, ?_⟩
      exact Prod.ext hxsx.symm hyty.symm
    have hfront : volume (frontier (R • t)) = 0 :=
      (ht.smul R).addHaar_frontier volume
    have hRF : volume ((R • t) \ F) = 0 := by
      apply measure_mono_null _ hfront
      intro y hy
      rw [frontier]
      exact ⟨subset_closure hy.1, fun hyi => hy.2 (hlower hyi)⟩
    have hFR : volume (F \ (R • t)) = 0 := by
      rw [Set.sdiff_eq_empty.mpr hupper]
      simp
    have hae : F =ᵐ[volume] R • t := ae_eq_set.mpr ⟨hFR, hRF⟩
    calc
      volume F = volume (R • t) := measure_congr hae
      _ = ENNReal.ofReal (R ^ Module.finrank ℝ (W → ℝ)) * volume t :=
        Measure.addHaar_smul_of_nonneg volume hR.le t
      _ = ENNReal.ofReal (R ^ Fintype.card W) * volume t := by simp
      _ = ENNReal.ofReal
          ((remainingRadius s x) ^ Fintype.card W) * volume t := by
        simp only [remainingRadius, hp, ↓reduceIte, R]
  · have hupper : F ⊆ ({0} : Set (W → ℝ)) := by
      intro y hy
      rcases mem_convexJoin_productAxis_iff.mp hy with
        ⟨a, b, ha, hb0, hab, sx, hsx, ty, hty, hxy⟩
      have hxas : x ∈ a • s :=
        ⟨sx, hsx, by simpa using (congrArg Prod.fst hxy).symm⟩
      let an : NNReal := ⟨a, ha⟩
      have hxan : x ∈ an • s := by
        rcases hxas with ⟨z, hz, rfl⟩
        refine ⟨z, hz, ?_⟩
        change (an : ℝ) • z = a • z
        rfl
      have hp_le : egauge NNReal s x ≤ (an : ENNReal) := by
        have h := egauge_le_of_mem_smul hxan
        change egauge NNReal s x ≤ (an : ENNReal) at h
        exact h
      have h1a : (1 : ℝ) ≤ a := by
        have h : (1 : ENNReal) ≤ (an : ENNReal) :=
          (le_of_not_gt hp).trans hp_le
        have h' := ENNReal.toReal_mono (by simp) h
        rw [ENNReal.coe_toReal] at h'
        change (1 : ℝ) ≤ a at h'
        exact h'
      have hbzero : b = 0 := by linarith
      have hy0 : y = 0 := by
        have := congrArg Prod.snd hxy
        simpa [hbzero] using this
      simp [hy0]
    have hvolF : volume F = 0 := by
      apply measure_mono_null hupper
      let _ : Nonempty W := Fintype.card_pos_iff.mp hb
      simp
    rw [hvolF]
    simp [remainingRadius, hp, hb.ne']

/-!
## Layer cake / beta integral

The tail distribution above says, for 0 ≤ r < 1,

  volume {x | r < remainingRadius s x}
    = (1-r)^a * volume s,

where a = card V, and the tail vanishes for r ≥ 1.

Applying
  `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`
with exponent b > 0 gives

  ∫ remainingRadius^b
    = b * ∫_0^1 (1-r)^a r^(b-1) dr * volume s.

The scalar integral is
  b * B(b, a+1) = a! b! / (a+b)!.

For natural exponents it may be easier in Lean to evaluate the scalar integral
by induction/integration-by-parts than to pass through `Complex.betaIntegral`;
both routes are mathematically equivalent.
-/

private lemma integral_beta_nat (a b : ℕ) (hb : 0 < b) :
    (∫ x : ℝ in 0..1, x ^ (b - 1) * (1 - x) ^ a) =
      (a.factorial : ℝ) * (b - 1).factorial /
        ((a + b).factorial : ℝ) := by
  have heval :=
    Complex.betaIntegral_eval_nat_add_one_right
      (u := (b : ℂ)) (by simpa using hb) a
  rw [Complex.betaIntegral.eq_1] at heval
  have hbsub : (b : ℂ) - 1 = ((b - 1 : ℕ) : ℂ) := by
    nth_rewrite 1 [← Nat.sub_add_cancel hb]
    push_cast
    ring
  have hasub : (a : ℂ) + 1 - 1 = (a : ℂ) := by ring
  rw [hbsub, hasub] at heval
  simp only [Complex.cpow_natCast] at heval
  have heval' :
      ((∫ x : ℝ in 0..1, x ^ (b - 1) * (1 - x) ^ a) : ℝ) =
        (a.factorial : ℂ) /
          ∏ j ∈ Finset.range (a + 1), ((b : ℂ) + (j : ℂ)) := by
    rw [← intervalIntegral.integral_ofReal]
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_natCast] using heval
  have hfac :
      (b - 1).factorial * b.ascFactorial (a + 1) =
        (a + b).factorial := by
    have h := Nat.factorial_mul_ascFactorial (b - 1) (a + 1)
    have hbpred : b - 1 + 1 = b := Nat.sub_add_cancel hb
    rw [hbpred] at h
    have harg : b - 1 + (a + 1) = a + b := by omega
    rw [harg] at h
    exact h
  have hprod_nat :
      (∏ j ∈ Finset.range (a + 1), (b + j)) =
        b.ascFactorial (a + 1) := by
    symm
    exact Nat.ascFactorial_eq_prod_range b (a + 1)
  have hprod_pos : 0 < b.ascFactorial (a + 1) := by
    rw [Nat.ascFactorial_eq_prod_range]
    apply Finset.prod_pos
    intro i hi
    omega
  have hprod_complex :
      (∏ j ∈ Finset.range (a + 1), ((b : ℂ) + (j : ℂ))) =
        (b.ascFactorial (a + 1) : ℂ) := by
    norm_cast
  have heval_real :
      (∫ x : ℝ in 0..1, x ^ (b - 1) * (1 - x) ^ a) =
        (a.factorial : ℝ) / b.ascFactorial (a + 1) := by
    apply Complex.ofReal_injective
    rw [heval', hprod_complex]
    exact
      (Complex.ofReal_div (a.factorial : ℝ)
        (b.ascFactorial (a + 1) : ℝ)).symm
  rw [heval_real]
  have hfac_real := congrArg (fun n : ℕ => (n : ℝ)) hfac
  norm_num only [Nat.cast_mul] at hfac_real
  field_simp
  nlinarith

private lemma remainingRadius_pow_lintegral
    {V : Type u} [Fintype V]
    (s : Set (V → ℝ))
    (hs : Convex ℝ s)
    (h0s : (0 : V → ℝ) ∈ s)
    {b : ℕ} (hb : 0 < b) :
    AEMeasurable
        (fun x : V → ℝ =>
          ENNReal.ofReal ((remainingRadius s x) ^ b))
        volume ∧
      (∫⁻ x : V → ℝ,
          ENNReal.ofReal ((remainingRadius s x) ^ b)) =
        ENNReal.ofReal
            (freeSumVolumeCoeff (Fintype.card V) b) *
          volume s := by
  classical
  have hf : AEMeasurable (remainingRadius s) volume := by
    have htails : ∀ r : ℝ,
        NullMeasurableSet (remainingRadius s ⁻¹' Set.Ioi r) volume := by
      intro r
      by_cases hr0 : r < 0
      · have hset :
            remainingRadius s ⁻¹' Set.Ioi r = Set.univ := by
          ext x
          simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
          exact lt_of_lt_of_le hr0 (remainingRadius_nonneg s x)
        rw [hset]
        exact nullMeasurableSet_univ
      · have hr0' : 0 ≤ r := le_of_not_gt hr0
        by_cases hr1 : r < 1
        · change NullMeasurableSet
            {x : V → ℝ | r < remainingRadius s x} volume
          rw [remainingRadius_gt_set s hr0' hr1]
          exact nullMeasurableSet_egauge_lt s hs h0s (sub_pos.mpr hr1)
        · have hr1' : 1 ≤ r := le_of_not_gt hr1
          have hset :
              remainingRadius s ⁻¹' Set.Ioi r = ∅ := by
            ext x
            simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_empty_iff_false,
              iff_false]
            exact not_lt_of_ge (le_trans (remainingRadius_le_one s x) hr1')
          rw [hset]
          exact nullMeasurableSet_empty
    apply NullMeasurable.aemeasurable
    apply measurable_of_Ioi
    exact htails
  have hpow : AEMeasurable
      (fun x : V → ℝ => ENNReal.ofReal ((remainingRadius s x) ^ b))
      volume := by
    exact (hf.pow aemeasurable_const).ennreal_ofReal
  refine ⟨hpow, ?_⟩
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hlayer :=
    lintegral_rpow_eq_lintegral_meas_lt_mul volume
      (Filter.Eventually.of_forall (remainingRadius_nonneg s)) hf hbR
  have hbsub : (b : ℝ) - 1 = ((b - 1 : ℕ) : ℝ) := by
    nth_rewrite 1 [← Nat.sub_add_cancel hb]
    push_cast
    ring
  have hlayer' :
      (∫⁻ x : V → ℝ,
          ENNReal.ofReal ((remainingRadius s x) ^ b)) =
        ENNReal.ofReal (b : ℝ) *
          ∫⁻ t : ℝ in Set.Ioi 0,
            volume {x : V → ℝ | t < remainingRadius s x} *
              ENNReal.ofReal (t ^ (b - 1)) := by
    simpa only [Real.rpow_natCast, hbsub] using hlayer
  have htail :
      (∫⁻ t : ℝ in Set.Ioi 0,
          volume {x : V → ℝ | t < remainingRadius s x} *
            ENNReal.ofReal (t ^ (b - 1))) =
        ∫⁻ t : ℝ in Set.Ioc 0 1,
          (ENNReal.ofReal ((1 - t) ^ Fintype.card V) * volume s) *
            ENNReal.ofReal (t ^ (b - 1)) := by
    rw [← lintegral_indicator measurableSet_Ioi,
      ← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr_ae
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by
      rw [ae_iff]
      have hset : {t : ℝ | ¬t ≠ 1} = {1} := by
        ext t
        simp
      rw [hset]
      simp
    filter_upwards [hne] with t ht
    simp only [Set.indicator]
    by_cases htI : t ∈ Set.Ioi (0 : ℝ)
    · simp only [htI, ↓reduceIte]
      by_cases htC : t ∈ Set.Ioc (0 : ℝ) 1
      · simp only [htC, ↓reduceIte]
        have ht1 : t < 1 := lt_of_le_of_ne htC.2 ht
        rw [volume_remainingRadius_gt s hs h0s htI.le ht1]
      · simp only [htC, ↓reduceIte]
        have h1t : 1 ≤ t := by
          by_contra hnot
          exact htC ⟨htI, (lt_of_not_ge hnot).le⟩
        rw [volume_remainingRadius_gt_of_one_le s h1t]
        simp
    · simp only [htI, ↓reduceIte]
      have htC : t ∉ Set.Ioc (0 : ℝ) 1 := fun h => htI h.1
      simp only [htC, ↓reduceIte]
  let g : ℝ → ENNReal := fun t =>
    ENNReal.ofReal
      (((1 - t) ^ Fintype.card V) * t ^ (b - 1))
  have hg : AEMeasurable g (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply Measurable.aemeasurable
    dsimp [g]
    fun_prop
  have hfactor :
      (∫⁻ t : ℝ in Set.Ioc 0 1,
          (ENNReal.ofReal ((1 - t) ^ Fintype.card V) * volume s) *
            ENNReal.ofReal (t ^ (b - 1))) =
        (∫⁻ t : ℝ in Set.Ioc 0 1, g t) * volume s := by
    rw [← lintegral_mul_const'' (volume s) hg]
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp [g]
    rw [ENNReal.ofReal_mul (pow_nonneg (sub_nonneg.mpr ht.2) _)]
    ac_rfl
  let q : ℝ → ℝ := fun t =>
    t ^ (b - 1) * (1 - t) ^ Fintype.card V
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hqint : Integrable q (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    exact (hqcont.intervalIntegrable 0 1).1
  have hqnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (pow_nonneg ht.1.le _) (pow_nonneg (sub_nonneg.mpr ht.2) _)
  have hscalar0 := ofReal_integral_eq_lintegral_ofReal hqint hqnonneg
  have hgq :
      (∫⁻ t : ℝ in Set.Ioc 0 1, g t) =
        ∫⁻ t : ℝ in Set.Ioc 0 1, ENNReal.ofReal (q t) := by
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp [g, q]
    apply congrArg ENNReal.ofReal
    ring
  have hscalar :
      (∫⁻ t : ℝ in Set.Ioc 0 1, g t) =
        ENNReal.ofReal
          ((Fintype.card V).factorial * (b - 1).factorial /
            ((Fintype.card V + b).factorial : ℝ)) := by
    rw [hgq, ← hscalar0]
    congr 1
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [integral_beta_nat (Fintype.card V) b hb]
  have hbfac : b.factorial = b * (b - 1).factorial := by
    have h := Nat.factorial_succ (b - 1)
    simpa [Nat.sub_add_cancel hb, Nat.mul_comm] using h
  have hcoeff :
      (b : ℝ) *
          ((Fintype.card V).factorial * (b - 1).factorial /
            ((Fintype.card V + b).factorial : ℝ)) =
        freeSumVolumeCoeff (Fintype.card V) b := by
    rw [freeSumVolumeCoeff, hbfac]
    push_cast
    ring
  calc
    (∫⁻ x : V → ℝ,
        ENNReal.ofReal ((remainingRadius s x) ^ b)) =
        ENNReal.ofReal (b : ℝ) *
          ∫⁻ t : ℝ in Set.Ioi 0,
            volume {x : V → ℝ | t < remainingRadius s x} *
              ENNReal.ofReal (t ^ (b - 1)) := hlayer'
    _ = ENNReal.ofReal (b : ℝ) *
        ((∫⁻ t : ℝ in Set.Ioc 0 1, g t) * volume s) := by
      rw [htail, hfactor]
    _ = ENNReal.ofReal (b : ℝ) *
        ENNReal.ofReal
          ((Fintype.card V).factorial * (b - 1).factorial /
            ((Fintype.card V + b).factorial : ℝ)) * volume s := by
      rw [hscalar]
      ac_rfl
    _ = ENNReal.ofReal
          (freeSumVolumeCoeff (Fintype.card V) b) * volume s := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ b), hcoeff]

/-!
## The nondegenerate ENNReal theorem

When W has positive dimension, Fubini over V followed by the fibre formula and
the radial integral is enough.  The zero-dimensional W case is handled
separately below using the empty-index Pi-volume normalization.
-/

private theorem volume_convexJoin_productAxis_ennreal_of_card_right_pos
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (s : Set (V → ℝ)) (t : Set (W → ℝ))
    (hs : Convex ℝ s) (ht : Convex ℝ t)
    (h0s : (0 : V → ℝ) ∈ s) (h0t : (0 : W → ℝ) ∈ t)
    (hb : 0 < Fintype.card W) :
    volume
        (convexJoin ℝ
          ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s)
          ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t)) =
      ENNReal.ofReal
          (freeSumVolumeCoeff (Fintype.card V) (Fintype.card W)) *
        volume s * volume t := by
  let J : Set ((V → ℝ) × (W → ℝ)) :=
    convexJoin ℝ
      ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s)
      ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t)
  have hJnull : NullMeasurableSet J volume := by
    dsimp [J]
    exact nullMeasurableSet_convexJoin_productAxis s t hs ht
  have hrad :=
    remainingRadius_pow_lintegral s hs h0s hb
  calc
    volume J =
        ∫⁻ x : V → ℝ,
          volume {y : W → ℝ | (x, y) ∈ J} := by
      exact volume_eq_lintegral_fiber_of_nullMeasurableSet hJnull
    _ =
        ∫⁻ x : V → ℝ,
          (ENNReal.ofReal
              ((remainingRadius s x) ^ Fintype.card W) *
            volume t) := by
      apply lintegral_congr
      intro x
      dsimp [J]
      exact
        volume_convexJoin_productAxis_fiber
          s t hs ht h0s h0t hb x
    _ =
        (∫⁻ x : V → ℝ,
          ENNReal.ofReal
            ((remainingRadius s x) ^ Fintype.card W)) *
          volume t := by
      exact lintegral_mul_const'' (volume t) hrad.1
    _ =
        (ENNReal.ofReal
            (freeSumVolumeCoeff
              (Fintype.card V) (Fintype.card W)) *
          volume s) *
          volume t := by
      rw [hrad.2]
    _ =
        ENNReal.ofReal
            (freeSumVolumeCoeff
              (Fintype.card V) (Fintype.card W)) *
          volume s * volume t := by
      rfl

/-!
## Zero-dimensional right factor

When `card W = 0`, `W → ℝ` is a singleton.  Since `0 ∈ t`, necessarily
`t = univ`, and its zero-dimensional Lebesgue volume is 1.  The free sum then
identifies with `s` sitting in the product with this singleton, so its product
volume is `volume s`.  The coefficient is also 1.

This is mathematically elementary, but the exact zero-dimensional Haar-volume
normalization lemmas are somewhat API-sensitive, so the whole edge branch is
isolated here rather than contaminating the positive-dimensional argument.
-/

private theorem volume_convexJoin_productAxis_ennreal_card_right_zero
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (s : Set (V → ℝ)) (t : Set (W → ℝ))
    (hs : Convex ℝ s) (_ht : Convex ℝ t)
    (h0s : (0 : V → ℝ) ∈ s) (h0t : (0 : W → ℝ) ∈ t)
    (hb : Fintype.card W = 0) :
    volume
        (convexJoin ℝ
          ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s)
          ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t)) =
      ENNReal.ofReal
          (freeSumVolumeCoeff (Fintype.card V) (Fintype.card W)) *
        volume s * volume t := by
  classical
  let hWempty : IsEmpty W := Fintype.card_eq_zero_iff.mp hb
  let _ : IsEmpty W := hWempty
  have ht_univ : t = Set.univ := by
    ext y
    constructor
    · intro
      simp
    · intro
      have hy : y = (0 : W → ℝ) := Subsingleton.elim _ _
      simpa [hy] using h0t
  have hTne :
      (((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t) :
        Set ((V → ℝ) × (W → ℝ))).Nonempty := by
    exact ⟨((0 : V → ℝ), (0 : W → ℝ)), ⟨0, h0t, rfl⟩⟩
  have hTS :
      ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t) ⊆
        ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s) := by
    rintro z ⟨y, hy, rfl⟩
    have hy0 : y = (0 : W → ℝ) := Subsingleton.elim _ _
    subst y
    exact ⟨0, h0s, rfl⟩
  have hSconv :
      Convex ℝ
        ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s) :=
    convex_productAxisLeft_image s hs
  have hjoin :
      convexJoin ℝ
          ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s)
          ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t) =
        ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s) := by
    apply Set.Subset.antisymm
    · exact convexJoin_subset (fun _ hx => hx) hTS hSconv
    · exact subset_convexJoin_left hTne
  have hSprod :
      ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s) =
        s ×ˢ (Set.univ : Set (W → ℝ)) := by
    ext z
    rcases z with ⟨x, y⟩
    have hy0 : y = (0 : W → ℝ) := Subsingleton.elim _ _
    subst y
    simp
  have hvolW :
      volume (Set.univ : Set (W → ℝ)) = 1 := by
    rw [Measure.volume_pi_eq_dirac]
    simp
  calc
    volume
        (convexJoin ℝ
          ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s)
          ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t))
        =
      volume
        ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s) := by
      rw [hjoin]
    _ = volume (s ×ˢ (Set.univ : Set (W → ℝ))) := by
      rw [hSprod]
    _ = volume s * volume (Set.univ : Set (W → ℝ)) := by
      rw [Measure.volume_eq_prod]
      exact Measure.prod_prod _ _
    _ = volume s := by
      rw [hvolW, mul_one]
    _ =
      ENNReal.ofReal
          (freeSumVolumeCoeff (Fintype.card V) (Fintype.card W)) *
        volume s * volume t := by
      rw [ht_univ, hb, freeSumVolumeCoeff_zero_right, hvolW]
      simp

/-!
## Strong ENNReal statement
-/

theorem volume_convexJoin_productAxis_ennreal
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (s : Set (V → ℝ)) (t : Set (W → ℝ))
    (hs : Convex ℝ s) (ht : Convex ℝ t)
    (h0s : (0 : V → ℝ) ∈ s) (h0t : (0 : W → ℝ) ∈ t)
    (_his : (interior s).Nonempty) (_hit : (interior t).Nonempty) :
    volume
        (convexJoin ℝ
          ((fun x : V → ℝ => (x, (0 : W → ℝ))) '' s)
          ((fun y : W → ℝ => ((0 : V → ℝ), y)) '' t)) =
      ENNReal.ofReal
          (freeSumVolumeCoeff (Fintype.card V) (Fintype.card W)) *
        volume s * volume t := by
  classical
  by_cases hb0 : Fintype.card W = 0
  · exact
      volume_convexJoin_productAxis_ennreal_card_right_zero
        s t hs ht h0s h0t hb0
  · exact
      volume_convexJoin_productAxis_ennreal_of_card_right_pos
        s t hs ht h0s h0t (Nat.pos_of_ne_zero hb0)

/--
The volume of the free sum of two full-dimensional convex bodies in
complementary finite coordinate spaces.

The factor is `a! b! / (a + b)!`, where `a` and `b` are the dimensions of the
two coordinate spaces. The sets are embedded as the two coordinate axes of
their product.-/
theorem volume_convexJoin_productAxis_toReal
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (s : Set (V → ℝ)) (t : Set (W → ℝ))
    (hs : Convex ℝ s) (ht : Convex ℝ t)
    (h0s : (0 : V → ℝ) ∈ s) (h0t : (0 : W → ℝ) ∈ t)
    (his : (interior s).Nonempty) (hit : (interior t).Nonempty) :
    (volume
      (convexJoin ℝ
        ((fun x : V → ℝ => (x, 0)) '' s)
        ((fun y : W → ℝ => (0, y)) '' t))).toReal =
      ((Fintype.card V).factorial : ℝ) *
      ((Fintype.card W).factorial : ℝ) /
      ((Fintype.card V + Fintype.card W).factorial : ℝ) *
      (volume s).toReal * (volume t).toReal := by
  have h :=
    volume_convexJoin_productAxis_ennreal
      s t hs ht h0s h0t his hit
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal
      (freeSumVolumeCoeff_nonneg
        (Fintype.card V) (Fintype.card W))] at h'
  simpa only [freeSumVolumeCoeff] using h'

end MeasureTheory
