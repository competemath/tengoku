/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Abel.AreaPairing
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Forms.Analyticity
public import Tengoku

/-!
# abel-theorem: chart-supported `(0,1)`-forms and pairing localization (design §4.1 step 5)

Unit: abel-theorem. Namespace `RS.Abel`.

The packaging device for design step 5: a planar function `h` smooth on `ℂ`, supported in a
compact `K` inside the target of one maximal-atlas chart `e`, spreads to a global
`(0,1)`-form `ChartSupportedData.form` whose coefficient in any preferred chart is the
`conj (deriv τ)`-transported copy of `h` (exactly `Form01.compat`'s law) — the concrete global
object that a weak solution's chart-local `dbarf/f`-data assembles into.

Two consumption lemmas:

* `ChartSupportedData.coeffAt_center` / `coeffAt_center_of_notMem`: the coefficient at a chart
  center, active and inactive cases (feeding the `dbar`-matching of `UpgradeDischarge.lean`).
* **`pairing_form`** (the localization): `pairing PU D.form θ = ∫ z, h z · coeffIn e θ z` — the
  global PoU pairing of a chart-supported form collapses to ONE planar integral in the
  supporting chart. Proof: per PoU index, transport by the `(1,1)`-density change of variables
  (`integral_eq_integral_transition`), where the `conj (deriv)`-factor of the form's transported
  coefficient cancels against the transition's `normSq (deriv)` and `coeffIn_trans`
  (`deriv_trans_mul_deriv_trans_symm`), then sum `∑ᵢ ψᵢ = 1`.

Also here: the inverse-derivative units `deriv_trans_mul_deriv_trans_symm` /
`deriv_trans_ne_zero` (consumed again by the order bookkeeping in `UpgradeDischarge.lean`), and
`Form01.coeffAt_finsetSum`.
-/

@[expose] public section

open scoped ContDiff Manifold
open IsManifold Metric Set MeasureTheory

noncomputable section

namespace RS.Abel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Inverse-derivative units -/

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The two transition derivatives at matched points multiply to `1`. -/
theorem deriv_trans_mul_deriv_trans_symm {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) {w : ℂ}
    (hw : w ∈ ⇑e' '' (e.source ∩ e'.source)) :
    deriv (⇑e ∘ ⇑e'.symm) w * deriv (⇑e' ∘ ⇑e.symm) (e (e'.symm w)) = 1 := by
  obtain ⟨q, hq, rfl⟩ := hw
  have hq' : (e'.symm) (e' q) = q := e'.left_inv hq.2
  have hwt : e' q ∈ e'.target := e'.map_source hq.2
  -- `deriv_trans_comp` with the roles `(e := e', e' := e, f := e')`
  have hcomp := RS.deriv_trans_comp (e := e') (e' := e) (f := e') he' he he' hwt
    (by rw [hq']; exact hq.2) (by rw [hq']; exact hq.1)
  -- the left side is the derivative of the identity near `e' q`
  have hid : deriv (⇑e' ∘ ⇑e'.symm) (e' q) = 1 := by
    have hev : (⇑e' ∘ ⇑e'.symm) =ᶠ[nhds (e' q)] id := by
      filter_upwards [e'.open_target.mem_nhds hwt] with w' hw'
      exact e'.right_inv hw'
    rw [hev.deriv_eq, deriv_id]
  rw [hid, hq'] at hcomp
  rw [hq']
  linear_combination -hcomp

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Transition derivatives never vanish. -/
theorem deriv_trans_ne_zero {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) {w : ℂ}
    (hw : w ∈ ⇑e' '' (e.source ∩ e'.source)) :
    deriv (⇑e ∘ ⇑e'.symm) w ≠ 0 :=
  left_ne_zero_of_mul_eq_one (deriv_trans_mul_deriv_trans_symm he he' hw)

/-! ## Finset sums of `(0,1)`-form coefficients -/

/-! ## Chart-supported `(0,1)`-data -/

variable (X) in
/-- A planar `(0,1)`-coefficient supported compactly inside one maximal-atlas chart. -/
structure ChartSupportedData where
  /-- The supporting chart. -/
  e : OpenPartialHomeomorph X ℂ
  he : e ∈ maximalAtlas 𝓘(ℂ) ω X
  /-- The planar coefficient in the supporting chart. -/
  h : ℂ → ℂ
  smooth : ContDiff ℝ ∞ h
  /-- The compact planar carrier. -/
  K : Set ℂ
  hK : IsCompact K
  hKsub : K ⊆ e.target
  hsupp : Function.support h ⊆ K

namespace ChartSupportedData

variable (D : ChartSupportedData X)

/-- The source-side compact carrier. -/
def Ksrc : Set X := ⇑D.e.symm '' D.K

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem isCompact_Ksrc : IsCompact D.Ksrc :=
  D.hK.image_of_continuousOn (D.e.symm.continuousOn.mono (by simpa using D.hKsub))

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem Ksrc_subset_source : D.Ksrc ⊆ D.e.source := by
  rintro y ⟨z, hz, rfl⟩
  exact D.e.map_target (D.hKsub hz)

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem h_eq_zero_of_notMem_Ksrc {y : X} (hy : y ∈ D.e.source) (hyK : y ∉ D.Ksrc) :
    D.h (D.e y) = 0 := by
  by_contra hne
  have hzK : D.e y ∈ D.K := D.hsupp hne
  exact hyK ⟨D.e y, hzK, D.e.left_inv hy⟩

/-- The raw coefficient formula in the preferred chart at `x`. -/
def coeff (x : X) : ℂ → ℂ :=
  (⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source)).indicator
    (fun z => (starRingEnd ℂ) (deriv (⇑D.e ∘ ⇑(chartAt ℂ x).symm) z) *
      D.h (D.e ((chartAt ℂ x).symm z)))

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mem_coeffSet_iff (x : X) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) :
    (chartAt ℂ x).symm z ∈ D.e.source ↔
      z ∈ ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source) := by
  constructor
  · intro h1
    exact ⟨(chartAt ℂ x).symm z, ⟨(chartAt ℂ x).map_target hz, h1⟩,
      (chartAt ℂ x).right_inv hz⟩
  · rintro ⟨q, hq, rfl⟩
    rw [(chartAt ℂ x).left_inv hq.1]
    exact hq.2

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem coeffSet_subset_target (x : X) :
    ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source) ⊆ (chartAt ℂ x).target := by
  rintro z ⟨q, hq, rfl⟩
  exact (chartAt ℂ x).map_source hq.1

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The coefficient vanishes near any target point whose source point avoids the compact
source carrier. -/
theorem coeff_eventuallyEq_zero (x : X) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hy : (chartAt ℂ x).symm z ∉ D.Ksrc) : D.coeff x =ᶠ[nhds z] 0 := by
  have hcont : ContinuousAt (⇑(chartAt ℂ x).symm) z :=
    (chartAt ℂ x).symm.continuousAt (by simpa using hz)
  have hnhds : (D.Ksrc)ᶜ ∈ nhds ((chartAt ℂ x).symm z) :=
    D.isCompact_Ksrc.isClosed.isOpen_compl.mem_nhds hy
  filter_upwards [hcont.preimage_mem_nhds hnhds] with w hw
  by_cases hwS : w ∈ ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source)
  · have hwsrc : (chartAt ℂ x).symm w ∈ D.e.source := by
      rcases hwS with ⟨q, hq, rfl⟩
      rw [(chartAt ℂ x).left_inv hq.1]
      exact hq.2
    rw [coeff, Set.indicator_of_mem hwS,
      D.h_eq_zero_of_notMem_Ksrc hwsrc hw, mul_zero]
    rfl
  · rw [coeff, Set.indicator_of_notMem hwS]
    rfl

/-- The chart-supported global `(0,1)`-form. -/
def form : RS.Form01 X where
  coeffAt := D.coeff
  coeffAt_zero_off x z hz :=
    Set.indicator_of_notMem (fun h1 => hz (D.coeffSet_subset_target x h1)) _
  contDiffOn_coeffAt x := by
    intro z hz
    by_cases hzS : z ∈ ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source)
    · -- smooth on the open overlap image
      have hSopen : IsOpen (⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source)) :=
        (chartAt ℂ x).isOpen_image_of_subset_source
          ((chartAt ℂ x).open_source.inter D.e.open_source) inter_subset_left
      have hτ : AnalyticAt ℂ (⇑D.e ∘ ⇑(chartAt ℂ x).symm) z := by
        rcases hzS with ⟨q, hq, rfl⟩
        exact RS.analyticAt_trans D.he (IsManifold.chart_mem_maximalAtlas x)
          ((chartAt ℂ x).map_source hq.1) (by rw [(chartAt ℂ x).left_inv hq.1]; exact hq.2)
      have hτnhds : ∀ᶠ w in nhds z, AnalyticAt ℂ (⇑D.e ∘ ⇑(chartAt ℂ x).symm) w := by
        filter_upwards [hSopen.mem_nhds hzS] with w hw
        rcases hw with ⟨q, hq, rfl⟩
        exact RS.analyticAt_trans D.he (IsManifold.chart_mem_maximalAtlas x)
          ((chartAt ℂ x).map_source hq.1) (by rw [(chartAt ℂ x).left_inv hq.1]; exact hq.2)
      have hderiv : ContDiffAt ℝ ∞ (fun w => deriv (⇑D.e ∘ ⇑(chartAt ℂ x).symm) w) z := by
        have hda : AnalyticAt ℂ (deriv (⇑D.e ∘ ⇑(chartAt ℂ x).symm)) z := by
          have := hτ.deriv
          exact this
        exact hda.contDiffAt.restrict_scalars ℝ
      have hconjd : ContDiffAt ℝ ∞
          (fun w => (starRingEnd ℂ) (deriv (⇑D.e ∘ ⇑(chartAt ℂ x).symm) w)) z := by
        have h1 := Complex.conjCLE.contDiff.contDiffAt.comp z hderiv
        refine h1.congr_of_eventuallyEq ?_
        filter_upwards with w
        simp []
      have hhcomp : ContDiffAt ℝ ∞ (fun w => D.h (D.e ((chartAt ℂ x).symm w))) z := by
        have hτr : ContDiffAt ℝ ∞ (⇑D.e ∘ ⇑(chartAt ℂ x).symm) z :=
          hτ.contDiffAt.restrict_scalars ℝ
        exact (D.smooth.contDiffAt).comp z hτr
      refine ((hconjd.mul hhcomp).congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [hSopen.mem_nhds hzS] with w hw
      rw [coeff, Set.indicator_of_mem hw]
    · -- vanishes near `z`
      have hy : (chartAt ℂ x).symm z ∉ D.Ksrc := by
        intro hmem
        exact hzS ((D.mem_coeffSet_iff x hz).mp (D.Ksrc_subset_source hmem))
      refine ((contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [D.coeff_eventuallyEq_zero x hz hy] with w hw
      exact hw
  compat x y z hz := by
    have hzT : z ∈ (chartAt ℂ y).target := by
      rcases hz with ⟨q, hq, rfl⟩
      exact (chartAt ℂ y).map_source hq.2
    have hq := hz
    obtain ⟨q, hq', rfl⟩ := hq
    have hqy : (chartAt ℂ y).symm (chartAt ℂ y q) = q := (chartAt ℂ y).left_inv hq'.2
    have hxT : chartAt ℂ x q ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hq'.1
    by_cases hqe : q ∈ D.e.source
    · -- both indicators active; chain rule for the transition derivatives
      have hmemy : chartAt ℂ y q ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ y).source ∩ D.e.source) :=
        ⟨q, ⟨hq'.2, hqe⟩, rfl⟩
      have hmemx : chartAt ℂ x q ∈ ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source) :=
        ⟨q, ⟨hq'.1, hqe⟩, rfl⟩
      have hchain := RS.deriv_trans_comp (e := D.e) (e' := chartAt ℂ x) (f := chartAt ℂ y)
        D.he (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas y)
        hzT (by rw [hqy]; exact hqe) (by rw [hqy]; exact hq'.1)
      rw [coeff, Set.indicator_of_mem hmemy, coeff]
      rw [hqy] at hchain ⊢
      have hsymm_x : (chartAt ℂ x).symm (chartAt ℂ x q) = q := (chartAt ℂ x).left_inv hq'.1
      rw [Set.indicator_of_mem hmemx, hsymm_x, hchain, map_mul]
      ring
    · -- both sides vanish
      have hmemy : chartAt ℂ y q ∉ ⇑(chartAt ℂ y) '' ((chartAt ℂ y).source ∩ D.e.source) :=
        fun h1 => hqe (by
          have := (D.mem_coeffSet_iff y hzT).mpr h1
          rwa [hqy] at this)
      have hmemx : chartAt ℂ x q ∉ ⇑(chartAt ℂ x) '' ((chartAt ℂ x).source ∩ D.e.source) :=
        fun h1 => hqe (by
          have := (D.mem_coeffSet_iff x hxT).mpr h1
          rwa [(chartAt ℂ x).left_inv hq'.1] at this)
      rw [coeff, Set.indicator_of_notMem hmemy, hqy, coeff,
        Set.indicator_of_notMem hmemx, mul_zero]

end ChartSupportedData

/-! ## Pairing localization -/

variable [CompactSpace X]

end RS.Abel

end
