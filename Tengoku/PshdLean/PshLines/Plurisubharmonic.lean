import Tengoku.Seed.MeasureTheory.Integral.CircleAverage
import Tengoku.Seed.Topology.Semicontinuity.Basic
import Tengoku.Seed.Topology.Instances.EReal.Lemmas
import Tengoku.PshdLean.PshLines.GluingTopology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extended-real local plurisubharmonic functions

The submean inequality is expressed by integrating the nonnegative deficit
`C - u` below a finite upper bound on a closed complex disc. Thus a pole is
never sent to `toReal`, and no difference of two infinite integrals occurs.
The raw disc condition is only used together with upper semicontinuity and
the exclusion of positive infinity. Identically negative infinity is allowed.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace PshLines

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The image of a closed complex disc under a complex affine line.-/
def affineClosedDisc (x v : E) (r : ℝ) : Set E :=
  (fun z : ℂ => x + z • v) '' closedBall 0 r

/-- Angular integral of a nonnegative extended-real deficit.-/
noncomputable def circleDeficit (u : E → EReal) (x v : E) (r C : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 (2 * Real.pi),
    ((C : EReal) - u (x + circleMap 0 r t • v)).toENNReal

/-- Disc submean inequalities, tested below every real upper bound on the disc.-/
def HasDiscSubmeanOn (u : E → EReal) (U : Set E) : Prop :=
  ∀ (x v : E) (r : ℝ), 0 < r → affineClosedDisc x v r ⊆ U →
    ∀ C : ℝ, (∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal)) →
      circleDeficit u x v r C ≤
        ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - u x).toENNReal

/-- The complete disc criterion; its regularity fields prevent vacuous tests.-/
structure DiscPshOn (u : E → EReal) (U : Set E) : Prop where
  ne_top : ∀ x ∈ U, u x ≠ ⊤
  upperSemicontinuousOn : UpperSemicontinuousOn u U
  submean : HasDiscSubmeanOn u U

/-- A germ satisfying the extended-real plurisubharmonic disc criterion.-/
def PlurisubharmonicAt (u : E → EReal) (x : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ DiscPshOn u U

/-- Plurisubharmonicity is a local property; the value `⊥` is permitted.
On a nonopen set this means ambient germs at its points, not an intrinsic
notion on an arbitrary closed subset.-/
def PlurisubharmonicOn (u : E → EReal) (U : Set E) : Prop :=
  ∀ x ∈ U, PlurisubharmonicAt u x

/--
@isnad1 id=mem.1h4v.s5.896fbfd38a3a from=translated src=- shape=fde5a954 vocab=aa490a00
-/
theorem center_mem_affineClosedDisc (x v : E) {r : ℝ} (hr : 0 ≤ r) :
    x ∈ affineClosedDisc x v r := by
  refine ⟨0, ?_, by simp⟩
  simpa using hr

/--
@isnad1 id=mem.1h5v.s7.fd96b868cdaf from=translated src=- shape=1db1c569 vocab=a64d7323
-/
theorem circle_mem_affineClosedDisc (x v : E) {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    x + circleMap 0 r t • v ∈ affineClosedDisc x v r := by
  refine ⟨circleMap 0 r t, ?_, rfl⟩
  exact sphere_subset_closedBall (circleMap_mem_sphere 0 hr t)

/--
@isnad1 id=iscompac.0h4v.s5.4b6bc32afbcc from=translated src=- shape=eccf1155 vocab=a802be55
-/
theorem isCompact_affineClosedDisc (x v : E) (r : ℝ) :
    IsCompact (affineClosedDisc x v r) := by
  apply (isCompact_closedBall (0 : ℂ) r).image
  fun_prop

/-- Compact discs have finite upper bounds, including discs contained in poles.
@isnad1 id=ex.3h6v.s6.73af372446f4 from=translated src=- shape=37da165a vocab=036c9997
-/
theorem DiscPshOn.exists_disc_upper_bound {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (x v : E) {r : ℝ} (hr : 0 ≤ r)
    (hD : affineClosedDisc x v r ⊆ U) :
    ∃ C : ℝ, ∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal) := by
  obtain ⟨y, hy, hmax⟩ := (hu.upperSemicontinuousOn.mono hD).exists_isMaxOn
    ⟨x, center_mem_affineClosedDisc x v hr⟩ (isCompact_affineClosedDisc x v r)
  obtain ⟨C, hC, _⟩ := EReal.exists_rat_btwn_of_lt (lt_top_iff_ne_top.mpr (hu.ne_top y (hD hy)))
  exact ⟨C, fun z hz => (hmax hz).trans hC.le⟩

/--
@isnad1 id=hasdiscs.2h4v.s5.8574ae990131 from=translated src=- shape=79164061 vocab=e17dbc21
-/
theorem HasDiscSubmeanOn.mono {u : E → EReal} {U V : Set E}
    (hu : HasDiscSubmeanOn u U) (hVU : V ⊆ U) : HasDiscSubmeanOn u V := by
  intro x v r hr hD C hC
  exact hu x v r hr (hD.trans hVU) C hC

/--
@isnad1 id=discpsho.2h4v.s5.9a413701a48a from=translated src=- shape=79164061 vocab=0d48ed7f
-/
theorem DiscPshOn.mono {u : E → EReal} {U V : Set E}
    (hu : DiscPshOn u U) (hVU : V ⊆ U) : DiscPshOn u V :=
  ⟨fun x hx => hu.ne_top x (hVU hx), hu.upperSemicontinuousOn.mono hVU,
    hu.submean.mono hVU⟩

/-- Larger potentials have smaller deficits, without any finiteness premise.
@isnad1 id=le.1h7v.s8.11bb7e7a668b from=translated src=- shape=e401ff7a vocab=44baa51e
-/
theorem circleDeficit_antitone {u w : E → EReal} (x v : E) (r C : ℝ)
    (huw : ∀ t : ℝ, u (x + circleMap 0 r t • v) ≤
      w (x + circleMap 0 r t • v)) :
    circleDeficit w x v r C ≤ circleDeficit u x v r C := by
  unfold circleDeficit
  apply lintegral_mono
  intro t
  exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl (huw t))

/--
@isnad1 id=hasdiscs.2h4v.s6.b5520bff2941 from=translated src=- shape=1824acee vocab=cc82557d
-/
theorem HasDiscSubmeanOn.max {u w : E → EReal} {U : Set E}
    (hu : HasDiscSubmeanOn u U) (hw : HasDiscSubmeanOn w U) :
    HasDiscSubmeanOn (fun x => Max.max (u x) (w x)) U := by
  intro x v r hr hD C hC
  have hCu : ∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal) :=
    fun y hy => (le_max_left _ _).trans (hC y hy)
  have hCw : ∀ y ∈ affineClosedDisc x v r, w y ≤ (C : EReal) :=
    fun y hy => (le_max_right _ _).trans (hC y hy)
  rcases le_total (u x) (w x) with h | h
  · have hmono := circleDeficit_antitone (u := w)
      (w := fun y => Max.max (u y) (w y)) x v r C (fun _ => le_max_right _ _)
    simpa only [max_eq_right h] using hmono.trans (hw x v r hr hD C hCw)
  · have hmono := circleDeficit_antitone (u := u)
      (w := fun y => Max.max (u y) (w y)) x v r C (fun _ => le_max_left _ _)
    simpa only [max_eq_left h] using hmono.trans (hu x v r hr hD C hCu)

/--
@isnad1 id=discpsho.2h4v.s6.45aa123f1a22 from=translated src=- shape=1824acee vocab=fea40a87
-/
theorem DiscPshOn.max {u w : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (hw : DiscPshOn w U) :
    DiscPshOn (fun x => Max.max (u x) (w x)) U := by
  refine ⟨?_, hu.upperSemicontinuousOn.sup hw.upperSemicontinuousOn,
    hu.submean.max hw.submean⟩
  intro x hx
  exact ne_of_lt (max_lt (lt_top_iff_ne_top.mpr (hu.ne_top x hx))
    (lt_top_iff_ne_top.mpr (hw.ne_top x hx)))

/--
@isnad1 id=plurisub.2h3v.s5.61d0bfea3f5b from=translated src=- shape=6db4a69f vocab=b358ce25
-/
theorem DiscPshOn.plurisubharmonicOn {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (hU : IsOpen U) : PlurisubharmonicOn u U :=
  fun _ hx => ⟨U, hU, hx, hu⟩

/--
@isnad1 id=plurisub.2h4v.s6.510f0a2b29cd from=translated src=- shape=7c6844ca vocab=574bda93
-/
theorem PlurisubharmonicAt.max {u w : E → EReal} {x : E}
    (hu : PlurisubharmonicAt u x) (hw : PlurisubharmonicAt w x) :
    PlurisubharmonicAt (fun y => Max.max (u y) (w y)) x := by
  obtain ⟨U, hU, hxU, hu⟩ := hu
  obtain ⟨V, hV, hxV, hw⟩ := hw
  exact ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩,
    (hu.mono inter_subset_left).max (hw.mono inter_subset_right)⟩

/--
@isnad1 id=plurisub.2h4v.s6.3d2e3975ada5 from=translated src=- shape=1824acee vocab=690c1604
-/
theorem PlurisubharmonicOn.max {u w : E → EReal} {U : Set E}
    (hu : PlurisubharmonicOn u U) (hw : PlurisubharmonicOn w U) :
    PlurisubharmonicOn (fun x => Max.max (u x) (w x)) U :=
  fun x hx => (hu x hx).max (hw x hx)

/--
@isnad1 id=plurisub.2h4v.s5.a3e22cacf478 from=translated src=- shape=79164061 vocab=f33e333d
-/
theorem PlurisubharmonicOn.mono {u : E → EReal} {U V : Set E}
    (hu : PlurisubharmonicOn u U) (hVU : V ⊆ U) : PlurisubharmonicOn u V :=
  fun x hx => hu x (hVU hx)

/-- The submean condition is unchanged by equality on its domain.
@isnad1 id=hasdiscs.2h4v.s5.85a927fee51c from=translated src=- shape=1d74f7e5 vocab=9f3b5433
-/
theorem HasDiscSubmeanOn.congr {u w : E → EReal} {U : Set E}
    (hu : HasDiscSubmeanOn u U) (heq : EqOn u w U) : HasDiscSubmeanOn w U := by
  intro x v r hr hD C hC
  have hx : x ∈ U := hD (center_mem_affineClosedDisc x v hr.le)
  have hcircle : circleDeficit u x v r C = circleDeficit w x v r C := by
    apply lintegral_congr
    intro t
    rw [heq (hD (circle_mem_affineClosedDisc x v hr.le t))]
  rw [← hcircle, ← heq hx]
  exact hu x v r hr hD C (fun y hy => (heq (hD hy)).trans_le (hC y hy))

/--
@isnad1 id=discpsho.2h4v.s5.68ae521f67f7 from=translated src=- shape=1d74f7e5 vocab=97bcb0e5
-/
theorem DiscPshOn.congr {u w : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (heq : EqOn u w U) : DiscPshOn w U := by
  refine ⟨fun x hx => (heq hx) ▸ hu.ne_top x hx, ?_, hu.submean.congr heq⟩
  intro x hx
  apply (hu.upperSemicontinuousOn x hx).congr_of_eventuallyEq hx
  filter_upwards [self_mem_nhdsWithin] with y hy
  intro c
  rw [heq hy]

/-- Plurisubharmonicity depends on the actual germ, including pole values.
@isnad1 id=plurisub.2h4v.s5.a74759b57c19 from=translated src=- shape=fd4fa65c vocab=c346ff00
-/
theorem PlurisubharmonicAt.congr {u w : E → EReal} {x : E}
    (hu : PlurisubharmonicAt u x) (heq : u =ᶠ[𝓝 x] w) :
    PlurisubharmonicAt w x := by
  obtain ⟨U, hU, hxU, hu⟩ := hu
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp heq
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  exact (hu.mono inter_subset_left).congr (fun _ hy => hVsub hy.2)

/--
@isnad1 id=ne.1h3v.s5.3b08cd191bde from=translated src=- shape=d19eb6be vocab=2de0d5ae
-/
theorem PlurisubharmonicAt.ne_top {u : E → EReal} {x : E}
    (hu : PlurisubharmonicAt u x) : u x ≠ ⊤ := by
  obtain ⟨_, _, hx, hu⟩ := hu
  exact hu.ne_top x hx

/--
@isnad1 id=uppersem.1h3v.s5.d6bfd809d01d from=translated src=- shape=7a8421d0 vocab=6b8653aa
-/
theorem PlurisubharmonicAt.upperSemicontinuousAt {u : E → EReal} {x : E}
    (hu : PlurisubharmonicAt u x) : UpperSemicontinuousAt u x := by
  obtain ⟨U, hU, hx, hu⟩ := hu
  intro c hc
  have h := hu.upperSemicontinuousOn x hx c hc
  rwa [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hx)] at h

/-- The circle-deficit expression has the expected value for every constant,
including negative infinity.
@isnad1 id=eq.0h6v.s6.15ed86a9dcbe from=translated src=- shape=e1bf220d vocab=94c80cc5
-/
theorem circleDeficit_const (a : EReal) (x v : E) (r C : ℝ) :
    circleDeficit (fun _ => a) x v r C =
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - a).toENNReal := by
  simp [circleDeficit, mul_comm]

/--
@isnad1 id=discpsho.1h3v.s5.ac9424a2c52c from=translated src=- shape=a914a98a vocab=8c95167c
-/
theorem discPshOn_const (a : EReal) (ha : a ≠ ⊤) (U : Set E) :
    DiscPshOn (fun _ => a) U := by
  refine ⟨fun _ _ => ha, upperSemicontinuousOn_const, ?_⟩
  intro x v r _ _ C _
  exact (circleDeficit_const a x v r C).le

/--
@isnad1 id=plurisub.1h3v.s5.736b2ae0f706 from=translated src=- shape=89b5a07e vocab=2de0d5ae
-/
theorem plurisubharmonicAt_const (a : EReal) (ha : a ≠ ⊤) (x : E) :
    PlurisubharmonicAt (fun _ => a) x :=
  ⟨univ, isOpen_univ, mem_univ x, discPshOn_const a ha univ⟩

/-- Actual PSH stability for the collar construction already used in the
topological module. This does not assert a current correspondence.
@isnad1 id=plurisub.5h5v.s6.b4949f26e1f8 from=translated src=- shape=9da60d4b vocab=219256d0
-/
theorem gluedMax_plurisubharmonic {U U' : Set E} {u w : E → EReal}
    (hU : IsOpen U) (hclosure : closure U' ⊆ U)
    (hcollar : ∀ x ∈ U \ U', u x ≤ w x)
    (hu : PlurisubharmonicOn u U) (hw : PlurisubharmonicOn w univ) :
    PlurisubharmonicOn (gluedMax U u w) univ := by
  intro x _
  by_cases hx : x ∈ U
  · exact ((hu x hx).max (hw x (mem_univ x))).congr
      (gluedMax_eventually_eq_max hU hx).symm
  · exact (hw x (mem_univ x)).congr
      (gluedMax_eventually_eq_global hclosure hcollar hx).symm

/-- The angular restriction in every admissible disc is genuinely measurable.
@isnad1 id=measurab.3h6v.s7.6f9087e0e580 from=translated src=- shape=ef490eb6 vocab=e1b4ae14
-/
theorem DiscPshOn.measurable_circle {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (x v : E) {r : ℝ} (hr : 0 ≤ r)
    (hD : affineClosedDisc x v r ⊆ U) :
    Measurable (fun t : ℝ => u (x + circleMap 0 r t • v)) := by
  have hsc : UpperSemicontinuousOn (fun t : ℝ => u (x + circleMap 0 r t • v)) univ :=
    hu.upperSemicontinuousOn.comp (by fun_prop)
      (fun t _ => hD (circle_mem_affineClosedDisc x v hr t))
  exact (upperSemicontinuousOn_univ_iff.mp hsc).measurable

/--
@isnad1 id=measurab.3h7v.s7.5bb9223c8d43 from=translated src=- shape=8329eaac vocab=a67ba198
-/
theorem DiscPshOn.measurable_circle_deficit {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (x v : E) {r : ℝ} (hr : 0 ≤ r)
    (hD : affineClosedDisc x v r ⊆ U) (C : ℝ) :
    Measurable (fun t : ℝ => ((C : EReal) - u (x + circleMap 0 r t • v)).toENNReal) := by
  have hsub : Measurable (fun z : EReal => (C : EReal) - z) :=
    EReal.measurable_of_measurable_real (by
      simpa only [Pi.sub_apply, id_eq, EReal.coe_sub] using
        ((measurable_const : Measurable (fun _ : ℝ => C)).sub measurable_id).coe_real_ereal)
  exact (hsub.comp (hu.measurable_circle x v hr hD)).ereal_toENNReal

/-- Raising a finite majorant adds an ordinary finite constant to its deficit.
@isnad1 id=eq.2h3v.s6.492685e8a732 from=translated src=- shape=ebb333dd vocab=9f1a5ebc
-/
theorem finiteDeficit_add_bound (C a : ℝ) (ha : 0 ≤ a) (z : EReal)
    (hz : z ≤ (C : EReal)) :
    (((C + a : ℝ) : EReal) - z).toENNReal =
      ENNReal.ofReal a + ((C : EReal) - z).toENNReal := by
  have hn : 0 ≤ (C : EReal) - z :=
    (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top C)) (Or.inl (EReal.coe_ne_bot C))).mpr hz
  have heq : ((C + a : ℝ) : EReal) - z = (a : EReal) + ((C : EReal) - z) := by
    rw [EReal.coe_add]
    simp only [sub_eq_add_neg]
    ac_rfl
  rw [heq, EReal.toENNReal_add (EReal.coe_nonneg.mpr ha) hn,
    EReal.real_coe_toENNReal]

/--
@isnad1 id=eq.3h7v.s7.41a74272e2cc from=translated src=- shape=be0fcb9c vocab=9fba989d
-/
theorem circleDeficit_add_bound {u : E → EReal} (x v : E) {r : ℝ}
    (hr : 0 ≤ r) (C a : ℝ) (ha : 0 ≤ a)
    (hC : ∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal)) :
    circleDeficit u x v r (C + a) =
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal a + circleDeficit u x v r C := by
  unfold circleDeficit
  simp_rw [finiteDeficit_add_bound C a ha _
    (hC _ (circle_mem_affineClosedDisc x v hr _))]
  rw [lintegral_add_left measurable_const]
  simp [mul_comm]

/-- The submean test is independent of increasing the chosen finite bound.
@isnad1 id=iff.3h7v.s7.c6543c999a00 from=translated src=- shape=bcf503b7 vocab=58168f3d
-/
theorem discSubmean_add_bound_iff {u : E → EReal} (x v : E) {r : ℝ}
    (hr : 0 ≤ r) (C a : ℝ) (ha : 0 ≤ a)
    (hC : ∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal)) :
    (circleDeficit u x v r (C + a) ≤ ENNReal.ofReal (2 * Real.pi) *
      (((C + a : ℝ) : EReal) - u x).toENNReal) ↔
    (circleDeficit u x v r C ≤ ENNReal.ofReal (2 * Real.pi) *
      ((C : EReal) - u x).toENNReal) := by
  rw [circleDeficit_add_bound x v hr C a ha hC,
    finiteDeficit_add_bound C a ha _ (hC x (center_mem_affineClosedDisc x v hr)), mul_add]
  exact ENNReal.add_le_add_iff_left
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

end PshLines
