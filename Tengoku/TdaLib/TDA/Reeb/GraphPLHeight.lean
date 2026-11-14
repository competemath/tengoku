import Tengoku.TdaLib.TDA.Reeb.GraphRealization
import Tengoku.TdaLib.TDA.Reeb.Interval
import Tengoku.Seed.Analysis.Convex.PathConnected
import Tengoku.Seed.Topology.ContinuousMap.Algebra
import Tengoku.Seed.Topology.Order.ProjIcc

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Piecewise-linear heights on realizations of simple graphs

For `V : Type u`, `G : SimpleGraph V` and vertex heights `h : V → ℝ`, the affine height of a dart
`d` at `t : unitInterval` is `dartHeight h d t = (1 - t) * h d.fst + t * h d.snd`. It satisfies the
reversal equation `dartHeight h d.symm (σ t) = dartHeight h d t` and the start equation
`dartHeight h d 0 = h d.fst`, so the universal lift `TDA.Reeb.GraphRealization.continuousLift`
gives the piecewise-linear height `plHeight G h : C(Realization G, ℝ)`, with
`plHeight G h (vertex G v) = h v` and `plHeight G h (edgePoint G d t) = dartHeight h d t` by `rfl`
and uniqueness among continuous maps with these values (`plHeight_unique`). Uniqueness gives
`plHeight G (fun v => h v + c) = plHeight G h + c` (`plHeight_add_const`). Equal endpoint heights
are allowed: a horizontal dart has constant height (`dartHeight_of_eq`), while the height of a
nonhorizontal dart is injective in the parameter (`dartHeight_injective`). Along the subpath of any
dart between parameters `s` and `t`, `plHeight_edgeSegment_bounds` bounds the height between the
two endpoint heights, with no condition on their order or equality.

## Unoriented edges and their support

An unoriented edge is an element of mathlib's edge set `G.edgeSet`. `dartEdge d` is the edge of
the dart `d`, and two darts have the same edge exactly when they are equal or opposite
(`dartEdge_eq_iff`). For an open interval `I`, `EdgeActive G h I e` holds when some dart of `e`
has an interior parameter `0 < t < 1` whose height lies in `I`. Activity:

* does not depend on the orientation (`edgeActive_dartEdge_iff`, `EdgeActive.exists_mem`);
* is monotone in `I` (`EdgeActive.mono`);
* is equivalent to nonemptiness of the full parameter set `{t : unitInterval // dartHeight h d t ∈ I}`
  (`edgeActive_dartEdge_iff_nonempty`), where the direction from an endpoint parameter uses the
  openness of `I` (`exists_interior_of_mem`);
* holds for every edge incident to a surviving endpoint (`edgeActive_of_mem`);
* holds for a horizontal edge exactly when its common height lies in `I`
  (`edgeActive_dartEdge_iff_of_eq`).

The real parameters whose affine height lies in an order-convex set form an order-convex set, also
for a horizontal dart (`ordConnected_preimage_lineHeight`). Hence two edge points of one dart in
the height preimage of `I` are joined by a path inside that preimage (`joinedIn_edgePoint`).

No finiteness, injectivity of heights, nonemptiness or decidability is assumed. The short name
`mono` of `EdgeActive.mono` also occurs as `TDA.Reeb.Interleaving.mono` and
`TDA.Filtration.FilterFunction.mono`.
-/

open SimpleGraph Topology Set CategoryTheory

/-- The reversal of the unit interval; `open unitInterval` would make `I` a token.-/
local notation "σ" => unitInterval.symm

universe u

namespace TDA.Reeb.GraphPL

open TDA.Reeb.GraphRealization

noncomputable section

section dartHeight

variable {V : Type u} {G : SimpleGraph V} (h : V → ℝ)

/-- The affine height `L_d(t) = (1 - t) h(d.fst) + t h(d.snd)` on the interval of a dart.-/
def dartHeight (d : G.Dart) (t : unitInterval) : ℝ :=
  (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd

/--
@isnad1 id=continuo.0h4v.s5.65510f2f1180 from=translated src=- shape=e8968f8a vocab=5f11f337
-/
theorem continuous_dartHeight (d : G.Dart) : Continuous (dartHeight h d) := by
  unfold dartHeight
  fun_prop

/-- Reversal: `L_(d.symm)(1 - t) = L_d(t)`.
@isnad1 id=eq.0h5v.s5.da6abbc31b80 from=translated src=- shape=4f18af45 vocab=57217ba7
-/
theorem dartHeight_symm (d : G.Dart) (t : unitInterval) :
    dartHeight h d.symm (σ t) = dartHeight h d t := by
  show (1 - (σ t : ℝ)) * h d.snd + (σ t : ℝ) * h d.fst =
    (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd
  rw [unitInterval.coe_symm_eq]
  ring

/--
@isnad1 id=eq.0h4v.s5.b7ca3ee87616 from=translated src=- shape=bccedc86 vocab=e1b65962
-/
@[simp] theorem dartHeight_zero (d : G.Dart) : dartHeight h d 0 = h d.fst := by
  simp [dartHeight]

/--
@isnad1 id=eq.0h4v.s5.d9a8752d994c from=translated src=- shape=bccedc86 vocab=09b676f1
-/
@[simp] theorem dartHeight_one (d : G.Dart) : dartHeight h d 1 = h d.snd := by
  simp [dartHeight]

/-- Equal endpoint heights: a horizontal dart has constant height.
@isnad1 id=eq.1h5v.s5.48a224392ef9 from=translated src=- shape=d6ab8884 vocab=c3c22533
-/
theorem dartHeight_of_eq {d : G.Dart} (hd : h d.fst = h d.snd) (t : unitInterval) :
    dartHeight h d t = h d.fst := by
  rw [dartHeight, ← hd]
  ring

/-- On a nonhorizontal dart the height is injective in the parameter.
@isnad1 id=injectiv.1h4v.s5.061279b3175a from=translated src=- shape=12e88243 vocab=aee316fb
-/
theorem dartHeight_injective {d : G.Dart} (hne : h d.fst ≠ h d.snd) :
    Function.Injective (dartHeight h d) := by
  intro s t hst
  apply Subtype.ext
  apply mul_right_cancel₀ (sub_ne_zero.mpr hne.symm)
  unfold dartHeight at hst
  linear_combination hst

/-- The real parameters whose affine height lies in an order-convex set form an order-convex
set; the constant-height case is included.
@isnad1 id=ordconne.1h5v.s6.98804d260496 from=translated src=- shape=5a4a7371 vocab=183b677d
-/
theorem ordConnected_preimage_lineHeight (d : G.Dart) {s : Set ℝ} (hs : s.OrdConnected) :
    ((fun r : ℝ => (1 - r) * h d.fst + r * h d.snd) ⁻¹' s).OrdConnected := by
  rcases le_total (h d.fst) (h d.snd) with hab | hab
  · refine hs.preimage_mono fun r r' hrr' => ?_
    show (1 - r) * h d.fst + r * h d.snd ≤ (1 - r') * h d.fst + r' * h d.snd
    nlinarith [mul_nonneg (sub_nonneg.2 hrr') (sub_nonneg.2 hab)]
  · refine hs.preimage_anti fun r r' hrr' => ?_
    show (1 - r') * h d.fst + r' * h d.snd ≤ (1 - r) * h d.fst + r * h d.snd
    nlinarith [mul_nonneg (sub_nonneg.2 hrr') (sub_nonneg.2 hab)]

end dartHeight

section plHeight

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)

/-- The piecewise-linear height of the realization, from the universal lift `continuousLift`.-/
def plHeight : C(Realization G, ℝ) :=
  continuousLift G h (fun d => ⟨dartHeight h d, continuous_dartHeight h d⟩)
    (fun d t => dartHeight_symm h d t) (fun d => dartHeight_zero h d)

/--
@isnad1 id=eq.0h4v.s5.65cbd911c578 from=translated src=- shape=8dedda5d vocab=27cd120a
-/
@[simp] theorem plHeight_vertex (v : V) : plHeight G h (vertex G v) = h v := rfl

/--
@isnad1 id=eq.0h5v.s6.8f08e84dd1b0 from=translated src=- shape=5a2aa281 vocab=8fc981b6
-/
@[simp] theorem plHeight_edgePoint (d : G.Dart) (t : unitInterval) :
    plHeight G h (edgePoint G d t) = dartHeight h d t := rfl

/-- Along a dart subpath, the piecewise-linear height lies between its endpoint heights.
@isnad1 id=and.0h7v.s8.0efd8dcf52ef from=translated src=- shape=782a5bed vocab=30eb624c
-/
theorem plHeight_edgeSegment_bounds (d : G.Dart) (s t r : unitInterval) :
    min (plHeight G h (edgePoint G d s)) (plHeight G h (edgePoint G d t)) ≤
        plHeight G h (edgeSegment G d s t r) ∧
      plHeight G h (edgeSegment G d s t r) ≤
        max (plHeight G h (edgePoint G d s)) (plHeight G h (edgePoint G d t)) := by
  have hformula :
      plHeight G h (edgeSegment G d s t r) =
        (1 - (r : ℝ)) * plHeight G h (edgePoint G d s) +
          (r : ℝ) * plHeight G h (edgePoint G d t) := by
    simp only [edgeSegment_apply, plHeight_edgePoint, dartHeight, Set.Icc.coe_convexComb]
    ring
  have hr0 : 0 ≤ (r : ℝ) := r.2.1
  have hr1 : (r : ℝ) ≤ 1 := r.2.2
  have h1r0 : 0 ≤ 1 - (r : ℝ) := by linarith
  let a := plHeight G h (edgePoint G d s)
  let b := plHeight G h (edgePoint G d t)
  change min a b ≤ plHeight G h (edgeSegment G d s t r) ∧
    plHeight G h (edgeSegment G d s t r) ≤ max a b
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
    constructor
    · rw [hformula]
      nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hab)]
    · rw [hformula]
      nlinarith [mul_nonneg h1r0 (sub_nonneg.mpr hab)]
  · rw [min_eq_right hba, max_eq_left hba]
    constructor
    · rw [hformula]
      nlinarith [mul_nonneg h1r0 (sub_nonneg.mpr hba)]
    · rw [hformula]
      nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hba)]

/--
@isnad1 id=eq.2h4v.s7.38c9d77b455b from=translated src=- shape=fcdcd959 vocab=dba96222
-/
theorem plHeight_unique (g : C(Realization G, ℝ)) (hv : ∀ v, g (vertex G v) = h v)
    (he : ∀ d t, g (edgePoint G d t) = dartHeight h d t) : g = plHeight G h :=
  continuousLift_unique G _ _ _ _ g hv he

/-- Translating every vertex height by `c` translates the piecewise-linear height by `c`.
@isnad1 id=eq.0h4v.s7.8e079353ccd5 from=translated src=- shape=eeb65dd2 vocab=482cf786
-/
theorem plHeight_add_const (c : ℝ) :
    plHeight G (fun v => h v + c) = plHeight G h + ContinuousMap.const (Realization G) c :=
  (plHeight_unique G _ _ (fun v => by simp) fun d t => by
    simp only [ContinuousMap.add_apply, plHeight_edgePoint, ContinuousMap.const_apply,
      dartHeight]
    ring).symm

/--
@isnad1 id=eq.0h5v.s6.a5ff5b92a643 from=translated src=- shape=76eb279e vocab=42ee986a
-/
theorem plHeight_add_const_apply (c : ℝ) (x : Realization G) :
    plHeight G (fun v => h v + c) x = plHeight G h x + c := by
  rw [plHeight_add_const]
  rfl

end plHeight

section edges

variable {V : Type u} {G : SimpleGraph V}

/-- The unoriented edge of a dart, as an element of mathlib's edge set.-/
def dartEdge (d : G.Dart) : G.edgeSet := ⟨d.edge, d.edge_mem⟩

/--
@isnad1 id=eq.0h3v.s5.697c405ab255 from=translated src=- shape=8163c05c vocab=dde25276
-/
@[simp] theorem coe_dartEdge (d : G.Dart) : (dartEdge d : Sym2 V) = d.edge := rfl

/--
@isnad1 id=eq.0h3v.s4.b1fb0a8cd78a from=translated src=- shape=887c6541 vocab=fa9c480e
-/
@[simp] theorem dartEdge_symm (d : G.Dart) : dartEdge d.symm = dartEdge d :=
  Subtype.ext d.edge_symm

/--
@isnad1 id=iff.0h4v.s5.b263a6f9a2d9 from=translated src=- shape=a5915c8e vocab=fa9c480e
-/
theorem dartEdge_eq_iff {d₁ d₂ : G.Dart} :
    dartEdge d₁ = dartEdge d₂ ↔ d₁ = d₂ ∨ d₁ = d₂.symm :=
  Subtype.ext_iff.trans (dart_edge_eq_iff d₁ d₂)

/--
@isnad1 id=iff.0h4v.s6.4663a52b74c3 from=translated src=- shape=1fa34ba9 vocab=35885bae
-/
theorem mem_dartEdge {d : G.Dart} {v : V} :
    v ∈ (dartEdge d : Sym2 V) ↔ v = d.fst ∨ v = d.snd :=
  Sym2.mem_iff

/--
@isnad1 id=mem.0h3v.s5.2e8b4ca21ad5 from=translated src=- shape=dd6253a9 vocab=bf8a0715
-/
theorem fst_mem_dartEdge (d : G.Dart) : d.fst ∈ (dartEdge d : Sym2 V) := Sym2.mem_mk_left _ _

/--
@isnad1 id=mem.0h3v.s5.d2323396ae7a from=translated src=- shape=dd6253a9 vocab=f0df99db
-/
theorem snd_mem_dartEdge (d : G.Dart) : d.snd ∈ (dartEdge d : Sym2 V) := Sym2.mem_mk_right _ _

/--
@isnad1 id=ex.0h3v.s5.b27357ae3a6a from=translated src=- shape=ed184507 vocab=045d1304
-/
theorem exists_dartEdge_eq (e : G.edgeSet) : ∃ d : G.Dart, dartEdge d = e := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b => exact ⟨⟨(a, b), he⟩, rfl⟩

/-- Every endpoint of an edge is the start of a representing dart.
@isnad1 id=ex.1h4v.s6.288377f08711 from=translated src=- shape=4d6cbf89 vocab=2a7f60c9
-/
theorem exists_dartEdge_eq_fst {e : G.edgeSet} {v : V} (hv : v ∈ (e : Sym2 V)) :
    ∃ d : G.Dart, dartEdge d = e ∧ d.fst = v := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b =>
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact ⟨⟨(v, b), he⟩, rfl, rfl⟩
    · exact ⟨⟨(v, a), (G.mem_edgeSet.1 he).symm⟩, Subtype.ext Sym2.eq_swap, rfl⟩

end edges

section support

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)

/-- An unoriented edge is active over `I` when some representing dart has an interior parameter
`0 < t < 1` whose affine height lies in `I`.-/
def EdgeActive (I : OpenInterval) (e : G.edgeSet) : Prop :=
  ∃ d : G.Dart, dartEdge d = e ∧
    ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ dartHeight h d t ∈ I

variable {G h} {I J : OpenInterval}

/-- Openness of `I`: a parameter in the height preimage, interior or not, yields an interior one.
@isnad1 id=ex.1h6v.s6.5e76edcf7df8 from=translated src=- shape=2a91844d vocab=367f13e4
-/
theorem exists_interior_of_mem {d : G.Dart} {t : unitInterval} (ht : dartHeight h d t ∈ I) :
    ∃ s : unitInterval, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧ dartHeight h d s ∈ I := by
  have hc : Continuous fun r : ℝ => (1 - r) * h d.fst + r * h d.snd := by fun_prop
  have hmem : (t : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo zero_ne_one]
    exact t.2
  obtain ⟨r, hrI, hr⟩ := mem_closure_iff_nhds.1 hmem _
    (hc.continuousAt.preimage_mem_nhds (I.isOpen.mem_nhds ht))
  exact ⟨⟨r, Ioo_subset_Icc_self hr⟩, hr.1, hr.2, hrI⟩

/--
@isnad1 id=edgeacti.2h6v.s5.4cc9a0c8c6d8 from=translated src=- shape=da7cbedd vocab=640fc256
-/
theorem EdgeActive.mono (hIJ : I ≤ J) {e : G.edgeSet} (he : EdgeActive G h I e) :
    EdgeActive G h J e := by
  obtain ⟨d, hd, t, ht₀, ht₁, ht⟩ := he
  exact ⟨d, hd, t, ht₀, ht₁, OpenInterval.le_iff_subset.1 hIJ ht⟩

/-- **Orientation independence.** An edge is active exactly when any one of its darts has an
interior parameter in the height preimage.
@isnad1 id=iff.0h5v.s6.4910609427cf from=translated src=- shape=b9beb97c vocab=34dccf9f
-/
theorem edgeActive_dartEdge_iff (d : G.Dart) :
    EdgeActive G h I (dartEdge d) ↔
      ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ dartHeight h d t ∈ I := by
  constructor
  · rintro ⟨d', hd', t, ht₀, ht₁, ht⟩
    rcases dartEdge_eq_iff.1 hd' with rfl | rfl
    · exact ⟨t, ht₀, ht₁, ht⟩
    · refine ⟨σ t, ?_, ?_, ?_⟩
      · rw [unitInterval.coe_symm_eq]; linarith
      · rw [unitInterval.coe_symm_eq]; linarith
      · have hrev := dartHeight_symm h d.symm t
        rw [Dart.symm_symm] at hrev
        rwa [hrev]
  · rintro ⟨t, ht₀, ht₁, ht⟩
    exact ⟨d, rfl, t, ht₀, ht₁, ht⟩

/-- Activity is nonemptiness of the full restricted parameter set `E_d(I)`; the direction from an
arbitrary, possibly endpoint, parameter uses the openness of `I`.
@isnad1 id=iff.0h5v.s5.840dd8809e41 from=translated src=- shape=790ccf63 vocab=d539735c
-/
theorem edgeActive_dartEdge_iff_nonempty (d : G.Dart) :
    EdgeActive G h I (dartEdge d) ↔ Nonempty {t : unitInterval // dartHeight h d t ∈ I} := by
  rw [edgeActive_dartEdge_iff]
  constructor
  · rintro ⟨t, -, -, ht⟩
    exact ⟨⟨t, ht⟩⟩
  · rintro ⟨t, ht⟩
    exact exists_interior_of_mem ht

/--
@isnad1 id=edgeacti.1h6v.s5.49075199cb49 from=translated src=- shape=458b44f1 vocab=cc52a6ba
-/
theorem edgeActive_dartEdge_of_mem {d : G.Dart} {t : unitInterval} (ht : dartHeight h d t ∈ I) :
    EdgeActive G h I (dartEdge d) :=
  (edgeActive_dartEdge_iff_nonempty d).2 ⟨⟨t, ht⟩⟩

/-- Orientation independence for an arbitrary representing dart of an active edge.
@isnad1 id=ex.2h6v.s6.1b3a7c49de61 from=translated src=- shape=187d04b1 vocab=357e4cf8
-/
theorem EdgeActive.exists_mem {e : G.edgeSet} (he : EdgeActive G h I e) {d : G.Dart}
    (hd : dartEdge d = e) :
    ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ dartHeight h d t ∈ I := by
  subst hd
  exact (edgeActive_dartEdge_iff d).1 he

/-- A surviving endpoint makes every incident edge active.
@isnad1 id=edgeacti.2h6v.s6.d18214c6cca9 from=translated src=- shape=d3454d8b vocab=abcbd46a
-/
theorem edgeActive_of_mem {e : G.edgeSet} {v : V} (hv : v ∈ (e : Sym2 V)) (hI : h v ∈ I) :
    EdgeActive G h I e := by
  obtain ⟨d, rfl, rfl⟩ := exists_dartEdge_eq_fst hv
  exact edgeActive_dartEdge_of_mem (t := 0) (by rwa [dartHeight_zero])

/-- A horizontal edge is active exactly when its common height lies in `I`.
@isnad1 id=iff.1h5v.s5.47bffd00c6bf from=translated src=- shape=e150b339 vocab=fb323ed2
-/
theorem edgeActive_dartEdge_iff_of_eq {d : G.Dart} (hd : h d.fst = h d.snd) :
    EdgeActive G h I (dartEdge d) ↔ h d.fst ∈ I := by
  rw [edgeActive_dartEdge_iff_nonempty]
  constructor
  · rintro ⟨t, ht⟩
    rwa [dartHeight_of_eq h hd] at ht
  · intro hI
    exact ⟨⟨0, by rwa [dartHeight_zero]⟩⟩

end support

end

end TDA.Reeb.GraphPL
