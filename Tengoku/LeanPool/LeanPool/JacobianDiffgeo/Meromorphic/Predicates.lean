/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.LocalMultiplicity.Multiplicity
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Bridges
public import Tengoku

/-!
# Meromorphic predicates and orders on a Riemann surface (CC3, chart layer)

Unit: meromorphic-and-divisors (`docs/design/meromorphic-and-divisors.md` §4.1).

* `MeromorphicAtX f x` / `MeromorphicOnX f U`: CC3's frozen chart-composite predicate,
  `MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)`. Junk-robust: junk in the chart
  composite off the chart source never affects the germ at `chartAt x x`.
* `ordAtX f x : WithTop ℤ`: CC3's frozen chart-composite order. Chart-invariant
  (`ordAtX_eq_of_mem_source`), and `ordAtX_congr` needs **no meromorphy hypothesis** — it holds
  for arbitrary `f =ᶠ[𝓝[≠] x] g`, which is exactly what lets `ord` descend to germ classes later.
* The workhorse `eventually_nhdsNE_iff_comp_chart` transports any eventual/punctured-neighborhood
  statement about `f` near `x` to a statement about the chart composite near `chartAt ℂ x x`
  (and back); every other transport lemma in this file is a one-line specialization of it.
-/

@[expose] public section

open scoped ContDiff Manifold
open Set Filter Topology

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {f g : X → ℂ} {x : X} {c : ℂ}

/-- CC3 (frozen): meromorphy of the standard-chart composite. Junk-robust. -/
def MeromorphicAtX (f : X → ℂ) (x : X) : Prop :=
  MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

/-- Relative CC3 predicate; the frozen global one is `MeromorphicOnX f Set.univ`. -/
def MeromorphicOnX (f : X → ℂ) (U : Set X) : Prop := ∀ x ∈ U, MeromorphicAtX f x

/--
@isnad1 id=iff.0h2v.s5.899bf401e6fa from=translated src=- shape=108f661d vocab=9ef964a3
-/
theorem meromorphicOnX_univ : MeromorphicOnX f univ ↔ ∀ x, MeromorphicAtX f x := by
  simp [MeromorphicOnX]

/-- CC3 (frozen): the order at `x`, `WithTop ℤ`-valued, junk `0` off meromorphy. -/
noncomputable def ordAtX (f : X → ℂ) (x : X) : WithTop ℤ :=
  meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

/--
@isnad1 id=eq.0h3v.s7.68ff825fed20 from=translated src=- shape=4b98ca60 vocab=01dfb6cc
-/
theorem ordAtX_def (f : X → ℂ) (x : X) :
    ordAtX f x = meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := rfl

/-! ### The chart-transport workhorse -/

/-- Transport an eventual (punctured-neighborhood) property of `f` near `x` through the standard
chart at `x`, and back. Every `𝓝[≠]`-transport proof in this unit reduces to this one lemma.
@isnad1 id=iff.0h3v.s7.a9623c39bf23 from=translated src=- shape=bcf655eb vocab=bc2496ca
-/
theorem eventually_nhdsNE_iff_comp_chart {p : X → Prop} {x : X} :
    (∀ᶠ y in 𝓝[≠] x, p y) ↔ ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), p ((chartAt ℂ x).symm z) := by
  rw [← map_nhdsNE (chartAt ℂ x) (mem_chart_source ℂ x), eventually_map]
  have hleft : ∀ᶠ z in 𝓝[≠] x, (chartAt ℂ x).symm (chartAt ℂ x z) = z :=
    ((chartAt ℂ x).eventually_left_inverse (mem_chart_source ℂ x)).filter_mono nhdsWithin_le_nhds
  exact eventually_congr (hleft.mono fun y hy => by rw [hy])

/-- Simpler companion transport (no correction needed): a property `q` of the chart-image `c y`
transports directly by pulling back along `c`.
@isnad1 id=iff.0h3v.s7.0473ea373c93 from=translated src=- shape=e1013013 vocab=2e839d34
-/
theorem eventually_nhdsNE_comp_chart_apply_iff {q : ℂ → Prop} {x : X} :
    (∀ᶠ y in 𝓝[≠] x, q (chartAt ℂ x y)) ↔ ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), q z := by
  rw [← map_nhdsNE (chartAt ℂ x) (mem_chart_source ℂ x), eventually_map]

/-- `Frequently` version of `eventually_nhdsNE_iff_comp_chart`.
@isnad1 id=iff.0h3v.s7.75e5c86b2e81 from=translated src=- shape=bcf655eb vocab=03392cbe
-/
theorem frequently_nhdsNE_iff_comp_chart {p : X → Prop} {x : X} :
    (∃ᶠ y in 𝓝[≠] x, p y) ↔ ∃ᶠ z in 𝓝[≠] (chartAt ℂ x x), p ((chartAt ℂ x).symm z) :=
  not_congr (eventually_nhdsNE_iff_comp_chart (p := fun y => ¬ p y))

/-- Specialization of `eventually_nhdsNE_iff_comp_chart` to `EventuallyEq`: agreement of `f`, `g`
near `x` transports to agreement of their chart composites near `chartAt ℂ x x`.
@isnad1 id=iff.0h4v.s8.ad5c92af34ca from=translated src=- shape=507e5e2b vocab=a4aaed22
-/
theorem eventuallyEq_nhdsNE_comp_chart_iff {f g : X → ℂ} {x : X} :
    f =ᶠ[𝓝[≠] x] g ↔
      (f ∘ (chartAt ℂ x).symm) =ᶠ[𝓝[≠] (chartAt ℂ x x)] (g ∘ (chartAt ℂ x).symm) :=
  eventually_nhdsNE_iff_comp_chart (p := fun y => f y = g y)

/-- `Tendsto` version of the chart-transport workhorse.
@isnad1 id=iff.0h4v.s7.fefb93bd1005 from=translated src=- shape=d7f8f60a vocab=a1111970
-/
theorem tendsto_nhdsNE_comp_chart_iff {f : X → ℂ} {x : X} {l : Filter ℂ} :
    Tendsto f (𝓝[≠] x) l ↔ Tendsto (f ∘ (chartAt ℂ x).symm) (𝓝[≠] (chartAt ℂ x x)) l := by
  rw [← map_nhdsNE (chartAt ℂ x) (mem_chart_source ℂ x), tendsto_map'_iff]
  have hleft : ∀ᶠ z in 𝓝[≠] x, (chartAt ℂ x).symm (chartAt ℂ x z) = z :=
    ((chartAt ℂ x).eventually_left_inverse (mem_chart_source ℂ x)).filter_mono nhdsWithin_le_nhds
  exact (tendsto_congr' (hleft.mono fun z hz => by simp [Function.comp_apply, hz])).symm

/-! ### `MeromorphicAtX`: congruence and arithmetic -/

/--
@isnad1 id=meromorp.2h4v.s6.5b2b3d17c6c1 from=translated src=- shape=159853ec vocab=55eebe07
-/
theorem MeromorphicAtX.congr (hf : MeromorphicAtX f x) (h : f =ᶠ[𝓝[≠] x] g) :
    MeromorphicAtX g x :=
  MeromorphicAt.congr hf (eventuallyEq_nhdsNE_comp_chart_iff.mp h)

/-- Meromorphy-free: `ordAtX` respects `𝓝[≠]`-agreement of arbitrary functions.
@isnad1 id=eq.1h4v.s6.b287d30661f9 from=translated src=- shape=53b4ce77 vocab=e4defaf9
-/
theorem ordAtX_congr (h : f =ᶠ[𝓝[≠] x] g) : ordAtX f x = ordAtX g x :=
  meromorphicOrderAt_congr (eventuallyEq_nhdsNE_comp_chart_iff.mp h)

/--
@isnad1 id=meromorp.0h3v.s5.c2eb724ee5ab from=translated src=- shape=a4a4d330 vocab=5075819e
-/
theorem meromorphicAtX_const (c : ℂ) : MeromorphicAtX (fun _ => c) x :=
  MeromorphicAt.const c _

/--
@isnad1 id=meromorp.2h4v.s6.70bc103a9979 from=translated src=- shape=b3ba7044 vocab=633b70f2
-/
theorem MeromorphicAtX.add (hf : MeromorphicAtX f x) (hg : MeromorphicAtX g x) :
    MeromorphicAtX (f + g) x :=
  MeromorphicAt.add hf hg

/--
@isnad1 id=meromorp.2h4v.s6.960be301a3e3 from=translated src=- shape=b3ba7044 vocab=939dddb3
-/
theorem MeromorphicAtX.mul (hf : MeromorphicAtX f x) (hg : MeromorphicAtX g x) :
    MeromorphicAtX (f * g) x :=
  MeromorphicAt.mul hf hg

/--
@isnad1 id=meromorp.1h3v.s5.74e428e34565 from=translated src=- shape=9d83fe9c vocab=48eb9266
-/
theorem MeromorphicAtX.neg (hf : MeromorphicAtX f x) : MeromorphicAtX (-f) x :=
  MeromorphicAt.neg hf

/--
@isnad1 id=meromorp.2h4v.s6.dce64e5c5e57 from=translated src=- shape=b3ba7044 vocab=40670082
-/
theorem MeromorphicAtX.sub (hf : MeromorphicAtX f x) (hg : MeromorphicAtX g x) :
    MeromorphicAtX (f - g) x :=
  MeromorphicAt.sub hf hg

/--
@isnad1 id=meromorp.1h4v.s6.848cde74a9c9 from=translated src=- shape=8c480715 vocab=c1b9fb13
-/
theorem MeromorphicAtX.smul (c : ℂ) (hf : MeromorphicAtX f x) : MeromorphicAtX (c • f) x :=
  MeromorphicAt.smul (MeromorphicAt.const c _) hf

/--
@isnad1 id=meromorp.1h3v.s5.774ca3e2ccca from=translated src=- shape=9d83fe9c vocab=b420bd74
-/
theorem MeromorphicAtX.inv (hf : MeromorphicAtX f x) : MeromorphicAtX f⁻¹ x :=
  MeromorphicAt.inv hf

/--
@isnad1 id=meromorp.1h4v.s6.afdc5e7f7132 from=translated src=- shape=7bf90e42 vocab=b8628d09
-/
theorem MeromorphicAtX.pow (hf : MeromorphicAtX f x) (n : ℕ) : MeromorphicAtX (f ^ n) x :=
  MeromorphicAt.pow hf n

/--
@isnad1 id=meromorp.1h4v.s6.9b608f5adb35 from=translated src=- shape=7bf90e42 vocab=0d2595a3
-/
theorem MeromorphicAtX.zpow (hf : MeromorphicAtX f x) (n : ℤ) : MeromorphicAtX (f ^ n) x :=
  MeromorphicAt.zpow hf n

/-! ### `MeromorphicOnX`: pointwise lifting -/

/--
@isnad1 id=meromorp.2h4v.s6.ea8efa62e255 from=translated src=- shape=eb280ac3 vocab=777b60b3
-/
theorem MeromorphicOnX.add {U : Set X} (hf : MeromorphicOnX f U) (hg : MeromorphicOnX g U) :
    MeromorphicOnX (f + g) U :=
  fun x hx => (hf x hx).add (hg x hx)

/--
@isnad1 id=meromorp.2h4v.s6.651f5d9be1ff from=translated src=- shape=eb280ac3 vocab=945bb8af
-/
theorem MeromorphicOnX.mul {U : Set X} (hf : MeromorphicOnX f U) (hg : MeromorphicOnX g U) :
    MeromorphicOnX (f * g) U :=
  fun x hx => (hf x hx).mul (hg x hx)

/--
@isnad1 id=meromorp.1h3v.s5.0ae9f0587607 from=translated src=- shape=e54dd5a7 vocab=eb7dd29e
-/
theorem MeromorphicOnX.neg {U : Set X} (hf : MeromorphicOnX f U) : MeromorphicOnX (-f) U :=
  fun x hx => (hf x hx).neg

/--
@isnad1 id=meromorp.2h4v.s6.823be71ae84a from=translated src=- shape=eb280ac3 vocab=ea361fdf
-/
theorem MeromorphicOnX.sub {U : Set X} (hf : MeromorphicOnX f U) (hg : MeromorphicOnX g U) :
    MeromorphicOnX (f - g) U :=
  fun x hx => (hf x hx).sub (hg x hx)

/--
@isnad1 id=meromorp.1h4v.s6.610af7763e20 from=translated src=- shape=d62c69bc vocab=3e5c9028
-/
theorem MeromorphicOnX.smul {U : Set X} (c : ℂ) (hf : MeromorphicOnX f U) :
    MeromorphicOnX (c • f) U :=
  fun x hx => (hf x hx).smul c

/--
@isnad1 id=meromorp.1h3v.s5.cd41ac02547f from=translated src=- shape=e54dd5a7 vocab=5fea2eb5
-/
theorem MeromorphicOnX.inv {U : Set X} (hf : MeromorphicOnX f U) : MeromorphicOnX f⁻¹ U :=
  fun x hx => (hf x hx).inv

/--
@isnad1 id=meromorp.0h3v.s5.c106bcbabb11 from=translated src=- shape=c2006800 vocab=74f2d0ce
-/
theorem meromorphicOnX_const (c : ℂ) (U : Set X) : MeromorphicOnX (fun _ => c) U :=
  fun _x _ => meromorphicAtX_const c

/-! ### Classification of the order (no chart invariance needed) -/

/--
@isnad1 id=iff.0h3v.s6.6191f538e6f4 from=translated src=- shape=798c549f vocab=c34bc0f4
-/
theorem ordAtX_eq_top_iff : ordAtX f x = ⊤ ↔ f =ᶠ[𝓝[≠] x] 0 := by
  change meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) = ⊤ ↔ _
  rw [meromorphicOrderAt_eq_top_iff]
  have h2 : (f =ᶠ[𝓝[≠] x] (0 : X → ℂ)) ↔
      (f ∘ (chartAt ℂ x).symm) =ᶠ[𝓝[≠] (chartAt ℂ x x)] ((0 : X → ℂ) ∘ (chartAt ℂ x).symm) :=
    eventuallyEq_nhdsNE_comp_chart_iff (f := f) (g := (0 : X → ℂ))
  exact h2.symm

/--
@isnad1 id=iff.1h3v.s6.8a7b75e84bd9 from=translated src=- shape=80c99484 vocab=793f0215
-/
theorem ordAtX_ne_top_iff (hf : MeromorphicAtX f x) :
    ordAtX f x ≠ ⊤ ↔ ∀ᶠ z in 𝓝[≠] x, f z ≠ 0 := by
  change meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ≠ ⊤ ↔ _
  rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf]
  exact (eventually_nhdsNE_iff_comp_chart (p := fun y => f y ≠ 0)).symm

/--
@isnad1 id=iff.1h3v.s6.67ab2992914a from=translated src=- shape=0ea77e84 vocab=273d8e41
-/
theorem MeromorphicAtX.frequently_zero_iff (hf : MeromorphicAtX f x) :
    (∃ᶠ z in 𝓝[≠] x, f z = 0) ↔ f =ᶠ[𝓝[≠] x] 0 := by
  have h1 : (∃ᶠ z in 𝓝[≠] x, f z = 0) ↔
      ∃ᶠ w in 𝓝[≠] (chartAt ℂ x x), (f ∘ (chartAt ℂ x).symm) w = 0 :=
    frequently_nhdsNE_iff_comp_chart (p := fun y => f y = 0)
  have h2 : (f =ᶠ[𝓝[≠] x] (0 : X → ℂ)) ↔
      (f ∘ (chartAt ℂ x).symm) =ᶠ[𝓝[≠] (chartAt ℂ x x)] ((0 : X → ℂ) ∘ (chartAt ℂ x).symm) :=
    eventuallyEq_nhdsNE_comp_chart_iff (f := f) (g := (0 : X → ℂ))
  rw [h1, h2]
  exact MeromorphicAt.frequently_zero_iff_eventuallyEq_zero hf

/--
@isnad1 id=iff.1h3v.s6.23b613d0dd71 from=translated src=- shape=4fda2c25 vocab=7145e9d2
-/
theorem tendsto_nhds_iff_ordAtX_nonneg (hf : MeromorphicAtX f x) :
    (∃ c, Tendsto f (𝓝[≠] x) (𝓝 c)) ↔ 0 ≤ ordAtX f x := by
  rw [ordAtX_def]
  constructor
  · rintro ⟨d, hd⟩
    exact (tendsto_nhds_iff_meromorphicOrderAt_nonneg hf).1 ⟨d, tendsto_nhdsNE_comp_chart_iff.1 hd⟩
  · intro h
    obtain ⟨d, hd⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg hf).2 h
    exact ⟨d, tendsto_nhdsNE_comp_chart_iff.2 hd⟩

/-! ### Order arithmetic (chart composites are literal `+,*,⁻¹` of chart composites) -/

/--
@isnad1 id=le.2h4v.s6.0e0a8fa5009a from=translated src=- shape=88e428ae vocab=373d7860
-/
theorem ordAtX_add (hf : MeromorphicAtX f x) (hg : MeromorphicAtX g x) :
    min (ordAtX f x) (ordAtX g x) ≤ ordAtX (f + g) x :=
  meromorphicOrderAt_add hf hg

/--
@isnad1 id=eq.3h4v.s6.654951d29679 from=translated src=- shape=c722969e vocab=b10eb2da
-/
theorem ordAtX_add_of_ne (hf : MeromorphicAtX f x) (hg : MeromorphicAtX g x)
    (h : ordAtX f x ≠ ordAtX g x) : ordAtX (f + g) x = min (ordAtX f x) (ordAtX g x) :=
  meromorphicOrderAt_add_of_ne hf hg h

/--
@isnad1 id=eq.2h4v.s6.7899adbba9bf from=translated src=- shape=3965fa7a vocab=c1253043
-/
theorem ordAtX_mul (hf : MeromorphicAtX f x) (hg : MeromorphicAtX g x) :
    ordAtX (f * g) x = ordAtX f x + ordAtX g x :=
  meromorphicOrderAt_mul hf hg

/--
@isnad1 id=eq.0h3v.s5.eae771c985d8 from=translated src=- shape=0f268e8f vocab=970b68ab
-/
theorem ordAtX_inv : ordAtX f⁻¹ x = -ordAtX f x :=
  meromorphicOrderAt_inv

/--
@isnad1 id=eq.0h3v.s5.0e119b05ec3c from=translated src=- shape=36bfaccc vocab=cdfff255
-/
theorem ordAtX_neg : ordAtX (-f) x = ordAtX f x :=
  meromorphicOrderAt_neg.symm

/--
@isnad1 id=eq.1h4v.s6.55b5000d08b7 from=translated src=- shape=3d8a4456 vocab=a0e664b1
-/
theorem ordAtX_smul (hc : c ≠ 0) : ordAtX (c • f) x = ordAtX f x :=
  meromorphicOrderAt_smul_of_ne_zero analyticAt_const (by simpa using hc)

/--
@isnad1 id=eq.0h3v.s6.5144e60d6eb2 from=translated src=- shape=72245a00 vocab=f97a9437
-/
theorem ordAtX_const : ordAtX (fun _ : X => c) x = if c = 0 then ⊤ else 0 := by
  classical
  change meromorphicOrderAt (fun _ : ℂ => c) (chartAt ℂ x x) = if c = 0 then ⊤ else 0
  exact meromorphicOrderAt_const (chartAt ℂ x x) c

/--
@isnad1 id=eq.0h2v.s5.09747a9c2ade from=translated src=- shape=5251bcc0 vocab=251378c2
-/
theorem ordAtX_zero : ordAtX (0 : X → ℂ) x = ⊤ := by
  simpa [Pi.zero_def] using (ordAtX_const (c := 0) (x := x))

/--
@isnad1 id=eq.0h2v.s6.e0ef649bf171 from=translated src=- shape=edb02f7f vocab=89858041
-/
theorem ordAtX_one : ordAtX (1 : X → ℂ) x = 0 := by
  simpa [Pi.one_def] using (ordAtX_const (c := 1) (x := x))

/-- No chart invariance needed: `S = {x | ordAtX f x = ⊤}` is open (the analogue of the
`identity theorem`'s "S open" step, specialized to a single point).
@isnad1 id=eventual.1h3v.s6.389285532d82 from=translated src=- shape=800007be vocab=5cce9e12
-/
theorem eventually_ordAtX_eq_top [T1Space X] (h : ordAtX f x = ⊤) :
    ∀ᶠ y in 𝓝 x, ordAtX f y = ⊤ := by
  have hf0 : ∀ᶠ z in 𝓝 x, z ≠ x → f z = 0 := eventually_nhdsWithin_iff.mp (ordAtX_eq_top_iff.1 h)
  filter_upwards [hf0.eventually_nhds] with y hy
  apply ordAtX_eq_top_iff.2
  refine eventually_nhdsWithin_iff.mpr ?_
  rcases eq_or_ne y x with rfl | hyx
  · exact hy
  · have hxc : ({x}ᶜ : Set X) ∈ 𝓝 y := isOpen_compl_singleton.mem_nhds hyx
    filter_upwards [hy, hxc] with z hz1 hz2 _
    exact hz1 (by simpa using hz2)

/-! ### Chart invariance -/

section ChartInvariance

variable [IsManifold 𝓘(ℂ) ω X]

/-- Meromorphy at `x` may be read in ANY maximal-atlas chart whose source contains `x`.
@isnad1 id=iff.2h4v.s8.3d6b5fe7e4eb from=translated src=- shape=d78fe4eb vocab=50b8e59c
-/
theorem meromorphicAtX_iff_of_mem_source {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source) :
    MeromorphicAtX f x ↔ MeromorphicAt (f ∘ e.symm) (e x) := by
  set c := chartAt ℂ x with hc_def
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  obtain ⟨hτ, hτ'⟩ := analyticAt_transition he (IsManifold.chart_mem_maximalAtlas x) hx hxc
  have hgx : (c ∘ e.symm) (e x) = c x := by
    simp only [Function.comp_apply]
    rw [e.left_inv hx]
  have hev : (f ∘ e.symm) =ᶠ[𝓝[≠] (e x)] (f ∘ c.symm) ∘ (c ∘ e.symm) := by
    have h1 : ∀ᶠ z in 𝓝 (e x), e.symm z ∈ c.source := by
      apply (e.continuousAt_symm (e.map_source hx)).preimage_mem_nhds
      rw [e.left_inv hx]
      exact c.open_source.mem_nhds hxc
    filter_upwards [h1.filter_mono nhdsWithin_le_nhds] with z hz
    simp only [Function.comp_apply]
    rw [c.left_inv hz]
  change MeromorphicAt (f ∘ c.symm) (c x) ↔ MeromorphicAt (f ∘ e.symm) (e x)
  rw [MeromorphicAt.meromorphicAt_congr hev, meromorphicAt_comp_iff_of_deriv_ne_zero hτ hτ', hgx]

/-- CC3 chart invariance: the order at `x` may be read in ANY maximal-atlas chart whose source
contains `x`.
@isnad1 id=eq.2h4v.s8.ca2a8670f600 from=translated src=- shape=6297b50c vocab=875e6705
-/
theorem ordAtX_eq_of_mem_source {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source) :
    ordAtX f x = meromorphicOrderAt (f ∘ e.symm) (e x) := by
  set c := chartAt ℂ x with hc_def
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  obtain ⟨hτ, hτ'⟩ := analyticAt_transition he (IsManifold.chart_mem_maximalAtlas x) hx hxc
  have hgx : (c ∘ e.symm) (e x) = c x := by
    simp only [Function.comp_apply]; rw [e.left_inv hx]
  have hev : (f ∘ e.symm) =ᶠ[𝓝[≠] (e x)] (f ∘ c.symm) ∘ (c ∘ e.symm) := by
    have h1 : ∀ᶠ z in 𝓝 (e x), e.symm z ∈ c.source := by
      apply (e.continuousAt_symm (e.map_source hx)).preimage_mem_nhds
      rw [e.left_inv hx]
      exact c.open_source.mem_nhds hxc
    filter_upwards [h1.filter_mono nhdsWithin_le_nhds] with z hz
    simp only [Function.comp_apply]
    rw [c.left_inv hz]
  change meromorphicOrderAt (f ∘ c.symm) (c x) = meromorphicOrderAt (f ∘ e.symm) (e x)
  rw [meromorphicOrderAt_congr hev, meromorphicOrderAt_comp_of_deriv_ne_zero hτ hτ', hgx]

/--
@isnad1 id=meromorp.1h3v.s7.364398e3b55a from=translated src=- shape=07d68297 vocab=35285b56
-/
theorem ContMDiffAt.meromorphicAtX (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) : MeromorphicAtX f x :=
  (RS.contMDiffAt_iff_analyticAt_comp_chartAt.mp hf).meromorphicAt

/--
@isnad1 id=le.1h3v.s7.77b77c6b8105 from=translated src=- shape=69b1c0d4 vocab=9db68be8
-/
theorem ContMDiffAt.ordAtX_nonneg (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) : 0 ≤ ordAtX f x :=
  (RS.contMDiffAt_iff_analyticAt_comp_chartAt.mp hf).meromorphicOrderAt_nonneg

/-- `MeromorphicAtX` propagates to nearby points (read in the same chart, then converted by
chart invariance).
@isnad1 id=eventual.1h3v.s6.bad914af6136 from=translated src=- shape=9f9f7d91 vocab=be565f5e
-/
theorem eventually_meromorphicAtX (hf : MeromorphicAtX f x) :
    ∀ᶠ y in 𝓝[≠] x, MeromorphicAtX f y := by
  have h1 : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) z :=
    MeromorphicAt.eventually_analyticAt hf
  have h2 : ∀ᶠ y in 𝓝[≠] x, AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x y) :=
    eventually_nhdsNE_comp_chart_apply_iff.mpr h1
  have h3 : ∀ᶠ y in 𝓝[≠] x, y ∈ (chartAt ℂ x).source :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  filter_upwards [h2, h3] with y h2y h3y
  exact (meromorphicAtX_iff_of_mem_source (IsManifold.chart_mem_maximalAtlas x) h3y).2
    h2y.meromorphicAt

/-- `ordAtX` is eventually `0` away from a point where it is finite (read in the same chart,
then converted by chart invariance). Feeds the local finiteness of divisors.
@isnad1 id=eventual.2h3v.s7.0ece883b7dee from=translated src=- shape=68326ace vocab=f7095e73
-/
theorem eventually_ordAtX_eq_zero (hf : MeromorphicAtX f x) (h : ordAtX f x ≠ ⊤) :
    ∀ᶠ y in 𝓝[≠] x, ordAtX f y = 0 := by
  have h1 : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) z :=
    MeromorphicAt.eventually_analyticAt hf
  have h2 : ∀ᶠ y in 𝓝[≠] x, AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x y) :=
    eventually_nhdsNE_comp_chart_apply_iff.mpr h1
  have h3 : ∀ᶠ y in 𝓝[≠] x, y ∈ (chartAt ℂ x).source :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  have h4 : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 := ordAtX_ne_top_iff hf |>.1 h
  have h5 : ∀ᶠ y in 𝓝[≠] x, (chartAt ℂ x).symm (chartAt ℂ x y) = y :=
    ((chartAt ℂ x).eventually_left_inverse (mem_chart_source ℂ x)).filter_mono nhdsWithin_le_nhds
  filter_upwards [h2, h3, h4, h5] with y h2y h3y h4y h5y
  rw [ordAtX_eq_of_mem_source (IsManifold.chart_mem_maximalAtlas x) h3y]
  refine h2y.meromorphicOrderAt_eq.trans ?_
  have hval : (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x y) ≠ 0 := by
    simp only [Function.comp_apply, h5y]; exact h4y
  rw [h2y.analyticOrderAt_eq_zero.mpr hval]
  rfl

end ChartInvariance

/-! ### CC4 compatibility -/

/--
@isnad1 id=eq.2h3v.s7.63d2f636036a from=translated src=- shape=229f9dcf vocab=59dfedcc
-/
theorem ordAtX_of_contMDiffAt_eq_zero (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) (h0 : f x = 0) :
    ordAtX f x = (multiplicityENat f x).map (Nat.cast : ℕ → ℤ) :=
  meromorphicOrderAt_chart_of_eq_zero hf h0

end RS
