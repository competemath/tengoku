import Tengoku.Barbier.Barbier.ReuleauxLength
import Tengoku.Barbier.Barbier.ConvexBodyBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Layer 14: Mathlib-only restatements of the Barbier side

Every `l14_*` theorem below has a statement mentioning only Mathlib notions: the curve
`γ_h(t) = (h t + i h'(t)) e^{it}` is written out as a lambda, the perimeter is the integral
`∫₀^{2π} ‖γ_h'‖`, length is Mathlib's `eVariationOn`, the body is the intersection of half-planes
written out, and the Reuleaux support function is any `R` satisfying its defining equation.
The `l14b_*` lemmas are the bridges to the library's own definitions; the `l14w_*` theorems are
explicit witnesses (non-vacuity).
-/

noncomputable section

open Real MeasureTheory intervalIntegral

namespace Barbier

/-! ### Bridges -/

/--
@isnad1 id=eq.0h1v.s6.bac1f8aeb024 from=translated src=- shape=4be6bdaa vocab=f36fccb0
-/
theorem l14b_curve (h : ℝ → ℝ) :
    (fun t : ℝ => ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I))
      = curve h := rfl

/--
@isnad1 id=eq.0h1v.s7.76bae0b8c65c from=translated src=- shape=69476de3 vocab=332d2d3f
-/
theorem l14b_perimeter (h : ℝ → ℝ) :
    (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) θ‖)
      = perimeter h := rfl

/--
@isnad1 id=eq.0h1v.s5.d834f8cc18bd from=translated src=- shape=5ad6da51 vocab=502c857d
-/
theorem l14b_body (h : ℝ → ℝ) :
    (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ}) = body h := rfl

/--
@isnad1 id=constwid.4h2v.s7.be1322701d87 from=translated src=- shape=b7cf35a3 vocab=04441cbd
-/
theorem l14b_constWidth {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 2 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hc : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ) : ConstWidthSupport h w := ⟨hs, hp, hw, hc⟩

/--
@isnad1 id=piecewis.5h2v.s8.d57a71393d18 from=translated src=- shape=ba876993 vocab=6977f1b9
-/
theorem l14b_piecewise {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 1 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hS : ∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv h) θ) ∧
      (∀ θ ∉ S, 0 ≤ h θ + deriv (deriv h) θ))
    (hi : IntervalIntegrable (fun θ => h θ + deriv (deriv h) θ) volume 0 (2 * π)) :
    PiecewiseConstWidth h w := ⟨hs, hp, hw, hS, hi⟩

/--
@isnad1 id=iff.0h2v.s8.9d2130670ef6 from=translated src=- shape=d7909cdb vocab=6977f1b9
-/
theorem l14b_piecewise_iff {h : ℝ → ℝ} {w : ℝ} : PiecewiseConstWidth h w ↔
    (ContDiff ℝ 1 h ∧ Function.Periodic h (2 * π) ∧ (∀ θ, h θ + h (θ + π) = w) ∧
    (∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv h) θ) ∧
      (∀ θ ∉ S, 0 ≤ h θ + deriv (deriv h) θ)) ∧
    IntervalIntegrable (fun θ => h θ + deriv (deriv h) θ) volume 0 (2 * π)) :=
  ⟨fun H => ⟨H.smooth, H.periodic, H.width, H.breaks, H.integrable⟩,
   fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/--
@isnad1 id=eq.1h2v.s8.cd7ce90fac51 from=translated src=- shape=04dfe908 vocab=28333fba
-/
theorem l14b_reuleaux {w : ℝ} {R : ℝ → ℝ}
    (hR : ∀ θ, R θ =
      if toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ ≤ π / 6 then
        (w / Real.sqrt 3) * Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ)
      else w - (w / Real.sqrt 3) *
        Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ - π / 3)) :
    R = reuleaux w := funext fun θ => hR θ

/--
@isnad1 id=contdiff.1h1v.s6.a38eabc1ba86 from=translated src=- shape=52f5008f vocab=6acec22b
-/
theorem l14b_contDiff_curve {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) : ContDiff ℝ 1 (curve h) := by
  unfold curve
  apply ContDiff.mul
  · apply ContDiff.add
    · exact Complex.ofRealCLM.contDiff.comp (hh.of_le (by norm_num))
    · apply ContDiff.mul
      · exact Complex.ofRealCLM.contDiff.comp (contDiff_one_deriv hh)
      · exact contDiff_const
  · apply ContDiff.cexp
    apply ContDiff.mul
    · exact Complex.ofRealCLM.contDiff.comp contDiff_id
    · exact contDiff_const

/-! ### Theorem (Barbier, smooth) -/

/-- Barbier, smooth: the perimeter integral is `π w`, and so is Mathlib's length
(`eVariationOn`) of the curve over one period.
@isnad1 id=and.4h2v.s8.bd828f52e0b9 from=translated src=- shape=3a38144a vocab=015f3b2f
-/
theorem l14_barbier {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 2 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hc : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ) :
    (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) θ‖) = π * w ∧
    eVariationOn (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I))
      (Set.Icc 0 (2 * π)) = ENNReal.ofReal (π * w) := by
  have H := l14b_constWidth hs hp hw hc
  refine ⟨barbier H, ?_⟩
  rw [l14b_curve]
  have nt := eVariationOn_ne_top_of_contDiff (l14b_contDiff_curve hs)
    (by positivity : (0 : ℝ) ≤ 2 * π)
  rw [← ENNReal.ofReal_toReal nt, ← perimeter_eq_eVariationOn hs hp hc, barbier H]

/-! ### Proposition (smooth ⇒ piecewise) -/

/--
@isnad1 id=and.4h2v.s9.de3b83e0b6cb from=translated src=- shape=ce9188e3 vocab=2b81e3d1
-/
theorem l14_toPiecewise {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 2 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hc : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ) :
    ContDiff ℝ 1 h ∧ Function.Periodic h (2 * π) ∧ (∀ θ, h θ + h (θ + π) = w) ∧
    (∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv h) θ) ∧
      (∀ θ ∉ S, 0 ≤ h θ + deriv (deriv h) θ)) ∧
    IntervalIntegrable (fun θ => h θ + deriv (deriv h) θ) volume 0 (2 * π) :=
  l14b_piecewise_iff.1 (l14b_constWidth hs hp hw hc).toPiecewise

/-! ### Theorem (Barbier, with corners) -/

/--
@isnad1 id=eq.5h2v.s9.b38e31c1d13c from=translated src=- shape=b067dd0b vocab=291bf743
-/
theorem l14_barbier_piecewise {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 1 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hS : ∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv h) θ) ∧
      (∀ θ ∉ S, 0 ≤ h θ + deriv (deriv h) θ))
    (hi : IntervalIntegrable (fun θ => h θ + deriv (deriv h) θ) volume 0 (2 * π)) :
    (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) θ‖) = π * w :=
  barbier_piecewise (l14b_piecewise hs hp hw hS hi)

/-! ### Theorem (Reuleaux triangle), parts (a)–(f) -/

/-! ### Theorem (length of a `C¹` curve): already Mathlib-only -/

/--
@isnad1 id=and.2h3v.s7.30edcd132d23 from=translated src=- shape=f9a4f330 vocab=1b18522e
-/
theorem l14_length {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) {a b : ℝ} (hab : a ≤ b) :
    eVariationOn γ (Set.Icc a b) ≠ ⊤ ∧
      (eVariationOn γ (Set.Icc a b)).toReal = ∫ t in a..b, ‖deriv γ t‖ :=
  length_eq_integral_norm_deriv hγ hab

/-! ### Corollary (perimeter is length) -/

/--
@isnad1 id=and.3h1v.s9.7304ddf3fbeb from=translated src=- shape=c8c1a7d3 vocab=6500b576
-/
theorem l14_perimeter_eq_eVariationOn {h : ℝ → ℝ} (hs : ContDiff ℝ 2 h)
    (hp : Function.Periodic h (2 * π)) (hc : ∀ θ, 0 ≤ h θ + deriv (deriv h) θ) :
    (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) θ‖) =
    (eVariationOn (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I))
      (Set.Icc 0 (2 * π))).toReal ∧
    eVariationOn (fun t : ℝ =>
      ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I))
      (Set.Icc 0 (2 * π)) ≠ ⊤ :=
  ⟨perimeter_eq_eVariationOn hs hp hc,
   eVariationOn_ne_top_of_contDiff (l14b_contDiff_curve hs) (by positivity)⟩

/-! ### Theorem (the body) -/

/--
@isnad1 id=and.5h2v.s9.ecc8c0d093bf from=translated src=- shape=d7ea928c vocab=ab2ba198
-/
theorem l14_body {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 1 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hS : ∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv h) θ) ∧
      (∀ θ ∉ S, 0 ≤ h θ + deriv (deriv h) θ))
    (hi : IntervalIntegrable (fun θ => h θ + deriv (deriv h) θ) volume 0 (2 * π)) :
    Convex ℝ (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ}) ∧
    ∀ θ : ℝ,
      IsGreatest (Set.range fun φ => inner ℝ ((fun t : ℝ =>
        ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) φ)
        (Complex.exp (θ * Complex.I))) (h θ) ∧
      (fun t : ℝ => ((h t : ℂ) + ((deriv h t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (t * Complex.I)) θ ∈
        (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ}) ∧
      sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) ''
        (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ})) = h θ ∧
      sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) ''
        (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ}))
      + sSup ((fun z => (z * Complex.exp (-((θ + π : ℝ) : ℂ) * Complex.I)).re) ''
        (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ})) = w := by
  have H := l14b_piecewise hs hp hw hS hi
  exact ⟨convex_body h, fun θ => ⟨bridge_support_piecewise H θ, curve_mem_body_piecewise H θ,
    support_body_piecewise H θ, width_body_piecewise H θ⟩⟩

/-! ### Theorem (the body is a convex body) -/

/--
@isnad1 id=and.5h2v.s10.c3d46333ff28 from=translated src=- shape=b4b2e60e vocab=f340b437
-/
theorem l14_convexBody {h : ℝ → ℝ} {w : ℝ} (hs : ContDiff ℝ 1 h)
    (hp : Function.Periodic h (2 * π)) (hw : ∀ θ, h θ + h (θ + π) = w)
    (hS : ∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv h) θ) ∧
      (∀ θ ∉ S, 0 ≤ h θ + deriv (deriv h) θ))
    (hi : IntervalIntegrable (fun θ => h θ + deriv (deriv h) θ) volume 0 (2 * π)) :
    IsCompact (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ}) ∧
    (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ}).Nonempty ∧
    ∃ K : ConvexBody ℂ, (K : Set ℂ) = ⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ h θ} ∧
      (∀ θ : ℝ, sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) '' (K : Set ℂ)) = h θ) ∧
      (∀ θ : ℝ, sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) '' (K : Set ℂ))
        + sSup ((fun z => (z * Complex.exp (-((θ + π : ℝ) : ℂ) * Complex.I)).re) '' (K : Set ℂ)) = w) := by
  have H := l14b_piecewise hs hp hw hS hi
  exact ⟨isCompact_body_piecewise H, body_nonempty_piecewise H, exists_convexBody_piecewise H⟩

/--
@isnad1 id=ex.2h2v.s9.eac2e58602c4 from=translated src=- shape=99330c56 vocab=6f21e879
-/
theorem l14_reuleaux_convexBody {w : ℝ} (hw0 : 0 < w) {R : ℝ → ℝ}
    (hR : ∀ θ, R θ =
      if toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ ≤ π / 6 then
        (w / Real.sqrt 3) * Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ)
      else w - (w / Real.sqrt 3) *
        Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ - π / 3)) :
    ∃ K : ConvexBody ℂ, (K : Set ℂ) = ⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ R θ} ∧
      (∀ θ : ℝ, sSup ((fun z => (z * Complex.exp (-θ * Complex.I)).re) '' (K : Set ℂ))
        + sSup ((fun z => (z * Complex.exp (-((θ + π : ℝ) : ℂ) * Complex.I)).re) '' (K : Set ℂ)) = w) := by
  obtain rfl := l14b_reuleaux hR
  exact reuleaux_convexBody hw0

/-! ### Witnesses (non-vacuity) -/

/-- The smooth witness `h θ = 2 + cos(3θ)/4` (width 4) satisfies every hypothesis of
`l14_barbier`, `l14_toPiecewise` and `l14_perimeter_eq_eVariationOn`; it is not constant (not a
circle), and its curve is non-degenerate: `γ(0) ≠ γ(π)` and `γ(0) ≠ γ(π/3)`.
@isnad1 id=and.0h0v.s10.d113687bff04 from=translated src=- shape=0668f03f vocab=cdce7c8f
-/
theorem l14w_barbier :
    ContDiff ℝ 2 (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) ∧ Function.Periodic (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) (2 * π) ∧
    (∀ θ, (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) θ + (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) (θ + π) = 4) ∧
    (∀ θ, 0 ≤ (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) θ + deriv (deriv (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ))) θ) ∧
    (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) 0 ≠ (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) (π / 3) ∧
    (fun t : ℝ => (((fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) t : ℂ) + ((deriv (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) 0 ≠ (fun t : ℝ => (((fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) t : ℂ) + ((deriv (fun θ : ℝ => 2 + 1 / 4 * Real.cos (3 * θ)) t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) π ∧
    0 < π * 4 := by
  have H : ConstWidthSupport (trefoil 2 (1 / 4)) (2 * 2) :=
    trefoil_constWidth (by norm_num) (by norm_num)
  have hw := (bridge_constWidth H).1 0
  refine ⟨H.smooth, H.periodic, fun θ => by have := H.width θ; norm_num at this ⊢; exact this,
    H.convex, trefoil_not_const (by norm_num), ?_, by positivity⟩
  intro he
  change curve (trefoil 2 (1 / 4)) 0 = curve (trefoil 2 (1 / 4)) π at he
  rw [zero_add, he, sub_self, inner_zero_left] at hw
  norm_num at hw

/-- Reuleaux witness (`w = 1`): the function pinned down by the defining equation exists and
satisfies every hypothesis of `l14_barbier_piecewise`, `l14_body` and `l14_convexBody`; it is
genuinely non-smooth (`¬ C²`, so the smooth theorem does not apply) and its three corners
`γ(0), γ(2π/3), γ(4π/3)` are pairwise distinct; the perimeter `π · 1` is nonzero.
@isnad1 id=ex.0h0v.s10.d6a88e6c60ce from=translated src=- shape=e453acfb vocab=a4489726
-/
theorem l14w_reuleaux :
    ∃ R : ℝ → ℝ, (∀ θ, R θ =
      if toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ ≤ π / 6 then
        (1 / Real.sqrt 3) * Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ)
      else 1 - (1 / Real.sqrt 3) *
        Real.cos (toIcoMod (by positivity : (0 : ℝ) < 2 * π / 3) (-(π / 6)) θ - π / 3)) ∧
    (ContDiff ℝ 1 R ∧ Function.Periodic R (2 * π) ∧ (∀ θ, R θ + R (θ + π) = 1) ∧
    (∃ S : Set ℝ, S.Countable ∧ (∀ θ ∉ S, DifferentiableAt ℝ (deriv R) θ) ∧
      (∀ θ ∉ S, 0 ≤ R θ + deriv (deriv R) θ)) ∧
    IntervalIntegrable (fun θ => R θ + deriv (deriv R) θ) volume 0 (2 * π)) ∧
    ¬ ContDiff ℝ 2 R ∧
    (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) 0 ≠ (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) (2 * π / 3) ∧
    (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) (2 * π / 3) ≠ (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) (4 * π / 3) ∧
    (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) (4 * π / 3) ≠ (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) 0 ∧
    (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) 0 ∈ (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ R θ}) ∧ (fun t : ℝ => ((R t : ℂ) + ((deriv R t : ℝ) : ℂ) * Complex.I) * Complex.exp (t * Complex.I)) (2 * π / 3) ∈ (⋂ θ : ℝ, {z : ℂ | (z * Complex.exp (-θ * Complex.I)).re ≤ R θ}) ∧
    0 < π * 1 := by
  have hw : (0 : ℝ) < 1 := one_pos
  obtain ⟨d1, d2, d3⟩ := reuleaux_vertices hw
  refine ⟨reuleaux 1, fun θ => rfl, l14b_piecewise_iff.1 (reuleaux_constWidth hw),
    reuleaux_not_smooth hw, ?_, ?_, ?_, curve_mem_body_piecewise (reuleaux_constWidth hw) 0,
    curve_mem_body_piecewise (reuleaux_constWidth hw) _, by positivity⟩
  · intro he; change curve _ _ = curve _ _ at he; rw [he, dist_self] at d1; exact zero_ne_one d1
  · intro he; change curve _ _ = curve _ _ at he; rw [he, dist_self] at d2; exact zero_ne_one d2
  · intro he; change curve _ _ = curve _ _ at he; rw [he, dist_self] at d3; exact zero_ne_one d3

/-- Witness for `l14_length`: the `C¹` curve `t ↦ t` on `[0, 1]` (non-constant), whose length
integral is `1 ≠ 0`.
@isnad1 id=and.0h0v.s7.1c8e21f4cbd4 from=translated src=- shape=7fa9f53f vocab=2f0e06df
-/
theorem l14w_length :
    ContDiff ℝ 1 (fun t : ℝ => (t : ℂ)) ∧ (0 : ℝ) ≤ 1 ∧
    (fun t : ℝ => (t : ℂ)) 0 ≠ (fun t : ℝ => (t : ℂ)) 1 ∧
    (∫ t in (0 : ℝ)..1, ‖deriv (fun t : ℝ => (t : ℂ)) t‖) = 1 := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => (t : ℂ)) t = 1 := fun t =>
    ((hasDerivAt_id t).ofReal_comp).deriv
  refine ⟨Complex.ofRealCLM.contDiff, zero_le_one, by simp, ?_⟩
  simp [hd]

end Barbier
