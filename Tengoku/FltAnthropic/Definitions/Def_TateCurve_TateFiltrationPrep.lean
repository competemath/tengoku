import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_TateCurve_PointSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped NNReal

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/--
@isnad1 id=isometry.1h2v.s7.ab2a15a103e7 from=translated src=- shape=f9f9c1af vocab=cc48e6bf
-/
theorem isometry_of_forall_nnnorm {σ : K →+* K} (h : ∀ x, ‖σ x‖₊ = ‖x‖₊) : Isometry ⇑σ :=
  Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← coe_nnnorm, ← coe_nnnorm, h]

/--
@isnad1 id=eq.2h4v.s8.33991544a6a4 from=translated src=- shape=dde5b8cb vocab=d753f359
-/
theorem map_tsum_of_summable {ι : Type*} (σ : K →+* K) (hσ : Isometry ⇑σ) {f : ι → K}
    (hf : Summable f) : σ (∑' i, f i) = ∑' i, σ (f i) := by
  have h := hf.hasSum.map σ hσ.continuous
  simpa [Function.comp] using h.tsum_eq.symm

/--
@isnad1 id=eq.0h3v.s7.d292cee2da06 from=translated src=- shape=d3436171 vocab=d6153218
-/
theorem map_xfun (σ : K →+* K) (w : K) : σ (xfun w) = xfun (σ w) := by
  simp only [xfun, map_div₀, map_pow, map_sub, map_one]

/--
@isnad1 id=eq.0h3v.s7.6ceb16249d7b from=translated src=- shape=d3436171 vocab=73d13f04
-/
theorem map_yfun (σ : K →+* K) (w : K) : σ (yfun w) = yfun (σ w) := by
  simp only [yfun, map_div₀, map_pow, map_sub, map_one]

/--
@isnad1 id=eq.1h5v.s7.3d2c8a496b38 from=translated src=- shape=26125695 vocab=a6bb25ba
-/
theorem map_term (σ : K →+* K) {q : K} (hσq : σ q = q) (c : ℕ → ℕ) (n : ℕ) :
    σ (term c q n) = term c q n := by
  simp only [term, map_mul, map_natCast, map_div₀, map_pow, map_sub, map_one, hσq]

/--
@isnad1 id=eq.1h5v.s8.9a32e2d773c0 from=translated src=- shape=2155201f vocab=edb6a301
-/
theorem map_xTerm (σ : K →+* K) {q : K} (hσq : σ q = q) (u : K) (n : ℤ) :
    σ (xTerm q u n) = xTerm q (σ u) n := by
  simp only [xTerm, map_xfun, map_mul, map_zpow₀, hσq]

/--
@isnad1 id=eq.1h5v.s8.77f716c3b52f from=translated src=- shape=2155201f vocab=5c8eb18f
-/
theorem map_yTerm (σ : K →+* K) {q : K} (hσq : σ q = q) (u : K) (n : ℤ) :
    σ (yTerm q u n) = yTerm q (σ u) n := by
  simp only [yTerm, map_yfun, map_mul, map_zpow₀, hσq]

/--
@isnad1 id=eq.3h4v.s8.99a4fdf3ce33 from=translated src=- shape=f413a9b3 vocab=8a847dd6
-/
theorem map_coeffSum (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (c : ℕ → ℕ)
    (hsum : Summable (term c q)) : σ (coeffSum c q) = coeffSum c q := by
  have h := map_tsum_of_summable σ hσ hsum
  simp only [coeffSum]
  rw [h]
  exact tsum_congr fun n => map_term σ hσq c n

variable [CompleteSpace K]

/--
@isnad1 id=eq.3h3v.s8.a5f2887ab0e0 from=translated src=- shape=84dc1af7 vocab=826d9498
-/
theorem map_s₁ (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (hq : ‖q‖₊ < 1) :
    σ (s₁ q) = s₁ q := by
  simp only [s₁]
  exact map_coeffSum σ hσ hσq _ (summable_term _ hq)

/--
@isnad1 id=eq.3h3v.s8.4ea628c2cf62 from=translated src=- shape=84dc1af7 vocab=6d8e2409
-/
theorem map_a₄ (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (hq : ‖q‖₊ < 1) :
    σ (a₄ q) = a₄ q := by
  simp only [a₄, map_neg]
  exact congrArg Neg.neg (map_coeffSum σ hσ hσq _ (summable_term _ hq))

/--
@isnad1 id=eq.3h3v.s8.34691183f07b from=translated src=- shape=84dc1af7 vocab=f88f4d31
-/
theorem map_a₆ (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (hq : ‖q‖₊ < 1) :
    σ (a₆ q) = a₆ q := by
  simp only [a₆, map_neg]
  exact congrArg Neg.neg (map_coeffSum σ hσ hσq _ (summable_term _ hq))

/--
@isnad1 id=eq.3h3v.s8.5f5db367cabf from=translated src=- shape=e96cc3e9 vocab=5cb9ecc0
-/
theorem map_curve (σ : K →+* K) (hσ : Isometry ⇑σ) {q : K} (hσq : σ q = q) (hq : ‖q‖₊ < 1) :
    (curve q).map σ = curve q := by
  ext <;>
    simp [curve, WeierstrassCurve.map, map_a₄ σ hσ hσq hq, map_a₆ σ hσ hσq hq]

/--
@isnad1 id=eq.5h4v.s8.853039016e46 from=translated src=- shape=f0a05b21 vocab=0f8da602
-/
theorem map_pointX (σ : K →+* K) (hσ : Isometry ⇑σ) {q u : K} (hσq : σ q = q)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    σ (pointX q u) = pointX q (σ u) := by
  simp only [pointX, map_sub, map_mul, map_ofNat]
  rw [map_s₁ σ hσ hσq hq, map_tsum_of_summable σ hσ (summable_xTerm hq0 hq hu0)]
  congr 1
  exact tsum_congr fun n => map_xTerm σ hσq u n

/--
@isnad1 id=eq.5h4v.s8.445b0a05222c from=translated src=- shape=f0a05b21 vocab=d49905d3
-/
theorem map_pointY (σ : K →+* K) (hσ : Isometry ⇑σ) {q u : K} (hσq : σ q = q)
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    σ (pointY q u) = pointY q (σ u) := by
  simp only [pointY, map_add]
  rw [map_s₁ σ hσ hσq hq, map_tsum_of_summable σ hσ (summable_yTerm hq0 hq hu0)]
  congr 1
  exact tsum_congr fun n => map_yTerm σ hσq u n

/--
@isnad1 id=eq.6h4v.s8.b7280f06e26b from=translated src=- shape=37ab83c0 vocab=0f8da602
-/
theorem map_pointX_eq_self (σ : K →+* K) (hσ : Isometry ⇑σ) {q u : K} (hσq : σ q = q)
    (hσu : σ u = u) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    σ (pointX q u) = pointX q u := by
  rw [map_pointX σ hσ hσq hq0 hq hu0, hσu]

/--
@isnad1 id=eq.6h4v.s8.9f24f1793630 from=translated src=- shape=37ab83c0 vocab=d49905d3
-/
theorem map_pointY_eq_self (σ : K →+* K) (hσ : Isometry ⇑σ) {q u : K} (hσq : σ q = q)
    (hσu : σ u = u) (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    σ (pointY q u) = pointY q u := by
  rw [map_pointY σ hσ hσq hq0 hq hu0, hσu]

end TateCurve
