import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dandelin spheres

Points are vectors of a real inner product space `E` (e.g. `EuclideanSpace ℝ (Fin 3)`).
The cone with apex `V`, unit axis `u` and half-angle `α` (with `k = cos α`, `s = sin α`) is
`{X | ⟪X - V, u⟫ = k * ‖X - V‖}` (one nappe). The sphere of centre `V + d • u` and radius
`d * s` is inscribed in it.
-/

open RealInnerProductSpace

namespace Dandelin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## (1) Tangent lengths -/

/-- Pythagoras for a tangent segment: if `F` is on the sphere `(c, r)` and `X - F ⟂ F - c`,
then `‖X - F‖² = ‖X - c‖² - r²`.-/
theorem tangent_length_sq {c F X : E} {r : ℝ} (hF : ‖F - c‖ = r)
    (hperp : ⟪X - F, F - c⟫ = 0) : ‖X - F‖ ^ 2 = ‖X - c‖ ^ 2 - r ^ 2 := by
  have h : X - c = (X - F) + (F - c) := by abel
  rw [h, norm_add_sq_real, hperp, hF]
  ring

/-- All tangent segments from a point to a sphere have equal length.-/
theorem tangent_lengths_eq {c F T X : E} {r : ℝ} (hF : ‖F - c‖ = r) (hT : ‖T - c‖ = r)
    (hF' : ⟪X - F, F - c⟫ = 0) (hT' : ⟪X - T, T - c⟫ = 0) : ‖X - F‖ = ‖X - T‖ := by
  have h1 := tangent_length_sq hF hF'
  have h2 := tangent_length_sq hT hT'
  have : ‖X - F‖ ^ 2 = ‖X - T‖ ^ 2 := by rw [h1, h2]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- Mathlib-phrased version: if `X` lies on two affine subspaces tangent to the sphere `S`
at `F` and at `T`, then `dist X F = dist X T`.-/
theorem dist_eq_of_isTangentAt {S : EuclideanGeometry.Sphere E} {F T X : E}
    {π ℓ : AffineSubspace ℝ E} (hπ : S.IsTangentAt F π) (hℓ : S.IsTangentAt T ℓ)
    (hXπ : X ∈ π) (hXℓ : X ∈ ℓ) : dist X F = dist X T := by
  have h1 := hπ.dist_sq_eq_of_mem hXπ
  have h2 := hℓ.dist_sq_eq_of_mem hXℓ
  have : dist X F ^ 2 = dist X T ^ 2 := by linarith
  exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 this

/-! ## (2) The cone model -/

/-- One nappe of the right circular cone with apex `V`, unit axis `u`, `k = cos α`.-/
def cone (V u : E) (k : ℝ) : Set E := {X | ⟪X - V, u⟫ = k * ‖X - V‖}

/-- Squared tangent length from a point of the cone to the inscribed sphere
`(V + d • u, d * s)`: it is `(‖X - V‖ - d k)²`.-/
theorem cone_tangent_sq {V u X : E} {k s d : ℝ} (hu : ‖u‖ = 1) (hks : k ^ 2 + s ^ 2 = 1)
    (hX : X ∈ cone V u k) :
    ‖X - (V + d • u)‖ ^ 2 - (d * s) ^ 2 = (‖X - V‖ - d * k) ^ 2 := by
  have hX' : ⟪X - V, u⟫ = k * ‖X - V‖ := hX
  have h : X - (V + d • u) = (X - V) - d • u := by abel
  rw [h, norm_sub_sq_real, real_inner_smul_right, hX', norm_smul, hu, mul_one,
    Real.norm_eq_abs, sq_abs]
  linear_combination (-d ^ 2) * hks

/-- The cone never enters the open ball of an inscribed sphere.-/
theorem cone_outside_sphere {V u X : E} {k s d : ℝ} (hu : ‖u‖ = 1) (hks : k ^ 2 + s ^ 2 = 1)
    (hX : X ∈ cone V u k) : (d * s) ^ 2 ≤ ‖X - (V + d • u)‖ ^ 2 := by
  have := cone_tangent_sq (d := d) hu hks hX
  nlinarith [sq_nonneg (‖X - V‖ - d * k)]

/-- A point on the generator through `X`, at distance `τ` from the apex.-/
theorem generator_dist_sq {V u X : E} {k d τ : ℝ} (hu : ‖u‖ = 1)
    (hX : X ∈ cone V u k) (ht : ‖X - V‖ ≠ 0) :
    ‖(V + (τ / ‖X - V‖) • (X - V)) - (V + d • u)‖ ^ 2 = τ ^ 2 - 2 * τ * d * k + d ^ 2 := by
  have hX' : ⟪X - V, u⟫ = k * ‖X - V‖ := hX
  have h : (V + (τ / ‖X - V‖) • (X - V)) - (V + d • u) =
      (τ / ‖X - V‖) • (X - V) - d • u := by abel
  rw [h, norm_sub_sq_real, norm_smul, norm_smul, hu, real_inner_smul_left,
    real_inner_smul_right, hX', Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
    sq_abs]
  field_simp

/-- The tangency point of the generator through `X` with the inscribed sphere.-/
noncomputable def tangencyPoint (V X : E) (k d : ℝ) : E :=
  V + (d * k / ‖X - V‖) • (X - V)

/-- The tangency point lies on the inscribed sphere.-/
theorem tangencyPoint_mem_sphere {V u X : E} {k s d : ℝ} (hu : ‖u‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hds : 0 ≤ d * s) (hX : X ∈ cone V u k) (ht : ‖X - V‖ ≠ 0) :
    ‖tangencyPoint V X k d - (V + d • u)‖ = d * s := by
  have h := generator_dist_sq (τ := d * k) (d := d) hu hX ht
  unfold tangencyPoint
  have h2 : ‖(V + (d * k / ‖X - V‖) • (X - V)) - (V + d • u)‖ ^ 2 = (d * s) ^ 2 := by
    rw [h]; linear_combination (-d ^ 2) * hks
  exact (pow_left_inj₀ (norm_nonneg _) hds two_ne_zero).1 h2

/-- The generator is tangent to the sphere at the tangency point.-/
theorem tangencyPoint_perp {V u X : E} {k d : ℝ}
    (hX : X ∈ cone V u k) (ht : ‖X - V‖ ≠ 0) :
    ⟪X - tangencyPoint V X k d, tangencyPoint V X k d - (V + d • u)⟫ = 0 := by
  have hX' : ⟪X - V, u⟫ = k * ‖X - V‖ := hX
  unfold tangencyPoint
  have h1 : X - (V + (d * k / ‖X - V‖) • (X - V)) = (1 - d * k / ‖X - V‖) • (X - V) := by
    rw [sub_smul, one_smul]; abel
  have h2 : (V + (d * k / ‖X - V‖) • (X - V)) - (V + d • u) =
      (d * k / ‖X - V‖) • (X - V) - d • u := by abel
  rw [h1, h2, inner_sub_right, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_right, hX', real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- Distance from `X` to the tangency point along the generator.-/
theorem dist_tangencyPoint {V X : E} {k d : ℝ} (ht : ‖X - V‖ ≠ 0) :
    ‖X - tangencyPoint V X k d‖ = |‖X - V‖ - d * k| := by
  unfold tangencyPoint
  have h1 : X - (V + (d * k / ‖X - V‖) • (X - V)) = (1 - d * k / ‖X - V‖) • (X - V) := by
    rw [sub_smul, one_smul]; abel
  rw [h1, norm_smul, Real.norm_eq_abs, ← abs_norm (X - V), ← abs_mul, abs_norm]
  congr 1
  field_simp

/-- Tangent length from a point `X` of the cone, via a tangent plane touching the inscribed
sphere `(V + d • u, d * s)` at `F`: `‖X - F‖ = |‖X - V‖ - d k|`.-/
theorem dist_tangent_eq {V u X F : E} {k s d : ℝ} (hu : ‖u‖ = 1) (hks : k ^ 2 + s ^ 2 = 1)
    (hX : X ∈ cone V u k) (hF : ‖F - (V + d • u)‖ = d * s)
    (hperp : ⟪X - F, F - (V + d • u)⟫ = 0) : ‖X - F‖ = |‖X - V‖ - d * k| := by
  have h1 := tangent_length_sq hF hperp
  have h2 := cone_tangent_sq (d := d) hu hks hX
  have h3 : ‖X - F‖ ^ 2 = |‖X - V‖ - d * k| ^ 2 := by rw [sq_abs, h1, h2]
  exact (pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).1 h3

/-! ## (3) Dandelin's theorem -/

/-- **Dandelin's theorem**, with the "between the two tangency circles" hypothesis.
If a plane through `X` touches the two inscribed spheres `(V + dᵢ • u, dᵢ * s)` at `F₁`, `F₂`,
then `‖X - F₁‖ + ‖X - F₂‖ = (d₂ - d₁) k`.-/
theorem dandelin_of_between {V u X F₁ F₂ : E} {k s d₁ d₂ : ℝ} (hu : ‖u‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hX : X ∈ cone V u k)
    (hF₁ : ‖F₁ - (V + d₁ • u)‖ = d₁ * s) (hF₂ : ‖F₂ - (V + d₂ • u)‖ = d₂ * s)
    (hp₁ : ⟪X - F₁, F₁ - (V + d₁ • u)⟫ = 0) (hp₂ : ⟪X - F₂, F₂ - (V + d₂ • u)⟫ = 0)
    (hb₁ : d₁ * k ≤ ‖X - V‖) (hb₂ : ‖X - V‖ ≤ d₂ * k) :
    ‖X - F₁‖ + ‖X - F₂‖ = (d₂ - d₁) * k := by
  rw [dist_tangent_eq hu hks hX hF₁ hp₁, dist_tangent_eq hu hks hX hF₂ hp₂,
    abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  ring

/-- Same statement phrased with Mathlib's `EuclideanGeometry.Sphere` and `Sphere.IsTangentAt`
for an arbitrary affine subspace `π` (a plane) tangent to both spheres.-/
theorem dandelin_of_between_isTangentAt {V u X F₁ F₂ : E} {k s d₁ d₂ : ℝ}
    {S₁ S₂ : EuclideanGeometry.Sphere E} {π : AffineSubspace ℝ E} (hu : ‖u‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hX : X ∈ cone V u k)
    (hc₁ : S₁.center = V + d₁ • u) (hr₁ : S₁.radius = d₁ * s)
    (hc₂ : S₂.center = V + d₂ • u) (hr₂ : S₂.radius = d₂ * s)
    (ht₁ : S₁.IsTangentAt F₁ π) (ht₂ : S₂.IsTangentAt F₂ π) (hXπ : X ∈ π)
    (hb₁ : d₁ * k ≤ ‖X - V‖) (hb₂ : ‖X - V‖ ≤ d₂ * k) :
    dist X F₁ + dist X F₂ = (d₂ - d₁) * k := by
  have e₁ := ht₁.dist_sq_eq_of_mem hXπ
  have e₂ := ht₂.dist_sq_eq_of_mem hXπ
  rw [hc₁, hr₁, dist_eq_norm, dist_eq_norm] at e₁
  rw [hc₂, hr₂, dist_eq_norm, dist_eq_norm] at e₂
  have q₁ := cone_tangent_sq (d := d₁) hu hks hX
  have q₂ := cone_tangent_sq (d := d₂) hu hks hX
  have f₁ : ‖X - F₁‖ ^ 2 = (‖X - V‖ - d₁ * k) ^ 2 := by linear_combination q₁ - e₁
  have f₂ : ‖X - F₂‖ ^ 2 = (d₂ * k - ‖X - V‖) ^ 2 := by linear_combination q₂ - e₂
  rw [dist_eq_norm, dist_eq_norm,
    (pow_left_inj₀ (norm_nonneg _) (by linarith) two_ne_zero).1 f₁,
    (pow_left_inj₀ (norm_nonneg _) (by linarith) two_ne_zero).1 f₂]
  ring

/-- Real-algebra core of the "between" property: the Gram/Cauchy–Schwarz inequality
`Q(t) ≥ 0` together with the two tangency equations forces `d₁ k ≤ t ≤ d₂ k`.-/
theorem between_of_gram {k s m a t d₁ d₂ : ℝ} (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k)
    (hs : 0 < s) (hd₁ : 0 < d₁) (hd : d₁ < d₂) (h₁ : a = d₁ * (m + s)) (h₂ : a = d₂ * (m - s))
    (hQ : 0 ≤ (1 - k ^ 2 - m ^ 2) * t ^ 2 + 2 * k * m * a * t - a ^ 2) :
    d₁ * k ≤ t ∧ t ≤ d₂ * k := by
  have hprod : (d₂ - d₁) * (m - s) = 2 * d₁ * s := by linear_combination h₁ - h₂
  have hms : 0 < m - s := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hd.le) hc, mul_pos hd₁ hs]
  have hmps : 0 < m + s := by linarith
  have hsm : s ^ 2 - m ^ 2 < 0 := by nlinarith
  constructor
  · by_contra hc
    push Not at hc
    have hB : 0 < (s ^ 2 - m ^ 2) * (t + d₁ * k) + 2 * k * m * a := by
      rw [h₁]
      nlinarith [mul_pos_of_neg_of_neg hsm (sub_neg.2 hc),
        mul_pos (mul_pos hd₁ hk) (mul_pos hs hmps)]
    have hQ' : (1 - k ^ 2 - m ^ 2) * t ^ 2 + 2 * k * m * a * t - a ^ 2 =
        -(d₁ * (m + s) * s) ^ 2 +
          (t - d₁ * k) * ((s ^ 2 - m ^ 2) * (t + d₁ * k) + 2 * k * m * a) := by
      rw [h₁]
      linear_combination (d₁ ^ 2 * (m + s) ^ 2 - t ^ 2) * hks
    have hneg := mul_neg_of_neg_of_pos (sub_neg.2 hc) hB
    have hpos : 0 < d₁ * (m + s) * s := mul_pos (mul_pos hd₁ hmps) hs
    nlinarith
  · by_contra hc
    push Not at hc
    have hB : (s ^ 2 - m ^ 2) * (t + d₂ * k) + 2 * k * m * a < 0 := by
      rw [h₂]
      nlinarith [mul_neg_of_neg_of_pos hsm (sub_pos.2 hc),
        mul_pos (mul_pos (hd₁.trans hd) hk) (mul_pos hs hms)]
    have hQ' : (1 - k ^ 2 - m ^ 2) * t ^ 2 + 2 * k * m * a * t - a ^ 2 =
        -(d₂ * (m - s) * s) ^ 2 +
          (t - d₂ * k) * ((s ^ 2 - m ^ 2) * (t + d₂ * k) + 2 * k * m * a) := by
      rw [h₂]
      linear_combination (d₂ ^ 2 * (m - s) ^ 2 - t ^ 2) * hks
    have hneg := mul_neg_of_pos_of_neg (sub_pos.2 hc) hB
    have hpos : 0 < d₂ * (m - s) * s := mul_pos (mul_pos (hd₁.trans hd) hms) hs
    nlinarith

/-- **Dandelin's theorem** (no "between" hypothesis). Cone with apex `V`, unit axis `u`,
`cos α = k > 0`, `sin α = s > 0`. Inscribed spheres with centres `V + dᵢ • u`, radii `dᵢ s`,
`0 < d₁ < d₂`. The plane with unit normal `n` through `F₁ = V + d₁ • u + (d₁ s) • n` and
`F₂ = V + d₂ • u - (d₂ s) • n` is tangent to both spheres, at `F₁` and `F₂`, with the spheres
on opposite sides. Then every point `X` of the section plane ∩ cone satisfies
`‖X - F₁‖ + ‖X - F₂‖ = (d₂ - d₁) cos α`.-/
theorem dandelin {V u n X F₁ F₂ : E} {k s d₁ d₂ : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hF₁ : F₁ = V + d₁ • u + (d₁ * s) • n) (hF₂ : F₂ = V + d₂ • u - (d₂ * s) • n)
    (hF₂π : ⟪F₂ - F₁, n⟫ = 0) (hXπ : ⟪X - F₁, n⟫ = 0) (hX : X ∈ cone V u k) :
    ‖X - F₁‖ + ‖X - F₂‖ = (d₂ - d₁) * k := by
  have hwu : ⟪X - V, u⟫ = k * ‖X - V‖ := hX
  have hXπ₂ : ⟪X - F₂, n⟫ = 0 := by
    have : X - F₂ = (X - F₁) - (F₂ - F₁) := by abel
    rw [this, inner_sub_left, hXπ, hF₂π, sub_zero]
  -- the two tangency equations
  have ha₁ : ⟪X - V, n⟫ = d₁ * ⟪u, n⟫ + d₁ * s := by
    have e : X - F₁ = (X - V) - (d₁ • u + (d₁ * s) • n) := by rw [hF₁]; abel
    rw [e, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hn] at hXπ
    linarith
  have ha₂ : ⟪X - V, n⟫ = d₂ * ⟪u, n⟫ - d₂ * s := by
    have e : X - F₂ = (X - V) - (d₂ • u - (d₂ * s) • n) := by rw [hF₂]; abel
    rw [e, inner_sub_left (X - V), inner_sub_left (d₂ • u), real_inner_smul_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq, hn] at hXπ₂
    linarith
  -- Cauchy–Schwarz after projecting out the axis
  have hQ : 0 ≤ (1 - k ^ 2 - ⟪u, n⟫ ^ 2) * ‖X - V‖ ^ 2 + 2 * k * ⟪u, n⟫ * ⟪X - V, n⟫ * ‖X - V‖
      - ⟪X - V, n⟫ ^ 2 := by
    clear ha₁ ha₂ hXπ hXπ₂ hF₂π hF₁ hF₂ hX
    generalize X - V = w at *
    have hcs := real_inner_mul_inner_self_le (w - (k * ‖w‖) • u) (n - ⟪u, n⟫ • u)
    have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
    have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
    have hww : ⟪w, w⟫ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq _
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      huu, hnn, hww] at hcs
    have c1 : ⟪u, w⟫ = k * ‖w‖ := by rw [real_inner_comm]; exact hwu
    have c2 : ⟪n, u⟫ = ⟪u, n⟫ := real_inner_comm _ _
    simp only [c1, c2, hwu] at hcs
    nlinarith [hcs]
  have hbt := between_of_gram hks hk hs hd₁ hd (by rw [ha₁]; ring) (by rw [ha₂]; ring) hQ
  -- tangency of the plane
  have hc₁ : F₁ - (V + d₁ • u) = (d₁ * s) • n := by rw [hF₁]; abel
  have hc₂ : F₂ - (V + d₂ • u) = -((d₂ * s) • n) := by rw [hF₂]; abel
  have hr₁ : ‖F₁ - (V + d₁ • u)‖ = d₁ * s := by
    rw [hc₁, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos (mul_pos hd₁ hs)]
  have hr₂ : ‖F₂ - (V + d₂ • u)‖ = d₂ * s := by
    rw [hc₂, norm_neg, norm_smul, hn, mul_one, Real.norm_eq_abs,
      abs_of_pos (mul_pos (hd₁.trans hd) hs)]
  have hp₁ : ⟪X - F₁, F₁ - (V + d₁ • u)⟫ = 0 := by
    rw [hc₁, real_inner_smul_right, hXπ, mul_zero]
  have hp₂ : ⟪X - F₂, F₂ - (V + d₂ • u)⟫ = 0 := by
    rw [hc₂, inner_neg_right, real_inner_smul_right, hXπ₂, mul_zero, neg_zero]
  exact dandelin_of_between hu hks hX hr₁ hr₂ hp₁ hp₂ hbt.1 hbt.2

/-! ## (4) Focus–directrix-plane form -/

/-- For `X` on the cone beyond the first tangency circle, the focal distance equals
`1 / cos α` times the (signed) distance from `X` to the plane `⟪Y - V, u⟫ = d₁ k²` of the
first tangency circle.-/
theorem focal_dist_eq_div {V u X F : E} {k s d : ℝ} (hu : ‖u‖ = 1) (hks : k ^ 2 + s ^ 2 = 1)
    (hk : 0 < k) (hX : X ∈ cone V u k) (hF : ‖F - (V + d • u)‖ = d * s)
    (hperp : ⟪X - F, F - (V + d • u)⟫ = 0) (hb : d * k ≤ ‖X - V‖) :
    ‖X - F‖ = (⟪X - V, u⟫ - d * k ^ 2) / k := by
  have hX' : ⟪X - V, u⟫ = k * ‖X - V‖ := hX
  rw [dist_tangent_eq hu hks hX hF hperp, abs_of_nonneg (by linarith), hX']
  field_simp

end Dandelin
