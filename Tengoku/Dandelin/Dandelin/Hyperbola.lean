import Tengoku.Dandelin.Dandelin.Directrix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dandelin spheres, phase 4: the hyperbola

Two-nappe cone `cone2 V u k = {X | ⟪X - V, u⟫² = k² ‖X - V‖²}` (apex `V`, unit axis `u`,
`k = cos α`, `s = sin α`). Cutting plane `plane p₀ n`, `m = ⟪u, n⟫`, `c = ⟪p₀ - V, n⟫`.
Hyperbola regime: `|m| < s` (the plane is steeper than a generator) and `c ≠ 0` (it misses the
apex); normalised: `0 < c`. The two Dandelin spheres are `(V + dᵢ • u, |dᵢ| s)` with
`d₁ = c / (m + s) > 0` (upper nappe) and `d₂ = c / (m - s) < 0` (lower nappe), i.e. the
`param₁`, `param₂` of `Existence.lean`.
-/

open RealInnerProductSpace

namespace Dandelin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The double (two-nappe) cone.-/
def cone2 (V u : E) (k : ℝ) : Set E := {X | ⟪X - V, u⟫ ^ 2 = k ^ 2 * ‖X - V‖ ^ 2}

/-- The double cone is the union of the nappe `cone V u k` and the opposite nappe
`cone V (-u) k`.-/
theorem mem_cone2_iff {V u X : E} {k : ℝ} :
    X ∈ cone2 V u k ↔ X ∈ cone V u k ∨ X ∈ cone V (-u) k := by
  show ⟪X - V, u⟫ ^ 2 = k ^ 2 * ‖X - V‖ ^ 2 ↔
    ⟪X - V, u⟫ = k * ‖X - V‖ ∨ ⟪X - V, -u⟫ = k * ‖X - V‖
  rw [inner_neg_right, ← mul_pow, sq_eq_sq_iff_eq_or_eq_neg, neg_eq_iff_eq_neg]

/-- Tangent length from a point of the nappe `cone V u k` to an axis sphere
`(V + d • u, |d| s)` with `d` of either sign: `‖X - F‖ = |‖X - V‖ - d k|`.-/
theorem dist_tangent_eq_abs {V u X F : E} {k s d : ℝ} (hu : ‖u‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hX : X ∈ cone V u k) (hF : ‖F - (V + d • u)‖ = |d| * s)
    (hperp : ⟪X - F, F - (V + d • u)⟫ = 0) : ‖X - F‖ = |‖X - V‖ - d * k| := by
  have h1 := tangent_length_sq hF hperp
  have h2 := cone_tangent_sq (d := d) hu hks hX
  have e : (|d| * s) ^ 2 = (d * s) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
  have h3 : ‖X - F‖ ^ 2 = |‖X - V‖ - d * k| ^ 2 := by
    rw [sq_abs, h1, e]; linarith [h2]
  exact (pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).1 h3

/-- Cauchy–Schwarz after projecting out the axis (as in the proof of `dandelin`).-/
theorem gram_ineq {u n w : E} {k : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hwu : ⟪w, u⟫ = k * ‖w‖) :
    0 ≤ (1 - k ^ 2 - ⟪u, n⟫ ^ 2) * ‖w‖ ^ 2 + 2 * k * ⟪u, n⟫ * ⟪w, n⟫ * ‖w‖
      - ⟪w, n⟫ ^ 2 := by
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

/-- Real-algebra core: on the upper nappe, a point of a hyperbola-regime plane is beyond the
tangency circle of the upper sphere, `d₁ k ≤ ‖X - V‖`.-/
theorem hyp_between {k s m a t d₁ : ℝ} (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k)
    (hs : 0 < s) (hm1 : -s < m) (hm2 : m < s) (hd₁ : 0 < d₁) (h₁ : a = d₁ * (m + s))
    (ht : 0 ≤ t) (hQ : 0 ≤ (1 - k ^ 2 - m ^ 2) * t ^ 2 + 2 * k * m * a * t - a ^ 2) :
    d₁ * k ≤ t := by
  by_contra hc
  push Not at hc
  have hQ' : (1 - k ^ 2 - m ^ 2) * t ^ 2 + 2 * k * m * a * t - a ^ 2 =
      (m + s) * (-((s - m) * t * (d₁ * k - t)) + d₁ * (m + s) * (k * t - d₁)) := by
    rw [h₁]; linear_combination (-t ^ 2) * hks
  have e : k * t - d₁ = -(k * (d₁ * k - t)) - d₁ * (s * s) := by
    linear_combination d₁ * hks
  have hkt : k * t - d₁ < 0 := by
    rw [e]; nlinarith [mul_pos hk (sub_pos.2 hc), mul_pos hd₁ (mul_pos hs hs)]
  have h1 : 0 ≤ (s - m) * t * (d₁ * k - t) :=
    mul_nonneg (mul_nonneg (sub_nonneg.2 hm2.le) ht) (sub_nonneg.2 hc.le)
  have h2 : d₁ * (m + s) * (k * t - d₁) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hd₁ (by linarith)) hkt
  have h3 : (m + s) * (-((s - m) * t * (d₁ * k - t)) + d₁ * (m + s) * (k * t - d₁)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  linarith

/-! ## Parameters and tangency in the hyperbola regime -/

/-- **Exactly two axis spheres `(V + d • u, |d| s)` are tangent to the plane** in the hyperbola
regime `-s < ⟪u, n⟫ < s`: `d = d₁ = c/(m+s)` or `d = d₂ = c/(m-s)`.-/
theorem hyp_tangent_iff {V u n p₀ : E} {s : ℝ} (hs : 0 < s) (hm1 : -s < ⟪u, n⟫)
    (hm2 : ⟪u, n⟫ < s) (d : ℝ) :
    |⟪(V + d • u) - p₀, n⟫| = |d| * s ↔ d = param₁ V u n p₀ s ∨ d = param₂ V u n p₀ s := by
  have h1 : param₁ V u n p₀ s * (⟪u, n⟫ + s) = ⟪p₀ - V, n⟫ := by
    unfold param₁; field_simp [show ⟪u, n⟫ + s ≠ 0 by linarith]
  have h2 : param₂ V u n p₀ s * (⟪u, n⟫ - s) = ⟪p₀ - V, n⟫ := by
    unfold param₂; field_simp [show ⟪u, n⟫ - s ≠ 0 by linarith]
  have e : |d| * s = |d * s| := by rw [abs_mul, abs_of_pos hs]
  rw [inner_center_sub, e, abs_eq_abs]
  constructor
  · rintro (h | h)
    · right
      have : (d - param₂ V u n p₀ s) * (⟪u, n⟫ - s) = 0 := by linear_combination h - h2
      rcases mul_eq_zero.1 this with h3 | h3
      · linarith
      · exact absurd h3 (by linarith)
    · left
      have : (d - param₁ V u n p₀ s) * (⟪u, n⟫ + s) = 0 := by linear_combination h - h1
      rcases mul_eq_zero.1 this with h3 | h3
      · linarith
      · exact absurd h3 (by linarith)
  · rintro (rfl | rfl)
    · right; linear_combination h1
    · left; linear_combination h2

theorem hyp_param₁_pos {V u n p₀ : E} {s : ℝ} (hm1 : -s < ⟪u, n⟫) (hc : 0 < ⟪p₀ - V, n⟫) :
    0 < param₁ V u n p₀ s := div_pos hc (by linarith)

theorem hyp_param₂_neg {V u n p₀ : E} {s : ℝ} (hm2 : ⟪u, n⟫ < s) (hc : 0 < ⟪p₀ - V, n⟫) :
    param₂ V u n p₀ s < 0 := div_neg_of_pos_of_neg hc (by linarith)

/-- Squared tangent length from any point `X` (not necessarily on the cone) to an axis sphere
`(V + d • u, |d| s)` touched at `F` by a plane through `X`.-/
theorem focal_sq {V u X F : E} {k s d : ℝ} (hu : ‖u‖ = 1) (hks : k ^ 2 + s ^ 2 = 1)
    (hF : ‖F - (V + d • u)‖ = |d| * s) (hp : ⟪X - F, F - (V + d • u)⟫ = 0) :
    ‖X - F‖ ^ 2 = ‖X - V‖ ^ 2 - 2 * d * ⟪X - V, u⟫ + d ^ 2 * k ^ 2 := by
  have e := tangent_length_sq hF hp
  have expand : ‖X - (V + d • u)‖ ^ 2 = ‖X - V‖ ^ 2 - 2 * d * ⟪X - V, u⟫ + d ^ 2 := by
    have h : X - (V + d • u) = (X - V) - d • u := by abel
    rw [h, norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, mul_one,
      Real.norm_eq_abs, sq_abs]
    ring
  rw [expand, mul_pow, sq_abs] at e
  linear_combination e - d ^ 2 * hks

/-! ## The focal-difference theorem -/

/-- **Upper nappe.** In the hyperbola regime, with spheres `(V + dᵢ • u, |dᵢ| s)`,
`d₂ < 0 < d₁`, `⟪p₀ - V, n⟫ = d₁ (⟪u,n⟫ + s)`, touched at `Fᵢ` by the cutting plane: every `X` of
plane ∩ `cone V u k` has `‖X - F₂‖ - ‖X - F₁‖ = (d₁ - d₂) cos α`.-/
theorem hyp_upper {V u n p₀ X F₁ F₂ : E} {k s d₁ d₂ : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm1 : -s < ⟪u, n⟫)
    (hm2 : ⟪u, n⟫ < s) (hd₁ : 0 < d₁) (hd₂ : d₂ < 0) (hc : ⟪p₀ - V, n⟫ = d₁ * (⟪u, n⟫ + s))
    (hF₁ : ‖F₁ - (V + d₁ • u)‖ = |d₁| * s) (hp₁ : ⟪X - F₁, F₁ - (V + d₁ • u)⟫ = 0)
    (hF₂ : ‖F₂ - (V + d₂ • u)‖ = |d₂| * s) (hp₂ : ⟪X - F₂, F₂ - (V + d₂ • u)⟫ = 0)
    (hXπ : X ∈ plane p₀ n) (hX : X ∈ cone V u k) :
    ‖X - F₂‖ - ‖X - F₁‖ = (d₁ - d₂) * k := by
  have hXπ' : ⟪X - p₀, n⟫ = 0 := hXπ
  have ha : ⟪X - V, n⟫ = ⟪p₀ - V, n⟫ := by
    have : X - V = (X - p₀) + (p₀ - V) := by abel
    rw [this, inner_add_left, hXπ', zero_add]
  have hQ := gram_ineq (w := X - V) hu hn hX
  have hb := hyp_between (a := ⟪X - V, n⟫) (t := ‖X - V‖) (m := ⟪u, n⟫) hks hk hs hm1 hm2
    hd₁ (by rw [ha, hc]) (norm_nonneg _) hQ
  have hd₂k : d₂ * k < 0 := mul_neg_of_neg_of_pos hd₂ hk
  rw [dist_tangent_eq_abs hu hks hX hF₁ hp₁, dist_tangent_eq_abs hu hks hX hF₂ hp₂,
    abs_of_nonneg (show 0 ≤ ‖X - V‖ - d₂ * k by linarith [norm_nonneg (X - V)]),
    abs_of_nonneg (show 0 ≤ ‖X - V‖ - d₁ * k by linarith)]
  ring

/-- **Lower nappe** (`cone V (-u) k`): `‖X - F₁‖ - ‖X - F₂‖ = (d₁ - d₂) cos α`.-/
theorem hyp_lower {V u n p₀ X F₁ F₂ : E} {k s d₁ d₂ : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm1 : -s < ⟪u, n⟫)
    (hm2 : ⟪u, n⟫ < s) (hd₁ : 0 < d₁) (hd₂ : d₂ < 0) (hc₂ : ⟪p₀ - V, n⟫ = d₂ * (⟪u, n⟫ - s))
    (hF₁ : ‖F₁ - (V + d₁ • u)‖ = |d₁| * s) (hp₁ : ⟪X - F₁, F₁ - (V + d₁ • u)⟫ = 0)
    (hF₂ : ‖F₂ - (V + d₂ • u)‖ = |d₂| * s) (hp₂ : ⟪X - F₂, F₂ - (V + d₂ • u)⟫ = 0)
    (hXπ : X ∈ plane p₀ n) (hX : X ∈ cone V (-u) k) :
    ‖X - F₁‖ - ‖X - F₂‖ = (d₁ - d₂) * k := by
  have := hyp_upper (u := -u) (d₁ := -d₂) (d₂ := -d₁) (F₁ := F₂) (F₂ := F₁)
    (by rw [norm_neg, hu]) hn hks hk hs (by rw [inner_neg_left]; linarith)
    (by rw [inner_neg_left]; linarith) (by linarith) (by linarith)
    (by rw [inner_neg_left, hc₂]; ring) (by rw [neg_smul_neg, abs_neg]; exact hF₂)
    (by rw [neg_smul_neg]; exact hp₂) (by rw [neg_smul_neg, abs_neg]; exact hF₁)
    (by rw [neg_smul_neg]; exact hp₁) hXπ hX
  linear_combination this

/-! ## Converse -/

/-- Real-algebra core of the hyperbola converse.-/
theorem hyp_converse_alg {A B t p k d₁ d₂ e : ℝ} (hd : d₁ ≠ d₂) (he : e ^ 2 = 1)
    (hA2 : A ^ 2 = t ^ 2 - 2 * d₁ * p + d₁ ^ 2 * k ^ 2)
    (hB2 : B ^ 2 = t ^ 2 - 2 * d₂ * p + d₂ ^ 2 * k ^ 2)
    (hdiff : A - B = e * ((d₁ - d₂) * k)) : p ^ 2 = k ^ 2 * t ^ 2 := by
  have h0 : (d₁ - d₂) * (-2 * p + (d₁ + d₂) * k ^ 2 - e * k * (A + B)) = 0 := by
    linear_combination hB2 - hA2 + (A + B) * hdiff
  have h1 : -2 * p + (d₁ + d₂) * k ^ 2 - e * k * (A + B) = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h) hd
    · exact h
  have hk : e * k * A = d₁ * k ^ 2 - p := by
    linear_combination (-1 / 2 : ℝ) * h1 + (e * k / 2) * hdiff + ((d₁ - d₂) * k ^ 2 / 2) * he
  linear_combination (k ^ 2 * A ^ 2) * he + k ^ 2 * hA2 - (e * k * A + d₁ * k ^ 2 - p) * hk

/-- **Converse**: if planes through `X` touch the axis spheres `(V + dᵢ • u, |dᵢ| s)`
(`d₁ ≠ d₂`) at `F₁`, `F₂`, and `|‖X - F₁‖ - ‖X - F₂‖| = (d₁ - d₂) cos α`, then `X` is on the
double cone.-/
theorem hyp_converse {V u X F₁ F₂ : E} {k s d₁ d₂ : ℝ} (hu : ‖u‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hd : d₁ ≠ d₂)
    (hF₁ : ‖F₁ - (V + d₁ • u)‖ = |d₁| * s) (hp₁ : ⟪X - F₁, F₁ - (V + d₁ • u)⟫ = 0)
    (hF₂ : ‖F₂ - (V + d₂ • u)‖ = |d₂| * s) (hp₂ : ⟪X - F₂, F₂ - (V + d₂ • u)⟫ = 0)
    (hdiff : |‖X - F₁‖ - ‖X - F₂‖| = (d₁ - d₂) * k) : X ∈ cone2 V u k := by
  have hA := focal_sq hu hks hF₁ hp₁
  have hB := focal_sq hu hks hF₂ hp₂
  show ⟪X - V, u⟫ ^ 2 = k ^ 2 * ‖X - V‖ ^ 2
  have h0 : 0 ≤ (d₁ - d₂) * k := hdiff ▸ abs_nonneg _
  rcases (abs_eq h0).1 hdiff with h | h
  · exact hyp_converse_alg (e := 1) hd (one_pow 2) hA hB (by rw [h]; ring)
  · exact hyp_converse_alg (e := -1) hd (by norm_num) hA hB (by rw [h]; ring)

/-! ## Directrix on both nappes -/

theorem ecc_neg (m k : ℝ) : ecc (-m) k = ecc m k := by unfold ecc; rw [neg_sq]

theorem axisPlane_neg (V u : E) (b : ℝ) : axisPlane V (-u) (-b) = axisPlane V u b := by
  ext Y
  show ⟪Y - V, -u⟫ = -b ↔ ⟪Y - V, u⟫ = b
  rw [inner_neg_right, neg_inj]

/-- Focus–directrix property for an axis sphere `(V + d • u, |d| s)` of either sign of `d`,
on the nappe `cone V u k`.-/
theorem focal_dist_eq_ecc_mul_abs {V u n p₀ X F : E} {k s d : ℝ} (hu : ‖u‖ = 1)
    (hn : ‖n‖ = 1) (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hm : ⟪u, n⟫ ^ 2 < 1)
    (hXπ : X ∈ plane p₀ n) (hX : X ∈ cone V u k) (hF : ‖F - (V + d • u)‖ = |d| * s)
    (hperp : ⟪X - F, F - (V + d • u)⟫ = 0) :
    ‖X - F‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d * k ^ 2)) := by
  have hX' : ⟪X - V, u⟫ = k * ‖X - V‖ := hX
  rw [dist_tangent_eq_abs hu hks hX hF hperp, ecc, div_mul_eq_mul_div,
    ← infDist_axisPlane_eq_mul (V := V) (b := d * k ^ 2) hu hn hm hXπ, infDist_axisPlane hu,
    hX', show k * ‖X - V‖ - d * k ^ 2 = k * (‖X - V‖ - d * k) by ring, abs_mul,
    abs_of_pos hk]
  field_simp

/-- Focus–directrix property on the opposite nappe `cone V (-u) k`.-/
theorem focal_dist_eq_ecc_mul_lower {V u n p₀ X F : E} {k s d : ℝ} (hu : ‖u‖ = 1)
    (hn : ‖n‖ = 1) (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hm : ⟪u, n⟫ ^ 2 < 1)
    (hXπ : X ∈ plane p₀ n) (hX : X ∈ cone V (-u) k) (hF : ‖F - (V + d • u)‖ = |d| * s)
    (hperp : ⟪X - F, F - (V + d • u)⟫ = 0) :
    ‖X - F‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d * k ^ 2)) := by
  have := focal_dist_eq_ecc_mul_abs (u := -u) (d := -d) (by rw [norm_neg, hu]) hn hks hk
    (by rw [inner_neg_left, neg_sq]; exact hm) hXπ hX
    (by rw [neg_smul_neg, abs_neg]; exact hF) (by rw [neg_smul_neg]; exact hperp)
  rw [inner_neg_left, ecc_neg, neg_mul] at this
  unfold directrix at this ⊢
  rwa [axisPlane_neg] at this

/-! ## Main corollary: the hyperbola from the cone and the plane alone -/

/-- The focal constant in closed form: `d₁ - d₂ = 2 s c / (s² - m²)`.-/
theorem hyp_param_sub {V u n p₀ : E} {s : ℝ} (hm1 : -s < ⟪u, n⟫) (hm2 : ⟪u, n⟫ < s) :
    param₁ V u n p₀ s - param₂ V u n p₀ s =
      2 * s * ⟪p₀ - V, n⟫ / (s ^ 2 - ⟪u, n⟫ ^ 2) := by
  have h1 : ⟪u, n⟫ + s ≠ 0 := by intro h; linarith
  have h2 : ⟪u, n⟫ - s ≠ 0 := by intro h; linarith
  have h3 : s ^ 2 - ⟪u, n⟫ ^ 2 ≠ 0 := by
    have := mul_pos (sub_pos.2 hm2) (show 0 < ⟪u, n⟫ + s by linarith)
    intro h; nlinarith
  unfold param₁ param₂
  rw [div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h3]
  ring

/-- Reorient the normal so that `0 < ⟪p₀ - V, n'⟫`, in the hyperbola regime.-/
theorem hyp_orient {V u n p₀ : E} {s : ℝ} (hn : ‖n‖ = 1) (hm : |⟪u, n⟫| < s)
    (hc : ⟪p₀ - V, n⟫ ≠ 0) :
    ∃ n' : E, ‖n'‖ = 1 ∧ plane p₀ n' = plane p₀ n ∧ -s < ⟪u, n'⟫ ∧ ⟪u, n'⟫ < s ∧
      0 < ⟪p₀ - V, n'⟫ ∧ (∀ C : E, |⟪C - p₀, n'⟫| = |⟪C - p₀, n⟫|) := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hm
  rcases lt_or_gt_of_ne hc with h | h
  · refine ⟨-n, by rw [norm_neg, hn], plane_neg p₀ n, ?_, ?_, ?_, ?_⟩
    · rw [inner_neg_right]; linarith
    · rw [inner_neg_right]; linarith
    · rw [inner_neg_right]; linarith
    · intro C; rw [inner_neg_right, abs_neg]
  · exact ⟨n, hn, rfl, h1, h2, h, fun _ => rfl⟩

/-- **Dandelin's theorem for the hyperbola, from the cone and the plane alone.**

Double cone `cone2 V u k` (apex `V`, unit axis `u`, `k = cos α > 0`, `s = sin α > 0`,
`k² + s² = 1`); plane through `p₀` with unit normal `n`. Hyperbola regime: `|⟪u, n⟫| < sin α`
(steeper than a generator) and `⟪p₀ - V, n⟫ ≠ 0` (misses the apex).

Conclusion: `e > 1`, and there are `d₂ < 0 < d₁` such that the axis sphere
`(V + d • u, |d| s)` is tangent to the plane iff `d = d₁` or `d = d₂` (one sphere in each
nappe); the tangency points `Fᵢ` (projections of the centres) lie in the plane; on the upper
nappe `‖X - F₂‖ - ‖X - F₁‖ = (d₁ - d₂) cos α`, on the lower nappe
`‖X - F₁‖ - ‖X - F₂‖ = (d₁ - d₂) cos α`; a point of the plane is on the double cone iff
`|‖X - F₁‖ - ‖X - F₂‖| = (d₁ - d₂) cos α` (section = hyperbola, both branches); and every point
of the section satisfies the focus–directrix property for both foci.-/
theorem dandelin_hyperbola {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : |⟪u, n⟫| < s)
    (hc : ⟪p₀ - V, n⟫ ≠ 0) :
    1 < ecc ⟪u, n⟫ k ∧
    ∃ d₁ d₂ : ℝ, ∃ F₁ F₂ : E, d₂ < 0 ∧ 0 < d₁ ∧
      (∀ d : ℝ, |⟪(V + d • u) - p₀, n⟫| = |d| * s ↔ d = d₁ ∨ d = d₂) ∧
      F₁ ∈ plane p₀ n ∧ F₂ ∈ plane p₀ n ∧
      F₁ = (V + d₁ • u) - ⟪(V + d₁ • u) - p₀, n⟫ • n ∧
      F₂ = (V + d₂ • u) - ⟪(V + d₂ • u) - p₀, n⟫ • n ∧
      (∀ X ∈ plane p₀ n, X ∈ cone V u k → ‖X - F₂‖ - ‖X - F₁‖ = (d₁ - d₂) * k) ∧
      (∀ X ∈ plane p₀ n, X ∈ cone V (-u) k → ‖X - F₁‖ - ‖X - F₂‖ = (d₁ - d₂) * k) ∧
      (∀ X ∈ plane p₀ n, X ∈ cone2 V u k ↔ |‖X - F₁‖ - ‖X - F₂‖| = (d₁ - d₂) * k) ∧
      (∀ X ∈ plane p₀ n, X ∈ cone2 V u k →
        ‖X - F₁‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d₁ * k ^ 2)) ∧
        ‖X - F₂‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d₂ * k ^ 2))) := by
  obtain ⟨n', hn', hpl, hm1, hm2, hc', habs⟩ := hyp_orient (V := V) (u := u) hn hm hc
  have hd₁ : 0 < param₁ V u n' p₀ s := hyp_param₁_pos hm1 hc'
  have hd₂ : param₂ V u n' p₀ s < 0 := hyp_param₂_neg hm2 hc'
  have e₁ : ⟪p₀ - V, n'⟫ = param₁ V u n' p₀ s * (⟪u, n'⟫ + s) := by
    unfold param₁; field_simp [show ⟪u, n'⟫ + s ≠ 0 by linarith]
  have e₂ : ⟪p₀ - V, n'⟫ = param₂ V u n' p₀ s * (⟪u, n'⟫ - s) := by
    unfold param₂; field_simp [show ⟪u, n'⟫ - s ≠ 0 by linarith]
  have htan : ∀ d : ℝ, |⟪(V + d • u) - p₀, n⟫| = |d| * s ↔
      d = param₁ V u n' p₀ s ∨ d = param₂ V u n' p₀ s := fun d => by
    rw [← habs]; exact hyp_tangent_iff hs hm1 hm2 d
  have hmu : ⟪u, n⟫ ^ 2 < 1 := by
    have := mul_pos (sub_pos.2 hm) (show 0 < s + |⟪u, n⟫| by linarith [abs_nonneg ⟪u, n⟫])
    nlinarith [sq_abs ⟪u, n⟫, mul_pos hk hk]
  have hD : 0 ≤ (param₁ V u n' p₀ s - param₂ V u n' p₀ s) * k :=
    mul_nonneg (by linarith) hk.le
  refine ⟨(one_lt_ecc_iff hks hk hs).2 hm, param₁ V u n' p₀ s, param₂ V u n' p₀ s, _, _,
    hd₂, hd₁, htan, proj_mem_plane hn, proj_mem_plane hn, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro X hX hXc
    obtain ⟨a1, b1⟩ := tangent_of_proj hn rfl ((htan _).2 (Or.inl rfl)) hX (proj_mem_plane hn)
    obtain ⟨a2, b2⟩ := tangent_of_proj hn rfl ((htan _).2 (Or.inr rfl)) hX (proj_mem_plane hn)
    exact hyp_upper hu hn' hks hk hs hm1 hm2 hd₁ hd₂ e₁ a1 b1 a2 b2 (by rw [hpl]; exact hX) hXc
  · intro X hX hXc
    obtain ⟨a1, b1⟩ := tangent_of_proj hn rfl ((htan _).2 (Or.inl rfl)) hX (proj_mem_plane hn)
    obtain ⟨a2, b2⟩ := tangent_of_proj hn rfl ((htan _).2 (Or.inr rfl)) hX (proj_mem_plane hn)
    exact hyp_lower hu hn' hks hk hs hm1 hm2 hd₁ hd₂ e₂ a1 b1 a2 b2 (by rw [hpl]; exact hX) hXc
  · intro X hX
    obtain ⟨a1, b1⟩ := tangent_of_proj hn rfl ((htan _).2 (Or.inl rfl)) hX (proj_mem_plane hn)
    obtain ⟨a2, b2⟩ := tangent_of_proj hn rfl ((htan _).2 (Or.inr rfl)) hX (proj_mem_plane hn)
    have hX' : X ∈ plane p₀ n' := by rw [hpl]; exact hX
    constructor
    · intro h
      rcases mem_cone2_iff.1 h with h | h
      · rw [abs_sub_comm, hyp_upper hu hn' hks hk hs hm1 hm2 hd₁ hd₂ e₁ a1 b1 a2 b2 hX' h,
          abs_of_nonneg hD]
      · rw [hyp_lower hu hn' hks hk hs hm1 hm2 hd₁ hd₂ e₂ a1 b1 a2 b2 hX' h,
          abs_of_nonneg hD]
    · intro h
      exact hyp_converse hu hks (hd₂.trans hd₁).ne' a1 b1 a2 b2 h
  · intro X hX hXc
    obtain ⟨a1, b1⟩ := tangent_of_proj hn rfl ((htan _).2 (Or.inl rfl)) hX (proj_mem_plane hn)
    obtain ⟨a2, b2⟩ := tangent_of_proj hn rfl ((htan _).2 (Or.inr rfl)) hX (proj_mem_plane hn)
    rcases mem_cone2_iff.1 hXc with h | h
    · exact ⟨focal_dist_eq_ecc_mul_abs hu hn hks hk hmu hX h a1 b1,
        focal_dist_eq_ecc_mul_abs hu hn hks hk hmu hX h a2 b2⟩
    · exact ⟨focal_dist_eq_ecc_mul_lower hu hn hks hk hmu hX h a1 b1,
        focal_dist_eq_ecc_mul_lower hu hn hks hk hmu hX h a2 b2⟩

end Dandelin
