import Tengoku.Dandelin.Dandelin.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dandelin spheres, phase 2: existence, uniqueness and the converse

Plane `plane p₀ n = {X | ⟪X - p₀, n⟫ = 0}` with unit normal `n`. Write `c = ⟪p₀ - V, n⟫`
(signed distance from the apex to the plane) and `m = ⟪u, n⟫`.
Normalised bounded-section hypotheses: `0 < c` (the plane misses the apex; `n` points from `V`
towards the plane) and `sin α < m`.
-/

open RealInnerProductSpace

namespace Dandelin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The plane through `p₀` with normal `n`.-/
def plane (p₀ n : E) : Set E := {X | ⟪X - p₀, n⟫ = 0}

/-- Parameter of the small Dandelin sphere (centre `V + d₁ • u`, radius `d₁ s`).-/
noncomputable def param₁ (V u n p₀ : E) (s : ℝ) : ℝ := ⟪p₀ - V, n⟫ / (⟪u, n⟫ + s)

/-- Parameter of the large Dandelin sphere.-/
noncomputable def param₂ (V u n p₀ : E) (s : ℝ) : ℝ := ⟪p₀ - V, n⟫ / (⟪u, n⟫ - s)

/-- Tangency point of the small sphere with the plane.-/
noncomputable def focus₁ (V u n p₀ : E) (s : ℝ) : E :=
  V + param₁ V u n p₀ s • u + (param₁ V u n p₀ s * s) • n

/-- Tangency point of the large sphere with the plane.-/
noncomputable def focus₂ (V u n p₀ : E) (s : ℝ) : E :=
  V + param₂ V u n p₀ s • u - (param₂ V u n p₀ s * s) • n

/-- Signed distance from an axis point to the plane.-/
theorem inner_center_sub (V u n p₀ : E) (d : ℝ) :
    ⟪(V + d • u) - p₀, n⟫ = d * ⟪u, n⟫ - ⟪p₀ - V, n⟫ := by
  have h : (V + d • u) - p₀ = d • u - (p₀ - V) := by abel
  rw [h, inner_sub_left, real_inner_smul_left]

section params

variable {V u n p₀ : E} {s : ℝ}

theorem param₁_mul (hs : 0 < s) (hm : s < ⟪u, n⟫) :
    param₁ V u n p₀ s * (⟪u, n⟫ + s) = ⟪p₀ - V, n⟫ := by
  unfold param₁; field_simp [show ⟪u, n⟫ + s ≠ 0 by linarith]

theorem param₂_mul (hm : s < ⟪u, n⟫) :
    param₂ V u n p₀ s * (⟪u, n⟫ - s) = ⟪p₀ - V, n⟫ := by
  unfold param₂; field_simp [show ⟪u, n⟫ - s ≠ 0 by linarith]

theorem param₁_pos (hs : 0 < s) (hm : s < ⟪u, n⟫) (hc : 0 < ⟪p₀ - V, n⟫) :
    0 < param₁ V u n p₀ s := div_pos hc (by linarith)

theorem param₁_lt_param₂ (hs : 0 < s) (hm : s < ⟪u, n⟫) (hc : 0 < ⟪p₀ - V, n⟫) :
    param₁ V u n p₀ s < param₂ V u n p₀ s := by
  unfold param₁ param₂
  exact div_lt_div_of_pos_left hc (by linarith) (by linarith)

/-- **Exactly two inscribed spheres are tangent to the plane**: an axis sphere
`(V + d • u, d s)` is tangent to the plane (distance from centre to plane = radius) iff
`d = d₁` or `d = d₂`; and `d₁ ≠ d₂`.-/
theorem tangent_iff (hs : 0 < s) (hm : s < ⟪u, n⟫) (hc : 0 < ⟪p₀ - V, n⟫) (d : ℝ) :
    |⟪(V + d • u) - p₀, n⟫| = d * s ↔ d = param₁ V u n p₀ s ∨ d = param₂ V u n p₀ s := by
  have h1 := param₁_mul (V := V) (p₀ := p₀) hs hm
  have h2 := param₂_mul (V := V) (p₀ := p₀) hm
  have hp1 := param₁_pos (V := V) hs hm hc
  have hp2 := hp1.trans (param₁_lt_param₂ (V := V) hs hm hc)
  rw [inner_center_sub]
  constructor
  · intro h
    have hb : 0 ≤ d * s := h ▸ abs_nonneg _
    rcases (abs_eq hb).1 h with h' | h'
    · right
      have : (d - param₂ V u n p₀ s) * (⟪u, n⟫ - s) = 0 := by linear_combination h' - h2
      rcases mul_eq_zero.1 this with h3 | h3
      · linarith
      · exact absurd h3 (by linarith)
    · left
      have : (d - param₁ V u n p₀ s) * (⟪u, n⟫ + s) = 0 := by linear_combination h' - h1
      rcases mul_eq_zero.1 this with h3 | h3
      · linarith
      · exact absurd h3 (by linarith)
  · rintro (rfl | rfl)
    · rw [abs_of_neg (by nlinarith [mul_pos hp1 hs])]; linear_combination -h1
    · rw [abs_of_pos (by nlinarith [mul_pos hp2 hs])]; linear_combination h2

/-- The two sphere centres lie strictly on opposite sides of the plane: signed distances
`-d₁ s < 0 < d₂ s`.-/
theorem opposite_sides (hs : 0 < s) (hm : s < ⟪u, n⟫) :
    ⟪(V + param₁ V u n p₀ s • u) - p₀, n⟫ = -(param₁ V u n p₀ s * s) ∧
    ⟪(V + param₂ V u n p₀ s • u) - p₀, n⟫ = param₂ V u n p₀ s * s := by
  have h1 := param₁_mul (V := V) (p₀ := p₀) hs hm
  have h2 := param₂_mul (V := V) (p₀ := p₀) hm
  rw [inner_center_sub, inner_center_sub]
  constructor
  · linear_combination h1
  · linear_combination h2

/-- `F₁` is the orthogonal projection of the small centre onto the plane.-/
theorem focus₁_eq_proj (hs : 0 < s) (hm : s < ⟪u, n⟫) :
    focus₁ V u n p₀ s = (V + param₁ V u n p₀ s • u)
      - ⟪(V + param₁ V u n p₀ s • u) - p₀, n⟫ • n := by
  rw [(opposite_sides (V := V) (p₀ := p₀) hs hm).1, focus₁, neg_smul, sub_neg_eq_add]

/-- `F₂` is the orthogonal projection of the large centre onto the plane.-/
theorem focus₂_eq_proj (hs : 0 < s) (hm : s < ⟪u, n⟫) :
    focus₂ V u n p₀ s = (V + param₂ V u n p₀ s • u)
      - ⟪(V + param₂ V u n p₀ s • u) - p₀, n⟫ • n := by
  rw [(opposite_sides (V := V) (p₀ := p₀) hs hm).2, focus₂]

theorem focus₁_mem (hn : ‖n‖ = 1) (hs : 0 < s) (hm : s < ⟪u, n⟫) :
    focus₁ V u n p₀ s ∈ plane p₀ n := by
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  show ⟪focus₁ V u n p₀ s - p₀, n⟫ = 0
  have e : focus₁ V u n p₀ s - p₀ = ((V + param₁ V u n p₀ s • u) - p₀)
      + (param₁ V u n p₀ s * s) • n := by unfold focus₁; abel
  rw [e, inner_add_left, real_inner_smul_left, hnn, (opposite_sides hs hm).1]
  ring

theorem focus₂_mem (hn : ‖n‖ = 1) (hs : 0 < s) (hm : s < ⟪u, n⟫) :
    focus₂ V u n p₀ s ∈ plane p₀ n := by
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  show ⟪focus₂ V u n p₀ s - p₀, n⟫ = 0
  have e : focus₂ V u n p₀ s - p₀ = ((V + param₂ V u n p₀ s • u) - p₀)
      - (param₂ V u n p₀ s * s) • n := by unfold focus₂; abel
  rw [e, inner_sub_left, real_inner_smul_left, hnn, (opposite_sides hs hm).2]
  ring

end params

/-! ## Converse: the ellipse lies on the cone -/

/-- Real-algebra core of the converse.-/
theorem converse_alg {A B t p k d₁ d₂ : ℝ} (hk : 0 < k) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hA2 : A ^ 2 = t ^ 2 - 2 * d₁ * p + d₁ ^ 2 * k ^ 2)
    (hB2 : B ^ 2 = t ^ 2 - 2 * d₂ * p + d₂ ^ 2 * k ^ 2) (hsum : A + B = (d₂ - d₁) * k) :
    p = k * t := by
  have h0 : (d₂ - d₁) * (2 * k * A - 2 * p + 2 * d₁ * k ^ 2) = 0 := by
    linear_combination hA2 - hB2 + (B - A + (d₂ - d₁) * k) * hsum
  have hkA : k * A = p - d₁ * k ^ 2 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (by linarith)
    · linarith
  have hp : 0 < p := by nlinarith [mul_nonneg hk.le hA, mul_pos hd₁ (mul_pos hk hk)]
  have hsq : (p - k * t) * (p + k * t) = 0 := by
    linear_combination k ^ 2 * hA2 - (k * A + p - d₁ * k ^ 2) * hkA
  rcases mul_eq_zero.1 hsq with h | h
  · linarith
  · nlinarith [mul_nonneg hk.le ht]

/-- **Converse of Dandelin's theorem.** With the tangent configuration of `dandelin`, every
point `X` of the plane with `‖X - F₁‖ + ‖X - F₂‖ = (d₂ - d₁) k` lies on the cone.-/
theorem dandelin_converse {V u n X F₁ F₂ : E} {k s d₁ d₂ : ℝ} (hn : ‖n‖ = 1)
    (hu : ‖u‖ = 1) (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hF₁ : F₁ = V + d₁ • u + (d₁ * s) • n) (hF₂ : F₂ = V + d₂ • u - (d₂ * s) • n)
    (hF₂π : ⟪F₂ - F₁, n⟫ = 0) (hXπ : ⟪X - F₁, n⟫ = 0)
    (hsum : ‖X - F₁‖ + ‖X - F₂‖ = (d₂ - d₁) * k) : X ∈ cone V u k := by
  have hXπ₂ : ⟪X - F₂, n⟫ = 0 := by
    have : X - F₂ = (X - F₁) - (F₂ - F₁) := by abel
    rw [this, inner_sub_left, hXπ, hF₂π, sub_zero]
  have hc₁ : F₁ - (V + d₁ • u) = (d₁ * s) • n := by rw [hF₁]; abel
  have hc₂ : F₂ - (V + d₂ • u) = -((d₂ * s) • n) := by rw [hF₂]; abel
  have hr₁ : ‖F₁ - (V + d₁ • u)‖ = |d₁ * s| := by
    rw [hc₁, norm_smul, hn, mul_one, Real.norm_eq_abs]
  have hr₂ : ‖F₂ - (V + d₂ • u)‖ = |d₂ * s| := by
    rw [hc₂, norm_neg, norm_smul, hn, mul_one, Real.norm_eq_abs]
  have hp₁ : ⟪X - F₁, F₁ - (V + d₁ • u)⟫ = 0 := by
    rw [hc₁, real_inner_smul_right, hXπ, mul_zero]
  have hp₂ : ⟪X - F₂, F₂ - (V + d₂ • u)⟫ = 0 := by
    rw [hc₂, inner_neg_right, real_inner_smul_right, hXπ₂, mul_zero, neg_zero]
  have e₁ := tangent_length_sq hr₁ hp₁
  have e₂ := tangent_length_sq hr₂ hp₂
  have expand : ∀ d : ℝ, ‖X - (V + d • u)‖ ^ 2 =
      ‖X - V‖ ^ 2 - 2 * d * ⟪X - V, u⟫ + d ^ 2 := by
    intro d
    have h : X - (V + d • u) = (X - V) - d • u := by abel
    rw [h, norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, mul_one,
      Real.norm_eq_abs, sq_abs]
    ring
  rw [expand, sq_abs] at e₁ e₂
  show ⟪X - V, u⟫ = k * ‖X - V‖
  exact converse_alg hk hd₁ hd (norm_nonneg _) (norm_nonneg _)
    (by linear_combination e₁ - d₁ ^ 2 * hks) (by linear_combination e₂ - d₂ ^ 2 * hks) hsum

/-! ## Hypothesis-light corollaries -/

theorem inner_sub_eq_zero_of_mem {p₀ n X Y : E} (hX : X ∈ plane p₀ n) (hY : Y ∈ plane p₀ n) :
    ⟪X - Y, n⟫ = 0 := by
  have hX' : ⟪X - p₀, n⟫ = 0 := hX
  have hY' : ⟪Y - p₀, n⟫ = 0 := hY
  have : X - Y = (X - p₀) - (Y - p₀) := by abel
  rw [this, inner_sub_left, hX', hY', sub_zero]

theorem plane_neg (p₀ n : E) : plane p₀ (-n) = plane p₀ n := by
  ext X; simp [plane, inner_neg_right]

/-- **Section = ellipse** (normalised orientation `sin α < ⟪u, n⟫`, `0 < ⟪p₀ - V, n⟫`).
A point of the plane is on the cone iff its focal distances to `F₁`, `F₂` sum to
`(d₂ - d₁) cos α`.-/
theorem mem_cone_iff_of_normalised {V u n p₀ X : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : s < ⟪u, n⟫)
    (hc : 0 < ⟪p₀ - V, n⟫) (hX : X ∈ plane p₀ n) :
    X ∈ cone V u k ↔ ‖X - focus₁ V u n p₀ s‖ + ‖X - focus₂ V u n p₀ s‖ =
      (param₂ V u n p₀ s - param₁ V u n p₀ s) * k := by
  have h1 := focus₁_mem (V := V) (p₀ := p₀) hn hs hm
  have h2 := focus₂_mem (V := V) (p₀ := p₀) hn hs hm
  have hF₂π := inner_sub_eq_zero_of_mem h2 h1
  have hXπ := inner_sub_eq_zero_of_mem hX h1
  have hd₁ := param₁_pos (V := V) hs hm hc
  have hd := param₁_lt_param₂ (V := V) hs hm hc
  constructor
  · exact dandelin hu hn hks hk hs hd₁ hd rfl rfl hF₂π hXπ
  · exact dandelin_converse hn hu hks hk hd₁ hd rfl rfl hF₂π hXπ

/-- **Existence and uniqueness of the Dandelin spheres, and Dandelin's theorem with its
converse, from the cone and the plane alone.**

Cone: apex `V`, unit axis `u`, `k = cos α`, `s = sin α`, `0 < k`, `0 < s`, `k² + s² = 1`.
Plane: through `p₀`, unit normal `n`. Bounded-section condition (the plane meets the nappe
`cone V u k` in a closed bounded curve, and misses the apex):
`sin α < |⟪u, n⟫|` and `0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫`.

Conclusion: there are `0 < d₁ < d₂` such that the axis sphere `(V + d • u, d s)` is tangent to
the plane (distance from the centre to the plane equals the radius) iff `d = d₁` or `d = d₂`;
the two centres are on opposite sides of the plane; there are points `F₁`, `F₂` of the plane,
the orthogonal projections of the two centres (hence the tangency points); and a point of the
plane lies on the cone iff `‖X - F₁‖ + ‖X - F₂‖ = (d₂ - d₁) cos α`.-/
theorem dandelin_exists {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : s < |⟪u, n⟫|)
    (hc : 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫) :
    ∃ d₁ d₂ : ℝ, ∃ F₁ F₂ : E, 0 < d₁ ∧ d₁ < d₂ ∧
      (∀ d : ℝ, |⟪(V + d • u) - p₀, n⟫| = d * s ↔ d = d₁ ∨ d = d₂) ∧
      ⟪(V + d₁ • u) - p₀, n⟫ * ⟪(V + d₂ • u) - p₀, n⟫ < 0 ∧
      F₁ ∈ plane p₀ n ∧ F₂ ∈ plane p₀ n ∧
      F₁ = (V + d₁ • u) - ⟪(V + d₁ • u) - p₀, n⟫ • n ∧
      F₂ = (V + d₂ • u) - ⟪(V + d₂ • u) - p₀, n⟫ • n ∧
      ∀ X ∈ plane p₀ n, (X ∈ cone V u k ↔ ‖X - F₁‖ + ‖X - F₂‖ = (d₂ - d₁) * k) := by
  -- reduce to the normalised orientation `n' = ± n` with `s < ⟪u, n'⟫`, `0 < ⟪p₀ - V, n'⟫`
  obtain ⟨n', hn', hpl, hm', hc', habs, hproj, hmul⟩ :
      ∃ n' : E, ‖n'‖ = 1 ∧ plane p₀ n' = plane p₀ n ∧
      s < ⟪u, n'⟫ ∧ 0 < ⟪p₀ - V, n'⟫ ∧
      (∀ C : E, |⟪C - p₀, n'⟫| = |⟪C - p₀, n⟫|) ∧
      (∀ C : E, ⟪C - p₀, n'⟫ • n' = ⟪C - p₀, n⟫ • n) ∧
      (∀ C D : E, ⟪C - p₀, n'⟫ * ⟪D - p₀, n'⟫ = ⟪C - p₀, n⟫ * ⟪D - p₀, n⟫) := by
    rcases le_or_gt 0 ⟪u, n⟫ with h | h
    · refine ⟨n, hn, rfl, by rwa [abs_of_nonneg h] at hm, ?_, fun _ => rfl, fun _ => rfl,
        fun _ _ => rfl⟩
      rcases h.eq_or_lt with h' | h'
      · rw [← h', zero_mul] at hc; exact absurd hc (lt_irrefl 0)
      · exact pos_of_mul_pos_right hc h'.le
    · refine ⟨-n, by rw [norm_neg, hn], plane_neg p₀ n, ?_, ?_, ?_, ?_, ?_⟩
      · rw [abs_of_neg h] at hm; rw [inner_neg_right]; exact hm
      · rw [inner_neg_right]; nlinarith
      · intro C; rw [inner_neg_right, abs_neg]
      · intro C; rw [inner_neg_right, neg_smul_neg]
      · intro C D; rw [inner_neg_right, inner_neg_right, neg_mul_neg]
  have hd₁ := param₁_pos (V := V) (p₀ := p₀) hs hm' hc'
  have hd := param₁_lt_param₂ (V := V) (p₀ := p₀) hs hm' hc'
  refine ⟨param₁ V u n' p₀ s, param₂ V u n' p₀ s, focus₁ V u n' p₀ s, focus₂ V u n' p₀ s,
    hd₁, hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d; rw [← habs]; exact tangent_iff hs hm' hc' d
  · rw [← hmul, (opposite_sides (V := V) (p₀ := p₀) hs hm').1,
      (opposite_sides (V := V) (p₀ := p₀) hs hm').2]
    have := mul_pos (mul_pos hd₁ hs) (mul_pos (hd₁.trans hd) hs)
    linarith
  · rw [← hpl]; exact focus₁_mem hn' hs hm'
  · rw [← hpl]; exact focus₂_mem hn' hs hm'
  · rw [← hproj]; exact focus₁_eq_proj hs hm'
  · rw [← hproj]; exact focus₂_eq_proj hs hm'
  · intro X hX
    rw [← hpl] at hX
    exact mem_cone_iff_of_normalised hu hn' hks hk hs hm' hc' hX

/-- Under the bounded-section condition the section `plane ∩ cone` is bounded.-/
theorem section_bounded {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : s < |⟪u, n⟫|)
    (hc : 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫) :
    ∃ R : ℝ, ∀ X ∈ plane p₀ n, X ∈ cone V u k → ‖X - V‖ ≤ R := by
  obtain ⟨d₁, d₂, F₁, F₂, -, -, -, -, -, -, -, -, h⟩ :=
    dandelin_exists (V := V) (p₀ := p₀) hu hn hks hk hs hm hc
  refine ⟨(d₂ - d₁) * k + ‖F₁ - V‖, fun X hX hXc => ?_⟩
  have hsum := (h X hX).1 hXc
  have htri : ‖X - V‖ ≤ ‖X - F₁‖ + ‖F₁ - V‖ := by
    have : X - V = (X - F₁) + (F₁ - V) := by abel
    rw [this]; exact norm_add_le _ _
  linarith [norm_nonneg (X - F₂)]

end Dandelin
