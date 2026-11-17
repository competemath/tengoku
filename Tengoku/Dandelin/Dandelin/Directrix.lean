import Tengoku.Dandelin.Dandelin.Existence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dandelin spheres, phase 3: focus and directrix

Cone `cone V u k` (apex `V`, unit axis `u`, `k = cos α`, `s = sin α`), cutting plane
`plane p₀ n` (unit normal `n`), `m = ⟪u, n⟫`. An inscribed sphere `(V + d • u, d s)` touches the
cone along a circle lying in the plane `axisPlane V u (d k²) = {Y | ⟪Y - V, u⟫ = d k²}`
(perpendicular to the axis). The directrix is `plane p₀ n ∩ axisPlane V u (d k²)`.

Main result: for `X` on plane ∩ cone, `‖X - F‖ = e * infDist X directrix` with
`e = √(1 - ⟪u, n⟫²) / cos α` (= cos β / cos α, β the angle between the plane and the axis).
-/

open RealInnerProductSpace

namespace Dandelin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The plane `⟪Y - V, u⟫ = b`, perpendicular to the axis `u`.-/
def axisPlane (V u : E) (b : ℝ) : Set E := {Y | ⟪Y - V, u⟫ = b}

/-- The line `plane p₀ n ∩ axisPlane V u b`.-/
def directrix (V u n p₀ : E) (b : ℝ) : Set E := plane p₀ n ∩ axisPlane V u b

/-- The eccentricity `√(1 - m²) / k`.-/
noncomputable def ecc (m k : ℝ) : ℝ := Real.sqrt (1 - m ^ 2) / k

/-- The tangency circle of the inscribed sphere `(V + d • u, d s)` lies in the plane
`⟪Y - V, u⟫ = d k²`.-/
theorem tangencyPoint_mem_axisPlane {V u X : E} {k d : ℝ} (hX : X ∈ cone V u k)
    (ht : ‖X - V‖ ≠ 0) : tangencyPoint V X k d ∈ axisPlane V u (d * k ^ 2) := by
  have hX' : ⟪X - V, u⟫ = k * ‖X - V‖ := hX
  show ⟪tangencyPoint V X k d - V, u⟫ = d * k ^ 2
  unfold tangencyPoint
  rw [add_sub_cancel_left, real_inner_smul_left, hX']
  field_simp

theorem norm_sub_inner_smul_sq {u n : E} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1) :
    ‖u - ⟪u, n⟫ • n‖ ^ 2 = 1 - ⟪u, n⟫ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, hn, Real.norm_eq_abs, mul_one,
    sq_abs]
  ring

/-- Distance from a point to the plane `⟪Y - V, u⟫ = b`.-/
theorem infDist_axisPlane {V u X : E} {b : ℝ} (hu : ‖u‖ = 1) :
    Metric.infDist X (axisPlane V u b) = |⟪X - V, u⟫ - b| := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = ⟪X - V, u⟫ - b := ⟨_, rfl⟩
  rw [← hh]
  have hY : X - h • u ∈ axisPlane V u b := by
    show ⟪X - h • u - V, u⟫ = b
    have : X - h • u - V = (X - V) - h • u := by abel
    rw [this, inner_sub_left, real_inner_smul_left, huu, hh]
    ring
  apply le_antisymm
  · have := Metric.infDist_le_dist_of_mem (x := X) hY
    rwa [dist_eq_norm, sub_sub_cancel, norm_smul, hu, mul_one, Real.norm_eq_abs] at this
  · refine (Metric.le_infDist ⟨_, hY⟩).2 fun Y hY' => ?_
    have hY'' : ⟪Y - V, u⟫ = b := hY'
    have e : h = ⟪X - Y, u⟫ := by
      have : X - Y = (X - V) - (Y - V) := by abel
      rw [this, inner_sub_left, hY'', hh]
    rw [e, dist_eq_norm]
    calc |⟪X - Y, u⟫| ≤ ‖X - Y‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ = ‖X - Y‖ := by rw [hu, mul_one]

/-- **Distance to the directrix.** For `X` in the cutting plane (`⟪u, n⟫² < 1`, i.e. the plane
is not perpendicular to the axis), the distance from `X` to the line
`plane p₀ n ∩ axisPlane V u b` is `|⟪X - V, u⟫ - b| / √(1 - ⟪u, n⟫²)`.-/
theorem infDist_directrix {V u n p₀ X : E} {b : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hm : ⟪u, n⟫ ^ 2 < 1) (hX : X ∈ plane p₀ n) :
    Metric.infDist X (directrix V u n p₀ b) =
      |⟪X - V, u⟫ - b| / Real.sqrt (1 - ⟪u, n⟫ ^ 2) := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hX' : ⟪X - p₀, n⟫ = 0 := hX
  have hw2 := norm_sub_inner_smul_sq hu hn
  obtain ⟨m, hm'⟩ : ∃ m, m = ⟪u, n⟫ := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ⟪X - V, u⟫ - b := ⟨_, rfl⟩
  rw [← hm', ← hδ]
  rw [← hm'] at hm hw2
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (1 - m ^ 2) := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 (by linarith)
  have hr2 : r ^ 2 = 1 - m ^ 2 := by rw [hr]; exact Real.sq_sqrt (by linarith)
  have hw : ‖u - m • n‖ = r := by
    rw [← hr2] at hw2
    exact (pow_left_inj₀ (norm_nonneg _) hr0.le two_ne_zero).1 hw2
  have hwn : ⟪u - m • n, n⟫ = 0 := by
    rw [inner_sub_left, real_inner_smul_left, hnn, ← hm']; ring
  have hwu : ⟪u - m • n, u⟫ = r ^ 2 := by
    rw [inner_sub_left, real_inner_smul_left, huu, real_inner_comm, ← hm', hr2]; ring
  have hr2' : r ^ 2 ≠ 0 := by positivity
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = X - (δ / r ^ 2) • (u - m • n) := ⟨_, rfl⟩
  have hY : Y ∈ directrix V u n p₀ b := by
    refine ⟨?_, ?_⟩
    · show ⟪Y - p₀, n⟫ = 0
      have : Y - p₀ = (X - p₀) - (δ / r ^ 2) • (u - m • n) := by rw [hYdef]; abel
      rw [this, inner_sub_left, real_inner_smul_left, hX', hwn]; ring
    · show ⟪Y - V, u⟫ = b
      have : Y - V = (X - V) - (δ / r ^ 2) • (u - m • n) := by rw [hYdef]; abel
      rw [this, inner_sub_left, real_inner_smul_left, hwu, div_mul_cancel₀ δ hr2']
      linarith
  apply le_antisymm
  · refine (Metric.infDist_le_dist_of_mem hY).trans_eq ?_
    rw [hYdef, dist_eq_norm, sub_sub_cancel, norm_smul, hw, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < r ^ 2)]
    field_simp
  · refine (Metric.le_infDist ⟨Y, hY⟩).2 fun Z hZ => ?_
    have hZ' : Z ∈ plane p₀ n ∧ Z ∈ axisPlane V u b := hZ
    have h1 : ⟪X - Z, n⟫ = 0 := inner_sub_eq_zero_of_mem hX hZ'.1
    have hZu : ⟪Z - V, u⟫ = b := hZ'.2
    have h2 : ⟪X - Z, u - m • n⟫ = δ := by
      have : X - Z = (X - V) - (Z - V) := by abel
      rw [inner_sub_right, real_inner_smul_right, h1, this, inner_sub_left, hZu, hδ]; ring
    rw [dist_eq_norm, div_le_iff₀ hr0]
    calc |δ| = |⟪X - Z, u - m • n⟫| := by rw [h2]
      _ ≤ ‖X - Z‖ * ‖u - m • n‖ := abs_real_inner_le_norm _ _
      _ = ‖X - Z‖ * r := by rw [hw]

/-- Focal distance = distance to the plane of the tangency circle, divided by `cos α`.-/
theorem focal_dist_eq_infDist_axisPlane {V u X F : E} {k s d : ℝ} (hu : ‖u‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hX : X ∈ cone V u k)
    (hF : ‖F - (V + d • u)‖ = d * s) (hperp : ⟪X - F, F - (V + d • u)⟫ = 0) :
    ‖X - F‖ = Metric.infDist X (axisPlane V u (d * k ^ 2)) / k := by
  have hX' : ⟪X - V, u⟫ = k * ‖X - V‖ := hX
  rw [infDist_axisPlane hu, dist_tangent_eq hu hks hX hF hperp, hX',
    show k * ‖X - V‖ - d * k ^ 2 = k * (‖X - V‖ - d * k) by ring, abs_mul, abs_of_pos hk]
  field_simp

/-- For `X` in the cutting plane, `dist(X, σ) = sin(angle(π, σ)) · dist(X, ℓ)`, where
`sin(angle(π, σ)) = √(1 - ⟪u, n⟫²)`.-/
theorem infDist_axisPlane_eq_mul {V u n p₀ X : E} {b : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hm : ⟪u, n⟫ ^ 2 < 1) (hX : X ∈ plane p₀ n) :
    Metric.infDist X (axisPlane V u b) =
      Real.sqrt (1 - ⟪u, n⟫ ^ 2) * Metric.infDist X (directrix V u n p₀ b) := by
  have hr0 : 0 < Real.sqrt (1 - ⟪u, n⟫ ^ 2) := Real.sqrt_pos.2 (by linarith)
  rw [infDist_axisPlane hu, infDist_directrix hu hn hm hX]
  field_simp

/-- **Focus–directrix property.** Cone `(V, u, k = cos α)`, cutting plane `plane p₀ n` not
perpendicular to the axis (`⟪u, n⟫² < 1`), and an inscribed sphere `(V + d • u, d s)` tangent
at `F` to a plane through `X` (e.g. the cutting plane). For `X` on plane ∩ cone,
`‖X - F‖ = e · dist(X, ℓ)` with `ℓ = plane p₀ n ∩ axisPlane V u (d k²)` and
`e = ecc ⟪u, n⟫ k = √(1 - ⟪u, n⟫²) / cos α`.-/
theorem focal_dist_eq_ecc_mul {V u n p₀ X F : E} {k s d : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hm : ⟪u, n⟫ ^ 2 < 1) (hXπ : X ∈ plane p₀ n)
    (hX : X ∈ cone V u k) (hF : ‖F - (V + d • u)‖ = d * s)
    (hperp : ⟪X - F, F - (V + d • u)⟫ = 0) :
    ‖X - F‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d * k ^ 2)) := by
  have hr0 : 0 < Real.sqrt (1 - ⟪u, n⟫ ^ 2) := Real.sqrt_pos.2 (by linarith)
  rw [focal_dist_eq_infDist_axisPlane hu hks hk hX hF hperp,
    infDist_axisPlane_eq_mul hu hn hm hXπ, ecc]
  field_simp

/-! ## The eccentricity -/

theorem ecc_lt_one_iff {m k s : ℝ} (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) :
    ecc m k < 1 ↔ s < |m| := by
  unfold ecc
  rw [div_lt_one hk, Real.sqrt_lt' hk]
  have : s < |m| ↔ s ^ 2 < m ^ 2 := by rw [sq_lt_sq, abs_of_pos hs]
  rw [this]
  constructor <;> intro h <;> nlinarith

theorem ecc_eq_one {m k s : ℝ} (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hm : s = |m|) :
    ecc m k = 1 := by
  unfold ecc
  rw [← sq_abs m, ← hm, show 1 - s ^ 2 = k ^ 2 by linarith, Real.sqrt_sq hk.le,
    div_self hk.ne']

theorem one_lt_ecc_iff {m k s : ℝ} (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) :
    1 < ecc m k ↔ |m| < s := by
  unfold ecc
  rw [one_lt_div hk, Real.lt_sqrt hk.le]
  have : |m| < s ↔ m ^ 2 < s ^ 2 := by rw [sq_lt_sq, abs_of_pos hs]
  rw [this]
  constructor <;> intro h <;> nlinarith

/-! ## Corollaries from the cone and the plane alone -/

theorem proj_mem_plane {C p₀ n : E} (hn : ‖n‖ = 1) : C - ⟪C - p₀, n⟫ • n ∈ plane p₀ n := by
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  show ⟪C - ⟪C - p₀, n⟫ • n - p₀, n⟫ = 0
  have : C - ⟪C - p₀, n⟫ • n - p₀ = (C - p₀) - ⟪C - p₀, n⟫ • n := by abel
  rw [this, inner_sub_left, real_inner_smul_left, hnn, mul_one, sub_self]

/-- If `F` is the projection of `C` onto the plane and `|⟪C - p₀, n⟫| = r`, then `F` is on the
sphere `(C, r)` and `X - F ⟂ F - C` for every `X` of the plane (tangency).-/
theorem tangent_of_proj {C p₀ n F X : E} {r : ℝ} (hn : ‖n‖ = 1)
    (hF : F = C - ⟪C - p₀, n⟫ • n) (hr : |⟪C - p₀, n⟫| = r) (hX : X ∈ plane p₀ n)
    (hFπ : F ∈ plane p₀ n) : ‖F - C‖ = r ∧ ⟪X - F, F - C⟫ = 0 := by
  have e : F - C = -(⟪C - p₀, n⟫ • n) := by rw [hF]; abel
  refine ⟨?_, ?_⟩
  · rw [e, norm_neg, norm_smul, hn, mul_one, Real.norm_eq_abs, hr]
  · rw [e, inner_neg_right, real_inner_smul_right, inner_sub_eq_zero_of_mem hX hFπ, mul_zero,
      neg_zero]

/-- **Ellipse: focus–directrix form, from the cone and the plane alone.** Under the
bounded-section condition of `dandelin_exists` (`sin α < |⟪u, n⟫|`,
`0 < ⟪u, n⟫ ⟪p₀ - V, n⟫`) and `⟪u, n⟫² < 1` (not a circle): `e < 1`, and for both Dandelin
spheres `(V + dᵢ • u, dᵢ s)`, with foci `Fᵢ` (projections of the centres), every point `X` of
plane ∩ cone satisfies `‖X - Fᵢ‖ = e · dist(X, ℓᵢ)`, `ℓᵢ = plane ∩ axisPlane V u (dᵢ k²)`.-/
theorem directrix_ellipse {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : s < |⟪u, n⟫|)
    (hc : 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫) (hm1 : ⟪u, n⟫ ^ 2 < 1) :
    ecc ⟪u, n⟫ k < 1 ∧ ∃ d₁ d₂ : ℝ, ∃ F₁ F₂ : E, 0 < d₁ ∧ d₁ < d₂ ∧
      (∀ d : ℝ, |⟪(V + d • u) - p₀, n⟫| = d * s ↔ d = d₁ ∨ d = d₂) ∧
      F₁ ∈ plane p₀ n ∧ F₂ ∈ plane p₀ n ∧
      F₁ = (V + d₁ • u) - ⟪(V + d₁ • u) - p₀, n⟫ • n ∧
      F₂ = (V + d₂ • u) - ⟪(V + d₂ • u) - p₀, n⟫ • n ∧
      ∀ X ∈ plane p₀ n, X ∈ cone V u k →
        ‖X - F₁‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d₁ * k ^ 2)) ∧
        ‖X - F₂‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d₂ * k ^ 2)) := by
  refine ⟨(ecc_lt_one_iff hks hk hs).2 hm, ?_⟩
  obtain ⟨d₁, d₂, F₁, F₂, hd₁, hd, htan, -, hF₁, hF₂, hp₁, hp₂, -⟩ :=
    dandelin_exists hu hn hks hk hs hm hc
  refine ⟨d₁, d₂, F₁, F₂, hd₁, hd, htan, hF₁, hF₂, hp₁, hp₂, fun X hX hXc => ⟨?_, ?_⟩⟩
  · obtain ⟨h1, h2⟩ := tangent_of_proj hn hp₁ ((htan d₁).2 (Or.inl rfl)) hX hF₁
    exact focal_dist_eq_ecc_mul hu hn hks hk hm1 hX hXc h1 h2
  · obtain ⟨h1, h2⟩ := tangent_of_proj hn hp₂ ((htan d₂).2 (Or.inr rfl)) hX hF₂
    exact focal_dist_eq_ecc_mul hu hn hks hk hm1 hX hXc h1 h2

/-! ## Parabola -/

/-- Reorient the normal so that `0 ≤ ⟪u, n'⟫` and `0 < ⟪p₀ - V, n'⟫`.-/
theorem exists_orient {V u n p₀ : E} (hn : ‖n‖ = 1) (hc : 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫) :
    ∃ n' : E, ‖n'‖ = 1 ∧ plane p₀ n' = plane p₀ n ∧ ⟪u, n'⟫ = |⟪u, n⟫| ∧
      0 < ⟪p₀ - V, n'⟫ ∧ (∀ C : E, |⟪C - p₀, n'⟫| = |⟪C - p₀, n⟫|) := by
  rcases le_or_gt 0 ⟪u, n⟫ with h | h
  · refine ⟨n, hn, rfl, (abs_of_nonneg h).symm, ?_, fun _ => rfl⟩
    rcases h.eq_or_lt with h' | h'
    · rw [← h', zero_mul] at hc; exact absurd hc (lt_irrefl 0)
    · exact pos_of_mul_pos_right hc h'.le
  · refine ⟨-n, by rw [norm_neg, hn], plane_neg p₀ n, ?_, ?_, ?_⟩
    · rw [abs_of_neg h, inner_neg_right]
    · rw [inner_neg_right]; nlinarith
    · intro C; rw [inner_neg_right, abs_neg]

/-- **Parabola (Dandelin, one sphere).** If the cutting plane is parallel to a generator
(`sin α = |⟪u, n⟫|`) and misses the apex on the nappe side (`0 < ⟪u, n⟫ ⟪p₀ - V, n⟫`), then
`e = 1`, there is exactly one inscribed sphere `(V + d • u, d s)` tangent to the plane, and
every `X` of plane ∩ cone is equidistant from the focus `F` and the directrix
`ℓ = plane ∩ axisPlane V u (d k²)`.-/
theorem directrix_parabola {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : s = |⟪u, n⟫|)
    (hc : 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫) :
    ecc ⟪u, n⟫ k = 1 ∧ ∃ d : ℝ, ∃ F : E, 0 < d ∧
      (∀ d' : ℝ, |⟪(V + d' • u) - p₀, n⟫| = d' * s ↔ d' = d) ∧
      F ∈ plane p₀ n ∧ F = (V + d • u) - ⟪(V + d • u) - p₀, n⟫ • n ∧
      ∀ X ∈ plane p₀ n, X ∈ cone V u k →
        ‖X - F‖ = Metric.infDist X (directrix V u n p₀ (d * k ^ 2)) := by
  have he : ecc ⟪u, n⟫ k = 1 := ecc_eq_one hks hk hm
  have hm1 : ⟪u, n⟫ ^ 2 < 1 := by rw [← sq_abs, ← hm]; nlinarith
  refine ⟨he, ?_⟩
  obtain ⟨n', -, -, hm', hc', habs⟩ := exists_orient (V := V) hn hc
  rw [← hm] at hm'
  obtain ⟨d0, hd0⟩ : ∃ d0 : ℝ, d0 = ⟪p₀ - V, n'⟫ / (2 * s) := ⟨_, rfl⟩
  have hd2 : d0 * (2 * s) = ⟪p₀ - V, n'⟫ := by
    rw [hd0]; exact div_mul_cancel₀ _ (by positivity)
  have hd0pos : 0 < d0 := by rw [hd0]; exact div_pos hc' (by positivity)
  have htan : ∀ d' : ℝ, |⟪(V + d' • u) - p₀, n⟫| = d' * s ↔ d' = d0 := by
    intro d'
    rw [← habs, inner_center_sub, hm']
    constructor
    · intro h
      have hb : 0 ≤ d' * s := h ▸ abs_nonneg _
      rcases (abs_eq hb).1 h with h' | h'
      · linarith
      · have : d' * (2 * s) = d0 * (2 * s) := by linear_combination h' - hd2
        exact mul_right_cancel₀ (by positivity) this
    · rintro rfl
      rw [show d' * s - ⟪p₀ - V, n'⟫ = -(d' * s) by linear_combination hd2, abs_neg,
        abs_of_pos (mul_pos hd0pos hs)]
  refine ⟨d0, (V + d0 • u) - ⟪(V + d0 • u) - p₀, n⟫ • n, hd0pos, htan, proj_mem_plane hn, rfl,
    fun X hX hXc => ?_⟩
  obtain ⟨h1, h2⟩ := tangent_of_proj hn rfl ((htan d0).2 rfl) hX (proj_mem_plane hn)
  rw [← one_mul (Metric.infDist _ _), ← he]
  exact focal_dist_eq_ecc_mul hu hn hks hk hm1 hX hXc h1 h2

end Dandelin
