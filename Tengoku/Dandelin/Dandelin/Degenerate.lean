import Tengoku.Dandelin.Dandelin.Regime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dandelin spheres, phase 6: the directrix converse and planes through the apex

Cone `cone2 V u k` (two nappes, apex `V`, unit axis `u`, `k = cos α`, `s = sin α`), cutting
plane `plane p₀ n` (unit normal `n`), `m = ⟪u, n⟫`, `c = ⟪p₀ - V, n⟫`.

* Converse of the focus–directrix property: for `X` in the plane and any axis sphere
  `(V + d • u, |d| s)` touched by the plane at `F`, `‖X - F‖ = e · dist(X, ℓ)` forces `X` onto
  the double cone. This holds in every regime (and any `E`); in the ellipse and parabola regimes
  the double cone can be replaced by the nappe met by the plane, in the hyperbola regime it
  cannot.
* The plane through the apex (`c = 0`): the section is `{V}` (`s < |m|`), one generator line
  (`|m| = s`), or two generator lines (`|m| < s`, `finrank E = 3`).
-/

open RealInnerProductSpace

namespace Dandelin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## (1) Converse of the focus–directrix property -/

/-- **Converse of the focus–directrix property** (any regime, any `E`). If `X` is in the cutting
plane (not perpendicular to the axis), the plane touches the axis sphere `(V + d • u, |d| s)`
at `F`, and `‖X - F‖ = e · dist(X, ℓ)` with `ℓ = plane ∩ axisPlane V u (d k²)`,
`e = √(1 - ⟪u, n⟫²) / cos α`, then `X` lies on the double cone.
@isnad1 id=mem.9h10v.s9.10b796d77789 from=translated src=- shape=87e7f762 vocab=9dfff6fc
-/
theorem directrix_converse {V u n p₀ X F : E} {k s d : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hm : ⟪u, n⟫ ^ 2 < 1) (hXπ : X ∈ plane p₀ n)
    (hF : ‖F - (V + d • u)‖ = |d| * s) (hp : ⟪X - F, F - (V + d • u)⟫ = 0)
    (h : ‖X - F‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d * k ^ 2))) :
    X ∈ cone2 V u k := by
  have hr0 : 0 < Real.sqrt (1 - ⟪u, n⟫ ^ 2) := Real.sqrt_pos.2 (by linarith)
  rw [infDist_directrix hu hn hm hXπ, ecc] at h
  have h1 : k * ‖X - F‖ = |⟪X - V, u⟫ - d * k ^ 2| := by
    rw [h]; field_simp
  have h2 : (k * ‖X - F‖) ^ 2 = (⟪X - V, u⟫ - d * k ^ 2) ^ 2 := by rw [h1, sq_abs]
  have hA := focal_sq hu hks hF hp
  show ⟪X - V, u⟫ ^ 2 = k ^ 2 * ‖X - V‖ ^ 2
  linear_combination k ^ 2 * hA - h2

/-- **Focus–directrix characterisation of the section** (any regime, any `E`): for `X` in the
plane, `X` is on the double cone iff `‖X - F‖ = e · dist(X, ℓ)`.
@isnad1 id=iff.8h10v.s9.40d8fc742e1a from=translated src=- shape=b2c0a72f vocab=9dfff6fc
-/
theorem mem_cone2_iff_focal_directrix {V u n p₀ X F : E} {k s d : ℝ} (hu : ‖u‖ = 1)
    (hn : ‖n‖ = 1) (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hm : ⟪u, n⟫ ^ 2 < 1)
    (hXπ : X ∈ plane p₀ n) (hF : ‖F - (V + d • u)‖ = |d| * s)
    (hp : ⟪X - F, F - (V + d • u)⟫ = 0) :
    X ∈ cone2 V u k ↔
      ‖X - F‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d * k ^ 2)) := by
  constructor
  · intro hX
    rcases mem_cone2_iff.1 hX with h | h
    · exact focal_dist_eq_ecc_mul_abs hu hn hks hk hm hXπ h hF hp
    · exact focal_dist_eq_ecc_mul_lower hu hn hks hk hm hXπ h hF hp
  · exact directrix_converse hu hn hks hk hm hXπ hF hp

/-- In the ellipse and parabola regimes (`sin α ≤ |⟪u, n⟫|`, `0 < ⟪u, n⟫ ⟪p₀ - V, n⟫`), the
directrix converse lands on the nappe `cone V u k` met by the plane.
@isnad1 id=mem.12h10v.s9.16f0fcbae5ae from=translated src=- shape=45a4c700 vocab=1f8cb150
-/
theorem directrix_converse_nappe {V u n p₀ X F : E} {k s d : ℝ} (hu : ‖u‖ = 1)
    (hn : ‖n‖ = 1) (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : s ≤ |⟪u, n⟫|)
    (hc : 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫) (hm1 : ⟪u, n⟫ ^ 2 < 1) (hXπ : X ∈ plane p₀ n)
    (hF : ‖F - (V + d • u)‖ = |d| * s) (hp : ⟪X - F, F - (V + d • u)⟫ = 0)
    (h : ‖X - F‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d * k ^ 2))) :
    X ∈ cone V u k := by
  have hc0 : ⟪p₀ - V, n⟫ ≠ 0 := by intro h0; rw [h0, mul_zero] at hc; exact lt_irrefl 0 hc
  have h2 := directrix_converse hu hn hks hk hm1 hXπ hF hp h
  rcases one_nappe hu hn hks hk hs hm hc0 with ⟨-, hsec⟩ | ⟨hneg, -⟩
  · exact hsec X hXπ h2
  · exact absurd hc (not_lt.2 hneg.le)

/-- A point on both nappes is the apex.-/
theorem eq_of_mem_both_nappes {V u X : E} {k : ℝ} (hk : 0 < k) (h1 : X ∈ cone V u k)
    (h2 : X ∈ cone V (-u) k) : X = V := by
  have h1' : ⟪X - V, u⟫ = k * ‖X - V‖ := h1
  have h2' : ⟪X - V, -u⟫ = k * ‖X - V‖ := h2
  rw [inner_neg_right] at h2'
  have : k * ‖X - V‖ = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hk.ne'
  · exact sub_eq_zero.1 (norm_eq_zero.1 h)

/-- **Ellipse: focus–directrix characterisation** (one nappe). Under the hypotheses of
`directrix_ellipse`, for each focus a point of the plane is on the nappe iff its focal distance
is `e` times its distance to the corresponding directrix.
@isnad1 id=ex.8h7v.s10.be30c8f722c5 from=translated src=- shape=7b597d3b vocab=1be96555
-/
theorem directrix_iff_ellipse {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : s < |⟪u, n⟫|)
    (hc : 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫) (hm1 : ⟪u, n⟫ ^ 2 < 1) :
    ∃ d₁ d₂ : ℝ, ∃ F₁ F₂ : E, 0 < d₁ ∧ d₁ < d₂ ∧
      F₁ ∈ plane p₀ n ∧ F₂ ∈ plane p₀ n ∧
      F₁ = (V + d₁ • u) - ⟪(V + d₁ • u) - p₀, n⟫ • n ∧
      F₂ = (V + d₂ • u) - ⟪(V + d₂ • u) - p₀, n⟫ • n ∧
      ∀ X ∈ plane p₀ n,
        (X ∈ cone V u k ↔
          ‖X - F₁‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d₁ * k ^ 2))) ∧
        (X ∈ cone V u k ↔
          ‖X - F₂‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d₂ * k ^ 2))) := by
  obtain ⟨d₁, d₂, F₁, F₂, hd₁, hd, htan, -, hF₁, hF₂, hp₁, hp₂, -⟩ :=
    dandelin_exists hu hn hks hk hs hm hc
  refine ⟨d₁, d₂, F₁, F₂, hd₁, hd, hF₁, hF₂, hp₁, hp₂, fun X hX => ⟨?_, ?_⟩⟩
  · obtain ⟨h1, h2⟩ := tangent_of_proj hn hp₁ ((htan d₁).2 (Or.inl rfl)) hX hF₁
    refine ⟨fun hXc => focal_dist_eq_ecc_mul hu hn hks hk hm1 hX hXc h1 h2, fun h => ?_⟩
    exact directrix_converse_nappe hu hn hks hk hs hm.le hc hm1 hX
      (by rw [abs_of_pos hd₁]; exact h1) h2 h
  · obtain ⟨h1, h2⟩ := tangent_of_proj hn hp₂ ((htan d₂).2 (Or.inr rfl)) hX hF₂
    refine ⟨fun hXc => focal_dist_eq_ecc_mul hu hn hks hk hm1 hX hXc h1 h2, fun h => ?_⟩
    exact directrix_converse_nappe hu hn hks hk hs hm.le hc hm1 hX
      (by rw [abs_of_pos (hd₁.trans hd)]; exact h1) h2 h

/-- **Parabola: focus–directrix characterisation** (one nappe, `e = 1`).
@isnad1 id=ex.7h7v.s9.ce335e834cf2 from=translated src=- shape=47ed19c7 vocab=3ca500db
-/
theorem directrix_iff_parabola {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : s = |⟪u, n⟫|)
    (hc : 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫) :
    ∃ d : ℝ, ∃ F : E, 0 < d ∧ F ∈ plane p₀ n ∧
      F = (V + d • u) - ⟪(V + d • u) - p₀, n⟫ • n ∧
      ∀ X ∈ plane p₀ n,
        (X ∈ cone V u k ↔ ‖X - F‖ = Metric.infDist X (directrix V u n p₀ (d * k ^ 2))) := by
  obtain ⟨he, d, F, hd, htan, hFπ, hFp, hdir⟩ := directrix_parabola hu hn hks hk hs hm hc
  have hm1 : ⟪u, n⟫ ^ 2 < 1 := by rw [← sq_abs, ← hm]; nlinarith
  refine ⟨d, F, hd, hFπ, hFp, fun X hX => ⟨hdir X hX, fun h => ?_⟩⟩
  obtain ⟨h1, h2⟩ := tangent_of_proj hn hFp ((htan d).2 rfl) hX hFπ
  have h1' : ‖F - (V + d • u)‖ = |d| * s := by rw [abs_of_pos hd]; exact h1
  rw [← one_mul (Metric.infDist _ _), ← he] at h
  exact directrix_converse_nappe hu hn hks hk hs hm.le hc hm1 hX h1' h2 h

/-- **Hyperbola: focus–directrix characterisation of the double-cone section, and failure of
the one-nappe converse.** In the hyperbola regime, for each focus `Fᵢ`, a point of the plane is
on the double cone iff `‖X - Fᵢ‖ = e · dist(X, ℓᵢ)`; but this does not force the upper nappe:
there is a point of the plane satisfying the relation for either focus which is not on
`cone V u k` (it is on the lower nappe), and symmetrically for `cone V (-u) k`.
@isnad1 id=ex.7h7v.s10.9a325296ce3a from=translated src=- shape=1708979c vocab=9b13018a
-/
theorem directrix_iff_hyperbola {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : |⟪u, n⟫| < s)
    (hc : ⟪p₀ - V, n⟫ ≠ 0) :
    ∃ d₁ d₂ : ℝ, ∃ F₁ F₂ : E, d₂ < 0 ∧ 0 < d₁ ∧ F₁ ∈ plane p₀ n ∧ F₂ ∈ plane p₀ n ∧
      F₁ = (V + d₁ • u) - ⟪(V + d₁ • u) - p₀, n⟫ • n ∧
      F₂ = (V + d₂ • u) - ⟪(V + d₂ • u) - p₀, n⟫ • n ∧
      (∀ X ∈ plane p₀ n,
        (X ∈ cone2 V u k ↔
          ‖X - F₁‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d₁ * k ^ 2))) ∧
        (X ∈ cone2 V u k ↔
          ‖X - F₂‖ = ecc ⟪u, n⟫ k * Metric.infDist X (directrix V u n p₀ (d₂ * k ^ 2)))) ∧
      (∃ Y ∈ plane p₀ n, Y ∉ cone V u k ∧
        ‖Y - F₁‖ = ecc ⟪u, n⟫ k * Metric.infDist Y (directrix V u n p₀ (d₁ * k ^ 2)) ∧
        ‖Y - F₂‖ = ecc ⟪u, n⟫ k * Metric.infDist Y (directrix V u n p₀ (d₂ * k ^ 2))) ∧
      (∃ Y ∈ plane p₀ n, Y ∉ cone V (-u) k ∧
        ‖Y - F₁‖ = ecc ⟪u, n⟫ k * Metric.infDist Y (directrix V u n p₀ (d₁ * k ^ 2)) ∧
        ‖Y - F₂‖ = ecc ⟪u, n⟫ k * Metric.infDist Y (directrix V u n p₀ (d₂ * k ^ 2))) := by
  obtain ⟨-, d₁, d₂, F₁, F₂, hd₂, hd₁, htan, hF₁, hF₂, hp₁, hp₂, -, -, -, hdir⟩ :=
    dandelin_hyperbola hu hn hks hk hs hm hc
  have hmu : ⟪u, n⟫ ^ 2 < 1 := by
    have := mul_pos (sub_pos.2 hm) (show 0 < s + |⟪u, n⟫| by linarith [abs_nonneg ⟪u, n⟫])
    nlinarith [sq_abs ⟪u, n⟫, mul_pos hk hk]
  have hVπ : ∀ X ∈ plane p₀ n, X ≠ V := by
    intro X hX hXV
    rw [hXV] at hX
    have h0 : ⟪V - p₀, n⟫ = 0 := hX
    have : p₀ - V = -(V - p₀) := by abel
    rw [this, inner_neg_left, h0, neg_zero] at hc
    exact hc rfl
  obtain ⟨⟨X, hX, hXc⟩, ⟨Y, hY, hYc⟩⟩ := hyp_both_nappes hu hn hks hk hs hm hc
  refine ⟨d₁, d₂, F₁, F₂, hd₂, hd₁, hF₁, hF₂, hp₁, hp₂, fun Z hZ => ⟨?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := tangent_of_proj hn hp₁ ((htan d₁).2 (Or.inl rfl)) hZ hF₁
    exact mem_cone2_iff_focal_directrix hu hn hks hk hmu hZ h1 h2
  · obtain ⟨h1, h2⟩ := tangent_of_proj hn hp₂ ((htan d₂).2 (Or.inr rfl)) hZ hF₂
    exact mem_cone2_iff_focal_directrix hu hn hks hk hmu hZ h1 h2
  · refine ⟨Y, hY, fun h => hVπ Y hY (eq_of_mem_both_nappes hk h hYc),
      hdir Y hY (mem_cone2_iff.2 (Or.inr hYc))⟩
  · refine ⟨X, hX, fun h => hVπ X hX (eq_of_mem_both_nappes hk hXc h),
      hdir X hX (mem_cone2_iff.2 (Or.inl hXc))⟩

/-! ## (2) The plane through the apex -/

/-- `u - ⟪u, n⟫ n`: the projection of the axis direction onto the cutting plane.-/
noncomputable def apexDir (u n : E) : E := u - ⟪u, n⟫ • n

/-- The slope `ρ = √((1 - m²)(s² - m²)) / k` of the two generator lines in the plane.-/
noncomputable def apexRho (m k s : ℝ) : ℝ := Real.sqrt ((1 - m ^ 2) * (s ^ 2 - m ^ 2)) / k

/--
@isnad1 id=eq.1h3v.s5.30f156c7f332 from=translated src=- shape=d284af60 vocab=959f0a46
-/
theorem apexDir_inner_n {u n : E} (hn : ‖n‖ = 1) : ⟪apexDir u n, n⟫ = 0 := by
  unfold apexDir
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hn]
  ring

/--
@isnad1 id=eq.1h3v.s6.f803485b8151 from=translated src=- shape=5df64836 vocab=3c47450d
-/
theorem apexDir_inner_u {u n : E} (hu : ‖u‖ = 1) : ⟪apexDir u n, u⟫ = 1 - ⟪u, n⟫ ^ 2 := by
  unfold apexDir
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu,
    real_inner_comm u n]
  ring

/--
@isnad1 id=eq.2h3v.s6.ff7fd584ae94 from=translated src=- shape=3c834e63 vocab=3c47450d
-/
theorem apexDir_norm_sq {u n : E} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1) :
    ‖apexDir u n‖ ^ 2 = 1 - ⟪u, n⟫ ^ 2 := norm_sub_inner_smul_sq hu hn

/--
@isnad1 id=eq.1h4v.s6.7fc9b8da29ef from=translated src=- shape=a7d8f7c3 vocab=a25d454d
-/
theorem inner_apexDir_of_perp {u n w : E} (hw : ⟪w, n⟫ = 0) : ⟪w, apexDir u n⟫ = ⟪w, u⟫ := by
  unfold apexDir
  rw [inner_sub_right, real_inner_smul_right, hw, mul_zero, sub_zero]

/--
@isnad1 id=eq.2h4v.s6.71f9ba64e945 from=translated src=- shape=13130d5f vocab=a25d454d
-/
theorem apexDir_inner_orth {u n f : E} (hfu : ⟪f, u⟫ = 0) (hfn : ⟪f, n⟫ = 0) :
    ⟪apexDir u n, f⟫ = 0 := by
  unfold apexDir
  rw [inner_sub_left, real_inner_smul_left, real_inner_comm f u, real_inner_comm f n, hfu, hfn,
    mul_zero, sub_zero]

/-- For a plane through the apex, membership is `⟪X - V, n⟫ = 0`.
@isnad1 id=iff.1h5v.s6.efa30afef5d0 from=translated src=- shape=f2c8ecbb vocab=dc79468e
-/
theorem mem_plane_iff_of_apex {V n p₀ X : E} (hc : ⟪p₀ - V, n⟫ = 0) :
    X ∈ plane p₀ n ↔ ⟪X - V, n⟫ = 0 := by
  constructor
  · intro h; rw [inner_sub_V_of_mem_plane h, hc]
  · intro h
    show ⟪X - p₀, n⟫ = 0
    have : X - p₀ = (X - V) - (p₀ - V) := by abel
    rw [this, inner_sub_left, h, hc, sub_zero]

/-- Cauchy–Schwarz in the plane: for `w ⟂ n`, `⟪w, u⟫² ≤ (1 - ⟪u, n⟫²) ‖w‖²`.
@isnad1 id=le.3h4v.s7.f8d6bf563c8b from=translated src=- shape=58ce55f2 vocab=35a0cefa
-/
theorem apex_cs {u n w : E} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1) (hw : ⟪w, n⟫ = 0) :
    ⟪w, u⟫ ^ 2 ≤ (1 - ⟪u, n⟫ ^ 2) * ‖w‖ ^ 2 := by
  have h := abs_real_inner_le_norm w (apexDir u n)
  rw [inner_apexDir_of_perp hw] at h
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow, apexDir_norm_sq hu hn] at h2
  linarith

/-- **Plane through the apex, `sin α < |⟪u, n⟫|`: the section is the apex alone** (any `E`).
@isnad1 id=eq.6h7v.s7.6a9e93d5b979 from=translated src=- shape=65658b80 vocab=e17f96bc
-/
theorem apex_section_point {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hs : 0 < s) (hm : s < |⟪u, n⟫|) (hc : ⟪p₀ - V, n⟫ = 0) :
    plane p₀ n ∩ cone2 V u k = {V} := by
  have hm2 : s ^ 2 < ⟪u, n⟫ ^ 2 := by
    nlinarith [sq_abs ⟪u, n⟫, mul_pos (sub_pos.2 hm) (show 0 < |⟪u, n⟫| + s by linarith)]
  ext X
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hX, hX2⟩
    have hw := (mem_plane_iff_of_apex hc).1 hX
    have hcs := apex_cs hu hn hw
    have hX2' : ⟪X - V, u⟫ ^ 2 = k ^ 2 * ‖X - V‖ ^ 2 := hX2
    have h0 : ‖X - V‖ = 0 := by
      by_contra hne
      have hp : 0 < ‖X - V‖ ^ 2 := pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)) 2
      nlinarith [mul_pos (sub_pos.2 hm2) hp]
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  · intro h
    rw [h]
    refine ⟨(mem_plane_iff_of_apex hc).2 (by simp), ?_⟩
    show ⟪V - V, u⟫ ^ 2 = k ^ 2 * ‖V - V‖ ^ 2
    simp

/-- **Plane through the apex, `|⟪u, n⟫| = sin α`: the section is one generator line**, the line
through `V` with direction `u - ⟪u, n⟫ n` (any `E`).
@isnad1 id=and.6h7v.s8.8b7c97dcf424 from=translated src=- shape=27063fed vocab=b833b615
-/
theorem apex_section_line {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hm : |⟪u, n⟫| = s) (hc : ⟪p₀ - V, n⟫ = 0) :
    apexDir u n ≠ 0 ∧
      plane p₀ n ∩ cone2 V u k = {X | ∃ t : ℝ, X = V + t • apexDir u n} := by
  have hm2 : ⟪u, n⟫ ^ 2 = s ^ 2 := by rw [← hm, sq_abs]
  have hk2m : 1 - ⟪u, n⟫ ^ 2 = k ^ 2 := by linarith
  have ha2 : ‖apexDir u n‖ ^ 2 = k ^ 2 := by rw [apexDir_norm_sq hu hn, hk2m]
  have hk2 : k ^ 2 ≠ 0 := by positivity
  refine ⟨fun h => by rw [h, norm_zero] at ha2; exact hk2 (by rw [← ha2]; ring), ?_⟩
  ext X
  constructor
  · rintro ⟨hX, hX2⟩
    have hw := (mem_plane_iff_of_apex hc).1 hX
    have hX2' : ⟪X - V, u⟫ ^ 2 = k ^ 2 * ‖X - V‖ ^ 2 := hX2
    have e : ‖(k ^ 2) • (X - V) - ⟪X - V, u⟫ • apexDir u n‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right,
        inner_apexDir_of_perp hw, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        mul_pow, mul_pow, sq_abs, sq_abs, ha2]
      linear_combination (-k ^ 2) * hX2'
    have h3 : (k ^ 2) • (X - V) = ⟪X - V, u⟫ • apexDir u n :=
      sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 e))
    refine ⟨⟪X - V, u⟫ / k ^ 2, ?_⟩
    rw [← sub_eq_iff_eq_add', div_eq_inv_mul, mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hk2,
      one_smul]
  · rintro ⟨t, rfl⟩
    refine ⟨(mem_plane_iff_of_apex hc).2 ?_, ?_⟩
    · rw [add_sub_cancel_left, real_inner_smul_left, apexDir_inner_n hn, mul_zero]
    · show ⟪V + t • apexDir u n - V, u⟫ ^ 2 = k ^ 2 * ‖V + t • apexDir u n - V‖ ^ 2
      rw [add_sub_cancel_left, real_inner_smul_left, apexDir_inner_u hu, norm_smul,
        Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, ha2, hk2m]
      ring

/-- Coordinates in the plane spanned by `apexDir u n` and a unit `f ⟂ u, n`.
@isnad1 id=and.5h6v.s9.4be4c55c4375 from=translated src=- shape=4a7248b1 vocab=ecd9183a
-/
theorem apex_comb {u n f : E} {α β : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1) (hf : ‖f‖ = 1)
    (hfu : ⟪f, u⟫ = 0) (hfn : ⟪f, n⟫ = 0) :
    ⟪α • apexDir u n + β • f, n⟫ = 0 ∧
      ⟪α • apexDir u n + β • f, u⟫ = α * (1 - ⟪u, n⟫ ^ 2) ∧
      ‖α • apexDir u n + β • f‖ ^ 2 = α ^ 2 * (1 - ⟪u, n⟫ ^ 2) + β ^ 2 := by
  have haf := apexDir_inner_orth (u := u) (n := n) hfu hfn
  refine ⟨?_, ?_, ?_⟩
  · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, apexDir_inner_n hn, hfn]
    ring
  · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, apexDir_inner_u hu, hfu]
    ring
  · rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, haf, norm_smul,
      norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs,
      apexDir_norm_sq hu hn, hf]
    ring

/-- The lines `V + t (apexDir u n + σ f)` with `σ² k² = (1 - m²)(s² - m²)` lie in
plane ∩ double cone (any `E`).
@isnad1 id=mem.8h10v.s9.bbca38a647f7 from=translated src=- shape=0c5da40b vocab=58943ea2
-/
theorem apex_gen_mem {V u n p₀ f : E} {k s σ : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hc : ⟪p₀ - V, n⟫ = 0) (hf : ‖f‖ = 1) (hfu : ⟪f, u⟫ = 0)
    (hfn : ⟪f, n⟫ = 0) (hσ : σ ^ 2 * k ^ 2 = (1 - ⟪u, n⟫ ^ 2) * (s ^ 2 - ⟪u, n⟫ ^ 2)) (t : ℝ) :
    V + t • (apexDir u n + σ • f) ∈ plane p₀ n ∩ cone2 V u k := by
  have e : t • (apexDir u n + σ • f) = t • apexDir u n + (t * σ) • f := by
    rw [smul_add, smul_smul]
  obtain ⟨h0, h1, h2⟩ := apex_comb (α := t) (β := t * σ) hu hn hf hfu hfn
  refine ⟨(mem_plane_iff_of_apex hc).2 ?_, ?_⟩
  · rw [add_sub_cancel_left, e, h0]
  · show ⟪V + t • (apexDir u n + σ • f) - V, u⟫ ^ 2 =
      k ^ 2 * ‖V + t • (apexDir u n + σ • f) - V‖ ^ 2
    rw [add_sub_cancel_left, e, h1, h2]
    linear_combination (-t ^ 2) * hσ - t ^ 2 * (1 - ⟪u, n⟫ ^ 2) * hks

/-- In `finrank E ≤ 3`: a vector orthogonal to `n` lies in the span of `a` and `f`, if
`n, a, f` are nonzero and pairwise orthogonal (`‖f‖ = 1`).
@isnad1 id=eq.8h5v.s8.bb1a9fe524f1 from=translated src=- shape=ddb9aac7 vocab=8e6fe5f4
-/
theorem decomp_of_finrank_le_three [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E ≤ 3)
    {n a f w : E} (hn0 : n ≠ 0) (ha0 : a ≠ 0) (hf : ‖f‖ = 1) (han : ⟪a, n⟫ = 0)
    (hfn : ⟪f, n⟫ = 0) (haf : ⟪a, f⟫ = 0) (hwn : ⟪w, n⟫ = 0) :
    w = (⟪w, a⟫ / ‖a‖ ^ 2) • a + ⟪w, f⟫ • f := by
  have hA : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 ha0)
  have hfa : ⟪f, a⟫ = 0 := by rw [real_inner_comm]; exact haf
  have hff : ⟪f, f⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hf]; norm_num
  obtain ⟨z, hz⟩ : ∃ z, z = w - (⟪w, a⟫ / ‖a‖ ^ 2) • a - ⟪w, f⟫ • f := ⟨_, rfl⟩
  have hzn : ⟪z, n⟫ = 0 := by
    rw [hz, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left, hwn,
      han, hfn]; ring
  have hza : ⟪z, a⟫ = 0 := by
    rw [hz, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left, hfa,
      real_inner_self_eq_norm_sq]; field_simp; ring
  have hzf : ⟪z, f⟫ = 0 := by
    rw [hz, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left, haf,
      hff]; ring
  have hnz : ⟪n, z⟫ = 0 := by rw [real_inner_comm]; exact hzn
  have haz : ⟪a, z⟫ = 0 := by rw [real_inner_comm]; exact hza
  have hfz : ⟪f, z⟫ = 0 := by rw [real_inner_comm]; exact hzf
  have hna : ⟪n, a⟫ = 0 := by rw [real_inner_comm]; exact han
  have hnf : ⟪n, f⟫ = 0 := by rw [real_inner_comm]; exact hfn
  have hf0 : f ≠ 0 := by intro h; rw [h, norm_zero] at hf; exact zero_ne_one hf
  by_contra hne
  have hz0 : z ≠ 0 := by
    intro h0; apply hne; rw [← sub_eq_zero, ← sub_sub, ← hz, h0]
  have hli : LinearIndependent ℝ ![n, a, f, z] := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ?_
    · intro i
      fin_cases i <;> simp [hn0, ha0, hf0, hz0]
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
        | exact absurd rfl hij
        | simp [han, hfn, haf, hzn, hza, hzf, hnz, haz, hfz, hna, hnf, hfa]
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  omega

/--
@isnad1 id=eq.2h3v.s7.c831d1d32c87 from=translated src=- shape=f5aa296e vocab=ff5075f6
-/
theorem apexRho_sq {m k s : ℝ} (hk : 0 < k) (hP : 0 ≤ (1 - m ^ 2) * (s ^ 2 - m ^ 2)) :
    apexRho m k s ^ 2 * k ^ 2 = (1 - m ^ 2) * (s ^ 2 - m ^ 2) := by
  unfold apexRho
  rw [div_pow, Real.sq_sqrt hP]
  field_simp

/-- **Plane through the apex, `|⟪u, n⟫| < sin α`, `finrank E = 3`: the section is a pair of
distinct generator lines through `V`**, with directions `apexDir u n ± ρ f`, where `f` is a unit
vector orthogonal to `u` and `n` and `ρ = √((1 - m²)(s² - m²)) / cos α > 0`; the two lines meet
only at `V`.
@isnad1 id=ex.7h7v.s10.a141b1aaf1ee from=translated src=- shape=6faab239 vocab=39e3e51b
-/
theorem apex_section_two_lines [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3)
    {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1) (hks : k ^ 2 + s ^ 2 = 1)
    (hk : 0 < k) (hm : |⟪u, n⟫| < s) (hc : ⟪p₀ - V, n⟫ = 0) :
    ∃ f : E, ‖f‖ = 1 ∧ ⟪f, u⟫ = 0 ∧ ⟪f, n⟫ = 0 ∧ 0 < apexRho ⟪u, n⟫ k s ∧
      plane p₀ n ∩ cone2 V u k =
        {X | ∃ t : ℝ, X = V + t • (apexDir u n + apexRho ⟪u, n⟫ k s • f)} ∪
          {X | ∃ t : ℝ, X = V + t • (apexDir u n - apexRho ⟪u, n⟫ k s • f)} ∧
      ∀ t t' : ℝ, V + t • (apexDir u n + apexRho ⟪u, n⟫ k s • f) =
          V + t' • (apexDir u n - apexRho ⟪u, n⟫ k s • f) → t = 0 ∧ t' = 0 := by
  classical
  obtain ⟨f, hf, hfS⟩ := exists_unit_orth ({u, n} : Finset E)
    (lt_of_le_of_lt Finset.card_le_two (by omega : 2 < Module.finrank ℝ E))
  have hfu : ⟪f, u⟫ = 0 := hfS u (by simp)
  have hfn : ⟪f, n⟫ = 0 := hfS n (by simp)
  have hm2 : ⟪u, n⟫ ^ 2 < s ^ 2 := by
    nlinarith [sq_abs ⟪u, n⟫, abs_nonneg ⟪u, n⟫,
      mul_pos (sub_pos.2 hm) (show 0 < s + |⟪u, n⟫| by linarith [abs_nonneg ⟪u, n⟫])]
  have h1m : 0 < 1 - ⟪u, n⟫ ^ 2 := by nlinarith [mul_pos hk hk]
  have hP : 0 < (1 - ⟪u, n⟫ ^ 2) * (s ^ 2 - ⟪u, n⟫ ^ 2) := mul_pos h1m (by linarith)
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = apexRho ⟪u, n⟫ k s := ⟨_, rfl⟩
  rw [← hρ]
  have hρ2 : ρ ^ 2 * k ^ 2 = (1 - ⟪u, n⟫ ^ 2) * (s ^ 2 - ⟪u, n⟫ ^ 2) := by
    rw [hρ]; exact apexRho_sq hk hP.le
  have hρ0 : 0 < ρ := by rw [hρ]; unfold apexRho; exact div_pos (Real.sqrt_pos.2 hP) hk
  have ha2 := apexDir_norm_sq (u := u) (n := n) hu hn
  have ha0 : apexDir u n ≠ 0 := by
    intro h; rw [h, norm_zero] at ha2; linarith [h1m, ha2]
  have hn0 : n ≠ 0 := by intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  have haf := apexDir_inner_orth (u := u) (n := n) hfu hfn
  have hfa : ⟪f, apexDir u n⟫ = 0 := by rw [real_inner_comm]; exact haf
  have hk2 : k ^ 2 ≠ 0 := by positivity
  have hneg : apexDir u n - ρ • f = apexDir u n + (-ρ) • f := by rw [neg_smul, sub_eq_add_neg]
  refine ⟨f, hf, hfu, hfn, hρ0, ?_, ?_⟩
  · ext X
    constructor
    · rintro ⟨hX, hX2⟩
      have hw := (mem_plane_iff_of_apex hc).1 hX
      have hX2' : ⟪X - V, u⟫ ^ 2 = k ^ 2 * ‖X - V‖ ^ 2 := hX2
      have hdec := decomp_of_finrank_le_three hdim.le hn0 ha0 hf (apexDir_inner_n hn) hfn haf hw
      obtain ⟨α, hα⟩ : ∃ α, α = ⟪X - V, apexDir u n⟫ / ‖apexDir u n‖ ^ 2 := ⟨_, rfl⟩
      obtain ⟨β, hβ⟩ : ∃ β, β = ⟪X - V, f⟫ := ⟨_, rfl⟩
      rw [← hα, ← hβ] at hdec
      obtain ⟨c0, c1, c2⟩ := apex_comb (α := α) (β := β) hu hn hf hfu hfn
      rw [← hdec] at c1 c2
      rw [c1, c2] at hX2'
      have hprod : k ^ 2 * ((β - α * ρ) * (β + α * ρ)) = 0 := by
        linear_combination (-1 : ℝ) * hX2' + (-α ^ 2) * hρ2 + (-α ^ 2 * (1 - ⟪u, n⟫ ^ 2)) * hks
      rcases mul_eq_zero.1 ((mul_eq_zero.1 hprod).resolve_left hk2) with h | h
      · refine Or.inl ⟨α, ?_⟩
        rw [← sub_eq_iff_eq_add', hdec, show β = α * ρ by linarith]
        module
      · refine Or.inr ⟨α, ?_⟩
        rw [← sub_eq_iff_eq_add', hdec, show β = -(α * ρ) by linarith]
        module
    · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · exact apex_gen_mem hu hn hks hc hf hfu hfn hρ2 t
      · rw [hneg]
        exact apex_gen_mem hu hn hks hc hf hfu hfn (by rw [neg_sq]; exact hρ2) t
  · intro t t' h
    have h' := add_left_cancel h
    have e1 := congrArg (fun z => ⟪z, apexDir u n⟫) h'
    have e2 := congrArg (fun z => ⟪z, f⟫) h'
    simp only [real_inner_smul_left, inner_add_left, inner_sub_left, hfa, haf,
      real_inner_self_eq_norm_sq, ha2, hf] at e1 e2
    have q1 : (t - t') * (1 - ⟪u, n⟫ ^ 2) = 0 := by linear_combination e1
    have q2 : (t + t') * ρ = 0 := by linear_combination e2
    have r1 := (mul_eq_zero.1 q1).resolve_right h1m.ne'
    have r2 := (mul_eq_zero.1 q2).resolve_right hρ0.ne'
    constructor <;> linarith

/-- In any finite-dimensional `E` with `3 ≤ finrank`, for `|⟪u, n⟫| < sin α` the two generator
lines are contained in the section of a plane through the apex. Equality needs `finrank E = 3`:
in higher dimension the section is a quadric cone inside the cutting hyperplane (dimension `finrank E - 1`), not two lines.
@isnad1 id=ex.7h7v.s9.d3da76b91190 from=translated src=- shape=9fb058e7 vocab=ebaf7392
-/
theorem apex_two_lines_subset [FiniteDimensional ℝ E] (hdim : 3 ≤ Module.finrank ℝ E)
    {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1) (hks : k ^ 2 + s ^ 2 = 1)
    (hk : 0 < k) (hm : |⟪u, n⟫| < s) (hc : ⟪p₀ - V, n⟫ = 0) :
    ∃ f : E, ‖f‖ = 1 ∧ ⟪f, u⟫ = 0 ∧ ⟪f, n⟫ = 0 ∧ 0 < apexRho ⟪u, n⟫ k s ∧
      {X | ∃ t : ℝ, X = V + t • (apexDir u n + apexRho ⟪u, n⟫ k s • f)} ∪
          {X | ∃ t : ℝ, X = V + t • (apexDir u n - apexRho ⟪u, n⟫ k s • f)} ⊆
        plane p₀ n ∩ cone2 V u k := by
  classical
  obtain ⟨f, hf, hfS⟩ := exists_unit_orth ({u, n} : Finset E)
    (lt_of_le_of_lt Finset.card_le_two (by omega : 2 < Module.finrank ℝ E))
  have hfu : ⟪f, u⟫ = 0 := hfS u (by simp)
  have hfn : ⟪f, n⟫ = 0 := hfS n (by simp)
  have hm2 : ⟪u, n⟫ ^ 2 < s ^ 2 := by
    nlinarith [sq_abs ⟪u, n⟫, abs_nonneg ⟪u, n⟫,
      mul_pos (sub_pos.2 hm) (show 0 < s + |⟪u, n⟫| by linarith [abs_nonneg ⟪u, n⟫])]
  have h1m : 0 < 1 - ⟪u, n⟫ ^ 2 := by nlinarith [mul_pos hk hk]
  have hP : 0 < (1 - ⟪u, n⟫ ^ 2) * (s ^ 2 - ⟪u, n⟫ ^ 2) := mul_pos h1m (by linarith)
  have hρ2 := apexRho_sq (m := ⟪u, n⟫) (s := s) hk hP.le
  refine ⟨f, hf, hfu, hfn, div_pos (Real.sqrt_pos.2 hP) hk, ?_⟩
  rintro X (⟨t, rfl⟩ | ⟨t, rfl⟩)
  · exact apex_gen_mem hu hn hks hc hf hfu hfn hρ2 t
  · rw [show apexDir u n - apexRho ⟪u, n⟫ k s • f = apexDir u n + (-apexRho ⟪u, n⟫ k s) • f by
      rw [neg_smul, sub_eq_add_neg]]
    exact apex_gen_mem hu hn hks hc hf hfu hfn (by rw [neg_sq]; exact hρ2) t

/-- **Degenerate sections in `ℝ³`** (plane through the apex): a point, one generator line, or
two generator lines through `V`, according as `sin α < |⟪u, n⟫|`, `= `, `>`.
@isnad1 id=and.6h6v.s12.5fed77144927 from=translated src=- shape=9ae281bf vocab=2cf2b8f7
-/
theorem apex_section_R3 {V u n p₀ : EuclideanSpace ℝ (Fin 3)} {k s : ℝ} (hu : ‖u‖ = 1)
    (hn : ‖n‖ = 1) (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s)
    (hc : ⟪p₀ - V, n⟫ = 0) :
    (s < |⟪u, n⟫| → plane p₀ n ∩ cone2 V u k = {V}) ∧
    (|⟪u, n⟫| = s → apexDir u n ≠ 0 ∧
      plane p₀ n ∩ cone2 V u k = {X | ∃ t : ℝ, X = V + t • apexDir u n}) ∧
    (|⟪u, n⟫| < s → ∃ f : EuclideanSpace ℝ (Fin 3), ‖f‖ = 1 ∧ ⟪f, u⟫ = 0 ∧ ⟪f, n⟫ = 0 ∧
      0 < apexRho ⟪u, n⟫ k s ∧
      plane p₀ n ∩ cone2 V u k =
        {X | ∃ t : ℝ, X = V + t • (apexDir u n + apexRho ⟪u, n⟫ k s • f)} ∪
          {X | ∃ t : ℝ, X = V + t • (apexDir u n - apexRho ⟪u, n⟫ k s • f)} ∧
      ∀ t t' : ℝ, V + t • (apexDir u n + apexRho ⟪u, n⟫ k s • f) =
          V + t' • (apexDir u n - apexRho ⟪u, n⟫ k s • f) → t = 0 ∧ t' = 0) :=
  ⟨fun hm => apex_section_point hu hn hks hs hm hc,
    fun hm => apex_section_line hu hn hks hk hm hc,
    fun hm => apex_section_two_lines finrank_euclideanSpace_fin hu hn hks hk hm hc⟩

end Dandelin
