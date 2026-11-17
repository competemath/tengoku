import Tengoku.Dandelin.Dandelin.Hyperbola

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dandelin spheres, phase 5: non-emptiness and the regime characterisation

Generators of the cone are the rays `V + t • w` with `‖w‖ = 1`, `⟪w, u⟫ = cos α`. Intersecting
a generator with the plane `plane p₀ n` is a linear equation `t ⟪w, n⟫ = ⟪p₀ - V, n⟫`; the sign
of `t` decides the nappe. This gives explicit points of the section and, by letting `⟪w, n⟫`
tend to `0`, points of arbitrarily large norm.
-/

open RealInnerProductSpace

namespace Dandelin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Generators -/

/-- A point `V + t • w` of a generator (`‖w‖ = 1`, `⟪w, u⟫ = k`) with `t ≥ 0` is on the upper
nappe.
@isnad1 id=mem.3h6v.s7.b06d4a743274 from=translated src=- shape=405b8eaa vocab=b4a7c329
-/
theorem gen_mem_cone {V u w : E} {k t : ℝ} (hw : ‖w‖ = 1) (hwu : ⟪w, u⟫ = k) (ht : 0 ≤ t) :
    V + t • w ∈ cone V u k := by
  show ⟪V + t • w - V, u⟫ = k * ‖V + t • w - V‖
  rw [add_sub_cancel_left, real_inner_smul_left, hwu, norm_smul, hw, Real.norm_eq_abs,
    abs_of_nonneg ht]
  ring

/-- With `t ≤ 0` the point `V + t • w` is on the lower nappe.
@isnad1 id=mem.3h6v.s7.a80dca03196b from=translated src=- shape=b78b6784 vocab=e9020a7c
-/
theorem gen_mem_cone_neg {V u w : E} {k t : ℝ} (hw : ‖w‖ = 1) (hwu : ⟪w, u⟫ = k)
    (ht : t ≤ 0) : V + t • w ∈ cone V (-u) k := by
  show ⟪V + t • w - V, -u⟫ = k * ‖V + t • w - V‖
  rw [add_sub_cancel_left, inner_neg_right, real_inner_smul_left, hwu, norm_smul, hw,
    Real.norm_eq_abs, abs_of_nonpos ht]
  ring

/--
@isnad1 id=eq.1h4v.s7.d0d88c5357dd from=translated src=- shape=dd1c7879 vocab=f489a4bf
-/
theorem gen_norm {V w : E} {t : ℝ} (hw : ‖w‖ = 1) : ‖V + t • w - V‖ = |t| := by
  rw [add_sub_cancel_left, norm_smul, hw, Real.norm_eq_abs, mul_one]

/-- The generator in direction `w` meets the plane at parameter `t = ⟪p₀ - V, n⟫ / ⟪w, n⟫`.
@isnad1 id=mem.1h5v.s7.8fa4180ddb6c from=translated src=- shape=dfe63a1b vocab=4d63c691
-/
theorem gen_mem_plane {V w p₀ n : E} (hwn : ⟪w, n⟫ ≠ 0) :
    V + (⟪p₀ - V, n⟫ / ⟪w, n⟫) • w ∈ plane p₀ n := by
  show ⟪V + (⟪p₀ - V, n⟫ / ⟪w, n⟫) • w - p₀, n⟫ = 0
  have : V + (⟪p₀ - V, n⟫ / ⟪w, n⟫) • w - p₀ = (⟪p₀ - V, n⟫ / ⟪w, n⟫) • w - (p₀ - V) := by
    abel
  rw [this, inner_sub_left, real_inner_smul_left, div_mul_cancel₀ _ hwn, sub_self]

/-- The generator direction `k u + s e`, for `e` a unit vector orthogonal to `u`.
@isnad1 id=and.4h5v.s8.0005696c9dc5 from=translated src=- shape=6c062744 vocab=ba1e5565
-/
theorem gen_dir {u e : E} {k s : ℝ} (hu : ‖u‖ = 1) (he : ‖e‖ = 1) (heu : ⟪e, u⟫ = 0)
    (hks : k ^ 2 + s ^ 2 = 1) : ‖k • u + s • e‖ = 1 ∧ ⟪k • u + s • e, u⟫ = k := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hue : ⟪u, e⟫ = 0 := by rw [real_inner_comm]; exact heu
  constructor
  · have h : ‖k • u + s • e‖ ^ 2 = 1 ^ 2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
        hue, hu, he, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one, sq_abs, sq_abs]
      linear_combination hks
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h
  · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, huu, heu]; ring

/-- In finite dimension `> #S` there is a unit vector orthogonal to every vector of `S`.
@isnad1 id=ex.1h2v.s6.63345b4dd5e3 from=translated src=- shape=99b78947 vocab=fbc6c358
-/
theorem exists_unit_orth [FiniteDimensional ℝ E] (S : Finset E)
    (h : S.card < Module.finrank ℝ E) : ∃ f : E, ‖f‖ = 1 ∧ ∀ x ∈ S, ⟪f, x⟫ = 0 := by
  set K := Submodule.span ℝ (S : Set E)
  have hK : Module.finrank ℝ K ≤ S.card := finrank_span_finset_le_card S
  have hsum := Submodule.finrank_add_finrank_orthogonal K
  have hne : Kᗮ ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hsum
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  refine ⟨‖v‖⁻¹ • v, ?_, fun x hx => ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn]
  · rw [real_inner_smul_left,
      Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span hx) hv, mul_zero]

/-! ## The part of `n` orthogonal to the axis -/

/-- `n - ⟪u, n⟫ u`, the component of the plane normal orthogonal to the axis.-/
noncomputable def perpN (u n : E) : E := n - ⟪u, n⟫ • u

/--
@isnad1 id=eq.1h3v.s5.27c8b8aecfd7 from=translated src=- shape=8a6c79e7 vocab=acb78b8c
-/
theorem perpN_inner_u {u n : E} (hu : ‖u‖ = 1) : ⟪perpN u n, u⟫ = 0 := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hnu : ⟪n, u⟫ = ⟪u, n⟫ := real_inner_comm _ _
  unfold perpN
  rw [inner_sub_left, real_inner_smul_left, huu, hnu, mul_one, sub_self]

/--
@isnad1 id=eq.1h3v.s6.b60d483bad1b from=translated src=- shape=0f02014f vocab=b9894760
-/
theorem perpN_inner_n {u n : E} (hn : ‖n‖ = 1) : ⟪perpN u n, n⟫ = 1 - ⟪u, n⟫ ^ 2 := by
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  unfold perpN
  rw [inner_sub_left, real_inner_smul_left, hnn]
  ring

/--
@isnad1 id=eq.2h3v.s6.4a4fac1edbf0 from=translated src=- shape=3c834e63 vocab=b9894760
-/
theorem perpN_norm_sq {u n : E} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1) :
    ‖perpN u n‖ ^ 2 = 1 - ⟪u, n⟫ ^ 2 := by
  have h := norm_sub_inner_smul_sq (u := n) (n := u) hn hu
  unfold perpN
  rw [real_inner_comm] at h
  exact h

/--
@isnad1 id=eq.2h4v.s6.5c6d2a17ede3 from=translated src=- shape=13130d5f vocab=7c29c859
-/
theorem perpN_inner_orth {u n f : E} (hfu : ⟪f, u⟫ = 0) (hfn : ⟪f, n⟫ = 0) :
    ⟪perpN u n, f⟫ = 0 := by
  have h1 : ⟪n, f⟫ = 0 := by rw [real_inner_comm]; exact hfn
  have h2 : ⟪u, f⟫ = 0 := by rw [real_inner_comm]; exact hfu
  unfold perpN
  rw [inner_sub_left, real_inner_smul_left, h1, h2, mul_zero, sub_zero]

/-- The unit vectors `e = (a / ‖q‖) q + b f` (`q = perpN u n`, `f ⟂ u, n`) are orthogonal to `u`,
with `⟪e, n⟫ = a ‖q‖`.
@isnad1 id=and.6h6v.s9.89d6801710d8 from=translated src=- shape=67e234e9 vocab=373b4692
-/
theorem perp_dir {u n f : E} {a b : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hr : ‖perpN u n‖ ≠ 0) (hfu : ⟪f, u⟫ = 0) (hfn : ⟪f, n⟫ = 0)
    (hab : a ^ 2 + b ^ 2 * ‖f‖ ^ 2 = 1) :
    ‖(a / ‖perpN u n‖) • perpN u n + b • f‖ = 1 ∧
      ⟪(a / ‖perpN u n‖) • perpN u n + b • f, u⟫ = 0 ∧
      ⟪(a / ‖perpN u n‖) • perpN u n + b • f, n⟫ = a * ‖perpN u n‖ := by
  have hqf := perpN_inner_orth (u := u) (n := n) hfu hfn
  have hfq : ⟪f, perpN u n⟫ = 0 := by rw [real_inner_comm]; exact hqf
  have hx : a / ‖perpN u n‖ * ‖perpN u n‖ = a := div_mul_cancel₀ a hr
  have hq2 := perpN_norm_sq (u := u) (n := n) hu hn
  refine ⟨?_, ?_, ?_⟩
  · have h : ‖(a / ‖perpN u n‖) • perpN u n + b • f‖ ^ 2 = 1 ^ 2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
        hqf, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs, div_pow,
        div_mul_cancel₀ _ (pow_ne_zero 2 hr)]
      linear_combination hab
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h
  · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, perpN_inner_u hu, hfu]
    ring
  · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, perpN_inner_n hn, hfn]
    linear_combination (-(a / ‖perpN u n‖)) * hq2 + ‖perpN u n‖ * hx

/-! ## Explicit points of the section -/

/--
@isnad1 id=eq.1h5v.s6.5f3da02fe271 from=translated src=- shape=6b45d93d vocab=dc79468e
-/
theorem inner_sub_V_of_mem_plane {V p₀ n X : E} (hX : X ∈ plane p₀ n) :
    ⟪X - V, n⟫ = ⟪p₀ - V, n⟫ := by
  have hX' : ⟪X - p₀, n⟫ = 0 := hX
  have : X - V = (X - p₀) + (p₀ - V) := by abel
  rw [this, inner_add_left, hX', zero_add]

/-- **The generator construction.** For a unit `e ⟂ u`, the generator direction
`w = k u + s e` meets the plane (if `δ = ⟪w, n⟫ ≠ 0`) at `V + (c / δ) w`, `c = ⟪p₀ - V, n⟫`; this
point is at distance `|c / δ|` from the apex, on the upper nappe if `c / δ ≥ 0` and on the lower
nappe if `c / δ ≤ 0`.
@isnad1 id=ex.5h8v.s10.6b4b83d86c6f from=translated src=- shape=1cc0231d vocab=9fe40b4d
-/
theorem gen_point {V u n p₀ e : E} {k s : ℝ} (hu : ‖u‖ = 1) (he : ‖e‖ = 1) (heu : ⟪e, u⟫ = 0)
    (hks : k ^ 2 + s ^ 2 = 1) (hδ : ⟪k • u + s • e, n⟫ ≠ 0) :
    ∃ X ∈ plane p₀ n, ‖X - V‖ = |⟪p₀ - V, n⟫ / ⟪k • u + s • e, n⟫| ∧
      (0 ≤ ⟪p₀ - V, n⟫ / ⟪k • u + s • e, n⟫ → X ∈ cone V u k) ∧
      (⟪p₀ - V, n⟫ / ⟪k • u + s • e, n⟫ ≤ 0 → X ∈ cone V (-u) k) := by
  obtain ⟨hw, hwu⟩ := gen_dir hu he heu hks
  exact ⟨_, gen_mem_plane hδ, gen_norm hw, fun h => gen_mem_cone hw hwu h,
    fun h => gen_mem_cone_neg hw hwu h⟩

/--
@isnad1 id=mem.2h6v.s6.8944e953832d from=translated src=- shape=1935b0e6 vocab=a5d3c7bf
-/
theorem mem_cone2_of_le_total {V u X : E} {k t : ℝ} (h1 : 0 ≤ t → X ∈ cone V u k)
    (h2 : t ≤ 0 → X ∈ cone V (-u) k) : X ∈ cone2 V u k := by
  rcases le_total 0 t with h | h
  · exact mem_cone2_iff.2 (Or.inl (h1 h))
  · exact mem_cone2_iff.2 (Or.inr (h2 h))

/-! ## Which nappe: the sign of `⟪u, n⟫ ⟪p₀ - V, n⟫` -/

/-- If `sin α ≤ |⟪u, n⟫|` and the plane misses the apex, a point of the section on the upper nappe
forces `0 < ⟪u, n⟫ ⟪p₀ - V, n⟫`.
@isnad1 id=lt.8h8v.s8.ad7b3cb448e2 from=translated src=- shape=a04c1de0 vocab=39648d09
-/
theorem nappe_sign {V u n p₀ X : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hm : s ^ 2 ≤ ⟪u, n⟫ ^ 2)
    (hc : ⟪p₀ - V, n⟫ ≠ 0) (hX : X ∈ plane p₀ n) (hXc : X ∈ cone V u k) :
    0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫ := by
  have g := gram_ineq (w := X - V) hu hn hXc
  rw [inner_sub_V_of_mem_plane hX] at g
  have hL := norm_nonneg (X - V)
  have hc2 : 0 < ⟪p₀ - V, n⟫ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hc))
  by_contra h'
  have h := not_lt.1 h'
  have h1 : 1 - k ^ 2 = s ^ 2 := by linarith
  rw [h1] at g
  nlinarith [mul_nonneg (mul_nonneg hk.le hL) (neg_nonneg.2 h),
    mul_nonneg (sub_nonneg.2 hm) (sq_nonneg ‖X - V‖)]

/-- Same on the lower nappe: `⟪u, n⟫ ⟪p₀ - V, n⟫ < 0`.
@isnad1 id=lt.8h8v.s8.2629c7305d6e from=translated src=- shape=a7618bf3 vocab=395bb814
-/
theorem nappe_sign_neg {V u n p₀ X : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hm : s ^ 2 ≤ ⟪u, n⟫ ^ 2)
    (hc : ⟪p₀ - V, n⟫ ≠ 0) (hX : X ∈ plane p₀ n) (hXc : X ∈ cone V (-u) k) :
    ⟪u, n⟫ * ⟪p₀ - V, n⟫ < 0 := by
  have h := nappe_sign (u := -u) (by rw [norm_neg, hu]) hn hks hk
    (by rw [inner_neg_left, neg_sq]; exact hm) hc hX hXc
  rw [inner_neg_left] at h
  linarith

/-- **Meeting both nappes forces the hyperbola inequality** `|⟪u, n⟫| < sin α` (any `E`).
@isnad1 id=lt.10h9v.s8.48d543b752fd from=translated src=- shape=078e4b69 vocab=11e2c52a
-/
theorem abs_lt_of_both_nappes {V u n p₀ X Y : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hc : ⟪p₀ - V, n⟫ ≠ 0)
    (hX : X ∈ plane p₀ n) (hXc : X ∈ cone V u k) (hY : Y ∈ plane p₀ n)
    (hYc : Y ∈ cone V (-u) k) : |⟪u, n⟫| < s := by
  by_contra h'
  have h := not_lt.1 h'
  have hm : s ^ 2 ≤ ⟪u, n⟫ ^ 2 := by nlinarith [sq_abs ⟪u, n⟫, abs_nonneg ⟪u, n⟫]
  linarith [nappe_sign hu hn hks hk hm hc hX hXc, nappe_sign_neg hu hn hks hk hm hc hY hYc]

/-- A point on the generator of direction `k u + s e`, with `e = (a / ‖q‖) q + b f`
(`q = perpN u n`, `f ⟂ u, n`). The parameter is `c / (k m + s a ‖q‖)`.
@isnad1 id=ex.8h10v.s9.5b21a88e9f40 from=translated src=- shape=f7e42f55 vocab=b21fde4f
-/
theorem gen_point_a {V u n p₀ f : E} {k s a b : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hr : ‖perpN u n‖ ≠ 0) (hfu : ⟪f, u⟫ = 0) (hfn : ⟪f, n⟫ = 0)
    (hab : a ^ 2 + b ^ 2 * ‖f‖ ^ 2 = 1) (hδ : k * ⟪u, n⟫ + s * (a * ‖perpN u n‖) ≠ 0) :
    ∃ X ∈ plane p₀ n,
      ‖X - V‖ = |⟪p₀ - V, n⟫ / (k * ⟪u, n⟫ + s * (a * ‖perpN u n‖))| ∧
      (0 ≤ ⟪p₀ - V, n⟫ / (k * ⟪u, n⟫ + s * (a * ‖perpN u n‖)) → X ∈ cone V u k) ∧
      (⟪p₀ - V, n⟫ / (k * ⟪u, n⟫ + s * (a * ‖perpN u n‖)) ≤ 0 → X ∈ cone V (-u) k) := by
  obtain ⟨h1, h2, h3⟩ := perp_dir (a := a) (b := b) hu hn hr hfu hfn hab
  have hδ' : ⟪k • u + s • ((a / ‖perpN u n‖) • perpN u n + b • f), n⟫ =
      k * ⟪u, n⟫ + s * (a * ‖perpN u n‖) := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, h3]
  have h := gen_point (V := V) (p₀ := p₀) hu h1 h2 hks (by rw [hδ']; exact hδ)
  rw [hδ'] at h
  exact h

/-! ## (1) Non-emptiness -/

/-- **Hyperbola regime: the plane meets both nappes** (any real inner product space `E`).
Under `|⟪u, n⟫| < sin α` and `⟪p₀ - V, n⟫ ≠ 0` there are explicit points of the section on
`cone V u k` and on `cone V (-u) k`: the generators of direction `k u ± s q / ‖q‖`,
`q = n - ⟪u, n⟫ u`, meet the plane at parameters of opposite signs.
@isnad1 id=and.7h7v.s8.066239c376ca from=translated src=- shape=b0c299c8 vocab=11e2c52a
-/
theorem hyp_both_nappes {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (_hk : 0 < k) (hs : 0 < s) (hm : |⟪u, n⟫| < s)
    (hc : ⟪p₀ - V, n⟫ ≠ 0) :
    (∃ X ∈ plane p₀ n, X ∈ cone V u k) ∧ (∃ Y ∈ plane p₀ n, Y ∈ cone V (-u) k) := by
  have hq2 := perpN_norm_sq (u := u) (n := n) hu hn
  have hm2 : ⟪u, n⟫ ^ 2 < s ^ 2 := by
    nlinarith [sq_abs ⟪u, n⟫, abs_nonneg ⟪u, n⟫,
      mul_pos (sub_pos.2 hm) (show 0 < s + |⟪u, n⟫| by linarith [abs_nonneg ⟪u, n⟫])]
  have hr0 : 0 < ‖perpN u n‖ := by
    rcases (norm_nonneg (perpN u n)).eq_or_lt with h | h
    · rw [← h] at hq2; nlinarith
    · exact h
  have hkm : |k * ⟪u, n⟫| < s * ‖perpN u n‖ := by
    apply abs_lt_of_sq_lt_sq _ (mul_pos hs hr0).le
    rw [mul_pow, mul_pow, hq2, show k ^ 2 = 1 - s ^ 2 by linarith]
    nlinarith
  obtain ⟨hk1, hk2⟩ := abs_lt.1 hkm
  have h0 : ⟪(0 : E), u⟫ = 0 := inner_zero_left _
  have h0' : ⟪(0 : E), n⟫ = 0 := inner_zero_left _
  have dp : 0 < k * ⟪u, n⟫ + s * (1 * ‖perpN u n‖) := by linarith
  have dn : k * ⟪u, n⟫ + s * (-1 * ‖perpN u n‖) < 0 := by linarith
  obtain ⟨X, hX, -, hX1, hX2⟩ := gen_point_a (V := V) (p₀ := p₀) (a := 1) (b := 0) hu hn hks
    hr0.ne' h0 h0' (by norm_num) dp.ne'
  obtain ⟨Y, hY, -, hY1, hY2⟩ := gen_point_a (V := V) (p₀ := p₀) (a := -1) (b := 0) hu hn hks
    hr0.ne' h0 h0' (by norm_num) dn.ne
  rcases lt_or_gt_of_ne hc with h | h
  · exact ⟨⟨Y, hY, hY1 (div_pos_of_neg_of_neg h dn).le⟩,
      ⟨X, hX, hX2 (div_neg_of_neg_of_pos h dp).le⟩⟩
  · exact ⟨⟨X, hX, hX1 (div_pos h dp).le⟩, ⟨Y, hY, hY2 (div_neg_of_pos_of_neg h dn).le⟩⟩

/-- **Ellipse regime: the section is non-empty** (`E` finite-dimensional, `finrank ≥ 2`).
With the hypotheses of `dandelin_exists`, every generator of direction `k u + s e`
(`e ⟂ u` a unit vector) meets the plane on the nappe `cone V u k`.
@isnad1 id=ex.8h7v.s8.f203610668bb from=translated src=- shape=fb4d4789 vocab=c5032eb3
-/
theorem ellipse_nonempty [FiniteDimensional ℝ E] (hdim : 2 ≤ Module.finrank ℝ E)
    {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : s < |⟪u, n⟫|)
    (hc : 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫) : ∃ X ∈ plane p₀ n, X ∈ cone V u k := by
  obtain ⟨e, he, heS⟩ := exists_unit_orth ({u} : Finset E)
    (by rw [Finset.card_singleton]; omega)
  have heu : ⟪e, u⟫ = 0 := heS u (Finset.mem_singleton_self u)
  have hen : ⟪e, n⟫ = ⟪e, perpN u n⟫ := by
    unfold perpN; rw [inner_sub_right, real_inner_smul_right, heu, mul_zero, sub_zero]
  have hcs : |⟪e, n⟫| ≤ ‖perpN u n‖ := by
    rw [hen]
    have := abs_real_inner_le_norm e (perpN u n)
    rwa [he, one_mul] at this
  have hq2 := perpN_norm_sq (u := u) (n := n) hu hn
  have ha0 : 0 < |⟪u, n⟫| := hs.trans hm
  have hm2 : s ^ 2 < ⟪u, n⟫ ^ 2 := by
    nlinarith [sq_abs ⟪u, n⟫, mul_pos (sub_pos.2 hm) (show 0 < |⟪u, n⟫| + s by linarith)]
  have hsr : s * ‖perpN u n‖ < k * |⟪u, n⟫| := by
    have h := abs_lt_of_sq_lt_sq (a := s * ‖perpN u n‖) (b := k * |⟪u, n⟫|)
      (by rw [mul_pow, mul_pow, hq2, sq_abs, show k ^ 2 = 1 - s ^ 2 by linarith]; nlinarith)
      (mul_pos hk ha0).le
    exact lt_of_le_of_lt (le_abs_self _) h
  have h1 : -(|⟪u, n⟫| * ‖perpN u n‖) ≤ ⟪u, n⟫ * ⟪e, n⟫ := by
    have h := neg_abs_le (⟪u, n⟫ * ⟪e, n⟫)
    rw [abs_mul] at h
    nlinarith [mul_le_mul_of_nonneg_left hcs (abs_nonneg ⟪u, n⟫)]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ⟪k • u + s • e, n⟫ := ⟨_, rfl⟩
  have hδ' : δ = k * ⟪u, n⟫ + s * ⟪e, n⟫ := by
    rw [hδ, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hmd : 0 < ⟪u, n⟫ * δ := by
    rw [hδ']
    nlinarith [mul_pos ha0 (sub_pos.2 hsr), sq_abs ⟪u, n⟫, mul_le_mul_of_nonneg_left h1 hs.le]
  have hδ0 : δ ≠ 0 := by rintro rfl; rw [mul_zero] at hmd; exact lt_irrefl 0 hmd
  have hcd : 0 < ⟪p₀ - V, n⟫ * δ := by
    have e2 : ⟪u, n⟫ ^ 2 * (⟪p₀ - V, n⟫ * δ) = (⟪u, n⟫ * ⟪p₀ - V, n⟫) * (⟪u, n⟫ * δ) := by
      ring
    have := mul_pos hc hmd
    rw [← e2] at this
    exact pos_of_mul_pos_right this (sq_nonneg _)
  have ht : 0 ≤ ⟪p₀ - V, n⟫ / δ := by
    rcases lt_or_gt_of_ne hδ0 with h | h
    · exact (div_pos_of_neg_of_neg (by nlinarith) h).le
    · exact (div_pos (by nlinarith) h).le
  obtain ⟨X, hX, -, hX1, -⟩ := gen_point (V := V) (p₀ := p₀) hu he heu hks
    (by rw [← hδ]; exact hδ0)
  rw [← hδ] at hX1
  exact ⟨X, hX, hX1 ht⟩

/-! ## (2) The regime characterisation -/

/-- Real lemma: choice of a small nonzero `ε` near `x` (`|x| ≤ ρ`) with `|c / ε|` large.
@isnad1 id=ex.3h4v.s6.f98cfdcf6ba3 from=translated src=- shape=ad318ed4 vocab=2c477979
-/
theorem exists_small_eps {x ρ c R : ℝ} (hρ : 0 < ρ) (hx : |x| ≤ ρ) (hc : c ≠ 0) :
    ∃ ε : ℝ, ε ≠ 0 ∧ |ε - x| ≤ ρ ∧ R < |c / ε| := by
  have hc' : 0 < |c| := abs_pos.2 hc
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = |R| + |c| / ρ + 1 := ⟨_, rfl⟩
  have hcρ : ρ * (|c| / ρ) = |c| := mul_div_cancel₀ _ hρ.ne'
  have hcρ' : 0 < |c| / ρ := div_pos hc' hρ
  have hD0 : 0 < D := by rw [hD]; linarith [abs_nonneg R]
  have hη : 0 < |c| / D := div_pos hc' hD0
  have hηρ : |c| / D ≤ ρ := by
    rw [div_le_iff₀ hD0, hD]
    nlinarith [mul_nonneg hρ.le (abs_nonneg R)]
  have hval : ∀ ε : ℝ, |ε| = |c| / D → |c / ε| = D := by
    intro ε hε; rw [abs_div, hε, div_div_cancel₀ hc'.ne']
  have hRD : R < D := by rw [hD]; linarith [le_abs_self R]
  obtain ⟨hx1, hx2⟩ := abs_le.1 hx
  rcases le_total 0 x with h | h
  · refine ⟨|c| / D, hη.ne', abs_le.2 ⟨by linarith, by linarith⟩, ?_⟩
    rw [hval _ (abs_of_pos hη)]; exact hRD
  · refine ⟨-(|c| / D), neg_ne_zero.2 hη.ne', abs_le.2 ⟨by linarith, by linarith⟩, ?_⟩
    rw [hval _ (by rw [abs_neg, abs_of_pos hη])]; exact hRD

/-- **Failure of the ellipse inequality gives an unbounded section** (`finrank E ≥ 3`).
If `|⟪u, n⟫| ≤ sin α` (parabola or hyperbola regime) and the plane misses the apex, the
section `plane ∩ cone2` has points arbitrarily far from the apex.
@isnad1 id=ex.8h8v.s8.75603564726c from=translated src=- shape=ee2c63e2 vocab=5bb020c3
-/
theorem section_unbounded [FiniteDimensional ℝ E] (hdim : 3 ≤ Module.finrank ℝ E)
    {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : |⟪u, n⟫| ≤ s)
    (hc : ⟪p₀ - V, n⟫ ≠ 0) (R : ℝ) :
    ∃ X ∈ plane p₀ n, X ∈ cone2 V u k ∧ R < ‖X - V‖ := by
  classical
  obtain ⟨f, hf, hfS⟩ := exists_unit_orth ({u, n} : Finset E)
    (lt_of_le_of_lt Finset.card_le_two (by omega : 2 < Module.finrank ℝ E))
  have hfu : ⟪f, u⟫ = 0 := hfS u (by simp)
  have hfn : ⟪f, n⟫ = 0 := hfS n (by simp)
  have hq2 := perpN_norm_sq (u := u) (n := n) hu hn
  have hm2 : ⟪u, n⟫ ^ 2 ≤ s ^ 2 := by
    nlinarith [sq_abs ⟪u, n⟫, abs_nonneg ⟪u, n⟫,
      mul_nonneg (sub_nonneg.2 hm) (show 0 ≤ s + |⟪u, n⟫| by linarith [abs_nonneg ⟪u, n⟫])]
  have hr0 : 0 < ‖perpN u n‖ := by
    rcases (norm_nonneg (perpN u n)).eq_or_lt with h | h
    · rw [← h] at hq2; nlinarith [mul_pos hk hk]
    · exact h
  have hsr : 0 < s * ‖perpN u n‖ := mul_pos hs hr0
  have hkm : |k * ⟪u, n⟫| ≤ s * ‖perpN u n‖ := by
    apply abs_le_of_sq_le_sq _ hsr.le
    rw [mul_pow, mul_pow, hq2, show k ^ 2 = 1 - s ^ 2 by linarith]
    nlinarith
  obtain ⟨ε, hε0, hε, hεR⟩ := exists_small_eps (R := R) hsr hkm hc
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (ε - k * ⟪u, n⟫) / (s * ‖perpN u n‖) := ⟨_, rfl⟩
  have ha1 : |a| ≤ 1 := by
    rw [ha, abs_div, abs_of_pos hsr, div_le_one₀ hsr]; exact hε
  have ha2 : 0 ≤ 1 - a ^ 2 := by
    nlinarith [sq_abs a, abs_nonneg a,
      mul_nonneg (sub_nonneg.2 ha1) (show 0 ≤ 1 + |a| by linarith [abs_nonneg a])]
  have hab : a ^ 2 + Real.sqrt (1 - a ^ 2) ^ 2 * ‖f‖ ^ 2 = 1 := by
    rw [Real.sq_sqrt ha2, hf]; ring
  have hδ : k * ⟪u, n⟫ + s * (a * ‖perpN u n‖) = ε := by
    have : a * (s * ‖perpN u n‖) = ε - k * ⟪u, n⟫ := by
      rw [ha]; exact div_mul_cancel₀ _ hsr.ne'
    linear_combination this
  obtain ⟨X, hX, hXn, hX1, hX2⟩ := gen_point_a (V := V) (p₀ := p₀) (a := a)
    (b := Real.sqrt (1 - a ^ 2)) hu hn hks hr0.ne' hfu hfn hab (by rw [hδ]; exact hε0)
  rw [hδ] at hXn hX1 hX2
  exact ⟨X, hX, mem_cone2_of_le_total hX1 hX2, by rw [hXn]; exact hεR⟩

/-- **`sin α ≤ |⟪u, n⟫|` ⇒ the section of the double cone lies in one nappe** (any `E`),
namely `cone V u k` if `0 < ⟪u, n⟫ ⟪p₀ - V, n⟫` and `cone V (-u) k` otherwise.
@isnad1 id=or.7h7v.s8.af177eb8b2c1 from=translated src=- shape=582578ac vocab=df1466fc
-/
theorem one_nappe {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : s ≤ |⟪u, n⟫|)
    (hc : ⟪p₀ - V, n⟫ ≠ 0) :
    (0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫ ∧ ∀ X ∈ plane p₀ n, X ∈ cone2 V u k → X ∈ cone V u k) ∨
      (⟪u, n⟫ * ⟪p₀ - V, n⟫ < 0 ∧ ∀ X ∈ plane p₀ n, X ∈ cone2 V u k → X ∈ cone V (-u) k) := by
  have hm2 : s ^ 2 ≤ ⟪u, n⟫ ^ 2 := by
    nlinarith [sq_abs ⟪u, n⟫, mul_nonneg (sub_nonneg.2 hm) (show 0 ≤ |⟪u, n⟫| + s by linarith)]
  have hm0 : ⟪u, n⟫ ≠ 0 := by intro h; rw [h, abs_zero] at hm; linarith
  rcases lt_or_gt_of_ne (mul_ne_zero hm0 hc) with h | h
  · refine Or.inr ⟨h, fun X hX hX2 => ?_⟩
    rcases mem_cone2_iff.1 hX2 with h' | h'
    · exact absurd (nappe_sign hu hn hks hk hm2 hc hX h') (not_lt.2 h.le)
    · exact h'
  · refine Or.inl ⟨h, fun X hX hX2 => ?_⟩
    rcases mem_cone2_iff.1 hX2 with h' | h'
    · exact h'
    · exact absurd (nappe_sign_neg hu hn hks hk hm2 hc hX h') (not_lt.2 h.le)

/-- **Ellipse inequality ⇒ one nappe and bounded** (any `E`).
@isnad1 id=and.7h7v.s8.473391bbbe70 from=translated src=- shape=e341acd4 vocab=6b72649e
-/
theorem ellipse_regime {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : s < |⟪u, n⟫|)
    (hc : ⟪p₀ - V, n⟫ ≠ 0) :
    ((∀ X ∈ plane p₀ n, X ∈ cone2 V u k → X ∈ cone V u k) ∨
      (∀ X ∈ plane p₀ n, X ∈ cone2 V u k → X ∈ cone V (-u) k)) ∧
    ∃ R : ℝ, ∀ X ∈ plane p₀ n, X ∈ cone2 V u k → ‖X - V‖ ≤ R := by
  rcases one_nappe hu hn hks hk hs hm.le hc with ⟨h, hsec⟩ | ⟨h, hsec⟩
  · obtain ⟨R, hR⟩ := section_bounded (V := V) (p₀ := p₀) hu hn hks hk hs hm h
    exact ⟨Or.inl hsec, R, fun X hX hX2 => hR X hX (hsec X hX hX2)⟩
  · obtain ⟨R, hR⟩ := section_bounded (V := V) (p₀ := p₀) (u := -u) (by rw [norm_neg, hu]) hn
      hks hk hs (by rw [inner_neg_left, abs_neg]; exact hm)
      (by rw [inner_neg_left, neg_mul]; linarith)
    exact ⟨Or.inr hsec, R, fun X hX hX2 => hR X hX (hsec X hX hX2)⟩

/-- **Bounded ⇔ ellipse inequality** (`finrank E ≥ 3`, plane not through the apex).
@isnad1 id=iff.7h7v.s8.5244ebcc9640 from=translated src=- shape=cdf99a65 vocab=a5f0d408
-/
theorem bounded_iff [FiniteDimensional ℝ E] (hdim : 3 ≤ Module.finrank ℝ E)
    {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hc : ⟪p₀ - V, n⟫ ≠ 0) :
    s < |⟪u, n⟫| ↔ Bornology.IsBounded (plane p₀ n ∩ cone2 V u k) := by
  constructor
  · intro hm
    obtain ⟨-, R, hR⟩ := ellipse_regime hu hn hks hk hs hm hc
    rw [Metric.isBounded_iff_subset_closedBall V]
    exact ⟨R, fun X hX => by rw [Metric.mem_closedBall, dist_eq_norm]; exact hR X hX.1 hX.2⟩
  · intro hb
    by_contra h'
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall V).1 hb
    obtain ⟨X, hX, hX2, hXR⟩ := section_unbounded hdim hu hn hks hk hs (not_lt.1 h') hc R
    have h := hR ⟨hX, hX2⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    linarith

/-- **Regime characterisation, ellipse** (`finrank E ≥ 3`, plane not through the apex):
`sin α < |⟪u, n⟫|` iff the section of the double cone lies in one nappe and is bounded.
@isnad1 id=iff.7h7v.s8.02329954b153 from=translated src=- shape=0a86ff9e vocab=2bfa14de
-/
theorem ellipse_regime_iff [FiniteDimensional ℝ E] (hdim : 3 ≤ Module.finrank ℝ E)
    {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hc : ⟪p₀ - V, n⟫ ≠ 0) :
    s < |⟪u, n⟫| ↔
      ((∀ X ∈ plane p₀ n, X ∈ cone2 V u k → X ∈ cone V u k) ∨
        (∀ X ∈ plane p₀ n, X ∈ cone2 V u k → X ∈ cone V (-u) k)) ∧
      Bornology.IsBounded (plane p₀ n ∩ cone2 V u k) := by
  constructor
  · intro hm
    exact ⟨(ellipse_regime hu hn hks hk hs hm hc).1,
      (bounded_iff hdim hu hn hks hk hs hc).1 hm⟩
  · rintro ⟨-, hb⟩
    exact (bounded_iff hdim hu hn hks hk hs hc).2 hb

/-- **Regime characterisation, hyperbola** (any `E`, plane not through the apex):
`|⟪u, n⟫| < sin α` iff the plane meets both nappes.
@isnad1 id=iff.6h7v.s8.61ccf1fc2a2e from=translated src=- shape=8ad24845 vocab=11e2c52a
-/
theorem hyperbola_regime_iff {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hc : ⟪p₀ - V, n⟫ ≠ 0) :
    |⟪u, n⟫| < s ↔
      (∃ X ∈ plane p₀ n, X ∈ cone V u k) ∧ (∃ Y ∈ plane p₀ n, Y ∈ cone V (-u) k) :=
  ⟨fun hm => hyp_both_nappes hu hn hks hk hs hm hc,
    fun ⟨⟨_, hX, hXc⟩, ⟨_, hY, hYc⟩⟩ => abs_lt_of_both_nappes hu hn hks hk hs hc hX hXc hY hYc⟩

/-- **Parabola regime** (`finrank E ≥ 3`): if `|⟪u, n⟫| = sin α` and the plane misses the
apex, the section lies in one nappe and is unbounded.
@isnad1 id=and.8h7v.s8.23c70c666f70 from=translated src=- shape=d3765065 vocab=2bfa14de
-/
theorem parabola_regime [FiniteDimensional ℝ E] (hdim : 3 ≤ Module.finrank ℝ E)
    {V u n p₀ : E} {k s : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s) (hm : |⟪u, n⟫| = s)
    (hc : ⟪p₀ - V, n⟫ ≠ 0) :
    ((∀ X ∈ plane p₀ n, X ∈ cone2 V u k → X ∈ cone V u k) ∨
      (∀ X ∈ plane p₀ n, X ∈ cone2 V u k → X ∈ cone V (-u) k)) ∧
    ¬ Bornology.IsBounded (plane p₀ n ∩ cone2 V u k) := by
  refine ⟨?_, fun hb => ?_⟩
  · rcases one_nappe hu hn hks hk hs hm.ge hc with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · have := (bounded_iff hdim hu hn hks hk hs hc).2 hb
    rw [hm] at this
    exact lt_irrefl s this

/-! ## In `ℝ³` -/

/--
@isnad1 id=le.0h0v.s7.90986cb84415 from=translated src=- shape=2361627e vocab=03b458d5
-/
theorem finrank_R3 : 3 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
  le_of_eq finrank_euclideanSpace_fin.symm

/-- **The regime trichotomy in `EuclideanSpace ℝ (Fin 3)`**, for a plane not through the apex:
ellipse `sin α < |⟪u, n⟫|` ⇔ one nappe and bounded; hyperbola `|⟪u, n⟫| < sin α` ⇔ both
nappes met; in the ellipse case with the orientation of `dandelin_exists` the section is
non-empty.
@isnad1 id=and.6h6v.s11.8f6a35da29e7 from=translated src=- shape=35d3d447 vocab=a7bdf597
-/
theorem regime_R3 {V u n p₀ : EuclideanSpace ℝ (Fin 3)} {k s : ℝ} (hu : ‖u‖ = 1)
    (hn : ‖n‖ = 1) (hks : k ^ 2 + s ^ 2 = 1) (hk : 0 < k) (hs : 0 < s)
    (hc : ⟪p₀ - V, n⟫ ≠ 0) :
    (s < |⟪u, n⟫| ↔
      ((∀ X ∈ plane p₀ n, X ∈ cone2 V u k → X ∈ cone V u k) ∨
        (∀ X ∈ plane p₀ n, X ∈ cone2 V u k → X ∈ cone V (-u) k)) ∧
      Bornology.IsBounded (plane p₀ n ∩ cone2 V u k)) ∧
    (|⟪u, n⟫| < s ↔
      (∃ X ∈ plane p₀ n, X ∈ cone V u k) ∧ (∃ Y ∈ plane p₀ n, Y ∈ cone V (-u) k)) ∧
    (s < |⟪u, n⟫| → 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫ → ∃ X ∈ plane p₀ n, X ∈ cone V u k) :=
  ⟨ellipse_regime_iff finrank_R3 hu hn hks hk hs hc, hyperbola_regime_iff hu hn hks hk hs hc,
    fun hm hmc => ellipse_nonempty (by have := finrank_R3; omega) hu hn hks hk hs hm hmc⟩

end Dandelin
