import Tengoku.Dandelin.Dandelin.Bridge
import Tengoku.Dandelin.Dandelin.Degenerate
import Tengoku.Dandelin.Dandelin.Regime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Layer 14: Mathlib-only restatements and witnesses

The statements below mention only Mathlib notions. The cone with apex `V`, unit axis `u` and
half-angle `α` is described by its defining property, `X = V ∨ angle (X - V) u = α` (one nappe) or
`X = V ∨ angle (X - V) u = α ∨ angle (X - V) u = π - α` (double cone), using
`InnerProductGeometry.angle`. The cutting plane is the Mathlib affine subspace
`AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ`. Spheres are `EuclideanGeometry.Sphere`s and tangency is
Mathlib's `Sphere.IsTangentAt` / `Sphere.IsTangent`. Witnesses live in
`EuclideanSpace ℝ (Fin 3)` with the cone of half-angle `arccos (4/5)`.
-/

open RealInnerProductSpace InnerProductGeometry

namespace Dandelin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Bridges -/

/--
@isnad1 id=iff.2h5v.s6.62921fa623a5 from=translated src=- shape=5bb3bd35 vocab=85027b08
-/
theorem l14_mem_cone_iff {V u X : E} {α : ℝ} (hu : ‖u‖ = 1) (hα : α ∈ Set.Icc 0 Real.pi) :
    (X = V ∨ angle (X - V) u = α) ↔ X ∈ cone V u (Real.cos α) := by
  rcases eq_or_ne X V with rfl | hX
  · simp only [true_or, true_iff]
    show ⟪X - X, u⟫ = Real.cos α * ‖X - X‖
    simp
  · rw [← mem_cone_iff_angle hu hα hX]; simp [hX]

/--
@isnad1 id=iff.2h5v.s7.1d1a9683d449 from=translated src=- shape=0192cf66 vocab=e4560b62
-/
theorem l14_mem_cone2_iff {V u X : E} {α : ℝ} (hu : ‖u‖ = 1) (hα : α ∈ Set.Icc 0 Real.pi) :
    (X = V ∨ angle (X - V) u = α ∨ angle (X - V) u = Real.pi - α) ↔
      X ∈ cone2 V u (Real.cos α) := by
  rcases eq_or_ne X V with rfl | hX
  · simp only [true_or, true_iff]
    show ⟪X - X, u⟫ ^ 2 = Real.cos α ^ 2 * ‖X - X‖ ^ 2
    simp
  · rw [← mem_cone2_iff_angle hu hα hX]; simp [hX]

/--
@isnad1 id=iff.0h4v.s8.30ff7dae226e from=translated src=- shape=1254a320 vocab=208af509
-/
theorem l14_mem_plane_iff {p₀ n X : E} :
    X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ ↔ X ∈ plane p₀ n := by
  rw [plane_eq_mk', SetLike.mem_coe]

/-- A Mathlib tangency point of a sphere and the plane `mk' p₀ (ℝ ∙ n)ᗮ` is the projection of
the centre, and the radius is the distance from the centre to the plane.
@isnad1 id=and.2h6v.s8.583c52e765fd from=translated src=- shape=38a03545 vocab=a84650c2
-/
theorem l14_isTangentAt_plane {p₀ n C F : E} {r : ℝ} (hn : ‖n‖ = 1)
    (h : (⟨C, r⟩ : EuclideanGeometry.Sphere E).IsTangentAt F (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ)) :
    F = C - ⟪C - p₀, n⟫ • n ∧ |⟪C - p₀, n⟫| = r := by
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hFπ : ⟪F - p₀, n⟫ = 0 := l14_mem_plane_iff.1 h.mem_space
  have hFS : ‖F - C‖ = r := by
    have := h.mem_sphere
    rwa [EuclideanGeometry.mem_sphere, dist_eq_norm] at this
  set w := (F - C) - ⟪F - C, n⟫ • n with hw
  have hwn : ⟪w, n⟫ = 0 := by
    rw [hw, inner_sub_left, real_inner_smul_left, hnn, mul_one, sub_self]
  have hx : F + w ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ := by
    rw [l14_mem_plane_iff]
    show ⟪F + w - p₀, n⟫ = 0
    rw [show F + w - p₀ = (F - p₀) + w by abel, inner_add_left, hFπ, hwn, add_zero]
  have hperp := h.le_orthRadius hx
  rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left, vsub_eq_sub, vsub_eq_sub,
    show F + w - F = w by abel] at hperp
  have hww : ⟪w, w⟫ = 0 := by
    conv_lhs => rw [hw]
    rw [inner_sub_right, real_inner_smul_right, hwn, mul_zero, sub_zero]
    exact hperp
  have hw0 : w = 0 := inner_self_eq_zero.1 hww
  have hFC : ⟪F - C, n⟫ = -⟪C - p₀, n⟫ := by
    rw [show F - C = (F - p₀) - (C - p₀) by abel, inner_sub_left, hFπ, zero_sub]
  have e : F - C = ⟪F - C, n⟫ • n := by rw [← sub_eq_zero, ← hw, hw0]
  refine ⟨?_, ?_⟩
  · rw [hFC, neg_smul] at e
    rw [sub_eq_iff_eq_add'] at e
    rw [e, ← sub_eq_add_neg]
  · rw [← hFS, e, norm_smul, hn, mul_one, Real.norm_eq_abs, hFC, abs_neg]

/-- Conversely, if the centre is at distance `r` from the plane, the sphere touches the plane
(in Mathlib's sense) at the projection of the centre.
@isnad1 id=istangen.2h5v.s8.f7352d3fc290 from=translated src=- shape=65241aee vocab=a84650c2
-/
theorem l14_isTangentAt_proj {p₀ n C : E} {r : ℝ} (hn : ‖n‖ = 1) (hr : |⟪C - p₀, n⟫| = r) :
    (⟨C, r⟩ : EuclideanGeometry.Sphere E).IsTangentAt (C - ⟪C - p₀, n⟫ • n)
      (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) := by
  have hF := proj_mem_plane (C := C) (p₀ := p₀) hn
  refine ⟨?_, l14_mem_plane_iff.2 hF, fun x hx => ?_⟩
  · rw [EuclideanGeometry.mem_sphere, dist_eq_norm]
    exact (tangent_of_proj hn rfl hr hF hF).1
  · rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left, vsub_eq_sub, vsub_eq_sub]
    exact (tangent_of_proj hn rfl hr (l14_mem_plane_iff.1 hx) hF).2

/--
@isnad1 id=iff.1h5v.s7.d0d4a5f2da6b from=translated src=- shape=3083ce36 vocab=0da91268
-/
theorem l14_isTangent_plane_iff {p₀ n C : E} {r : ℝ} (hn : ‖n‖ = 1) :
    (⟨C, r⟩ : EuclideanGeometry.Sphere E).IsTangent (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ↔
      |⟪C - p₀, n⟫| = r :=
  ⟨fun ⟨_, h⟩ => (l14_isTangentAt_plane hn h).2, fun h => ⟨_, l14_isTangentAt_proj hn h⟩⟩

/-- Two projections of distinct axis points onto a plane not perpendicular to the axis are
distinct.
@isnad1 id=ne.4h7v.s9.77bad9204fed from=translated src=- shape=4a8fb0ef vocab=07c8dff6
-/
theorem l14_proj_ne {V u n p₀ : E} {d₁ d₂ : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hm : ⟪u, n⟫ ^ 2 < 1) (hd : d₁ ≠ d₂) :
    (V + d₁ • u) - ⟪(V + d₁ • u) - p₀, n⟫ • n ≠ (V + d₂ • u) - ⟪(V + d₂ • u) - p₀, n⟫ • n := by
  intro h
  have e : (d₁ - d₂) • (u - ⟪u, n⟫ • n) = 0 := by
    have h' := sub_eq_zero.2 h
    rw [← h']
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, smul_sub, sub_smul,
      add_smul, mul_smul]
    abel
  rcases smul_eq_zero.1 e with h0 | h0
  · exact hd (sub_eq_zero.1 h0)
  · have hu' : u = ⟪u, n⟫ • n := sub_eq_zero.1 h0
    have : ‖u‖ = |⟪u, n⟫| := by
      conv_lhs => rw [hu']
      rw [norm_smul, hn, mul_one, Real.norm_eq_abs]
    rw [hu] at this
    nlinarith [sq_abs ⟪u, n⟫]

/--
@isnad1 id=and.2h1v.s7.f94abceb714a from=translated src=- shape=db68dea7 vocab=0fceae81
-/
theorem l14_cos_sin {α : ℝ} (hα0 : 0 < α) (hα1 : α < Real.pi / 2) :
    Real.cos α ^ 2 + Real.sin α ^ 2 = 1 ∧ 0 < Real.cos α ∧ 0 < Real.sin α ∧
      α ∈ Set.Icc 0 Real.pi := by
  refine ⟨Real.cos_sq_add_sin_sq α, Real.cos_pos_of_mem_Ioo ⟨by linarith, hα1⟩,
    Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos]), ⟨hα0.le, by linarith [Real.pi_pos]⟩⟩

/-- Bridge: the axis plane `⟪Y - V, u⟫ = b` is the Mathlib hyperplane through `V + b • u` normal
to `u`, so `directrix` is the intersection of two Mathlib affine subspaces.
@isnad1 id=eq.1h6v.s9.c617b393a4e7 from=translated src=- shape=d6459057 vocab=faa1ecaf
-/
theorem l14_directrix_eq {V u n p₀ : E} {b : ℝ} (hu : ‖u‖ = 1) :
    directrix V u n p₀ b =
      ((AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ ⊓ AffineSubspace.mk' (V + b • u) (ℝ ∙ u)ᗮ :
        AffineSubspace ℝ E) : Set E) := by
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  ext X
  rw [SetLike.mem_coe, AffineSubspace.mem_inf_iff, l14_mem_plane_iff, AffineSubspace.mem_mk', vsub_eq_sub,
    Submodule.mem_orthogonal_singleton_iff_inner_left]
  show X ∈ plane p₀ n ∧ ⟪X - V, u⟫ = b ↔ _
  rw [show X - (V + b • u) = (X - V) - b • u by abel]
  rw [inner_sub_left (X - V) (b • u), real_inner_smul_left, huu, mul_one, sub_eq_zero]

/-! ## Main theorems, Mathlib-only -/

/-- **Dandelin, ellipse (Mathlib-only form).** Right circular cone with apex `V`, unit axis `u`,
half-angle `α ∈ (0, π/2)`; plane `π` through `p₀` with unit normal `n`, less steep than a
generator (`sin α < |⟪u, n⟫|`) and missing the apex on the side of the nappe. Among the axis
spheres `(V + d • u, d sin α)` exactly two (`0 < d₁ < d₂`) are tangent to `π`, on opposite sides
of it, touching it at `F₁`, `F₂`; and a point of `π` lies on the nappe iff its focal sum is the
constant `L`.
@isnad1 id=ex.6h6v.s10.b402005576e7 from=translated src=- shape=c274b3d9 vocab=a440abee
-/
theorem l14_dandelin_ellipse {V u n p₀ : E} {α : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hα0 : 0 < α) (hα1 : α < Real.pi / 2) (hm : Real.sin α < |⟪u, n⟫|)
    (hc : 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫) :
    ∃ d₁ d₂ : ℝ, ∃ F₁ F₂ : E, ∃ L : ℝ, 0 < d₁ ∧ d₁ < d₂ ∧ 0 < L ∧
      (∀ d : ℝ, (⟨V + d • u, d * Real.sin α⟩ : EuclideanGeometry.Sphere E).IsTangent
          (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ↔ d = d₁ ∨ d = d₂) ∧
      (⟨V + d₁ • u, d₁ * Real.sin α⟩ : EuclideanGeometry.Sphere E).IsTangentAt F₁
        (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ∧
      (⟨V + d₂ • u, d₂ * Real.sin α⟩ : EuclideanGeometry.Sphere E).IsTangentAt F₂
        (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ∧
      ⟪(V + d₁ • u) - p₀, n⟫ * ⟪(V + d₂ • u) - p₀, n⟫ < 0 ∧
      ∀ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ,
        ((X = V ∨ angle (X - V) u = α) ↔ dist X F₁ + dist X F₂ = L) := by
  obtain ⟨hks, hk, hs, hαI⟩ := l14_cos_sin hα0 hα1
  obtain ⟨d₁, d₂, F₁, F₂, hd₁, hd, htan, hopp, -, -, hp₁, hp₂, hsec⟩ :=
    dandelin_exists hu hn hks hk hs hm hc
  refine ⟨d₁, d₂, F₁, F₂, (d₂ - d₁) * Real.cos α, hd₁, hd, mul_pos (by linarith) hk,
    fun d => ?_, ?_, ?_, hopp, fun X hX => ?_⟩
  · rw [l14_isTangent_plane_iff hn]; exact htan d
  · rw [hp₁]; exact l14_isTangentAt_proj hn ((htan d₁).2 (Or.inl rfl))
  · rw [hp₂]; exact l14_isTangentAt_proj hn ((htan d₂).2 (Or.inr rfl))
  · rw [l14_mem_cone_iff hu hαI, dist_eq_norm, dist_eq_norm]
    exact hsec X (l14_mem_plane_iff.1 hX)

/-- **Inscribed spheres (Mathlib-only form).** For `d > 0`, the axis sphere
`(V + d • u, d sin α)` is tangent (Mathlib `IsTangentAt`) to every generator line `VX` of the
nappe, and no point of the nappe lies inside it.
@isnad1 id=and.6h6v.s8.f5679d9c831e from=translated src=- shape=1a9e5a97 vocab=1d2552a1
-/
theorem l14_inscribed {V u X : E} {α d : ℝ} (hu : ‖u‖ = 1) (hα0 : 0 < α)
    (hα1 : α < Real.pi / 2) (hd : 0 < d) (hX : X ≠ V) (hXα : angle (X - V) u = α) :
    (∃ T : E, (⟨V + d • u, d * Real.sin α⟩ : EuclideanGeometry.Sphere E).IsTangentAt T
      line[ℝ, V, X]) ∧ d * Real.sin α ≤ dist X (V + d • u) := by
  obtain ⟨hks, hk, hs, hαI⟩ := l14_cos_sin hα0 hα1
  have hc : X ∈ cone V u (Real.cos α) := (l14_mem_cone_iff hu hαI).1 (Or.inr hXα)
  have hn : ‖X - V‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hX)
  refine ⟨⟨_, isTangentAt_tangencyPoint hu hks (by positivity) hc hn⟩, ?_⟩
  have h := cone_outside_sphere (V := V) (u := u) (X := X) (d := d) hu hks hc
  rw [dist_eq_norm]
  exact le_of_sq_le_sq (by simpa using h) (norm_nonneg _) |> fun h' => by
    simpa [abs_of_pos (mul_pos hd hs)] using h'

/--
@isnad1 id=iff.2h5v.s6.473dc9b4e6a2 from=translated src=- shape=91a3c549 vocab=9c61c1ad
-/
theorem l14_mem_lower_iff {V u X : E} {α : ℝ} (hu : ‖u‖ = 1) (hα : α ∈ Set.Icc 0 Real.pi) :
    (X = V ∨ angle (X - V) u = Real.pi - α) ↔ X ∈ cone V (-u) (Real.cos α) := by
  rw [← l14_mem_cone_iff (by rw [norm_neg, hu]) hα, angle_neg_right]
  constructor <;> rintro (h | h) <;> first | exact Or.inl h | exact Or.inr (by linarith)

/--
@isnad1 id=lt.2h2v.s5.d2c0fcfca136 from=translated src=- shape=b8153e79 vocab=9d62249c
-/
theorem l14_sq_lt_one {m s : ℝ} (hs1 : s < 1) (hm : |m| ≤ s) : m ^ 2 < 1 := by
  have h0 : 0 ≤ |m| := abs_nonneg m
  nlinarith [sq_abs m]

/-- **Dandelin, hyperbola (Mathlib-only form).** If the plane is steeper than a generator
(`|⟪u, n⟫| < sin α`) and misses the apex, exactly two axis spheres `(V + d • u, |d| sin α)` are
tangent to it, one in each nappe (`d₂ < 0 < d₁`), at `F₁`, `F₂`; on the upper nappe
`XF₂ - XF₁ = L`, on the lower nappe `XF₁ - XF₂ = L`, and a point of the plane is on the double
cone iff `|XF₁ - XF₂| = L`. Moreover, with `e = cos β / cos α = √(1 - ⟪u,n⟫²) / cos α > 1`, a
point of the plane is on the double cone iff `XFᵢ = e · dist(X, ℓᵢ)`, where the directrix `ℓᵢ` is
the plane `π` intersected with the hyperplane normal to the axis at `V + dᵢ cos² α • u`.
@isnad1 id=and.6h6v.s11.b89ca0590e6d from=translated src=- shape=c5fd7878 vocab=a7fa0441
-/
theorem l14_dandelin_hyperbola {V u n p₀ : E} {α : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hα0 : 0 < α) (hα1 : α < Real.pi / 2) (hm : |⟪u, n⟫| < Real.sin α)
    (hc : V ∉ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) :
    1 < Real.sqrt (1 - ⟪u, n⟫ ^ 2) / Real.cos α ∧
    ∃ d₁ d₂ : ℝ, ∃ F₁ F₂ : E, ∃ L : ℝ, d₂ < 0 ∧ 0 < d₁ ∧ 0 < L ∧
      (∀ d : ℝ, (⟨V + d • u, |d| * Real.sin α⟩ : EuclideanGeometry.Sphere E).IsTangent
          (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ↔ d = d₁ ∨ d = d₂) ∧
      (⟨V + d₁ • u, |d₁| * Real.sin α⟩ : EuclideanGeometry.Sphere E).IsTangentAt F₁
        (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ∧
      (⟨V + d₂ • u, |d₂| * Real.sin α⟩ : EuclideanGeometry.Sphere E).IsTangentAt F₂
        (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ∧
      (∀ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ, (X = V ∨ angle (X - V) u = α) →
        dist X F₂ - dist X F₁ = L) ∧
      (∀ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ, (X = V ∨ angle (X - V) u = Real.pi - α) →
        dist X F₁ - dist X F₂ = L) ∧
      (∀ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ,
        (X = V ∨ angle (X - V) u = α ∨ angle (X - V) u = Real.pi - α) ↔
          |dist X F₁ - dist X F₂| = L) ∧
      (∀ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ,
        ((X = V ∨ angle (X - V) u = α ∨ angle (X - V) u = Real.pi - α) ↔
          dist X F₁ = Real.sqrt (1 - ⟪u, n⟫ ^ 2) / Real.cos α * Metric.infDist X
            ((AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ ⊓
              AffineSubspace.mk' (V + (d₁ * Real.cos α ^ 2) • u) (ℝ ∙ u)ᗮ :
                AffineSubspace ℝ E) : Set E)) ∧
        ((X = V ∨ angle (X - V) u = α ∨ angle (X - V) u = Real.pi - α) ↔
          dist X F₂ = Real.sqrt (1 - ⟪u, n⟫ ^ 2) / Real.cos α * Metric.infDist X
            ((AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ ⊓
              AffineSubspace.mk' (V + (d₂ * Real.cos α ^ 2) • u) (ℝ ∙ u)ᗮ :
                AffineSubspace ℝ E) : Set E))) := by
  obtain ⟨hks, hk, hs, hαI⟩ := l14_cos_sin hα0 hα1
  have hc' : ⟪p₀ - V, n⟫ ≠ 0 := by
    intro h; apply hc; rw [l14_mem_plane_iff]
    show ⟪V - p₀, n⟫ = 0
    rw [show V - p₀ = -(p₀ - V) by abel, inner_neg_left, h, neg_zero]
  have hs1 : Real.sin α < 1 := by nlinarith
  have hm1 := l14_sq_lt_one hs1 hm.le
  obtain ⟨he, d₁, d₂, F₁, F₂, hd₂, hd₁, htan, -, -, hp₁, hp₂, hup, hlow, hiff, -⟩ :=
    dandelin_hyperbola hu hn hks hk hs hm hc'
  have ht₁ := (htan d₁).2 (Or.inl rfl)
  have ht₂ := (htan d₂).2 (Or.inr rfl)
  refine ⟨he, d₁, d₂, F₁, F₂, (d₁ - d₂) * Real.cos α, hd₂, hd₁, mul_pos (by linarith) hk,
    fun d => ?_, ?_, ?_,
    fun X hX hXc => ?_, fun X hX hXc => ?_, fun X hX => ?_, fun X hX => ⟨?_, ?_⟩⟩
  · rw [l14_isTangent_plane_iff hn]; exact htan d
  · rw [hp₁]; exact l14_isTangentAt_proj hn ht₁
  · rw [hp₂]; exact l14_isTangentAt_proj hn ht₂
  · rw [dist_eq_norm, dist_eq_norm]
    exact hup X (l14_mem_plane_iff.1 hX) ((l14_mem_cone_iff hu hαI).1 hXc)
  · rw [dist_eq_norm, dist_eq_norm]
    exact hlow X (l14_mem_plane_iff.1 hX) ((l14_mem_lower_iff hu hαI).1 hXc)
  · rw [l14_mem_cone2_iff hu hαI, dist_eq_norm, dist_eq_norm]
    exact hiff X (l14_mem_plane_iff.1 hX)
  · obtain ⟨h1, h2⟩ := tangent_of_proj hn hp₁ ht₁ (l14_mem_plane_iff.1 hX)
      (hp₁ ▸ proj_mem_plane hn)
    rw [l14_mem_cone2_iff hu hαI, dist_eq_norm, ← l14_directrix_eq hu]
    exact mem_cone2_iff_focal_directrix hu hn hks hk hm1 (l14_mem_plane_iff.1 hX) h1 h2
  · obtain ⟨h1, h2⟩ := tangent_of_proj hn hp₂ ht₂ (l14_mem_plane_iff.1 hX)
      (hp₂ ▸ proj_mem_plane hn)
    rw [l14_mem_cone2_iff hu hαI, dist_eq_norm, ← l14_directrix_eq hu]
    exact mem_cone2_iff_focal_directrix hu hn hks hk hm1 (l14_mem_plane_iff.1 hX) h1 h2

/-- **Focus–directrix, ellipse (Mathlib-only form).** In the ellipse regime with the plane not
perpendicular to the axis, the eccentricity `e = √(1 - ⟪u,n⟫²)/cos α` is `< 1`, and for each
Dandelin focus `Fᵢ` (tangency point of `(V + dᵢ • u, dᵢ sin α)`), a point of the plane is on the
nappe iff `XFᵢ = e · dist(X, ℓᵢ)`.
@isnad1 id=and.7h6v.s11.a4647972a328 from=translated src=- shape=953f3d81 vocab=07c22f7f
-/
theorem l14_directrix_ellipse {V u n p₀ : E} {α : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hα0 : 0 < α) (hα1 : α < Real.pi / 2) (hm : Real.sin α < |⟪u, n⟫|)
    (hc : 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫) (hm1 : |⟪u, n⟫| < 1) :
    Real.sqrt (1 - ⟪u, n⟫ ^ 2) / Real.cos α < 1 ∧
    ∃ d₁ d₂ : ℝ, ∃ F₁ F₂ : E, 0 < d₁ ∧ d₁ < d₂ ∧
      (⟨V + d₁ • u, d₁ * Real.sin α⟩ : EuclideanGeometry.Sphere E).IsTangentAt F₁
        (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ∧
      (⟨V + d₂ • u, d₂ * Real.sin α⟩ : EuclideanGeometry.Sphere E).IsTangentAt F₂
        (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ∧
      ∀ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ,
        ((X = V ∨ angle (X - V) u = α) ↔
          dist X F₁ = Real.sqrt (1 - ⟪u, n⟫ ^ 2) / Real.cos α * Metric.infDist X
            ((AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ ⊓
              AffineSubspace.mk' (V + (d₁ * Real.cos α ^ 2) • u) (ℝ ∙ u)ᗮ :
                AffineSubspace ℝ E) : Set E)) ∧
        ((X = V ∨ angle (X - V) u = α) ↔
          dist X F₂ = Real.sqrt (1 - ⟪u, n⟫ ^ 2) / Real.cos α * Metric.infDist X
            ((AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ ⊓
              AffineSubspace.mk' (V + (d₂ * Real.cos α ^ 2) • u) (ℝ ∙ u)ᗮ :
                AffineSubspace ℝ E) : Set E)) := by
  obtain ⟨hks, hk, hs, hαI⟩ := l14_cos_sin hα0 hα1
  have hm1' : ⟪u, n⟫ ^ 2 < 1 := by nlinarith [sq_abs ⟪u, n⟫, abs_nonneg ⟪u, n⟫]
  have he := (ecc_lt_one_iff hks hk hs).2 hm
  obtain ⟨d₁, d₂, F₁, F₂, hd₁, hd, htan, -, -, -, hp₁, hp₂, -⟩ :=
    dandelin_exists hu hn hks hk hs hm hc
  have ht₁ := (htan d₁).2 (Or.inl rfl)
  have ht₂ := (htan d₂).2 (Or.inr rfl)
  refine ⟨he, d₁, d₂, F₁, F₂, hd₁, hd, ?_, ?_, fun X hX => ⟨?_, ?_⟩⟩
  · rw [hp₁]; exact l14_isTangentAt_proj hn ht₁
  · rw [hp₂]; exact l14_isTangentAt_proj hn ht₂
  · have hX' := l14_mem_plane_iff.1 hX
    obtain ⟨h1, h2⟩ := tangent_of_proj hn hp₁ ht₁ hX' (hp₁ ▸ proj_mem_plane hn)
    rw [l14_mem_cone_iff hu hαI, dist_eq_norm, ← l14_directrix_eq hu]
    refine ⟨fun hXc => focal_dist_eq_ecc_mul hu hn hks hk hm1' hX' hXc h1 h2, fun h => ?_⟩
    exact directrix_converse_nappe hu hn hks hk hs hm.le hc hm1' hX'
      (by rw [abs_of_pos hd₁]; exact h1) h2 h
  · have hX' := l14_mem_plane_iff.1 hX
    obtain ⟨h1, h2⟩ := tangent_of_proj hn hp₂ ht₂ hX' (hp₂ ▸ proj_mem_plane hn)
    rw [l14_mem_cone_iff hu hαI, dist_eq_norm, ← l14_directrix_eq hu]
    refine ⟨fun hXc => focal_dist_eq_ecc_mul hu hn hks hk hm1' hX' hXc h1 h2, fun h => ?_⟩
    exact directrix_converse_nappe hu hn hks hk hs hm.le hc hm1' hX'
      (by rw [abs_of_pos (hd₁.trans hd)]; exact h1) h2 h

/-- **Parabola (Mathlib-only form).** If the plane is parallel to a generator
(`|⟪u, n⟫| = sin α`) and misses the apex on the side of the nappe, exactly one axis sphere
`(V + d • u, d sin α)` with `d ∈ ℝ` is tangent to it, at `F`, and a point of the plane lies on the
nappe iff `XF = dist(X, ℓ)` (eccentricity `1`).
@isnad1 id=and.6h6v.s10.f75c926e6fdc from=translated src=- shape=cd5cc395 vocab=a7fa0441
-/
theorem l14_parabola {V u n p₀ : E} {α : ℝ} (hu : ‖u‖ = 1) (hn : ‖n‖ = 1)
    (hα0 : 0 < α) (hα1 : α < Real.pi / 2) (hm : |⟪u, n⟫| = Real.sin α)
    (hc : 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫) :
    Real.sqrt (1 - ⟪u, n⟫ ^ 2) / Real.cos α = 1 ∧
    ∃ d : ℝ, ∃ F : E, 0 < d ∧
      (∀ d' : ℝ, (⟨V + d' • u, d' * Real.sin α⟩ : EuclideanGeometry.Sphere E).IsTangent
          (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ↔ d' = d) ∧
      (⟨V + d • u, d * Real.sin α⟩ : EuclideanGeometry.Sphere E).IsTangentAt F
        (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) ∧
      ∀ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ,
        ((X = V ∨ angle (X - V) u = α) ↔
          dist X F = Metric.infDist X
            ((AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ ⊓
              AffineSubspace.mk' (V + (d * Real.cos α ^ 2) • u) (ℝ ∙ u)ᗮ :
                AffineSubspace ℝ E) : Set E)) := by
  obtain ⟨hks, hk, hs, hαI⟩ := l14_cos_sin hα0 hα1
  obtain ⟨he, d, F, hd, htan, -, hFp, hdir⟩ := directrix_parabola hu hn hks hk hs hm.symm hc
  have hm1 : ⟪u, n⟫ ^ 2 < 1 := by rw [← sq_abs, hm]; nlinarith
  have ht := (htan d).2 rfl
  refine ⟨he, d, F, hd, fun d' => ?_, ?_, fun X hX => ?_⟩
  · rw [l14_isTangent_plane_iff hn]; exact htan d'
  · rw [hFp]; exact l14_isTangentAt_proj hn ht
  · have hX' := l14_mem_plane_iff.1 hX
    obtain ⟨h1, h2⟩ := tangent_of_proj hn hFp ht hX' (hFp ▸ proj_mem_plane hn)
    rw [l14_mem_cone_iff hu hαI, dist_eq_norm, ← l14_directrix_eq hu]
    refine ⟨hdir X hX', fun h => ?_⟩
    rw [← one_mul (Metric.infDist _ _), ← he] at h
    exact directrix_converse_nappe hu hn hks hk hs hm.symm.le hc hm1 hX'
      (by rw [abs_of_pos hd]; exact h1) h2 h

/-- The section of the double cone of half-angle `α` by the plane, as a Mathlib-only set.
@isnad1 id=eq.2h6v.s8.eda724b848bb from=translated src=- shape=4e5a0a19 vocab=32bfcee3
-/
theorem l14_section_eq {V u n p₀ : E} {α : ℝ} (hu : ‖u‖ = 1) (hα : α ∈ Set.Icc 0 Real.pi) :
    ((AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ : Set E) ∩
      {X | X = V ∨ angle (X - V) u = α ∨ angle (X - V) u = Real.pi - α}) =
      plane p₀ n ∩ cone2 V u (Real.cos α) := by
  ext X
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, SetLike.mem_coe, l14_mem_plane_iff,
    l14_mem_cone2_iff hu hα]

/-- **Regimes in `ℝ³` (Mathlib-only form).** For a plane missing the apex: `sin α < |⟪u, n⟫|`
iff the section of the double cone lies in one nappe and is bounded; `|⟪u, n⟫| < sin α` iff the
plane meets both nappes; and in the ellipse regime on the side of the upper nappe the section of
that nappe is non-empty.
@isnad1 id=and.5h5v.s14.bed98bce3948 from=translated src=- shape=b32283fd vocab=37eac243
-/
theorem l14_regime_R3 {V u n p₀ : EuclideanSpace ℝ (Fin 3)} {α : ℝ} (hu : ‖u‖ = 1)
    (hn : ‖n‖ = 1) (hα0 : 0 < α) (hα1 : α < Real.pi / 2)
    (hc : V ∉ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) :
    (Real.sin α < |⟪u, n⟫| ↔
      ((∀ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ,
          (X = V ∨ angle (X - V) u = α ∨ angle (X - V) u = Real.pi - α) →
            X = V ∨ angle (X - V) u = α) ∨
        (∀ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ,
          (X = V ∨ angle (X - V) u = α ∨ angle (X - V) u = Real.pi - α) →
            X = V ∨ angle (X - V) u = Real.pi - α)) ∧
      Bornology.IsBounded ((AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ : Set (EuclideanSpace ℝ (Fin 3))) ∩
        {X | X = V ∨ angle (X - V) u = α ∨ angle (X - V) u = Real.pi - α})) ∧
    (|⟪u, n⟫| < Real.sin α ↔
      (∃ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ, angle (X - V) u = α) ∧
        (∃ Y ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ, angle (Y - V) u = Real.pi - α)) ∧
    (Real.sin α < |⟪u, n⟫| → 0 < ⟪u, n⟫ * ⟪p₀ - V, n⟫ →
      ∃ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ, angle (X - V) u = α) := by
  obtain ⟨hks, hk, hs, hαI⟩ := l14_cos_sin hα0 hα1
  have hc' : ⟪p₀ - V, n⟫ ≠ 0 := by
    intro h; apply hc; rw [l14_mem_plane_iff]
    show ⟪V - p₀, n⟫ = 0
    rw [show V - p₀ = -(p₀ - V) by abel, inner_neg_left, h, neg_zero]
  have hV : ∀ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ, X ≠ V := fun X hX h => hc (h ▸ hX)
  obtain ⟨h1, h2, h3⟩ := regime_R3 hu hn hks hk hs hc'
  have up : ∀ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ,
      (angle (X - V) u = α ↔ X ∈ cone V u (Real.cos α)) := fun X hX => by
    rw [← l14_mem_cone_iff hu hαI]; simp [hV X hX]
  have lo : ∀ X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ,
      (angle (X - V) u = Real.pi - α ↔ X ∈ cone V (-u) (Real.cos α)) := fun X hX => by
    rw [← l14_mem_lower_iff hu hαI]; simp [hV X hX]
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, l14_section_eq hu hαI]
    simp only [l14_mem_cone_iff hu hαI, l14_mem_cone2_iff hu hαI, l14_mem_lower_iff hu hαI]
    constructor
    · rintro ⟨hh, hb⟩
      exact ⟨hh.imp (fun h X hX => h X (l14_mem_plane_iff.1 hX))
        (fun h X hX => h X (l14_mem_plane_iff.1 hX)), hb⟩
    · rintro ⟨hh, hb⟩
      exact ⟨hh.imp (fun h X hX => h X (l14_mem_plane_iff.2 hX))
        (fun h X hX => h X (l14_mem_plane_iff.2 hX)), hb⟩
  · rw [h2]
    constructor
    · rintro ⟨⟨X, hX, hXc⟩, ⟨Y, hY, hYc⟩⟩
      exact ⟨⟨X, l14_mem_plane_iff.2 hX, (up X (l14_mem_plane_iff.2 hX)).2 hXc⟩,
        ⟨Y, l14_mem_plane_iff.2 hY, (lo Y (l14_mem_plane_iff.2 hY)).2 hYc⟩⟩
    · rintro ⟨⟨X, hX, hXc⟩, ⟨Y, hY, hYc⟩⟩
      exact ⟨⟨X, l14_mem_plane_iff.1 hX, (up X hX).1 hXc⟩, ⟨Y, l14_mem_plane_iff.1 hY, (lo Y hY).1 hYc⟩⟩
  · intro hm hmc
    obtain ⟨X, hX, hXc⟩ := h3 hm hmc
    exact ⟨X, l14_mem_plane_iff.2 hX, (up X (l14_mem_plane_iff.2 hX)).2 hXc⟩

/-- **Planes through the apex in `ℝ³` (Mathlib-only form).** With `a = u - ⟪u,n⟫ n`: if
`sin α < |⟪u, n⟫|` the section is `{V}`; if `|⟪u, n⟫| = sin α` it is the line `line[ℝ, V, V + a]`
with `a ≠ 0`; if `|⟪u, n⟫| < sin α` it is the union of two lines through `V` with distinct
directions `a ± ρ f` (`f` a unit vector orthogonal to `u` and `n`, `ρ > 0`), meeting only at `V`.
@isnad1 id=and.4h4v.s13.85847219ed44 from=translated src=- shape=232e817e vocab=69144f33
-/
theorem l14_apex_R3 {V u n : EuclideanSpace ℝ (Fin 3)} {α : ℝ} (hu : ‖u‖ = 1)
    (hn : ‖n‖ = 1) (hα0 : 0 < α) (hα1 : α < Real.pi / 2) :
    (Real.sin α < |⟪u, n⟫| → (AffineSubspace.mk' V (ℝ ∙ n)ᗮ : Set _) ∩
      {X | X = V ∨ angle (X - V) u = α ∨ angle (X - V) u = Real.pi - α} = {V}) ∧
    (|⟪u, n⟫| = Real.sin α → u - ⟪u, n⟫ • n ≠ 0 ∧ (AffineSubspace.mk' V (ℝ ∙ n)ᗮ : Set _) ∩
      {X | X = V ∨ angle (X - V) u = α ∨ angle (X - V) u = Real.pi - α} =
        (line[ℝ, V, V + (u - ⟪u, n⟫ • n)] : Set _)) ∧
    (|⟪u, n⟫| < Real.sin α → ∃ f : EuclideanSpace ℝ (Fin 3), ∃ ρ : ℝ,
      ‖f‖ = 1 ∧ ⟪f, u⟫ = 0 ∧ ⟪f, n⟫ = 0 ∧ 0 < ρ ∧
      (AffineSubspace.mk' V (ℝ ∙ n)ᗮ : Set _) ∩
        {X | X = V ∨ angle (X - V) u = α ∨ angle (X - V) u = Real.pi - α} =
        (line[ℝ, V, V + ((u - ⟪u, n⟫ • n) + ρ • f)] : Set _) ∪
          (line[ℝ, V, V + ((u - ⟪u, n⟫ • n) - ρ • f)] : Set _) ∧
      (line[ℝ, V, V + ((u - ⟪u, n⟫ • n) + ρ • f)] : Set _) ∩
          (line[ℝ, V, V + ((u - ⟪u, n⟫ • n) - ρ • f)] : Set _) = {V}) := by
  obtain ⟨hks, hk, hs, hαI⟩ := l14_cos_sin hα0 hα1
  have hc : ⟪V - V, n⟫ = 0 := by simp
  obtain ⟨A, B, C⟩ := apex_section_R3 (p₀ := V) hu hn hks hk hs hc
  have hsec := l14_section_eq (V := V) (p₀ := V) (n := n) hu hαI
  have hline : ∀ w : EuclideanSpace ℝ (Fin 3),
      (line[ℝ, V, V + w] : Set _) = {X | ∃ t : ℝ, X = V + t • w} := by
    intro w; ext X
    simp only [SetLike.mem_coe, mem_affineSpan_pair_iff_exists_lineMap_eq,
      AffineMap.lineMap_apply_module', Set.mem_ofPred_eq, add_sub_cancel_left]
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨t, add_comm _ _⟩
    · rintro ⟨t, rfl⟩; exact ⟨t, add_comm _ _⟩
  refine ⟨fun hm => hsec.trans (A hm), fun hm => ?_, fun hm => ?_⟩
  · obtain ⟨h0, h⟩ := B hm
    exact ⟨h0, by rw [hsec, h, hline]; rfl⟩
  · obtain ⟨f, hf, hfu, hfn, hρ, h, hmeet⟩ := C hm
    refine ⟨f, apexRho ⟪u, n⟫ (Real.cos α) (Real.sin α), hf, hfu, hfn, hρ, ?_, ?_⟩
    · rw [hsec, h, hline, hline]; rfl
    · rw [hline, hline]
      ext X
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨t, rfl⟩, ⟨t', ht'⟩⟩
        obtain ⟨rfl, -⟩ := hmeet t t' ht'
        simp
      · rintro rfl; exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩

/-! ## Witnesses in `EuclideanSpace ℝ (Fin 3)`, cone of half-angle `arccos (4/5)` -/

/--
@isnad1 id=eq.0h6v.s8.c173edf15ee4 from=translated src=- shape=20090b6e vocab=c1eefab0
-/
theorem l14w_inner3 (a b c x y z : ℝ) :
    ⟪(!₂[a, b, c] : EuclideanSpace ℝ (Fin 3)), !₂[x, y, z]⟫ = a * x + b * y + c * z := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

/--
@isnad1 id=eq.0h3v.s7.e558aa36a6fa from=translated src=- shape=0ff0bbc8 vocab=494e4ac0
-/
theorem l14w_norm3 (a b c : ℝ) :
    ‖(!₂[a, b, c] : EuclideanSpace ℝ (Fin 3))‖ = Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_three]

/--
@isnad1 id=eq.0h6v.s8.a1312799f42c from=translated src=- shape=f6bb0407 vocab=0e27571c
-/
theorem l14w_sub3 (a b c x y z : ℝ) :
    (!₂[a, b, c] : EuclideanSpace ℝ (Fin 3)) - !₂[x, y, z] = !₂[a - x, b - y, c - z] := by
  ext i; fin_cases i <;> simp

/--
@isnad1 id=eq.1h3v.s7.cec76d8e00d1 from=translated src=- shape=aad7d242 vocab=b37aa3fe
-/
theorem l14w_unit {a b c : ℝ} (h : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    ‖(!₂[a, b, c] : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
  rw [l14w_norm3, h, Real.sqrt_one]

/--
@isnad1 id=ne.1h6v.s7.406146512740 from=translated src=- shape=2131b88d vocab=4a3bc9f8
-/
theorem l14w_ne3 {a b c x y z : ℝ} (h : a ≠ x ∨ b ≠ y ∨ c ≠ z) :
    (!₂[a, b, c] : EuclideanSpace ℝ (Fin 3)) ≠ !₂[x, y, z] := by
  intro he
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) he
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) he
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) he
  simp at h0 h1 h2
  rcases h with h | h | h <;> contradiction

/--
@isnad1 id=mem.1h3v.s11.83a802acd2e6 from=translated src=- shape=47a56236 vocab=c1e1b6bc
-/
theorem l14w_mem_plane {p₀ n X : EuclideanSpace ℝ (Fin 3)} (h : ⟪X - p₀, n⟫ = 0) :
    X ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ := l14_mem_plane_iff.2 h

/--
@isnad1 id=and.0h0v.s7.4639226f9b12 from=translated src=- shape=9c61213e vocab=0312284d
-/
theorem l14w_alpha : 0 < Real.arccos (4 / 5) ∧ Real.arccos (4 / 5) < Real.pi / 2 ∧
    Real.sin (Real.arccos (4 / 5)) = 3 / 5 ∧ Real.cos (Real.arccos (4 / 5)) = 4 / 5 := by
  refine ⟨Real.arccos_pos.2 (by norm_num), Real.arccos_lt_pi_div_two.2 (by norm_num), ?_,
    Real.cos_arccos (by norm_num) (by norm_num)⟩
  rw [Real.sin_arccos, show (1 : ℝ) - (4 / 5) ^ 2 = (3 / 5) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

/-- Angle with the axis `e₃` of a vector `(a, b, c)` of norm `r > 0` with `c = (4/5) r`.
@isnad1 id=eq.3h4v.s9.d452344d2ab1 from=translated src=- shape=0b1be37d vocab=800ebe82
-/
theorem l14w_angle {a b c r : ℝ} (hr : 0 < r) (hn : a ^ 2 + b ^ 2 + c ^ 2 = r ^ 2)
    (hc : c = 4 / 5 * r ∨ c = -(4 / 5) * r) :
    angle (!₂[a, b, c] : EuclideanSpace ℝ (Fin 3)) !₂[0, 0, 1] =
      if c = 4 / 5 * r then Real.arccos (4 / 5) else Real.pi - Real.arccos (4 / 5) := by
  rw [InnerProductGeometry.angle, l14w_inner3, l14w_norm3, l14w_unit (by norm_num), hn,
    Real.sqrt_sq hr.le]
  rcases hc with h | h
  · rw [ite_eq_left h, h]; congr 1; field_simp; ring
  · have hne : ¬ c = 4 / 5 * r := by rw [h]; intro h'; linarith
    rw [ite_eq_right hne, ← Real.arccos_neg, h]; congr 1; field_simp; ring

/-- **Witness for `l14_dandelin_ellipse` and `l14_directrix_ellipse`.** Apex `0`, axis `e₃`,
`α = arccos (4/5)`, plane through `e₃` with unit normal `(0, 3/5, 4/5)` (so `⟪u, n⟫ = 4/5`).
All hypotheses hold; the two foci are distinct (a genuine ellipse, not a circle), the focal
constant is positive, the section contains the point `(0, 12/25, 16/25) ≠ V`, and every
directrix `π ∩ {⟪Y - V, u⟫ = b}` is non-empty (so `infDist` is not taken to `∅`).
@isnad1 id=and.0h0v.s14.04e01d464011 from=translated src=- shape=d65734bc vocab=0cd53f86
-/
theorem l14w_dandelin_ellipse :
    ‖(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3))‖ = 1 ∧
    ‖(!₂[0, 3 / 5, 4 / 5] : EuclideanSpace ℝ (Fin 3))‖ = 1 ∧
    0 < Real.arccos (4 / 5) ∧ Real.arccos (4 / 5) < Real.pi / 2 ∧
    Real.sin (Real.arccos (4 / 5)) <
      |⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[0, 3 / 5, 4 / 5]⟫| ∧
    0 < ⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[0, 3 / 5, 4 / 5]⟫ *
      ⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)) - !₂[0, 0, 0], !₂[0, 3 / 5, 4 / 5]⟫ ∧
    |⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[0, 3 / 5, 4 / 5]⟫| < 1 ∧
    (∃ d₁ d₂ : ℝ, ∃ F₁ F₂ : EuclideanSpace ℝ (Fin 3), ∃ L : ℝ, 0 < d₁ ∧ d₁ < d₂ ∧
      (⟨!₂[0, 0, 0] + d₁ • !₂[0, 0, 1], d₁ * Real.sin (Real.arccos (4 / 5))⟩ :
        EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 3))).IsTangentAt F₁
          (AffineSubspace.mk' !₂[0, 0, 1] (ℝ ∙ !₂[0, 3 / 5, 4 / 5])ᗮ) ∧
      (⟨!₂[0, 0, 0] + d₂ • !₂[0, 0, 1], d₂ * Real.sin (Real.arccos (4 / 5))⟩ :
        EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 3))).IsTangentAt F₂
          (AffineSubspace.mk' !₂[0, 0, 1] (ℝ ∙ !₂[0, 3 / 5, 4 / 5])ᗮ) ∧
      F₁ ≠ F₂ ∧ 0 < L ∧
      ∀ X ∈ AffineSubspace.mk' (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3))
          (ℝ ∙ !₂[0, 3 / 5, 4 / 5])ᗮ,
        ((X = !₂[0, 0, 0] ∨ angle (X - !₂[0, 0, 0]) !₂[0, 0, 1] = Real.arccos (4 / 5)) ↔
          dist X F₁ + dist X F₂ = L)) ∧
    (!₂[0, 12 / 25, 16 / 25] : EuclideanSpace ℝ (Fin 3)) ∈
      AffineSubspace.mk' !₂[0, 0, 1] (ℝ ∙ !₂[0, 3 / 5, 4 / 5])ᗮ ∧
    (!₂[0, 12 / 25, 16 / 25] : EuclideanSpace ℝ (Fin 3)) ≠ !₂[0, 0, 0] ∧
    angle ((!₂[0, 12 / 25, 16 / 25] : EuclideanSpace ℝ (Fin 3)) - !₂[0, 0, 0]) !₂[0, 0, 1] =
      Real.arccos (4 / 5) ∧
    ∀ b : ℝ, ((AffineSubspace.mk' !₂[0, 0, 1] (ℝ ∙ !₂[0, 3 / 5, 4 / 5])ᗮ ⊓
      AffineSubspace.mk' (!₂[0, 0, 0] + b • !₂[0, 0, 1]) (ℝ ∙ !₂[0, 0, 1])ᗮ :
        AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))) :
          Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
  obtain ⟨ha0, ha1, hsin, -⟩ := l14w_alpha
  have hu : ‖(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3))‖ = 1 := l14w_unit (by norm_num)
  have hn : ‖(!₂[0, 3 / 5, 4 / 5] : EuclideanSpace ℝ (Fin 3))‖ = 1 := l14w_unit (by norm_num)
  have hm : ⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[0, 3 / 5, 4 / 5]⟫ = 4 / 5 := by
    rw [l14w_inner3]; norm_num
  have hm' : Real.sin (Real.arccos (4 / 5)) <
      |⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[0, 3 / 5, 4 / 5]⟫| := by
    rw [hm, hsin]; norm_num [abs_of_pos]
  have hc : 0 < ⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[0, 3 / 5, 4 / 5]⟫ *
      ⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)) - !₂[0, 0, 0], !₂[0, 3 / 5, 4 / 5]⟫ := by
    rw [hm, l14w_sub3, l14w_inner3]; norm_num
  have hm1 : |⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[0, 3 / 5, 4 / 5]⟫| < 1 := by
    rw [hm]; norm_num [abs_of_pos]
  refine ⟨hu, hn, ha0, ha1, hm', hc, hm1, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨d₁, d₂, F₁, F₂, L, hd₁, hd, hL, -, ht₁, ht₂, -, hsec⟩ :=
      l14_dandelin_ellipse hu hn ha0 ha1 hm' hc
    have hne : F₁ ≠ F₂ := by
      rw [(l14_isTangentAt_plane hn ht₁).1, (l14_isTangentAt_plane hn ht₂).1]
      exact l14_proj_ne hu hn (by rw [hm]; norm_num) hd.ne
    exact ⟨d₁, d₂, F₁, F₂, L, hd₁, hd, ht₁, ht₂, hne, hL, hsec⟩
  · apply l14w_mem_plane; rw [l14w_sub3, l14w_inner3]; norm_num
  · exact l14w_ne3 (by norm_num)
  · rw [l14w_sub3, sub_zero, sub_zero, sub_zero, l14w_angle (r := 4 / 5) (by norm_num) (by norm_num)
      (Or.inl (by norm_num)), ite_eq_left (by norm_num)]
  · intro b
    refine ⟨!₂[0, (4 - 4 * b) / 3, b], ?_⟩
    rw [SetLike.mem_coe, AffineSubspace.mem_inf_iff]
    refine ⟨l14w_mem_plane ?_, ?_⟩
    · rw [l14w_sub3, l14w_inner3]; ring
    · rw [AffineSubspace.mem_mk', vsub_eq_sub, Submodule.mem_orthogonal_singleton_iff_inner_left]
      have e : (!₂[0, 0, 0] + b • !₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)) = !₂[0, 0, b] := by
        ext i; fin_cases i <;> simp
      rw [e, l14w_sub3, l14w_inner3]; ring

/--
@isnad1 id=eq.0h0v.s8.27d7288b75f1 from=translated src=- shape=9435b4d7 vocab=4a3bc9f8
-/
theorem l14w_V : (!₂[0, 0, 0] : EuclideanSpace ℝ (Fin 3)) = 0 := by
  ext i; fin_cases i <;> simp

/--
@isnad1 id=eq.3h4v.s9.b4f6d25ee89b from=translated src=- shape=17b60254 vocab=cefe3f14
-/
theorem l14w_angle_up {a b c r : ℝ} (hr : 0 < r) (hn : a ^ 2 + b ^ 2 + c ^ 2 = r ^ 2)
    (hc : c = 4 / 5 * r) :
    angle ((!₂[a, b, c] : EuclideanSpace ℝ (Fin 3)) - !₂[0, 0, 0]) !₂[0, 0, 1] =
      Real.arccos (4 / 5) := by
  rw [l14w_V, sub_zero, l14w_angle hr hn (Or.inl hc), ite_eq_left hc]

/--
@isnad1 id=eq.3h4v.s9.805c2793bc85 from=translated src=- shape=06db5de0 vocab=5fa5fcc0
-/
theorem l14w_angle_down {a b c r : ℝ} (hr : 0 < r) (hn : a ^ 2 + b ^ 2 + c ^ 2 = r ^ 2)
    (hc : c = -(4 / 5) * r) :
    angle ((!₂[a, b, c] : EuclideanSpace ℝ (Fin 3)) - !₂[0, 0, 0]) !₂[0, 0, 1] =
      Real.pi - Real.arccos (4 / 5) := by
  have hne : ¬ c = 4 / 5 * r := by rw [hc]; intro h; linarith
  rw [l14w_V, sub_zero, l14w_angle hr hn (Or.inr hc), ite_eq_right hne]

/-- **Witness for `l14_dandelin_hyperbola`.** Apex `0`, axis `e₃`, `α = arccos (4/5)`, plane
`x = 1` (normal `e₁`, `⟪u, n⟫ = 0 < 3/5`). All hypotheses hold; the plane meets the upper nappe
at `(1, 0, 4/3)` and the lower nappe at `(1, 0, -4/3)`; the two foci are distinct and the focal
constant `L` is positive.
@isnad1 id=and.0h0v.s14.e80620e5d9d5 from=translated src=- shape=ad2be638 vocab=d0d13929
-/
theorem l14w_dandelin_hyperbola :
    ‖(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3))‖ = 1 ∧
    ‖(!₂[1, 0, 0] : EuclideanSpace ℝ (Fin 3))‖ = 1 ∧
    0 < Real.arccos (4 / 5) ∧ Real.arccos (4 / 5) < Real.pi / 2 ∧
    |⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[1, 0, 0]⟫| < Real.sin (Real.arccos (4 / 5)) ∧
    (!₂[0, 0, 0] : EuclideanSpace ℝ (Fin 3)) ∉
      AffineSubspace.mk' !₂[1, 0, 0] (ℝ ∙ !₂[1, 0, 0])ᗮ ∧
    (∃ d₁ d₂ : ℝ, ∃ F₁ F₂ : EuclideanSpace ℝ (Fin 3), ∃ L : ℝ, d₂ < 0 ∧ 0 < d₁ ∧
      (⟨!₂[0, 0, 0] + d₁ • !₂[0, 0, 1], |d₁| * Real.sin (Real.arccos (4 / 5))⟩ :
        EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 3))).IsTangentAt F₁
          (AffineSubspace.mk' !₂[1, 0, 0] (ℝ ∙ !₂[1, 0, 0])ᗮ) ∧
      (⟨!₂[0, 0, 0] + d₂ • !₂[0, 0, 1], |d₂| * Real.sin (Real.arccos (4 / 5))⟩ :
        EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 3))).IsTangentAt F₂
          (AffineSubspace.mk' !₂[1, 0, 0] (ℝ ∙ !₂[1, 0, 0])ᗮ) ∧
      F₁ ≠ F₂ ∧ 0 < L ∧
      ∀ X ∈ AffineSubspace.mk' (!₂[1, 0, 0] : EuclideanSpace ℝ (Fin 3)) (ℝ ∙ !₂[1, 0, 0])ᗮ,
        ((X = !₂[0, 0, 0] ∨ angle (X - !₂[0, 0, 0]) !₂[0, 0, 1] = Real.arccos (4 / 5) ∨
          angle (X - !₂[0, 0, 0]) !₂[0, 0, 1] = Real.pi - Real.arccos (4 / 5)) ↔
          |dist X F₁ - dist X F₂| = L)) ∧
    (!₂[1, 0, 4 / 3] : EuclideanSpace ℝ (Fin 3)) ∈
      AffineSubspace.mk' !₂[1, 0, 0] (ℝ ∙ !₂[1, 0, 0])ᗮ ∧
    angle ((!₂[1, 0, 4 / 3] : EuclideanSpace ℝ (Fin 3)) - !₂[0, 0, 0]) !₂[0, 0, 1] =
      Real.arccos (4 / 5) ∧
    (!₂[1, 0, -4 / 3] : EuclideanSpace ℝ (Fin 3)) ∈
      AffineSubspace.mk' !₂[1, 0, 0] (ℝ ∙ !₂[1, 0, 0])ᗮ ∧
    angle ((!₂[1, 0, -4 / 3] : EuclideanSpace ℝ (Fin 3)) - !₂[0, 0, 0]) !₂[0, 0, 1] =
      Real.pi - Real.arccos (4 / 5) := by
  obtain ⟨ha0, ha1, hsin, -⟩ := l14w_alpha
  have hu : ‖(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3))‖ = 1 := l14w_unit (by norm_num)
  have hn : ‖(!₂[1, 0, 0] : EuclideanSpace ℝ (Fin 3))‖ = 1 := l14w_unit (by norm_num)
  have hm : ⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[1, 0, 0]⟫ = 0 := by
    rw [l14w_inner3]; norm_num
  have hm' : |⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[1, 0, 0]⟫| <
      Real.sin (Real.arccos (4 / 5)) := by rw [hm, hsin]; norm_num
  have hc : (!₂[0, 0, 0] : EuclideanSpace ℝ (Fin 3)) ∉
      AffineSubspace.mk' !₂[1, 0, 0] (ℝ ∙ !₂[1, 0, 0])ᗮ := by
    rw [l14_mem_plane_iff]; show ¬ ⟪_ - _, _⟫ = 0
    rw [l14w_sub3, l14w_inner3]; norm_num
  have hXu : (!₂[1, 0, 4 / 3] : EuclideanSpace ℝ (Fin 3)) ∈
      AffineSubspace.mk' !₂[1, 0, 0] (ℝ ∙ !₂[1, 0, 0])ᗮ := by
    apply l14w_mem_plane; rw [l14w_sub3, l14w_inner3]; norm_num
  have hXu' := l14w_angle_up (a := 1) (b := 0) (c := 4 / 3) (r := 5 / 3) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨hu, hn, ha0, ha1, hm', hc, ?_, hXu, hXu', ?_,
    l14w_angle_down (r := 5 / 3) (by norm_num) (by norm_num) (by norm_num)⟩
  · obtain ⟨-, d₁, d₂, F₁, F₂, L, hd₂, hd₁, hL, -, ht₁, ht₂, -, -, hiff, -⟩ :=
      l14_dandelin_hyperbola hu hn ha0 ha1 hm' hc
    have hne : F₁ ≠ F₂ := by
      rw [(l14_isTangentAt_plane hn ht₁).1, (l14_isTangentAt_plane hn ht₂).1]
      exact l14_proj_ne hu hn (by rw [hm]; norm_num) (by linarith)
    exact ⟨d₁, d₂, F₁, F₂, L, hd₂, hd₁, ht₁, ht₂, hne, hL, hiff⟩
  · apply l14w_mem_plane; rw [l14w_sub3, l14w_inner3]; norm_num

/-- **Witness for `l14_parabola`.** Apex `0`, axis `e₃`, `α = arccos (4/5)`, plane through `e₃`
with unit normal `(4/5, 0, 3/5)` (so `⟪u, n⟫ = 3/5 = sin α`). All hypotheses hold, and the
section contains the non-apex point `(3/8, 0, 1/2)` of the nappe.
@isnad1 id=and.0h0v.s12.1655530730b7 from=translated src=- shape=d6fd99ae vocab=208f4170
-/
theorem l14w_parabola :
    ‖(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3))‖ = 1 ∧
    ‖(!₂[4 / 5, 0, 3 / 5] : EuclideanSpace ℝ (Fin 3))‖ = 1 ∧
    0 < Real.arccos (4 / 5) ∧ Real.arccos (4 / 5) < Real.pi / 2 ∧
    |⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[4 / 5, 0, 3 / 5]⟫| =
      Real.sin (Real.arccos (4 / 5)) ∧
    0 < ⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[4 / 5, 0, 3 / 5]⟫ *
      ⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)) - !₂[0, 0, 0], !₂[4 / 5, 0, 3 / 5]⟫ ∧
    (!₂[3 / 8, 0, 1 / 2] : EuclideanSpace ℝ (Fin 3)) ∈
      AffineSubspace.mk' !₂[0, 0, 1] (ℝ ∙ !₂[4 / 5, 0, 3 / 5])ᗮ ∧
    (!₂[3 / 8, 0, 1 / 2] : EuclideanSpace ℝ (Fin 3)) ≠ !₂[0, 0, 0] ∧
    angle ((!₂[3 / 8, 0, 1 / 2] : EuclideanSpace ℝ (Fin 3)) - !₂[0, 0, 0]) !₂[0, 0, 1] =
      Real.arccos (4 / 5) := by
  obtain ⟨ha0, ha1, hsin, -⟩ := l14w_alpha
  refine ⟨l14w_unit (by norm_num), l14w_unit (by norm_num), ha0, ha1, ?_, ?_, ?_,
    l14w_ne3 (by norm_num), l14w_angle_up (r := 5 / 8) (by norm_num) (by norm_num) (by norm_num)⟩
  · rw [l14w_inner3, hsin]; norm_num [abs_of_pos]
  · rw [l14w_sub3, l14w_inner3, l14w_inner3]; norm_num
  · apply l14w_mem_plane; rw [l14w_sub3, l14w_inner3]; norm_num

/-- **Witness for `l14_apex_R3`.** Apex `0`, axis `e₃`, `α = arccos (4/5)` (`sin α = 3/5`), and
three planes through the apex: normal `e₃` (`⟪u, n⟫ = 1 > 3/5`, point case), normal
`(4/5, 0, 3/5)` (`⟪u, n⟫ = 3/5`, line case), normal `e₂` (`⟪u, n⟫ = 0 < 3/5`, two-line case).
The point `(-3, 0, 4)` lies on the line-case section and differs from the apex; the points `(3, 0, 4)` and `(-3, 0, 4)` lie on the
two-line section, are distinct, and differ from the apex.
@isnad1 id=and.0h0v.s13.ee5702567a1c from=translated src=- shape=cd35ae87 vocab=ae1d4454
-/
theorem l14w_apex :
    Real.sin (Real.arccos (4 / 5)) <
      |⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[0, 0, 1]⟫| ∧
    |⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[4 / 5, 0, 3 / 5]⟫| =
      Real.sin (Real.arccos (4 / 5)) ∧
    |⟪(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[0, 1, 0]⟫| < Real.sin (Real.arccos (4 / 5)) ∧
    ‖(!₂[0, 1, 0] : EuclideanSpace ℝ (Fin 3))‖ = 1 ∧
    (!₂[-3, 0, 4] : EuclideanSpace ℝ (Fin 3)) ∈
      AffineSubspace.mk' !₂[0, 0, 0] (ℝ ∙ !₂[4 / 5, 0, 3 / 5])ᗮ ∧
    angle ((!₂[-3, 0, 4] : EuclideanSpace ℝ (Fin 3)) - !₂[0, 0, 0]) !₂[0, 0, 1] =
      Real.arccos (4 / 5) ∧
    (!₂[3, 0, 4] : EuclideanSpace ℝ (Fin 3)) ∈ AffineSubspace.mk' !₂[0, 0, 0] (ℝ ∙ !₂[0, 1, 0])ᗮ ∧
    (!₂[-3, 0, 4] : EuclideanSpace ℝ (Fin 3)) ∈ AffineSubspace.mk' !₂[0, 0, 0] (ℝ ∙ !₂[0, 1, 0])ᗮ ∧
    angle ((!₂[3, 0, 4] : EuclideanSpace ℝ (Fin 3)) - !₂[0, 0, 0]) !₂[0, 0, 1] =
      Real.arccos (4 / 5) ∧
    angle ((!₂[-3, 0, 4] : EuclideanSpace ℝ (Fin 3)) - !₂[0, 0, 0]) !₂[0, 0, 1] =
      Real.arccos (4 / 5) ∧
    (!₂[3, 0, 4] : EuclideanSpace ℝ (Fin 3)) ≠ !₂[-3, 0, 4] ∧
    (!₂[3, 0, 4] : EuclideanSpace ℝ (Fin 3)) ≠ !₂[0, 0, 0] ∧
    (!₂[-3, 0, 4] : EuclideanSpace ℝ (Fin 3)) ≠ !₂[0, 0, 0] := by
  obtain ⟨-, -, hsin, -⟩ := l14w_alpha
  refine ⟨?_, ?_, ?_, l14w_unit (by norm_num), ?_,
    l14w_angle_up (r := 5) (by norm_num) (by norm_num) (by norm_num), ?_, ?_,
    l14w_angle_up (r := 5) (by norm_num) (by norm_num) (by norm_num),
    l14w_angle_up (r := 5) (by norm_num) (by norm_num) (by norm_num),
    l14w_ne3 (by norm_num), l14w_ne3 (by norm_num), l14w_ne3 (by norm_num)⟩
  · rw [l14w_inner3, hsin]; norm_num
  · rw [l14w_inner3, hsin]; norm_num [abs_of_pos]
  · rw [l14w_inner3, hsin]; norm_num
  all_goals apply l14w_mem_plane; rw [l14w_sub3, l14w_inner3]; norm_num

/-- **Witness for `l14_regime_R3` and `l14_inscribed`.** For the ellipse configuration of
`l14w_dandelin_ellipse` the hypotheses of `l14_regime_R3` hold (the apex is off the plane) and
its ellipse-regime conclusions are non-vacuous: the upper nappe meets the plane at a point
whose angle with the axis is `α`. For `l14_inscribed`, the non-apex point `(3, 0, 4)` of the
nappe and `d = 1` satisfy the hypotheses.
@isnad1 id=and.0h0v.s13.72111c2a448d from=translated src=- shape=6cfb7e0f vocab=dcad6b1e
-/
theorem l14w_regime_inscribed :
    (!₂[0, 0, 0] : EuclideanSpace ℝ (Fin 3)) ∉
      AffineSubspace.mk' !₂[0, 0, 1] (ℝ ∙ !₂[0, 3 / 5, 4 / 5])ᗮ ∧
    (∃ X ∈ AffineSubspace.mk' (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3))
        (ℝ ∙ !₂[0, 3 / 5, 4 / 5])ᗮ, angle (X - !₂[0, 0, 0]) !₂[0, 0, 1] = Real.arccos (4 / 5)) ∧
    (!₂[3, 0, 4] : EuclideanSpace ℝ (Fin 3)) ≠ !₂[0, 0, 0] ∧
    angle ((!₂[3, 0, 4] : EuclideanSpace ℝ (Fin 3)) - !₂[0, 0, 0]) !₂[0, 0, 1] =
      Real.arccos (4 / 5) ∧
    (∃ T : EuclideanSpace ℝ (Fin 3),
      (⟨!₂[0, 0, 0] + (1 : ℝ) • !₂[0, 0, 1], 1 * Real.sin (Real.arccos (4 / 5))⟩ :
        EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 3))).IsTangentAt T
          line[ℝ, !₂[0, 0, 0], !₂[3, 0, 4]]) := by
  obtain ⟨ha0, ha1, -, -⟩ := l14w_alpha
  have hX := l14w_angle_up (a := 3) (b := 0) (c := 4) (r := 5) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨?_, ?_, l14w_ne3 (by norm_num), hX,
    (l14_inscribed (l14w_unit (by norm_num)) ha0 ha1 one_pos (l14w_ne3 (by norm_num)) hX).1⟩
  · rw [l14_mem_plane_iff]; show ¬ ⟪_ - _, _⟫ = 0
    rw [l14w_sub3, l14w_inner3]; norm_num
  · refine ⟨!₂[0, 12 / 25, 16 / 25], ?_,
      l14w_angle_up (r := 4 / 5) (by norm_num) (by norm_num) (by norm_num)⟩
    apply l14w_mem_plane; rw [l14w_sub3, l14w_inner3]; norm_num

end Dandelin
