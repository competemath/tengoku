/-
Copyright (c) 2026. All rights reserved.

# Bridge lemmas: the project's definitions match the classical notions

* `cone V u k` (with `k = cos α`) is the nappe of the right circular cone with apex `V`, axis `u`
  and half-angle `α`: angle form and generator (parametric) form; `cone2` is the double cone;
* `plane p₀ n` is Mathlib's affine subspace through `p₀` with normal `n`;
* `tangencyPoint V X k d` is where the generator `VX` touches the inscribed sphere
  `(V + d • u, d s)`, as a Mathlib `Sphere.IsTangentAt` statement;
* `focus₁`, `focus₂` are the points where the two Dandelin spheres touch the cutting plane, again
  as `Sphere.IsTangentAt` statements (so the centre-to-plane distance equals the radius).
-/
import Tengoku.Dandelin.Dandelin.Hyperbola

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open RealInnerProductSpace InnerProductGeometry

namespace Dandelin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The cone -/

/-- Angle form: for `k = cos α` with `0 ≤ α ≤ π`, a point `X ≠ V` is on the nappe iff the
generator `VX` makes angle `α` with the axis `u`.-/
theorem mem_cone_iff_angle {V u X : E} {α : ℝ} (hu : ‖u‖ = 1) (hα : α ∈ Set.Icc 0 Real.pi)
    (hX : X ≠ V) : X ∈ cone V u (Real.cos α) ↔ angle (X - V) u = α := by
  have hn : ‖X - V‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hX)
  show ⟪X - V, u⟫ = Real.cos α * ‖X - V‖ ↔ _
  constructor
  · intro h
    apply Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ hα
    rw [cos_angle, h, hu, mul_one, mul_div_cancel_right₀ _ hn]
  · intro h
    have := cos_angle (X - V) u
    rw [h, hu, mul_one] at this
    rw [this, div_mul_cancel₀ _ hn]

/-- Angle form of the double cone: `X ≠ V` is on `cone2` iff `VX` makes angle `α` or `π - α`
with the axis.-/
theorem mem_cone2_iff_angle {V u X : E} {α : ℝ} (hu : ‖u‖ = 1) (hα : α ∈ Set.Icc 0 Real.pi)
    (hX : X ≠ V) :
    X ∈ cone2 V u (Real.cos α) ↔ angle (X - V) u = α ∨ angle (X - V) u = Real.pi - α := by
  rw [mem_cone2_iff, mem_cone_iff_angle hu hα hX,
    mem_cone_iff_angle (by rw [norm_neg, hu]) hα hX, angle_neg_right]
  constructor <;> rintro (h | h) <;> first | exact Or.inl h | exact Or.inr (by linarith)

/-- Generator (parametric) form: every point `V + t • w` with `t ≥ 0`, `‖w‖ = 1` and
`⟪w, u⟫ = k` lies on the nappe.-/
theorem generator_mem_cone {V u w : E} {k t : ℝ} (hw : ‖w‖ = 1) (hwu : ⟪w, u⟫ = k)
    (ht : 0 ≤ t) : V + t • w ∈ cone V u k := by
  show ⟪V + t • w - V, u⟫ = k * ‖V + t • w - V‖
  rw [add_sub_cancel_left, real_inner_smul_left, hwu, norm_smul, hw, Real.norm_eq_abs,
    abs_of_nonneg ht]
  ring

/-- Conversely, every point `X ≠ V` of the nappe is `V + t • w` with `t > 0` and `w` a unit
vector with `⟪w, u⟫ = k` (the unit direction of the generator).-/
theorem exists_generator_of_mem_cone {V u X : E} {k : ℝ} (hX : X ∈ cone V u k) (hXV : X ≠ V) :
    ∃ t : ℝ, 0 < t ∧ ∃ w : E, ‖w‖ = 1 ∧ ⟪w, u⟫ = k ∧ X = V + t • w := by
  have hX' : ⟪X - V, u⟫ = k * ‖X - V‖ := hX
  have hn : 0 < ‖X - V‖ := norm_pos_iff.2 (sub_ne_zero.2 hXV)
  refine ⟨‖X - V‖, hn, ‖X - V‖⁻¹ • (X - V), ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  · rw [real_inner_smul_left, hX']
    field_simp
  · rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul, add_sub_cancel]

/-! ## The plane -/

/-- Membership in `plane` is the normal equation `⟪X - p₀, n⟫ = 0`.-/
theorem mem_plane_iff {p₀ n X : E} : X ∈ plane p₀ n ↔ ⟪X - p₀, n⟫ = 0 := Iff.rfl

/-- `plane p₀ n` is Mathlib's affine subspace through `p₀` with direction `n^⊥`.-/
theorem plane_eq_mk' (p₀ n : E) :
    plane p₀ n = (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ : Set E) := by
  ext X
  show ⟪X - p₀, n⟫ = 0 ↔ _
  rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub,
    Submodule.mem_orthogonal_singleton_iff_inner_left]

/-! ## Tangency points as Mathlib tangencies -/

/-- `tangencyPoint V X k d` lies on the generator line through `V` and `X`.-/
theorem tangencyPoint_mem_line (V X : E) (k d : ℝ) :
    tangencyPoint V X k d ∈ line[ℝ, V, X] := by
  have : tangencyPoint V X k d = AffineMap.lineMap V X (d * k / ‖X - V‖) := by
    rw [tangencyPoint, AffineMap.lineMap_apply_module', add_comm]
  rw [this]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- The generator line `VX` is tangent to the inscribed sphere `(V + d • u, d s)` at
`tangencyPoint V X k d` (point on the sphere, radius perpendicular to the line).-/
theorem isTangentAt_tangencyPoint {V u X : E} {k s d : ℝ} (hu : ‖u‖ = 1)
    (hks : k ^ 2 + s ^ 2 = 1) (hds : 0 ≤ d * s) (hX : X ∈ cone V u k) (ht : ‖X - V‖ ≠ 0) :
    (⟨V + d • u, d * s⟩ : EuclideanGeometry.Sphere E).IsTangentAt (tangencyPoint V X k d)
      line[ℝ, V, X] := by
  have hX' : ⟪X - V, u⟫ = k * ‖X - V‖ := hX
  have key : ⟪X - V, tangencyPoint V X k d - (V + d • u)⟫ = 0 := by
    have h2 : tangencyPoint V X k d - (V + d • u) = (d * k / ‖X - V‖) • (X - V) - d • u := by
      unfold tangencyPoint; abel
    rw [h2, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hX']
    field_simp
    ring
  refine ⟨?_, tangencyPoint_mem_line V X k d, ?_⟩
  · rw [EuclideanGeometry.mem_sphere, dist_eq_norm]
    exact tangencyPoint_mem_sphere hu hks hds hX ht
  · apply affineSpan_pair_le_of_mem_of_mem <;>
      rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left, vsub_eq_sub, vsub_eq_sub]
    · have : V - tangencyPoint V X k d = (-(d * k / ‖X - V‖)) • (X - V) := by
        unfold tangencyPoint; rw [neg_smul]; abel
      rw [this, real_inner_smul_left, key, mul_zero]
    · exact tangencyPoint_perp hX ht

/-- The small Dandelin sphere `(V + d₁ • u, d₁ s)` touches the cutting plane exactly at
`focus₁` (Mathlib tangency to the plane as an affine subspace).-/
theorem isTangentAt_focus₁ {V u n p₀ : E} {s : ℝ} (hn : ‖n‖ = 1) (hs : 0 < s)
    (hm : s < ⟪u, n⟫) (hc : 0 < ⟪p₀ - V, n⟫) :
    (⟨V + param₁ V u n p₀ s • u, param₁ V u n p₀ s * s⟩ : EuclideanGeometry.Sphere E).IsTangentAt
      (focus₁ V u n p₀ s) (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) := by
  have hr := (tangent_iff (V := V) (p₀ := p₀) hs hm hc (param₁ V u n p₀ s)).2 (Or.inl rfl)
  have hF := focus₁_mem (V := V) (p₀ := p₀) hn hs hm
  have hpl : ∀ x, x ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ ↔ x ∈ plane p₀ n := fun x => by
    rw [plane_eq_mk', SetLike.mem_coe]
  refine ⟨?_, (hpl _).2 hF, fun x hx => ?_⟩
  · rw [EuclideanGeometry.mem_sphere, dist_eq_norm]
    exact (tangent_of_proj hn (focus₁_eq_proj (V := V) (p₀ := p₀) hs hm) hr hF hF).1
  · rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left, vsub_eq_sub, vsub_eq_sub]
    exact (tangent_of_proj hn (focus₁_eq_proj (V := V) (p₀ := p₀) hs hm) hr ((hpl x).1 hx) hF).2

/-- The large Dandelin sphere `(V + d₂ • u, d₂ s)` touches the cutting plane exactly at
`focus₂`.-/
theorem isTangentAt_focus₂ {V u n p₀ : E} {s : ℝ} (hn : ‖n‖ = 1) (hs : 0 < s)
    (hm : s < ⟪u, n⟫) (hc : 0 < ⟪p₀ - V, n⟫) :
    (⟨V + param₂ V u n p₀ s • u, param₂ V u n p₀ s * s⟩ : EuclideanGeometry.Sphere E).IsTangentAt
      (focus₂ V u n p₀ s) (AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ) := by
  have hr := (tangent_iff (V := V) (p₀ := p₀) hs hm hc (param₂ V u n p₀ s)).2 (Or.inr rfl)
  have hF := focus₂_mem (V := V) (p₀ := p₀) hn hs hm
  have hpl : ∀ x, x ∈ AffineSubspace.mk' p₀ (ℝ ∙ n)ᗮ ↔ x ∈ plane p₀ n := fun x => by
    rw [plane_eq_mk', SetLike.mem_coe]
  refine ⟨?_, (hpl _).2 hF, fun x hx => ?_⟩
  · rw [EuclideanGeometry.mem_sphere, dist_eq_norm]
    exact (tangent_of_proj hn (focus₂_eq_proj (V := V) (p₀ := p₀) hs hm) hr hF hF).1
  · rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left, vsub_eq_sub, vsub_eq_sub]
    exact (tangent_of_proj hn (focus₂_eq_proj (V := V) (p₀ := p₀) hs hm) hr ((hpl x).1 hx) hF).2

end Dandelin
