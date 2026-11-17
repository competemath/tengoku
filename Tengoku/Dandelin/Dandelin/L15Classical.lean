import Tengoku.Dandelin.Dandelin.Basic
import Tengoku.Dandelin.Dandelin.Existence
import Tengoku.Dandelin.Dandelin.Directrix
import Tengoku.Dandelin.Dandelin.Hyperbola
import Tengoku.Dandelin.Dandelin.Regime
import Tengoku.Dandelin.Dandelin.Degenerate
import Tengoku.Dandelin.Dandelin.Bridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Layer 15: classical-statement comparison

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.

Each writer statement `classical_X` is packaged as `def classical_X : Prop := ∀ binders, statement`,
with the binders and body unchanged. The `l15_*` declarations are the bridge lemmas and new proofs
needed for the comparison. `cov_Conics3_obligation` proves the writer's well-formedness obligation
(the directrix `P ⊓ affineSpan C` is a line). `classical_Conics3_c` (the planar converse in standard
form) is not proved here. No writer statement was found to be false.
-/

open EuclideanGeometry InnerProductGeometry Real

noncomputable section

namespace Dandelin.Classical

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-! ## Cone, generators, nappes, plane–axis angle (Conics1–3) -/

/-- OWN DEFINITION. The right circular double cone with apex `V`, axis the line through `V`
with direction `u`, half-opening angle `α`: the union of all lines through `V` making angle
`α` with the axis (a line through `V` with direction `w` makes angle `α` with the axis iff
`∠(w,u) = α` or `∠(w,u) = π - α`).-/
def cone (V u : E3) (α : ℝ) : Set E3 :=
  {X | X = V ∨ InnerProductGeometry.angle (X -ᵥ V) u = α ∨ InnerProductGeometry.angle (X -ᵥ V) u = π - α}

/-- OWN DEFINITION. `g` is a generator of the cone: a line through `V` making angle `α`
with the axis.-/
def IsGenerator (V u : E3) (α : ℝ) (g : AffineSubspace ℝ E3) : Prop :=
  ∃ w : E3, w ≠ 0 ∧ InnerProductGeometry.angle w u = α ∧ g = line[ℝ, V, w +ᵥ V]

/-- OWN DEFINITION. `X` lies strictly inside the solid nappe on the side `σ • u`
(`σ = 1` or `σ = -1`) of the apex.-/
def InsideNappe (V u : E3) (α σ : ℝ) (X : E3) : Prop :=
  X ≠ V ∧ InnerProductGeometry.angle (X -ᵥ V) (σ • u) < α

/-- OWN DEFINITION. The angle `β ∈ [0, π/2]` between the axis direction `u` and the plane
`P`: the angle between `u` and its orthogonal projection onto the direction of `P`
(equal to `π/2` when `u ⊥ P`, by the convention `angle u 0 = π/2`).-/
def planeAxisAngle (u : E3) (P : AffineSubspace ℝ E3) : ℝ :=
  InnerProductGeometry.angle u (P.direction.starProjection u)

/-- OWN DEFINITION. The sphere `S` (positive radius) is tangent to the cone along `C`:
every generator is a tangent line of `S` (meets it in exactly one point), and `C` is the
set of points of contact `S ∩ K` (which is then a circle).-/
def TangentToConeAlong (V u : E3) (α : ℝ) (S : Sphere E3) (C : Set E3) : Prop :=
  0 < S.radius ∧
  (∀ g, IsGenerator V u α g → ∃ x, (g : Set E3) ∩ Metric.sphere S.center S.radius = {x}) ∧
  C = Metric.sphere S.center S.radius ∩ cone V u α

/-- OWN DEFINITION. `S` is tangent to the plane `P` at `F`.-/
def TangentToPlaneAt (P : AffineSubspace ℝ E3) (S : Sphere E3) (F : E3) : Prop :=
  (P : Set E3) ∩ Metric.sphere S.center S.radius = {F}

/-- OWN DEFINITION. A Dandelin sphere of the section `P ∩ K`: tangent to the cone along a
circle and tangent to `P`.-/
def IsDandelinSphere (V u : E3) (α : ℝ) (P : AffineSubspace ℝ E3) (S : Sphere E3) : Prop :=
  (∃ C, TangentToConeAlong V u α S C) ∧ ∃ F, TangentToPlaneAt P S F

/-! ## Conics1: Dandelin spheres, ellipse -/

def classical_Conics1_a : Prop := ∀ (V u : E3) (hu : u ≠ 0) (α : ℝ) (hα0 : 0 < α) (hα1 : α < π / 2)
    (P : AffineSubspace ℝ E3) (hP : Module.finrank ℝ P.direction = 2) (hVP : V ∉ P)
    (hβ : α < planeAxisAngle u P),
   ∃ S₁ S₂ : Sphere E3, S₁ ≠ S₂ ∧
      IsDandelinSphere V u α P S₁ ∧ IsDandelinSphere V u α P S₂ ∧
      (∀ S, IsDandelinSphere V u α P S → S = S₁ ∨ S = S₂) ∧
      -- AMBIGUOUS: "lie inside the same nappe" read as: both centres strictly inside the
      -- same solid nappe (alternative: the whole closed balls lie in the closed solid nappe)
      (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        InsideNappe V u α σ S₁.center ∧ InsideNappe V u α σ S₂.center) ∧
      P.SOppSide S₁.center S₂.center

def classical_Conics1_b : Prop := ∀ (V u : E3) (hu : u ≠ 0) (α : ℝ) (hα0 : 0 < α) (hα1 : α < π / 2)
    (P : AffineSubspace ℝ E3) (hP : Module.finrank ℝ P.direction = 2) (hVP : V ∉ P)
    (hβ : α < planeAxisAngle u P)
    (S₁ S₂ : Sphere E3) (hS : S₁ ≠ S₂) (C₁ C₂ : Set E3) (F₁ F₂ : E3)
    (hC₁ : TangentToConeAlong V u α S₁ C₁) (hC₂ : TangentToConeAlong V u α S₂ C₂)
    (hF₁ : TangentToPlaneAt P S₁ F₁) (hF₂ : TangentToPlaneAt P S₂ F₂),
   ∃ k : ℝ,
      (∀ X ∈ (P : Set E3) ∩ cone V u α, dist X F₁ + dist X F₂ = k) ∧
      (∀ g, IsGenerator V u α g → ∀ Y₁ ∈ (g : Set E3) ∩ C₁, ∀ Y₂ ∈ (g : Set E3) ∩ C₂,
        dist Y₁ Y₂ = k) ∧
      -- major axis `2a` = the largest distance between two points of `E`
      IsGreatest {d | ∃ x ∈ (P : Set E3) ∩ cone V u α, ∃ y ∈ (P : Set E3) ∩ cone V u α,
        d = dist x y} k

/-! ## Conics2: Dandelin spheres, hyperbola -/

def classical_Conics2_a : Prop := ∀ (V u : E3) (hu : u ≠ 0) (α : ℝ) (hα0 : 0 < α) (hα1 : α < π / 2)
    (P : AffineSubspace ℝ E3) (hP : Module.finrank ℝ P.direction = 2) (hVP : V ∉ P)
    (hβ : planeAxisAngle u P < α),
   ∃ S₁ S₂ : Sphere E3, S₁ ≠ S₂ ∧
      IsDandelinSphere V u α P S₁ ∧ IsDandelinSphere V u α P S₂ ∧
      (∀ S, IsDandelinSphere V u α P S → S = S₁ ∨ S = S₂) ∧
      -- AMBIGUOUS: "one inside each nappe" read via the centres (as in Conics1_a)
      InsideNappe V u α 1 S₁.center ∧ InsideNappe V u α (-1) S₂.center

def classical_Conics2_b : Prop := ∀ (V u : E3) (hu : u ≠ 0) (α : ℝ) (hα0 : 0 < α) (hα1 : α < π / 2)
    (P : AffineSubspace ℝ E3) (hP : Module.finrank ℝ P.direction = 2) (hVP : V ∉ P)
    (hβ : planeAxisAngle u P < α)
    (S₁ S₂ : Sphere E3) (hS : S₁ ≠ S₂) (C₁ C₂ : Set E3) (F₁ F₂ : E3)
    (hC₁ : TangentToConeAlong V u α S₁ C₁) (hC₂ : TangentToConeAlong V u α S₂ C₂)
    (hF₁ : TangentToPlaneAt P S₁ F₁) (hF₂ : TangentToPlaneAt P S₂ F₂),
   ∃ k : ℝ,
      (∀ X ∈ (P : Set E3) ∩ cone V u α, |dist X F₁ - dist X F₂| = k) ∧
      (∀ g, IsGenerator V u α g → ∀ Y₁ ∈ (g : Set E3) ∩ C₁, ∀ Y₂ ∈ (g : Set E3) ∩ C₂,
        dist Y₁ Y₂ = k) ∧
      -- transverse axis `2a` = the least distance between the two branches
      -- (branch on a nappe = points of `P ∩ K` on that side of `V` along the axis)
      IsLeast {d | ∃ x ∈ (P : Set E3) ∩ cone V u α, ∃ y ∈ (P : Set E3) ∩ cone V u α,
        0 < inner ℝ (x -ᵥ V) u ∧ inner ℝ (y -ᵥ V) u < 0 ∧ d = dist x y} k

/-! ## Conics3: focus–directrix property -/

/-- Well-formedness: when the section is not a circle (`β < π/2`), the plane `P` meets the
plane of the contact circle in a line.-/
def classical_Conics3_obligation : Prop := ∀ (V u : E3) (hu : u ≠ 0) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α < π / 2) (P : AffineSubspace ℝ E3) (hP : Module.finrank ℝ P.direction = 2)
    (hVP : V ∉ P) (hβ : planeAxisAngle u P < π / 2)
    (S : Sphere E3) (C : Set E3) (F : E3)
    (hC : TangentToConeAlong V u α S C) (hF : TangentToPlaneAt P S F),
   ∃ p q : E3, p ≠ q ∧ P ⊓ affineSpan ℝ C = line[ℝ, p, q]

def classical_Conics3_a : Prop := ∀ (V u : E3) (hu : u ≠ 0) (α : ℝ) (hα0 : 0 < α) (hα1 : α < π / 2)
    (P : AffineSubspace ℝ E3) (hP : Module.finrank ℝ P.direction = 2) (hVP : V ∉ P)
    (hβ : planeAxisAngle u P < π / 2)
    (S : Sphere E3) (C : Set E3) (F : E3)
    (hC : TangentToConeAlong V u α S C) (hF : TangentToPlaneAt P S F),
   ∀ X ∈ (P : Set E3) ∩ cone V u α,
      dist X F = (cos (planeAxisAngle u P) / cos α) *
        Metric.infDist X ((P ⊓ affineSpan ℝ C : AffineSubspace ℝ E3) : Set E3)

/-- The parenthetical claim of Conics3: for the parabola there is exactly one Dandelin
sphere.-/
def classical_Conics3_parabola_unique : Prop := ∀ (V u : E3) (hu : u ≠ 0) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α < π / 2) (P : AffineSubspace ℝ E3) (hP : Module.finrank ℝ P.direction = 2)
    (hVP : V ∉ P) (hβ : planeAxisAngle u P = α),
   ∃! S : Sphere E3, IsDandelinSphere V u α P S

def classical_Conics3_b : Prop := ∀ (V u : E3) (hu : u ≠ 0) (α : ℝ) (hα0 : 0 < α) (hα1 : α < π / 2)
    (P : AffineSubspace ℝ E3) (hP : Module.finrank ℝ P.direction = 2) (hVP : V ∉ P)
    (hβ : planeAxisAngle u P < π / 2)
    (S : Sphere E3) (C : Set E3) (F : E3)
    (hC : TangentToConeAlong V u α S C) (hF : TangentToPlaneAt P S F),
   (α < planeAxisAngle u P → cos (planeAxisAngle u P) / cos α < 1) ∧
    (planeAxisAngle u P = α →
      cos (planeAxisAngle u P) / cos α = 1 ∧
      (P : Set E3) ∩ cone V u α =
        {X | X ∈ P ∧ dist X F =
          Metric.infDist X ((P ⊓ affineSpan ℝ C : AffineSubspace ℝ E3) : Set E3)}) ∧
    (planeAxisAngle u P < α → 1 < cos (planeAxisAngle u P) / cos α)

/-! ### Conics3(c): planar conics in standard form -/

/-- OWN DEFINITION. `Q` is an ellipse with focus `F` and corresponding directrix `d`:
up to a Euclidean motion `φ`, `Q = {x²/a² + y²/b² = 1}` with `a > b > 0`,
`F = (c, 0)`, `d = {x = a²/c}`, where `c = √(a² - b²)`.-/
def IsEllipseFD (Q : Set E2) (F : E2) (d : AffineSubspace ℝ E2) : Prop :=
  ∃ (φ : E2 ≃ᵃⁱ[ℝ] E2) (a b : ℝ), 0 < b ∧ b < a ∧
    Q = {X | (φ.symm X) 0 ^ 2 / a ^ 2 + (φ.symm X) 1 ^ 2 / b ^ 2 = 1} ∧
    (φ.symm F) 0 = √(a ^ 2 - b ^ 2) ∧ (φ.symm F) 1 = 0 ∧
    (d : Set E2) = {X | (φ.symm X) 0 = a ^ 2 / √(a ^ 2 - b ^ 2)}

/-- OWN DEFINITION. `Q` is a hyperbola with focus `F` and corresponding directrix `d`:
up to a Euclidean motion, `Q = {x²/a² - y²/b² = 1}`, `a, b > 0`, `F = (c, 0)`,
`d = {x = a²/c}`, `c = √(a² + b²)`.-/
def IsHyperbolaFD (Q : Set E2) (F : E2) (d : AffineSubspace ℝ E2) : Prop :=
  ∃ (φ : E2 ≃ᵃⁱ[ℝ] E2) (a b : ℝ), 0 < a ∧ 0 < b ∧
    Q = {X | (φ.symm X) 0 ^ 2 / a ^ 2 - (φ.symm X) 1 ^ 2 / b ^ 2 = 1} ∧
    (φ.symm F) 0 = √(a ^ 2 + b ^ 2) ∧ (φ.symm F) 1 = 0 ∧
    (d : Set E2) = {X | (φ.symm X) 0 = a ^ 2 / √(a ^ 2 + b ^ 2)}

/-- OWN DEFINITION. `Q` is a parabola with focus `F` and directrix `d`: up to a Euclidean
motion, `Q = {y² = 4px}`, `p > 0`, `F = (p, 0)`, `d = {x = -p}`.-/
def IsParabolaFD (Q : Set E2) (F : E2) (d : AffineSubspace ℝ E2) : Prop :=
  ∃ (φ : E2 ≃ᵃⁱ[ℝ] E2) (p : ℝ), 0 < p ∧
    Q = {X | (φ.symm X) 1 ^ 2 = 4 * p * (φ.symm X) 0} ∧
    (φ.symm F) 0 = p ∧ (φ.symm F) 1 = 0 ∧
    (d : Set E2) = {X | (φ.symm X) 0 = -p}

def classical_Conics3_c : Prop := ∀ (d : AffineSubspace ℝ E2) (hd : Module.finrank ℝ d.direction = 1)
    (F : E2) (hF : F ∉ d) (e : ℝ) (he : 0 < e),
   let Q : Set E2 := {X | dist X F = e * Metric.infDist X (d : Set E2)};
    (e < 1 → IsEllipseFD Q F d) ∧ (e = 1 → IsParabolaFD Q F d) ∧
    (1 < e → IsHyperbolaFD Q F d)

/-! ### Comparer bridges (NEW) -/

lemma l15_inner_self (x : E3) : inner ℝ x x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x

lemma l15_unit {x : E3} (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]

/-- Normal form of a plane of `E3`.-/
lemma l15_plane_normal (P : AffineSubspace ℝ E3) (hP : Module.finrank ℝ P.direction = 2) :
    ∃ p₀ n : E3, ‖n‖ = 1 ∧ p₀ ∈ P ∧ P.direction = (ℝ ∙ n)ᗮ ∧
      ∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0 := by
  have hne : (P : Set E3).Nonempty := by
    rw [AffineSubspace.nonempty_iff_ne_bot]
    rintro rfl
    rw [AffineSubspace.direction_bot, finrank_bot] at hP
    omega
  obtain ⟨p₀, hp₀⟩ := hne
  have h3 : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  have hsum := Submodule.finrank_add_finrank_orthogonal P.direction
  have hperp : Module.finrank ℝ P.directionᗮ = 1 := by omega
  have hne' : P.directionᗮ ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hperp; omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
  set n := ‖v‖⁻¹ • v
  have hn : ‖n‖ = 1 := l15_unit hv0
  have hnmem : n ∈ P.directionᗮ := Submodule.smul_mem _ _ hv
  have hle : P.direction ≤ (ℝ ∙ n)ᗮ := by
    intro x hx
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact Submodule.inner_right_of_mem_orthogonal hx hnmem
  have hn0 : n ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  have hdim : Module.finrank ℝ (ℝ ∙ n)ᗮ = 2 := by
    have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ n)
    rw [finrank_span_singleton hn0] at this; omega
  have heq : P.direction = (ℝ ∙ n)ᗮ := Submodule.eq_of_le_of_finrank_eq hle (by rw [hP, hdim])
  refine ⟨p₀, n, hn, hp₀, heq, fun X => ?_⟩
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hp₀, heq,
    Submodule.mem_orthogonal_singleton_iff_inner_left, vsub_eq_sub]

/-- The angle between the axis and the plane.-/
lemma l15_planeAxisAngle {u n : E3} (hu : u ≠ 0) (hn : ‖n‖ = 1) (P : AffineSubspace ℝ E3)
    (hdir : P.direction = (ℝ ∙ n)ᗮ) :
    Real.cos (planeAxisAngle u P) = √(1 - inner ℝ (‖u‖⁻¹ • u) n ^ 2) ∧
      0 ≤ planeAxisAngle u P ∧ planeAxisAngle u P ≤ π / 2 := by
  obtain ⟨e, he_def⟩ : ∃ e : E3, e = ‖u‖⁻¹ • u := ⟨_, rfl⟩
  rw [← he_def]
  have he : ‖e‖ = 1 := by rw [he_def]; exact l15_unit hu
  have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hue : u = ‖u‖ • e := by rw [he_def, smul_smul, mul_inv_cancel₀ hnu.ne', one_smul]
  have hnu' : inner ℝ n u = ‖u‖ * inner ℝ e n := by
    rw [hue, real_inner_smul_right, real_inner_comm, norm_smul, he, Real.norm_eq_abs,
      abs_of_pos hnu, mul_one]
  have hproj : P.direction.starProjection u = ‖u‖ • (e - inner ℝ e n • n) := by
    rw [hdir, Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton, hn]
    simp only [one_pow, RCLike.ofReal_one, div_one]
    rw [hnu', smul_sub, smul_smul, ← hue]
  have hang : planeAxisAngle u P = InnerProductGeometry.angle e (e - inner ℝ e n • n) := by
    unfold planeAxisAngle
    rw [hproj, angle_smul_right_of_pos _ _ hnu]
    conv_lhs => rw [hue]
    rw [angle_smul_left_of_pos _ _ hnu]
  have hw2 := Dandelin.norm_sub_inner_smul_sq he hn
  have hcos : Real.cos (planeAxisAngle u P) = √(1 - inner ℝ e n ^ 2) := by
    rw [hang, cos_angle, he, one_mul]
    have hin : inner ℝ e (e - inner ℝ e n • n) = 1 - inner ℝ e n ^ 2 := by
      rw [inner_sub_right, real_inner_smul_right, l15_inner_self e, he]; ring
    rw [hin, show ‖e - inner ℝ e n • n‖ = √(1 - inner ℝ e n ^ 2) by
      rw [← hw2, Real.sqrt_sq (norm_nonneg _)], Real.div_sqrt]
  refine ⟨hcos, InnerProductGeometry.angle_nonneg _ _, ?_⟩
  by_contra h
  push_neg at h
  have : Real.cos (planeAxisAngle u P) < 0 := by
    rw [hang] at h ⊢
    exact Real.cos_neg_of_pi_div_two_lt_of_lt h (by
      linarith [InnerProductGeometry.angle_le_pi e (e - inner ℝ e n • n), Real.pi_pos])
  rw [hcos] at this
  linarith [Real.sqrt_nonneg (1 - inner ℝ e n ^ 2)]

/-- Writer cone = repository double cone with unit axis.-/
lemma l15_cone_eq {V u : E3} (hu : u ≠ 0) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ π) (X : E3) :
    X ∈ cone V u α ↔ X ∈ Dandelin.cone2 V (‖u‖⁻¹ • u) (Real.cos α) := by
  have he : ‖‖u‖⁻¹ • u‖ = 1 := l15_unit hu
  have hpos : 0 < ‖u‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hu)
  by_cases hX : X = V
  · subst hX
    simp only [cone, Set.mem_ofPred_eq, true_or, true_iff]
    show inner ℝ (X - X) _ ^ 2 = _ * ‖X - X‖ ^ 2
    simp
  · rw [Dandelin.mem_cone2_iff_angle he ⟨hα0, hα1⟩ hX, angle_smul_right_of_pos _ _ hpos]
    simp only [cone, Set.mem_ofPred_eq, hX, false_or, vsub_eq_sub]

/-- Generators, parametrised by a unit direction.-/
lemma l15_generator_param {V u : E3} (hu : u ≠ 0) {α : ℝ} {g : AffineSubspace ℝ E3}
    (hg : IsGenerator V u α g) :
    ∃ w : E3, ‖w‖ = 1 ∧ inner ℝ w (‖u‖⁻¹ • u) = Real.cos α ∧
      ∀ X, X ∈ g ↔ ∃ t : ℝ, X = V + t • w := by
  obtain ⟨w, hw0, hwa, rfl⟩ := hg
  have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw0
  refine ⟨‖w‖⁻¹ • w, l15_unit hw0, ?_, fun X => ?_⟩
  · have he : ‖‖u‖⁻¹ • u‖ = 1 := l15_unit hu
    have := cos_angle (‖w‖⁻¹ • w) (‖u‖⁻¹ • u)
    rw [angle_smul_left_of_pos _ _ (inv_pos.2 hnw),
      angle_smul_right_of_pos _ _ (inv_pos.2 (norm_pos_iff.2 hu)), hwa] at this
    rw [this, l15_unit hw0, he, mul_one, div_one]
  · rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    constructor
    · rintro ⟨r, rfl⟩
      refine ⟨r * ‖w‖, ?_⟩
      rw [AffineMap.lineMap_apply, vadd_eq_add, vadd_eq_add, vsub_eq_sub, smul_smul,
        mul_assoc, mul_inv_cancel₀ hnw.ne', mul_one]
      abel
    · rintro ⟨t, rfl⟩
      refine ⟨t * ‖w‖⁻¹, ?_⟩
      rw [AffineMap.lineMap_apply, vadd_eq_add, vadd_eq_add, vsub_eq_sub, smul_smul]
      abel

/-- Every unit direction with `⟪w, û⟫ = cos α` gives a generator.-/
lemma l15_generator_of_unit {V u w : E3} (hu : u ≠ 0) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ π)
    (hw : ‖w‖ = 1) (hwu : inner ℝ w (‖u‖⁻¹ • u) = Real.cos α) :
    IsGenerator V u α line[ℝ, V, w +ᵥ V] := by
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; norm_num at hw
  refine ⟨w, hw0, ?_, rfl⟩
  rw [← angle_smul_right_of_pos w u (inv_pos.2 (norm_pos_iff.2 hu))]
  apply Real.injOn_cos ⟨InnerProductGeometry.angle_nonneg _ _,
    InnerProductGeometry.angle_le_pi _ _⟩ ⟨hα0, hα1⟩
  rw [cos_angle, hw, l15_unit hu, hwu]; ring

/-- Plane–sphere: a singleton intersection means tangency at the foot of the centre.-/
lemma l15_plane_sphere {P : AffineSubspace ℝ E3} {p₀ n : E3} (hn : ‖n‖ = 1)
    (hPn : ∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0) (Q F : E3) (r : ℝ) (hr : 0 < r)
    (h : (P : Set E3) ∩ Metric.sphere Q r = {F}) :
    |inner ℝ (Q - p₀) n| = r ∧ F = Q - inner ℝ (Q - p₀) n • n := by
  set h0 := inner ℝ (Q - p₀) n
  set F₀ := Q - h0 • n
  have hnn : inner ℝ n n = 1 := by rw [l15_inner_self, hn]; norm_num
  have hF₀P : F₀ ∈ P := by
    rw [hPn]; simp only [F₀]
    rw [show Q - h0 • n - p₀ = (Q - p₀) - h0 • n by abel, inner_sub_left, real_inner_smul_left,
      hnn]; simp [h0]
  have pyth : ∀ X ∈ P, ‖X - Q‖ ^ 2 = ‖X - F₀‖ ^ 2 + h0 ^ 2 := by
    intro X hX
    rw [hPn] at hX
    have hXF : inner ℝ (X - F₀) n = 0 := by
      simp only [F₀]
      rw [show X - (Q - h0 • n) = (X - p₀) - (Q - p₀) + h0 • n by abel, inner_add_left,
        inner_sub_left, hX, real_inner_smul_left, hnn]; simp [h0]
    rw [show X - Q = (X - F₀) - h0 • n by simp only [F₀]; abel, norm_sub_sq_real,
      real_inner_smul_right, hXF, norm_smul, hn, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hFmem : F ∈ (P : Set E3) ∩ Metric.sphere Q r := by rw [h]; rfl
  have hFP : F ∈ P := hFmem.1
  have hFS : ‖F - Q‖ = r := by have := hFmem.2; rwa [Metric.mem_sphere, dist_eq_norm] at this
  have hpF := pyth F hFP
  rw [hFS] at hpF
  have hle : h0 ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg ‖F - F₀‖]
  have heq : h0 ^ 2 = r ^ 2 := by
    by_contra hne
    have hlt : h0 ^ 2 < r ^ 2 := lt_of_le_of_ne hle hne
    obtain ⟨e, he, heS⟩ := Dandelin.exists_unit_orth ({n} : Finset E3)
      (by rw [Finset.card_singleton, finrank_euclideanSpace_fin]; norm_num)
    have hen : inner ℝ e n = 0 := heS n (Finset.mem_singleton_self n)
    set ρ := √(r ^ 2 - h0 ^ 2)
    have hρ : 0 < ρ := Real.sqrt_pos.2 (by linarith)
    have hρ2 : ρ ^ 2 = r ^ 2 - h0 ^ 2 := Real.sq_sqrt (by linarith)
    have mem : ∀ σ : ℝ, σ ^ 2 = 1 → F₀ + (σ * ρ) • e ∈ (P : Set E3) ∩ Metric.sphere Q r := by
      intro σ hσ
      have hP' : F₀ + (σ * ρ) • e ∈ P := by
        rw [hPn]
        rw [show F₀ + (σ * ρ) • e - p₀ = (F₀ - p₀) + (σ * ρ) • e by abel, inner_add_left,
          real_inner_smul_left, hen, mul_zero, add_zero]
        exact (hPn F₀).1 hF₀P
      refine ⟨hP', ?_⟩
      rw [Metric.mem_sphere, dist_eq_norm]
      have := pyth _ hP'
      rw [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs, mul_pow, hσ,
        one_mul, hρ2] at this
      have h2 : ‖F₀ + (σ * ρ) • e - Q‖ ^ 2 = r ^ 2 := by linarith
      exact (pow_left_inj₀ (norm_nonneg _) hr.le two_ne_zero).1 h2
    have m1 := mem 1 (by norm_num)
    have m2 := mem (-1) (by norm_num)
    rw [h] at m1 m2
    have : F₀ + (1 * ρ) • e = F₀ + (-1 * ρ) • e := by rw [m1, m2]
    have h2 : (2 * ρ) • e = 0 := by
      have := congrArg (fun x => x - F₀) this
      simp only [add_sub_cancel_left] at this
      rw [show (2 * ρ) • e = (1 * ρ) • e - (-1 * ρ) • e by rw [← sub_smul]; ring_nf, this,
        sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · linarith
    · rw [h3, norm_zero] at he; norm_num at he
  have habs : |h0| = r := by rw [← Real.sqrt_sq_eq_abs, heq, Real.sqrt_sq hr.le]
  refine ⟨habs, ?_⟩
  have : ‖F - F₀‖ ^ 2 = 0 := by linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))

/-- Converse: distance = radius gives the singleton intersection at the foot.-/
lemma l15_plane_sphere_conv {P : AffineSubspace ℝ E3} {p₀ n : E3} (hn : ‖n‖ = 1)
    (hPn : ∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0) (Q : E3) (r : ℝ)
    (h : |inner ℝ (Q - p₀) n| = r) :
    (P : Set E3) ∩ Metric.sphere Q r = {Q - inner ℝ (Q - p₀) n • n} := by
  set h0 := inner ℝ (Q - p₀) n
  set F₀ := Q - h0 • n
  have hnn : inner ℝ n n = 1 := by rw [l15_inner_self, hn]; norm_num
  have hF₀P : F₀ ∈ P := by
    rw [hPn]; simp only [F₀]
    rw [show Q - h0 • n - p₀ = (Q - p₀) - h0 • n by abel, inner_sub_left, real_inner_smul_left,
      hnn]; simp [h0]
  have pyth : ∀ X ∈ P, ‖X - Q‖ ^ 2 = ‖X - F₀‖ ^ 2 + h0 ^ 2 := by
    intro X hX
    rw [hPn] at hX
    have hXF : inner ℝ (X - F₀) n = 0 := by
      simp only [F₀]
      rw [show X - (Q - h0 • n) = (X - p₀) - (Q - p₀) + h0 • n by abel, inner_add_left,
        inner_sub_left, hX, real_inner_smul_left, hnn]; simp [h0]
    rw [show X - Q = (X - F₀) - h0 • n by simp only [F₀]; abel, norm_sub_sq_real,
      real_inner_smul_right, hXF, norm_smul, hn, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hr2 : h0 ^ 2 = r ^ 2 := by rw [← h, sq_abs]
  ext X
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Metric.mem_sphere, dist_eq_norm,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hX, hXr⟩
    have := pyth X hX
    rw [hXr, hr2] at this
    have : ‖X - F₀‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))
  · rintro rfl
    refine ⟨hF₀P, ?_⟩
    have := pyth F₀ hF₀P
    rw [sub_self, norm_zero, hr2] at this
    have hr0 : 0 ≤ r := h ▸ abs_nonneg _
    exact (pow_left_inj₀ (norm_nonneg _) hr0 two_ne_zero).1 (by linarith)

lemma l15_line_mem (V w X : E3) : X ∈ line[ℝ, V, w +ᵥ V] ↔ ∃ t : ℝ, X = V + t • w := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨r, ?_⟩
    rw [AffineMap.lineMap_apply, vadd_eq_add, vadd_eq_add, vsub_eq_sub, add_sub_cancel_right]
    abel
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    rw [AffineMap.lineMap_apply, vadd_eq_add, vadd_eq_add, vsub_eq_sub, add_sub_cancel_right]
    abel

/-- Line–sphere: for a line `V + t w` (`‖w‖ = 1`) and a sphere `(Q, r)`, `r > 0`, the
intersection is a singleton iff `‖Q - V‖² - ⟪Q - V, w⟫² = r²`.-/
lemma l15_line_sphere (V w Q : E3) (hw : ‖w‖ = 1) (r : ℝ) (hr : 0 < r) (g : Set E3)
    (hg : ∀ X, X ∈ g ↔ ∃ t : ℝ, X = V + t • w) :
    (∃ x, g ∩ Metric.sphere Q r = {x}) ↔ ‖Q - V‖ ^ 2 - inner ℝ (Q - V) w ^ 2 = r ^ 2 := by
  set a := inner ℝ (Q - V) w
  set D := r ^ 2 - (‖Q - V‖ ^ 2 - a ^ 2)
  have key : ∀ t : ℝ, V + t • w ∈ Metric.sphere Q r ↔ (t - a) ^ 2 = D := by
    intro t
    rw [Metric.mem_sphere, dist_eq_norm, show V + t • w - Q = t • w - (Q - V) by abel,
      ← (pow_left_inj₀ (norm_nonneg _) hr.le two_ne_zero), norm_sub_sq_real,
      real_inner_smul_left, norm_smul, hw, Real.norm_eq_abs, mul_one, sq_abs,
      real_inner_comm]
    simp only [D, a]
    constructor <;> intro h <;> nlinarith [h]
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; norm_num at hw
  constructor
  · rintro ⟨x, hx⟩
    have hxm : x ∈ g ∩ Metric.sphere Q r := by rw [hx]; rfl
    obtain ⟨t₀, rfl⟩ := (hg x).1 hxm.1
    have hD : (t₀ - a) ^ 2 = D := (key t₀).1 hxm.2
    by_contra hne
    have hDpos : 0 < D := by
      rcases (sq_nonneg (t₀ - a)).eq_or_lt with h | h
      · exfalso; apply hne; simp only [D] at hD; linarith
      · linarith
    have mem : ∀ t, (t - a) ^ 2 = D → V + t • w = V + t₀ • w := by
      intro t ht
      have : V + t • w ∈ g ∩ Metric.sphere Q r := ⟨(hg _).2 ⟨t, rfl⟩, (key t).2 ht⟩
      rw [hx] at this; exact this
    have e1 := mem (a + √D) (by rw [add_sub_cancel_left, Real.sq_sqrt hDpos.le])
    have e2 := mem (a - √D) (by rw [sub_sub_cancel_left, neg_sq, Real.sq_sqrt hDpos.le])
    have : (a + √D) • w = (a - √D) • w := by
      have := e1.trans e2.symm
      exact add_left_cancel this
    have h3 : (2 * √D) • w = 0 := by
      rw [show (2 * √D) = (a + √D) - (a - √D) by ring, sub_smul, this, sub_self]
    rcases smul_eq_zero.1 h3 with h4 | h4
    · have := Real.sqrt_pos.2 hDpos; linarith
    · exact hw0 h4
  · intro h
    have hD : D = 0 := by simp only [D]; linarith
    refine ⟨V + a • w, ?_⟩
    ext X
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hX, hXs⟩
      obtain ⟨t, rfl⟩ := (hg X).1 hX
      have := (key t).1 hXs
      rw [hD] at this
      have : t = a := by nlinarith [sq_nonneg (t - a)]
      rw [this]
    · rintro rfl
      exact ⟨(hg _).2 ⟨a, rfl⟩, (key a).2 (by rw [sub_self, hD]; ring)⟩

/-- Setup constants for the cone.-/
lemma l15_ks {α : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2) :
    0 < Real.cos α ∧ 0 < Real.sin α ∧ Real.cos α ^ 2 + Real.sin α ^ 2 = 1 :=
  ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith, hα1⟩,
    Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos]), Real.cos_sq_add_sin_sq α⟩

/-- **Classification of spheres tangent to the cone along a circle** (writer's notion): they are
exactly the axis spheres `(V + d û, |d| sin α)`, `d ≠ 0`.-/
lemma l15_tangent_cone_iff {V u : E3} (hu : u ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2)
    (S : Sphere E3) (C : Set E3) :
    TangentToConeAlong V u α S C ↔
      (∃ d : ℝ, d ≠ 0 ∧ S.center = V + d • (‖u‖⁻¹ • u) ∧ S.radius = |d| * Real.sin α) ∧
        C = Metric.sphere S.center S.radius ∩ cone V u α := by
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  obtain ⟨e, he_def⟩ : ∃ e : E3, e = ‖u‖⁻¹ • u := ⟨_, rfl⟩
  rw [← he_def]
  have he : ‖e‖ = 1 := by rw [he_def]; exact l15_unit hu
  have hee : inner ℝ e e = 1 := by rw [l15_inner_self, he]; norm_num
  have hαI0 : 0 ≤ α := hα0.le
  have hαI1 : α ≤ π := by linarith [Real.pi_pos]
  constructor
  · rintro ⟨hr, hgen, hC⟩
    refine ⟨?_, hC⟩
    obtain ⟨q, hq_def⟩ : ∃ q : E3, q = S.center - V := ⟨_, rfl⟩
    obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = inner ℝ q e := ⟨_, rfl⟩
    have cond : ∀ w : E3, ‖w‖ = 1 → inner ℝ w e = Real.cos α →
        ‖q‖ ^ 2 - inner ℝ q w ^ 2 = S.radius ^ 2 := by
      intro w hw hwe
      have hg := l15_generator_of_unit (V := V) hu hαI0 hαI1 hw (by rw [← he_def]; exact hwe)
      rw [hq_def]
      exact (l15_line_sphere V w S.center hw S.radius hr _ (fun X => l15_line_mem V w X)).1
        (hgen _ hg)
    obtain ⟨v, hv_def⟩ : ∃ v : E3, v = q - a • e := ⟨_, rfl⟩
    have hve : inner ℝ v e = 0 := by
      rw [hv_def, inner_sub_left, real_inner_smul_left, hee, ha_def]; ring
    have hv0 : v = 0 := by
      by_contra hv0
      obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = ‖v‖ := ⟨_, rfl⟩
      have hb : 0 < b := by rw [hb_def]; exact norm_pos_iff.2 hv0
      obtain ⟨f, hf_def⟩ : ∃ f : E3, f = b⁻¹ • v := ⟨_, rfl⟩
      have hf : ‖f‖ = 1 := by rw [hf_def, hb_def]; exact l15_unit hv0
      have hfe : inner ℝ f e = 0 := by rw [hf_def, real_inner_smul_left, hve, mul_zero]
      have hqv : q = a • e + b • f := by
        rw [hf_def, smul_smul, mul_inv_cancel₀ hb.ne', one_smul, hv_def]; abel
      have hqe : inner ℝ q e = a := ha_def.symm
      have hqf : inner ℝ q f = b := by
        rw [hqv, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_comm,
          hfe, l15_inner_self f, hf]; ring
      obtain ⟨g, hg, hgS⟩ := Dandelin.exists_unit_orth ({e, f} : Finset E3)
        (by
          calc ({e, f} : Finset E3).card ≤ 2 := Finset.card_le_two
            _ < Module.finrank ℝ E3 := by rw [finrank_euclideanSpace_fin]; norm_num)
      have hge : inner ℝ g e = 0 := hgS e (by simp)
      have hgf : inner ℝ g f = 0 := hgS f (by simp)
      have hqg : inner ℝ q g = 0 := by
        rw [hqv, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_comm g e,
          real_inner_comm g f] at *
        rw [hge, hgf]; ring
      obtain ⟨w1, w1e⟩ := Dandelin.gen_dir (k := Real.cos α) (s := Real.sin α) he hf hfe hks
      obtain ⟨w2, w2e⟩ := Dandelin.gen_dir (k := Real.cos α) (s := -Real.sin α) he hf hfe
        (by rw [neg_sq]; exact hks)
      obtain ⟨w3, w3e⟩ := Dandelin.gen_dir (k := Real.cos α) (s := Real.sin α) he hg hge hks
      have c1 := cond _ w1 w1e
      have c2 := cond _ w2 w2e
      have c3 := cond _ w3 w3e
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hqe, hqf] at c1 c2
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hqe, hqg] at c3
      have h2 : (b * Real.sin α) ^ 2 = 0 := by linear_combination (-1 / 2 : ℝ) * (c1 + c2 - 2 * c3)
      have h3 : b * Real.sin α = 0 := pow_eq_zero_iff two_ne_zero |>.1 h2
      have := mul_pos hb hs
      linarith
    have hq : q = a • e := by rw [hv_def] at hv0; exact sub_eq_zero.1 hv0
    obtain ⟨w1, w1n, w1e⟩ : ∃ w : E3, ‖w‖ = 1 ∧ inner ℝ w e = Real.cos α := by
      obtain ⟨f, hf, hfS⟩ := Dandelin.exists_unit_orth ({e} : Finset E3)
        (by rw [Finset.card_singleton, finrank_euclideanSpace_fin]; norm_num)
      exact ⟨_, Dandelin.gen_dir he hf (hfS e (by simp)) hks⟩
    have c1 := cond _ w1n w1e
    rw [hq, real_inner_smul_left, real_inner_comm, w1e, norm_smul, he, Real.norm_eq_abs,
      mul_one, sq_abs] at c1
    have hr2 : S.radius ^ 2 = (|a| * Real.sin α) ^ 2 := by
      rw [mul_pow, sq_abs]; linear_combination (-1 : ℝ) * c1 - a ^ 2 * hks
    have hrad : S.radius = |a| * Real.sin α :=
      (pow_left_inj₀ hr.le (by positivity) two_ne_zero).1 hr2
    refine ⟨a, ?_, by rw [← hq, hq_def]; abel, hrad⟩
    rintro rfl
    rw [abs_zero, zero_mul] at hrad; linarith
  · rintro ⟨⟨d, hd, hc, hr⟩, hC⟩
    have hr0 : 0 < S.radius := by rw [hr]; exact mul_pos (abs_pos.2 hd) hs
    refine ⟨hr0, fun g hg => ?_, hC⟩
    obtain ⟨w, hw, hwe, hgw⟩ := l15_generator_param hu hg
    rw [← he_def] at hwe
    refine (l15_line_sphere V w S.center hw S.radius hr0 g hgw).2 ?_
    rw [hc, add_sub_cancel_left, real_inner_smul_left, real_inner_comm, hwe, norm_smul, he,
      Real.norm_eq_abs, mul_one, hr, mul_pow, sq_abs]
    rw [mul_pow, sq_abs]; linear_combination (-d ^ 2) * hks

/-! ### Setup lemmas -/

lemma l15_vnot {P : AffineSubspace ℝ E3} {p₀ n V : E3}
    (hPn : ∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0) (hVP : V ∉ P) :
    inner ℝ (p₀ - V) n ≠ 0 := by
  intro h; apply hVP
  rw [hPn, show V - p₀ = -(p₀ - V) by abel, inner_neg_left, h, neg_zero]

lemma l15_m_sq_le {e n : E3} (he : ‖e‖ = 1) (hn : ‖n‖ = 1) : inner ℝ e n ^ 2 ≤ 1 := by
  have := abs_real_inner_le_norm e n
  rw [he, hn, mul_one] at this
  nlinarith [abs_nonneg (inner ℝ e n), sq_abs (inner ℝ e n)]

lemma l15_regime_ell {α β m : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2) (hβ0 : 0 ≤ β) (hβ1 : β ≤ π / 2)
    (hm1 : m ^ 2 ≤ 1) (hcos : Real.cos β = √(1 - m ^ 2)) (h : α < β) : Real.sin α < |m| := by
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  have h1 : Real.cos β < Real.cos α :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hα0.le (by linarith [Real.pi_pos]) h
  rw [hcos] at h1
  have h2 : 1 - m ^ 2 < Real.cos α ^ 2 := (Real.sqrt_lt' hk).1 h1
  by_contra h3; push_neg at h3
  nlinarith [abs_nonneg m, sq_abs m]

lemma l15_regime_hyp {α β m : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2) (hβ0 : 0 ≤ β)
    (hm1 : m ^ 2 ≤ 1) (hcos : Real.cos β = √(1 - m ^ 2)) (h : β < α) : |m| < Real.sin α := by
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  have h1 : Real.cos α < Real.cos β :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hβ0 (by linarith [Real.pi_pos]) h
  rw [hcos] at h1
  have h2 : Real.cos α ^ 2 < 1 - m ^ 2 := (Real.lt_sqrt hk.le).1 h1
  by_contra h3; push_neg at h3
  nlinarith [abs_nonneg m, sq_abs m]

lemma l15_regime_par {α β m : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2)
    (hm1 : m ^ 2 ≤ 1) (hcos : Real.cos β = √(1 - m ^ 2)) (h : β = α) : |m| = Real.sin α := by
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  rw [h] at hcos
  have h2 : Real.cos α ^ 2 = 1 - m ^ 2 := by rw [hcos, Real.sq_sqrt (by linarith)]
  have : |m| ^ 2 = Real.sin α ^ 2 := by rw [sq_abs]; linarith
  exact (pow_left_inj₀ (abs_nonneg m) hs.le two_ne_zero).1 this

lemma l15_noncirc {β m : ℝ} (hcos : Real.cos β = √(1 - m ^ 2)) (h0 : 0 ≤ β) (h : β < π / 2) :
    m ^ 2 < 1 := by
  have : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith, h⟩
  rw [hcos] at this
  have := Real.sqrt_pos.1 this
  linarith

/-- The axis sphere with parameter `d`.-/
def l15_S (V e : E3) (s d : ℝ) : Sphere E3 := ⟨V + d • e, |d| * s⟩

/-- Data of a writer Dandelin configuration.-/
lemma l15_dandelin_data {V u : E3} (hu : u ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2)
    {P : AffineSubspace ℝ E3} {p₀ n : E3} (hn : ‖n‖ = 1)
    (hPn : ∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0) {e : E3} (he_def : e = ‖u‖⁻¹ • u)
    (S : Sphere E3) (C : Set E3) (F : E3)
    (hC : TangentToConeAlong V u α S C) (hF : TangentToPlaneAt P S F) :
    ∃ d : ℝ, d ≠ 0 ∧ S = l15_S V e (Real.sin α) d ∧
      |d * inner ℝ e n - inner ℝ (p₀ - V) n| = |d| * Real.sin α ∧
      F = (V + d • e) - inner ℝ ((V + d • e) - p₀) n • n ∧
      C = Metric.sphere (V + d • e) (|d| * Real.sin α) ∩ cone V u α := by
  have hr := hC.1
  obtain ⟨⟨d, hd, hc, hrad⟩, hCeq⟩ := (l15_tangent_cone_iff hu hα0 hα1 S C).1 hC
  rw [← he_def] at hc
  obtain ⟨habs, hFeq⟩ := l15_plane_sphere hn hPn S.center F S.radius hr hF
  rw [hc, hrad, Dandelin.inner_center_sub] at habs
  refine ⟨d, hd, EuclideanGeometry.Sphere.ext hc hrad, habs, by rw [hFeq, hc], ?_⟩
  rw [hCeq, hc, hrad]

/-- Conversely, every parameter solving the tangency equation gives a Dandelin sphere.-/
lemma l15_mk_dandelin {V u : E3} (hu : u ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2)
    {P : AffineSubspace ℝ E3} {p₀ n : E3} (hn : ‖n‖ = 1)
    (hPn : ∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0) {e : E3} (he_def : e = ‖u‖⁻¹ • u)
    (d : ℝ) (hd : d ≠ 0)
    (htan : |d * inner ℝ e n - inner ℝ (p₀ - V) n| = |d| * Real.sin α) :
    IsDandelinSphere V u α P (l15_S V e (Real.sin α) d) := by
  refine ⟨⟨_, (l15_tangent_cone_iff hu hα0 hα1 _ _).2 ⟨⟨d, hd, by rw [he_def]; rfl, rfl⟩, rfl⟩⟩,
    _, l15_plane_sphere_conv hn hPn _ _ ?_⟩
  show |inner ℝ ((V + d • e) - p₀) n| = |d| * Real.sin α
  rw [Dandelin.inner_center_sub]; exact htan

lemma l15_two_roots {m c s d d₁ d₂ : ℝ} (hL : m ^ 2 - s ^ 2 ≠ 0) (hne : d₁ ≠ d₂)
    (h : |d * m - c| = |d| * s) (h₁ : |d₁ * m - c| = |d₁| * s) (h₂ : |d₂ * m - c| = |d₂| * s) :
    d = d₁ ∨ d = d₂ := by
  have sq : ∀ x : ℝ, |x * m - c| = |x| * s → (x * m - c) ^ 2 = x ^ 2 * s ^ 2 := by
    intro x hx
    have := congrArg (· ^ 2) hx
    simp only [sq_abs, mul_pow] at this
    exact this
  have q := sq d h; have q₁ := sq d₁ h₁; have q₂ := sq d₂ h₂
  have e1 : (d₁ - d₂) * ((m ^ 2 - s ^ 2) * (d₁ + d₂) - 2 * m * c) = 0 := by
    linear_combination q₁ - q₂
  have e1' : (m ^ 2 - s ^ 2) * (d₁ + d₂) - 2 * m * c = 0 := by
    rcases mul_eq_zero.1 e1 with h' | h'
    · exact absurd (sub_eq_zero.1 h') hne
    · exact h'
  have e2 : (d - d₁) * ((m ^ 2 - s ^ 2) * (d + d₁) - 2 * m * c) = 0 := by
    linear_combination q - q₁
  rcases mul_eq_zero.1 e2 with h' | h'
  · exact Or.inl (sub_eq_zero.1 h')
  · right
    have : (m ^ 2 - s ^ 2) * (d - d₂) = 0 := by linear_combination h' - e1'
    rcases mul_eq_zero.1 this with h'' | h''
    · exact absurd h'' hL
    · exact sub_eq_zero.1 h''

lemma l15_sOppSide {P : AffineSubspace ℝ E3} {p₀ n : E3} (hp₀ : p₀ ∈ P)
    (hPn : ∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0) (x y : E3)
    (h : inner ℝ (x - p₀) n * inner ℝ (y - p₀) n < 0) : P.SOppSide x y := by
  have hx : inner ℝ (x - p₀) n ≠ 0 := by intro h0; rw [h0, zero_mul] at h; exact lt_irrefl 0 h
  have hy : inner ℝ (y - p₀) n ≠ 0 := by intro h0; rw [h0, mul_zero] at h; exact lt_irrefl 0 h
  rw [AffineSubspace.sOppSide_iff_exists_left hp₀]
  set t := -inner ℝ (y - p₀) n / inner ℝ (x - p₀) n
  have ht : 0 ≤ t := by
    have : 0 < -inner ℝ (y - p₀) n * inner ℝ (x - p₀) n := by linarith
    have h2 : t = -inner ℝ (y - p₀) n * inner ℝ (x - p₀) n / (inner ℝ (x - p₀) n) ^ 2 := by
      simp only [t]; field_simp
    rw [h2]; positivity
  refine ⟨fun hm => hx ((hPn x).1 hm), fun hm => hy ((hPn y).1 hm), y + t • (x - p₀), ?_, ?_⟩
  · rw [hPn, show y + t • (x - p₀) - p₀ = (y - p₀) + t • (x - p₀) by abel, inner_add_left,
      real_inner_smul_left]
    simp only [t]; field_simp; ring
  · rw [vsub_eq_sub, vsub_eq_sub, add_sub_cancel_left]
    exact SameRay.sameRay_nonneg_smul_right _ ht

lemma l15_inside_pos {V u e : E3} (hu : u ≠ 0) (he_def : e = ‖u‖⁻¹ • u) {α d : ℝ}
    (hα0 : 0 < α) (hd : 0 < d) : InsideNappe V u α 1 (V + d • e) := by
  have hpos : 0 < ‖u‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hu)
  have he0 : e ≠ 0 := by
    rw [he_def]; exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hu)) hu
  refine ⟨fun h => ?_, ?_⟩
  · have : d • e = 0 := by
      have := congrArg (· - V) h; simpa using this
    rcases smul_eq_zero.1 this with h' | h'
    · linarith
    · exact he0 h'
  · rw [one_smul, vsub_eq_sub, add_sub_cancel_left, InnerProductGeometry.angle_smul_left_of_pos _ _ hd, he_def,
      InnerProductGeometry.angle_smul_left_of_pos _ _ hpos, InnerProductGeometry.angle_self hu]
    exact hα0

lemma l15_inside_neg {V u e : E3} (hu : u ≠ 0) (he_def : e = ‖u‖⁻¹ • u) {α d : ℝ}
    (hα0 : 0 < α) (hd : d < 0) : InsideNappe V u α (-1) (V + d • e) := by
  have hpos : 0 < ‖u‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hu)
  have he0 : e ≠ 0 := by
    rw [he_def]; exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hu)) hu
  refine ⟨fun h => ?_, ?_⟩
  · have : d • e = 0 := by
      have := congrArg (· - V) h; simpa using this
    rcases smul_eq_zero.1 this with h' | h'
    · linarith
    · exact he0 h'
  · rw [vsub_eq_sub, add_sub_cancel_left, show d • e = -((-d) • e) by rw [neg_smul, neg_neg],
      neg_one_smul, InnerProductGeometry.angle_neg_neg, InnerProductGeometry.angle_smul_left_of_pos _ _ (by linarith),
      he_def, InnerProductGeometry.angle_smul_left_of_pos _ _ hpos, InnerProductGeometry.angle_self hu]
    exact hα0

/-- A point of a generator lying on the axis sphere with parameter `d`.-/
lemma l15_gen_on_sphere {V w e : E3} {k s d t : ℝ} (hw : ‖w‖ = 1) (he : ‖e‖ = 1)
    (hwe : inner ℝ w e = k) (hks : k ^ 2 + s ^ 2 = 1)
    (h : V + t • w ∈ Metric.sphere (V + d • e) (|d| * s)) : t = d * k := by
  rw [Metric.mem_sphere, dist_eq_norm, show V + t • w - (V + d • e) = t • w - d • e by abel] at h
  have h2 : ‖t • w - d • e‖ ^ 2 = (|d| * s) ^ 2 := by rw [h]
  rw [norm_sub_sq_real, norm_smul, norm_smul, hw, he, real_inner_smul_left,
    real_inner_smul_right, hwe, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one, mul_pow,
    sq_abs] at h2
  rw [sq_abs] at h2
  have : (t - d * k) ^ 2 = 0 := by linear_combination h2 + d ^ 2 * hks
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

/-- Generator segment between two axis spheres.-/
lemma l15_gen_segment {V u : E3} (hu : u ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2)
    {e : E3} (he_def : e = ‖u‖⁻¹ • u) (g : AffineSubspace ℝ E3) (hg : IsGenerator V u α g)
    (d₁ d₂ : ℝ) (Y₁ Y₂ : E3) (hY₁ : Y₁ ∈ (g : Set E3)) (hY₂ : Y₂ ∈ (g : Set E3))
    (hS₁ : Y₁ ∈ Metric.sphere (V + d₁ • e) (|d₁| * Real.sin α))
    (hS₂ : Y₂ ∈ Metric.sphere (V + d₂ • e) (|d₂| * Real.sin α)) :
    dist Y₁ Y₂ = |d₁ - d₂| * Real.cos α := by
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  obtain ⟨w, hw, hwe, hgw⟩ := l15_generator_param hu hg
  rw [← he_def] at hwe
  have he : ‖e‖ = 1 := by rw [he_def]; exact l15_unit hu
  obtain ⟨t₁, rfl⟩ := (hgw Y₁).1 hY₁
  obtain ⟨t₂, rfl⟩ := (hgw Y₂).1 hY₂
  have e1 := l15_gen_on_sphere hw he hwe hks hS₁
  have e2 := l15_gen_on_sphere hw he hwe hks hS₂
  rw [dist_eq_norm, show V + t₁ • w - (V + t₂ • w) = (t₁ - t₂) • w by rw [sub_smul]; abel,
    norm_smul, hw, mul_one, e1, e2, Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_pos hk]

/-- Unit vector along `F₂ - F₁` in the plane (any unit plane vector if `F₁ = F₂`).-/
lemma l15_plane_dir {p₀ n F₁ F₂ : E3} (hn : ‖n‖ = 1) (h₁ : inner ℝ (F₁ - p₀) n = 0)
    (h₂ : inner ℝ (F₂ - p₀) n = 0) :
    ∃ v : E3, ‖v‖ = 1 ∧ inner ℝ v n = 0 ∧ F₂ - F₁ = ‖F₂ - F₁‖ • v := by
  have h12 : inner ℝ (F₂ - F₁) n = 0 := by
    rw [show F₂ - F₁ = (F₂ - p₀) - (F₁ - p₀) by abel, inner_sub_left, h₁, h₂, sub_zero]
  by_cases h : F₂ - F₁ = 0
  · obtain ⟨v, hv, hvS⟩ := Dandelin.exists_unit_orth ({n} : Finset E3)
      (by rw [Finset.card_singleton, finrank_euclideanSpace_fin]; norm_num)
    exact ⟨v, hv, hvS n (by simp), by rw [h, norm_zero, zero_smul]⟩
  · refine ⟨‖F₂ - F₁‖⁻¹ • (F₂ - F₁), l15_unit h, by rw [real_inner_smul_left, h12, mul_zero], ?_⟩
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_smul]

/-- Major axis = diameter.-/
lemma l15_isGreatest {P : AffineSubspace ℝ E3} {p₀ n : E3} (hn : ‖n‖ = 1)
    (hPn : ∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0) (Q : Set E3) (F₁ F₂ : E3) (K : ℝ)
    (hF₁ : F₁ ∈ P) (hF₂ : F₂ ∈ P)
    (hQ : ∀ X ∈ P, X ∈ Q ↔ dist X F₁ + dist X F₂ = K) (hne : ∃ X ∈ P, X ∈ Q) :
    IsGreatest {d | ∃ x ∈ (P : Set E3) ∩ Q, ∃ y ∈ (P : Set E3) ∩ Q, d = dist x y} K := by
  obtain ⟨v, hv, hvn, hF⟩ := l15_plane_dir hn ((hPn _).1 hF₁) ((hPn _).1 hF₂)
  set δ := ‖F₂ - F₁‖
  obtain ⟨X₀, hX₀P, hX₀Q⟩ := hne
  have hK : δ ≤ K := by
    have := (hQ X₀ hX₀P).1 hX₀Q
    have h3 := dist_triangle_left F₂ F₁ X₀
    rw [dist_eq_norm] at h3
    linarith
  have hδ : 0 ≤ δ := norm_nonneg _
  have mk : ∀ r : ℝ, F₁ + r • v ∈ P := by
    intro r
    rw [hPn, show F₁ + r • v - p₀ = (F₁ - p₀) + r • v by abel, inner_add_left,
      real_inner_smul_left, hvn, mul_zero, add_zero]
    exact (hPn _).1 hF₁
  have dist1 : ∀ r : ℝ, dist (F₁ + r • v) F₁ = |r| := by
    intro r; rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs]
  have dist2 : ∀ r : ℝ, dist (F₁ + r • v) F₂ = |r - δ| := by
    intro r
    rw [dist_eq_norm, show F₁ + r • v - F₂ = r • v - (F₂ - F₁) by abel, hF, ← sub_smul,
      norm_smul, hv, mul_one, Real.norm_eq_abs]
  have memQ : ∀ r : ℝ, |r| + |r - δ| = K → F₁ + r • v ∈ (P : Set E3) ∩ Q := fun r hr =>
    ⟨mk r, (hQ _ (mk r)).2 (by rw [dist1, dist2]; exact hr)⟩
  refine ⟨⟨F₁ + ((δ + K) / 2) • v, memQ _ ?_, F₁ + ((δ - K) / 2) • v, memQ _ ?_, ?_⟩, ?_⟩
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; ring
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; ring
  · rw [dist_eq_norm, show F₁ + ((δ + K) / 2) • v - (F₁ + ((δ - K) / 2) • v)
        = ((δ + K) / 2 - (δ - K) / 2) • v by rw [sub_smul]; abel, norm_smul, hv, mul_one,
      Real.norm_eq_abs, show (δ + K) / 2 - (δ - K) / 2 = K by ring, abs_of_nonneg (by linarith)]
  · rintro d ⟨x, ⟨hxP, hxQ⟩, y, ⟨hyP, hyQ⟩, rfl⟩
    have hx := (hQ x hxP).1 hxQ
    have hy := (hQ y hyP).1 hyQ
    have t1 := dist_triangle x F₁ y
    have t2 := dist_triangle x F₂ y
    rw [dist_comm F₁ y] at t1; rw [dist_comm F₂ y] at t2
    linarith

/-! ### Orientation and classification -/

lemma l15_orient {e n : E3} (he : ‖e‖ = 1) {c s : ℝ} (hc : c ≠ 0) (hs : 0 < s)
    (hm : s < |inner ℝ e n|) :
    ∃ σ : ℝ, ∃ e' : E3, (σ = 1 ∨ σ = -1) ∧ e' = σ • e ∧ ‖e'‖ = 1 ∧
      s < |inner ℝ e' n| ∧ 0 < inner ℝ e' n * c := by
  have hm0 : inner ℝ e n ≠ 0 := by intro h; rw [h, abs_zero] at hm; linarith
  rcases lt_or_gt_of_ne (mul_ne_zero hm0 hc) with h | h
  · refine ⟨-1, -e, Or.inr rfl, by rw [neg_one_smul], by rw [norm_neg, he], ?_, ?_⟩
    · rw [inner_neg_left, abs_neg]; exact hm
    · rw [inner_neg_left]; linarith
  · exact ⟨1, e, Or.inl rfl, by rw [one_smul], he, hm, h⟩

lemma l15_sigma_sq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ * σ = 1 ∧ |σ| = 1 := by
  rcases hσ with rfl | rfl <;> norm_num

lemma l15_center {V e e' : E3} {σ d : ℝ} (hσ : σ = 1 ∨ σ = -1) (he' : e' = σ • e) :
    V + d • e = V + (σ * d) • e' := by
  rw [he', smul_smul, show σ * d * σ = (σ * σ) * d by ring, (l15_sigma_sq hσ).1, one_mul]

lemma l15_S_eq {V e e' : E3} {σ s d : ℝ} (hσ : σ = 1 ∨ σ = -1) (he' : e' = σ • e) :
    l15_S V e s d = l15_S V e' s (σ * d) := by
  unfold l15_S
  rw [← l15_center hσ he', abs_mul, (l15_sigma_sq hσ).2, one_mul]

lemma l15_cone2_sigma {V e e' X : E3} {σ k : ℝ} (hσ : σ = 1 ∨ σ = -1) (he' : e' = σ • e) :
    X ∈ Dandelin.cone2 V e k ↔ X ∈ Dandelin.cone2 V e' k := by
  show inner ℝ (X - V) e ^ 2 = k ^ 2 * ‖X - V‖ ^ 2 ↔ inner ℝ (X - V) e' ^ 2 = k ^ 2 * ‖X - V‖ ^ 2
  rw [he', real_inner_smul_right, mul_pow,
    show σ ^ 2 = 1 by rcases hσ with rfl | rfl <;> norm_num, one_mul]

/-- Writer Dandelin spheres = axis spheres solving the tangency equation (any orientation).-/
lemma l15_dandelin_iff {V u : E3} (hu : u ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2)
    {P : AffineSubspace ℝ E3} {p₀ n : E3} (hn : ‖n‖ = 1)
    (hPn : ∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0) {e : E3} (he_def : e = ‖u‖⁻¹ • u)
    {σ : ℝ} {e' : E3} (hσ : σ = 1 ∨ σ = -1) (he' : e' = σ • e) (S : Sphere E3) :
    IsDandelinSphere V u α P S ↔ ∃ d : ℝ, d ≠ 0 ∧ S = l15_S V e' (Real.sin α) d ∧
      |d * inner ℝ e' n - inner ℝ (p₀ - V) n| = |d| * Real.sin α := by
  have hσσ := (l15_sigma_sq hσ).1
  have hin : ∀ d : ℝ, (σ * d) * inner ℝ e' n = d * inner ℝ e n := by
    intro d; rw [he', real_inner_smul_left]
    linear_combination (d * inner ℝ e n) * hσσ
  constructor
  · rintro ⟨⟨C, hC⟩, F, hF⟩
    obtain ⟨d, hd, hS, htan, -, -⟩ := l15_dandelin_data hu hα0 hα1 hn hPn he_def S C F hC hF
    refine ⟨σ * d, mul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hd,
      by rw [hS]; exact l15_S_eq hσ he', ?_⟩
    rw [hin, abs_mul, (l15_sigma_sq hσ).2, one_mul]; exact htan
  · rintro ⟨d, hd, rfl, htan⟩
    have hd' : σ * d ≠ 0 := mul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hd
    have e1 : l15_S V e' (Real.sin α) d = l15_S V e (Real.sin α) (σ * d) := by
      rw [l15_S_eq (s := Real.sin α) (d := σ * d) hσ he', ← mul_assoc, hσσ, one_mul]
    rw [e1]
    refine l15_mk_dandelin hu hα0 hα1 hn hPn he_def (σ * d) hd' ?_
    have h3 : (σ * d) * inner ℝ e n = d * inner ℝ e' n := by
      rw [he', real_inner_smul_left]; ring
    rw [h3, abs_mul σ d, (l15_sigma_sq hσ).2, one_mul]; exact htan

/-- Data of a writer Dandelin sphere in a given orientation.-/
lemma l15_data' {V u : E3} (hu : u ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2)
    {P : AffineSubspace ℝ E3} {p₀ n : E3} (hn : ‖n‖ = 1)
    (hPn : ∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0) {e : E3} (he_def : e = ‖u‖⁻¹ • u)
    {σ : ℝ} {e' : E3} (hσ : σ = 1 ∨ σ = -1) (he' : e' = σ • e)
    (S : Sphere E3) (C : Set E3) (F : E3)
    (hC : TangentToConeAlong V u α S C) (hF : TangentToPlaneAt P S F) (d₀ : ℝ)
    (hS : S = l15_S V e' (Real.sin α) d₀) :
    F = (V + d₀ • e') - inner ℝ ((V + d₀ • e') - p₀) n • n ∧
      C = Metric.sphere (V + d₀ • e') (|d₀| * Real.sin α) ∩ cone V u α := by
  obtain ⟨d, -, hS', -, hFe, hCe⟩ := l15_dandelin_data hu hα0 hα1 hn hPn he_def S C F hC hF
  have hSe : l15_S V e (Real.sin α) d = l15_S V e' (Real.sin α) d₀ := hS'.symm.trans hS
  have hc : V + d • e = V + d₀ • e' := congrArg Sphere.center hSe
  have hr : |d| * Real.sin α = |d₀| * Real.sin α := congrArg Sphere.radius hSe
  rw [hc] at hFe hCe; rw [hr] at hCe
  exact ⟨hFe, hCe⟩

/-! ### Ellipse package -/

lemma l15_ell_pkg {V u : E3} (hu : u ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2)
    {P : AffineSubspace ℝ E3} {p₀ n : E3} (hn : ‖n‖ = 1)
    (hPn : ∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0) {e : E3} (he_def : e = ‖u‖⁻¹ • u)
    {σ : ℝ} {e' : E3} (hσ : σ = 1 ∨ σ = -1) (he' : e' = σ • e) (he'n : ‖e'‖ = 1)
    (hm : Real.sin α < |inner ℝ e' n|) (hc : 0 < inner ℝ e' n * inner ℝ (p₀ - V) n) :
    ∃ d₁ d₂ : ℝ, ∃ F₁ F₂ : E3, 0 < d₁ ∧ d₁ < d₂ ∧
      (∀ S, IsDandelinSphere V u α P S ↔
        S = l15_S V e' (Real.sin α) d₁ ∨ S = l15_S V e' (Real.sin α) d₂) ∧
      inner ℝ ((V + d₁ • e') - p₀) n * inner ℝ ((V + d₂ • e') - p₀) n < 0 ∧
      F₁ ∈ P ∧ F₂ ∈ P ∧
      F₁ = (V + d₁ • e') - inner ℝ ((V + d₁ • e') - p₀) n • n ∧
      F₂ = (V + d₂ • e') - inner ℝ ((V + d₂ • e') - p₀) n • n ∧
      (∀ X ∈ P, X ∈ cone V u α ↔ dist X F₁ + dist X F₂ = (d₂ - d₁) * Real.cos α) ∧
      (∃ X ∈ P, X ∈ cone V u α) := by
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  have hαI1 : α ≤ π := by linarith [Real.pi_pos]
  obtain ⟨d₁, d₂, F₁, F₂, hd₁, hd, htan, hopp, hF₁, hF₂, hp₁, hp₂, hiff⟩ :=
    Dandelin.dandelin_exists (V := V) (p₀ := p₀) he'n hn hks hk hs hm hc
  have hc0 : inner ℝ (p₀ - V) n ≠ 0 := by
    intro h; rw [h, mul_zero] at hc; exact lt_irrefl 0 hc
  have hconeiff : ∀ X ∈ P, X ∈ cone V u α ↔ X ∈ Dandelin.cone V e' (Real.cos α) := by
    intro X hX
    rw [l15_cone_eq hu hα0.le hαI1, ← he_def, l15_cone2_sigma hσ he']
    constructor
    · intro h2
      rcases Dandelin.one_nappe he'n hn hks hk hs hm.le hc0 with ⟨-, h⟩ | ⟨hneg, -⟩
      · exact h X ((hPn X).1 hX) h2
      · exact absurd hc (not_lt.2 hneg.le)
    · intro h; exact Dandelin.mem_cone2_iff.2 (Or.inl h)
  have tan_eq : ∀ d : ℝ, |inner ℝ ((V + d • e') - p₀) n| = |d * inner ℝ e' n - inner ℝ (p₀ - V) n|
    := fun d => by rw [Dandelin.inner_center_sub]
  have hL : inner ℝ e' n ^ 2 - Real.sin α ^ 2 ≠ 0 := by
    have : Real.sin α ^ 2 < inner ℝ e' n ^ 2 := by
      nlinarith [sq_abs (inner ℝ e' n), abs_nonneg (inner ℝ e' n)]
    linarith
  have r₁ := (htan d₁).2 (Or.inl rfl)
  have r₂ := (htan d₂).2 (Or.inr rfl)
  rw [tan_eq] at r₁ r₂
  replace r₁ : |d₁ * inner ℝ e' n - inner ℝ (p₀ - V) n| = |d₁| * Real.sin α := by
    rw [abs_of_pos hd₁]; exact r₁
  replace r₂ : |d₂ * inner ℝ e' n - inner ℝ (p₀ - V) n| = |d₂| * Real.sin α := by
    rw [abs_of_pos (hd₁.trans hd)]; exact r₂
  refine ⟨d₁, d₂, F₁, F₂, hd₁, hd, fun S => ?_, hopp, (hPn _).2 hF₁, (hPn _).2 hF₂, hp₁, hp₂,
    fun X hX => ?_, ?_⟩
  · rw [l15_dandelin_iff hu hα0 hα1 hn hPn he_def hσ he']
    constructor
    · rintro ⟨d, -, rfl, h⟩
      rcases l15_two_roots hL hd.ne h r₁ r₂ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨d₁, hd₁.ne', rfl, r₁⟩
      · exact ⟨d₂, (hd₁.trans hd).ne', rfl, r₂⟩
  · rw [hconeiff X hX, hiff X ((hPn X).1 hX), dist_eq_norm, dist_eq_norm]
  · obtain ⟨X, hX, hXc⟩ := Dandelin.ellipse_nonempty (V := V) (p₀ := p₀)
      (by rw [finrank_euclideanSpace_fin]; norm_num) he'n hn hks hk hs hm hc
    exact ⟨X, (hPn X).2 hX, (hconeiff X ((hPn X).2 hX)).2 hXc⟩

/-- Common writer setup.-/
lemma l15_setup {V u : E3} (hu : u ≠ 0) (P : AffineSubspace ℝ E3)
    (hP : Module.finrank ℝ P.direction = 2) (hVP : V ∉ P) :
    ∃ p₀ n e : E3, ‖n‖ = 1 ∧ p₀ ∈ P ∧ (∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0) ∧
      e = ‖u‖⁻¹ • u ∧ ‖e‖ = 1 ∧ inner ℝ (p₀ - V) n ≠ 0 ∧
      Real.cos (planeAxisAngle u P) = √(1 - inner ℝ e n ^ 2) ∧
      0 ≤ planeAxisAngle u P ∧ planeAxisAngle u P ≤ π / 2 ∧ inner ℝ e n ^ 2 ≤ 1 := by
  obtain ⟨p₀, n, hn, hp₀, hdir, hPn⟩ := l15_plane_normal P hP
  obtain ⟨hcos, hβ0, hβ1⟩ := l15_planeAxisAngle hu hn P hdir
  have he : ‖‖u‖⁻¹ • u‖ = 1 := l15_unit hu
  exact ⟨p₀, n, _, hn, hp₀, hPn, rfl, he, l15_vnot hPn hVP, hcos, hβ0, hβ1, l15_m_sq_le he hn⟩

/-! ### Comparison theorems: Conics1 -/

theorem cov_Conics1_a : classical_Conics1_a := by
  intro V u hu α hα0 hα1 P hP hVP hβ
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  obtain ⟨p₀, n, e, hn, hp₀, hPn, he_def, he, hc0, hcos, hβ0, hβ1, hm1⟩ := l15_setup hu P hP hVP
  have hreg := l15_regime_ell hα0 hα1 hβ0 hβ1 hm1 hcos hβ
  obtain ⟨σ, e', hσ, he', he'n, hm', hc'⟩ := l15_orient he hc0 hs hreg
  obtain ⟨d₁, d₂, F₁, F₂, hd₁, hd, hiffS, hopp, -, -, -, -, -, -⟩ :=
    l15_ell_pkg hu hα0 hα1 hn hPn he_def hσ he' he'n hm' hc'
  have he'0 : e' ≠ 0 := by intro h; rw [h, norm_zero] at he'n; norm_num at he'n
  refine ⟨l15_S V e' (Real.sin α) d₁, l15_S V e' (Real.sin α) d₂, ?_, (hiffS _).2 (Or.inl rfl),
    (hiffS _).2 (Or.inr rfl), fun S hS => (hiffS S).1 hS, ?_, ?_⟩
  · intro h
    have h1 : V + d₁ • e' = V + d₂ • e' := congrArg Sphere.center h
    have h2 : (d₁ - d₂) • e' = 0 := by rw [sub_smul]; exact sub_eq_zero.2 (add_left_cancel h1)
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact hd.ne (sub_eq_zero.1 h3)
    · exact he'0 h3
  · rcases hσ with rfl | rfl
    · rw [one_smul] at he'; subst he'
      exact ⟨1, Or.inl rfl, l15_inside_pos hu he_def hα0 hd₁,
        l15_inside_pos hu he_def hα0 (hd₁.trans hd)⟩
    · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
      · show InsideNappe V u α (-1) (V + d₁ • e')
        rw [he', neg_one_smul, smul_neg, ← neg_smul]
        exact l15_inside_neg hu he_def hα0 (by linarith)
      · show InsideNappe V u α (-1) (V + d₂ • e')
        rw [he', neg_one_smul, smul_neg, ← neg_smul]
        exact l15_inside_neg hu he_def hα0 (by linarith)
  · exact l15_sOppSide hp₀ hPn _ _ hopp

/-- Generator segment for either orientation.-/
lemma l15_gen_segment' {V u : E3} (hu : u ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2)
    {e : E3} (he_def : e = ‖u‖⁻¹ • u) {σ : ℝ} {e' : E3} (hσ : σ = 1 ∨ σ = -1)
    (he' : e' = σ • e) (g : AffineSubspace ℝ E3) (hg : IsGenerator V u α g)
    (d₁ d₂ : ℝ) (Y₁ Y₂ : E3) (hY₁ : Y₁ ∈ (g : Set E3)) (hY₂ : Y₂ ∈ (g : Set E3))
    (hS₁ : Y₁ ∈ Metric.sphere (V + d₁ • e') (|d₁| * Real.sin α))
    (hS₂ : Y₂ ∈ Metric.sphere (V + d₂ • e') (|d₂| * Real.sin α)) :
    dist Y₁ Y₂ = |d₁ - d₂| * Real.cos α := by
  have c1 : V + d₁ • e' = V + (σ * d₁) • e := by
    rw [he', smul_smul, mul_comm]
  have c2 : V + d₂ • e' = V + (σ * d₂) • e := by
    rw [he', smul_smul, mul_comm]
  have ha := (l15_sigma_sq hσ).2
  rw [c1, show |d₁| = |σ * d₁| by rw [abs_mul, ha, one_mul]] at hS₁
  rw [c2, show |d₂| = |σ * d₂| by rw [abs_mul, ha, one_mul]] at hS₂
  rw [l15_gen_segment hu hα0 hα1 he_def g hg _ _ Y₁ Y₂ hY₁ hY₂ hS₁ hS₂, ← mul_sub, abs_mul,
    ha, one_mul]

theorem cov_Conics1_b : classical_Conics1_b := by
  intro V u hu α hα0 hα1 P hP hVP hβ S₁ S₂ hS C₁ C₂ F₁ F₂ hC₁ hC₂ hF₁ hF₂
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  obtain ⟨p₀, n, e, hn, hp₀, hPn, he_def, he, hc0, hcos, hβ0, hβ1, hm1⟩ := l15_setup hu P hP hVP
  have hreg := l15_regime_ell hα0 hα1 hβ0 hβ1 hm1 hcos hβ
  obtain ⟨σ, e', hσ, he', he'n, hm', hc'⟩ := l15_orient he hc0 hs hreg
  obtain ⟨d₁, d₂, G₁, G₂, hd₁, hd, hiffS, -, hG₁, hG₂, hp₁, hp₂, hsum, hne⟩ :=
    l15_ell_pkg hu hα0 hα1 hn hPn he_def hσ he' he'n hm' hc'
  have D₁ : IsDandelinSphere V u α P S₁ := ⟨⟨C₁, hC₁⟩, F₁, hF₁⟩
  have D₂ : IsDandelinSphere V u α P S₂ := ⟨⟨C₂, hC₂⟩, F₂, hF₂⟩
  set K := (d₂ - d₁) * Real.cos α
  have hK : |d₁ - d₂| * Real.cos α = K := by
    rw [abs_of_neg (by linarith)]; simp only [K]; ring
  have hK' : |d₂ - d₁| * Real.cos α = K := by
    rw [abs_of_pos (by linarith)]
  -- identify the two spheres
  have key : ∀ (S : Sphere E3) (C : Set E3) (F : E3), TangentToConeAlong V u α S C →
      TangentToPlaneAt P S F → ∀ i : ℝ, S = l15_S V e' (Real.sin α) i →
      F = (V + i • e') - inner ℝ ((V + i • e') - p₀) n • n ∧
        C = Metric.sphere (V + i • e') (|i| * Real.sin α) ∩ cone V u α :=
    fun S C F hC hF i hi => l15_data' hu hα0 hα1 hn hPn he_def hσ he' S C F hC hF i hi
  have gen : ∀ (i j : ℝ) (C C' : Set E3),
      C = Metric.sphere (V + i • e') (|i| * Real.sin α) ∩ cone V u α →
      C' = Metric.sphere (V + j • e') (|j| * Real.sin α) ∩ cone V u α →
      ∀ g, IsGenerator V u α g → ∀ Y₁ ∈ (g : Set E3) ∩ C, ∀ Y₂ ∈ (g : Set E3) ∩ C',
        dist Y₁ Y₂ = |i - j| * Real.cos α := by
    intro i j C C' hC hC' g hg Y₁ hY₁ Y₂ hY₂
    rw [hC] at hY₁; rw [hC'] at hY₂
    exact l15_gen_segment' hu hα0 hα1 he_def hσ he' g hg i j Y₁ Y₂ hY₁.1 hY₂.1 hY₁.2.1 hY₂.2.1
  have great := l15_isGreatest hn hPn (cone V u α) G₁ G₂ K hG₁ hG₂ hsum hne
  rcases (hiffS S₁).1 D₁ with h1 | h1 <;> rcases (hiffS S₂).1 D₂ with h2 | h2
  · exact absurd (h1.trans h2.symm) hS
  · obtain ⟨eF₁, eC₁⟩ := key S₁ C₁ F₁ hC₁ hF₁ d₁ h1
    obtain ⟨eF₂, eC₂⟩ := key S₂ C₂ F₂ hC₂ hF₂ d₂ h2
    refine ⟨K, fun X hX => ?_, fun g hg Y₁ hY₁ Y₂ hY₂ => ?_, great⟩
    · rw [eF₁, eF₂, ← hp₁, ← hp₂]; exact (hsum X hX.1).1 hX.2
    · rw [gen d₁ d₂ C₁ C₂ eC₁ eC₂ g hg Y₁ hY₁ Y₂ hY₂, hK]
  · obtain ⟨eF₁, eC₁⟩ := key S₁ C₁ F₁ hC₁ hF₁ d₂ h1
    obtain ⟨eF₂, eC₂⟩ := key S₂ C₂ F₂ hC₂ hF₂ d₁ h2
    refine ⟨K, fun X hX => ?_, fun g hg Y₁ hY₁ Y₂ hY₂ => ?_, great⟩
    · rw [eF₁, eF₂, ← hp₁, ← hp₂, add_comm]; exact (hsum X hX.1).1 hX.2
    · rw [gen d₂ d₁ C₁ C₂ eC₁ eC₂ g hg Y₁ hY₁ Y₂ hY₂, hK']
  · exact absurd (h1.trans h2.symm) hS

/-! ### Conics2 (hyperbola) -/

lemma l15_hyp_pkg {V u : E3} (hu : u ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2)
    {P : AffineSubspace ℝ E3} {p₀ n : E3} (hn : ‖n‖ = 1)
    (hPn : ∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0) {e : E3} (he_def : e = ‖u‖⁻¹ • u)
    (he : ‖e‖ = 1) (hm : |inner ℝ e n| < Real.sin α) (hc : inner ℝ (p₀ - V) n ≠ 0) :
    ∃ d₁ d₂ : ℝ, ∃ F₁ F₂ : E3, d₂ < 0 ∧ 0 < d₁ ∧
      (∀ S, IsDandelinSphere V u α P S ↔
        S = l15_S V e (Real.sin α) d₁ ∨ S = l15_S V e (Real.sin α) d₂) ∧
      F₁ ∈ P ∧ F₂ ∈ P ∧
      F₁ = (V + d₁ • e) - inner ℝ ((V + d₁ • e) - p₀) n • n ∧
      F₂ = (V + d₂ • e) - inner ℝ ((V + d₂ • e) - p₀) n • n ∧
      (∀ X ∈ P, X ∈ Dandelin.cone V e (Real.cos α) →
        dist X F₂ - dist X F₁ = (d₁ - d₂) * Real.cos α) ∧
      (∀ X ∈ P, X ∈ Dandelin.cone V (-e) (Real.cos α) →
        dist X F₁ - dist X F₂ = (d₁ - d₂) * Real.cos α) ∧
      (∀ X ∈ P, X ∈ cone V u α ↔ |dist X F₁ - dist X F₂| = (d₁ - d₂) * Real.cos α) ∧
      (∃ X ∈ P, X ∈ Dandelin.cone V e (Real.cos α)) ∧
      (∃ Y ∈ P, Y ∈ Dandelin.cone V (-e) (Real.cos α)) := by
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  have hαI1 : α ≤ π := by linarith [Real.pi_pos]
  obtain ⟨-, d₁, d₂, F₁, F₂, hd₂, hd₁, htan, hF₁, hF₂, hp₁, hp₂, hup, hlo, hiff, -⟩ :=
    Dandelin.dandelin_hyperbola (V := V) (p₀ := p₀) he hn hks hk hs hm hc
  obtain ⟨hX, hY⟩ := Dandelin.hyp_both_nappes (V := V) (p₀ := p₀) he hn hks hk hs hm hc
  have hL : inner ℝ e n ^ 2 - Real.sin α ^ 2 ≠ 0 := by
    have : inner ℝ e n ^ 2 < Real.sin α ^ 2 := by
      nlinarith [sq_abs (inner ℝ e n), abs_nonneg (inner ℝ e n)]
    linarith
  have r₁ := (htan d₁).2 (Or.inl rfl)
  have r₂ := (htan d₂).2 (Or.inr rfl)
  rw [Dandelin.inner_center_sub] at r₁ r₂
  have hσ : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have he' : e = (1 : ℝ) • e := (one_smul ℝ e).symm
  refine ⟨d₁, d₂, F₁, F₂, hd₂, hd₁, fun S => ?_, (hPn _).2 hF₁, (hPn _).2 hF₂, hp₁, hp₂,
    fun X hX hXc => ?_, fun X hX hXc => ?_, fun X hX => ?_, ?_, ?_⟩
  · rw [l15_dandelin_iff hu hα0 hα1 hn hPn he_def hσ he']
    constructor
    · rintro ⟨d, -, rfl, h⟩
      rcases l15_two_roots hL (by linarith : d₁ ≠ d₂) h r₁ r₂ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨d₁, hd₁.ne', rfl, r₁⟩
      · exact ⟨d₂, hd₂.ne, rfl, r₂⟩
  · rw [dist_eq_norm, dist_eq_norm]; exact hup X ((hPn X).1 hX) hXc
  · rw [dist_eq_norm, dist_eq_norm]; exact hlo X ((hPn X).1 hX) hXc
  · rw [l15_cone_eq hu hα0.le hαI1, ← he_def, hiff X ((hPn X).1 hX), dist_eq_norm, dist_eq_norm]
  · obtain ⟨X, hX, hXc⟩ := hX; exact ⟨X, (hPn X).2 hX, hXc⟩
  · obtain ⟨Y, hY, hYc⟩ := hY; exact ⟨Y, (hPn Y).2 hY, hYc⟩

theorem cov_Conics2_a : classical_Conics2_a := by
  intro V u hu α hα0 hα1 P hP hVP hβ
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  obtain ⟨p₀, n, e, hn, hp₀, hPn, he_def, he, hc0, hcos, hβ0, hβ1, hm1⟩ := l15_setup hu P hP hVP
  have hreg := l15_regime_hyp hα0 hα1 hβ0 hm1 hcos hβ
  obtain ⟨d₁, d₂, -, -, hd₂, hd₁, hiffS, -⟩ := l15_hyp_pkg hu hα0 hα1 hn hPn he_def he hreg hc0
  have he0 : e ≠ 0 := by intro h; rw [h, norm_zero] at he; norm_num at he
  refine ⟨l15_S V e (Real.sin α) d₁, l15_S V e (Real.sin α) d₂, ?_, (hiffS _).2 (Or.inl rfl),
    (hiffS _).2 (Or.inr rfl), fun S hS => (hiffS S).1 hS,
    l15_inside_pos hu he_def hα0 hd₁, l15_inside_neg hu he_def hα0 hd₂⟩
  intro h
  have h1 : V + d₁ • e = V + d₂ • e := congrArg Sphere.center h
  have h2 : (d₁ - d₂) • e = 0 := by rw [sub_smul]; exact sub_eq_zero.2 (add_left_cancel h1)
  rcases smul_eq_zero.1 h2 with h3 | h3
  · linarith [sub_eq_zero.1 h3]
  · exact he0 h3

lemma l15_cone_of_double {V e X : E3} {k : ℝ} (hk : 0 < k)
    (h2 : X ∈ Dandelin.cone2 V e k) (hpos : 0 < inner ℝ (X - V) e) :
    X ∈ Dandelin.cone V e k := by
  rcases Dandelin.mem_cone2_iff.1 h2 with h | h
  · exact h
  · exfalso
    have h' : inner ℝ (X - V) (-e) = k * ‖X - V‖ := h
    rw [inner_neg_right] at h'
    nlinarith [norm_nonneg (X - V)]

lemma l15_cone_of_double_neg {V e X : E3} {k : ℝ} (hk : 0 < k)
    (h2 : X ∈ Dandelin.cone2 V e k) (hneg : inner ℝ (X - V) e < 0) :
    X ∈ Dandelin.cone V (-e) k := by
  rcases Dandelin.mem_cone2_iff.1 h2 with h | h
  · exfalso
    have h' : inner ℝ (X - V) e = k * ‖X - V‖ := h
    nlinarith [norm_nonneg (X - V)]
  · exact h

lemma l15_inner_u {V u e X : E3} (hu : u ≠ 0) (he_def : e = ‖u‖⁻¹ • u) :
    inner ℝ (X - V) u = ‖u‖ * inner ℝ (X - V) e := by
  rw [he_def, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hu),
    one_mul]

theorem cov_Conics2_b : classical_Conics2_b := by
  intro V u hu α hα0 hα1 P hP hVP hβ S₁ S₂ hS C₁ C₂ F₁ F₂ hC₁ hC₂ hF₁ hF₂
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  have hαI1 : α ≤ π := by linarith [Real.pi_pos]
  obtain ⟨p₀, n, e, hn, hp₀, hPn, he_def, he, hc0, hcos, hβ0, hβ1, hm1⟩ := l15_setup hu P hP hVP
  have hreg := l15_regime_hyp hα0 hα1 hβ0 hm1 hcos hβ
  obtain ⟨d₁, d₂, G₁, G₂, hd₂, hd₁, hiffS, hG₁, hG₂, hp₁, hp₂, hup, hlo, hiff, hXu, hYl⟩ :=
    l15_hyp_pkg hu hα0 hα1 hn hPn he_def he hreg hc0
  have hσ : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have he' : e = (1 : ℝ) • e := (one_smul ℝ e).symm
  have D₁ : IsDandelinSphere V u α P S₁ := ⟨⟨C₁, hC₁⟩, F₁, hF₁⟩
  have D₂ : IsDandelinSphere V u α P S₂ := ⟨⟨C₂, hC₂⟩, F₂, hF₂⟩
  set K := (d₁ - d₂) * Real.cos α with hKdef
  have hKpos : 0 < K := mul_pos (by linarith) hk
  have gen : ∀ (i j : ℝ) (C C' : Set E3),
      C = Metric.sphere (V + i • e) (|i| * Real.sin α) ∩ cone V u α →
      C' = Metric.sphere (V + j • e) (|j| * Real.sin α) ∩ cone V u α →
      ∀ g, IsGenerator V u α g → ∀ Y₁ ∈ (g : Set E3) ∩ C, ∀ Y₂ ∈ (g : Set E3) ∩ C',
        dist Y₁ Y₂ = |i - j| * Real.cos α := by
    intro i j C C' hC hC' g hg Y₁ hY₁ Y₂ hY₂
    rw [hC] at hY₁; rw [hC'] at hY₂
    exact l15_gen_segment hu hα0 hα1 he_def g hg i j Y₁ Y₂ hY₁.1 hY₂.1 hY₁.2.1 hY₂.2.1
  have hK1 : |d₁ - d₂| * Real.cos α = K := by rw [abs_of_pos (by linarith)]
  have hK2 : |d₂ - d₁| * Real.cos α = K := by rw [abs_of_neg (by linarith)]; simp only [K]; ring
  -- transverse axis
  have least : IsLeast {d | ∃ x ∈ (P : Set E3) ∩ cone V u α, ∃ y ∈ (P : Set E3) ∩ cone V u α,
      0 < inner ℝ (x -ᵥ V) u ∧ inner ℝ (y -ᵥ V) u < 0 ∧ d = dist x y} K := by
    obtain ⟨v, hv, hvn, hF⟩ := l15_plane_dir hn ((hPn _).1 hG₁) ((hPn _).1 hG₂)
    set δ := ‖G₂ - G₁‖
    obtain ⟨X₀, hX₀P, hX₀c⟩ := hXu
    have hKδ : K ≤ δ := by
      have := hup X₀ hX₀P hX₀c
      have h3 := dist_triangle X₀ G₁ G₂
      have h4 : dist G₁ G₂ = δ := by rw [dist_comm, dist_eq_norm]
      linarith
    have mk : ∀ r : ℝ, G₁ + r • v ∈ P := by
      intro r
      rw [hPn, show G₁ + r • v - p₀ = (G₁ - p₀) + r • v by abel, inner_add_left,
        real_inner_smul_left, hvn, mul_zero, add_zero]
      exact (hPn _).1 hG₁
    have dist1 : ∀ r : ℝ, dist (G₁ + r • v) G₁ = |r| := by
      intro r; rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs]
    have dist2 : ∀ r : ℝ, dist (G₁ + r • v) G₂ = |r - δ| := by
      intro r
      rw [dist_eq_norm, show G₁ + r • v - G₂ = r • v - (G₂ - G₁) by abel, hF, ← sub_smul,
        norm_smul, hv, mul_one, Real.norm_eq_abs]
    have hVnot : ∀ X ∈ P, X ≠ V := fun X hX h => hVP (h ▸ hX)
    have pos_of_upper : ∀ X ∈ P, X ∈ Dandelin.cone V e (Real.cos α) →
        0 < inner ℝ (X -ᵥ V) u := by
      intro X hX hXc
      rw [vsub_eq_sub, l15_inner_u hu he_def]
      have h' : inner ℝ (X - V) e = Real.cos α * ‖X - V‖ := hXc
      rw [h']
      have : 0 < ‖X - V‖ := norm_pos_iff.2 (sub_ne_zero.2 (hVnot X hX))
      have := norm_pos_iff.2 hu
      positivity
    have neg_of_lower : ∀ X ∈ P, X ∈ Dandelin.cone V (-e) (Real.cos α) →
        inner ℝ (X -ᵥ V) u < 0 := by
      intro X hX hXc
      rw [vsub_eq_sub, l15_inner_u hu he_def]
      have h' : inner ℝ (X - V) (-e) = Real.cos α * ‖X - V‖ := hXc
      rw [inner_neg_right] at h'
      have h1 : 0 < ‖X - V‖ := norm_pos_iff.2 (sub_ne_zero.2 (hVnot X hX))
      have h2 := norm_pos_iff.2 hu
      have h3 : inner ℝ (X - V) e = -(Real.cos α * ‖X - V‖) := by linarith
      rw [h3]
      have := mul_pos hk h1
      nlinarith
    set xa := G₁ + ((δ - K) / 2) • v
    set ya := G₁ + ((δ + K) / 2) • v
    have hxa1 : dist xa G₁ = (δ - K) / 2 := by rw [dist1, abs_of_nonneg (by linarith)]
    have hxa2 : dist xa G₂ = (δ + K) / 2 := by
      rw [dist2, abs_of_nonpos (by linarith)]; ring
    have hya1 : dist ya G₁ = (δ + K) / 2 := by rw [dist1, abs_of_nonneg (by linarith)]
    have hya2 : dist ya G₂ = (δ - K) / 2 := by
      rw [dist2, abs_of_nonpos (by linarith)]; ring
    have hxac : xa ∈ cone V u α := by
      rw [hiff xa (mk _), hxa1, hxa2]; rw [abs_of_nonpos (by linarith)]; ring
    have hyac : ya ∈ cone V u α := by
      rw [hiff ya (mk _), hya1, hya2]; rw [abs_of_nonneg (by linarith)]; ring
    have to2 : ∀ X, X ∈ cone V u α → X ∈ Dandelin.cone2 V e (Real.cos α) := by
      intro X h; rw [he_def]; exact (l15_cone_eq hu hα0.le hαI1 X).1 h
    have hxu : xa ∈ Dandelin.cone V e (Real.cos α) := by
      rcases Dandelin.mem_cone2_iff.1 (to2 xa hxac) with h | h
      · exact h
      · have := hlo xa (mk _) h; rw [hxa1, hxa2] at this; linarith
    have hyl : ya ∈ Dandelin.cone V (-e) (Real.cos α) := by
      rcases Dandelin.mem_cone2_iff.1 (to2 ya hyac) with h | h
      · have := hup ya (mk _) h; rw [hya1, hya2] at this; linarith
      · exact h
    refine ⟨⟨xa, ⟨mk _, hxac⟩, ya, ⟨mk _, hyac⟩, pos_of_upper xa (mk _) hxu,
      neg_of_lower ya (mk _) hyl, ?_⟩, ?_⟩
    · rw [dist_eq_norm, show xa - ya = ((δ - K) / 2 - (δ + K) / 2) • v by
        simp only [xa, ya]; rw [sub_smul]; abel, norm_smul, hv, mul_one, Real.norm_eq_abs,
        show (δ - K) / 2 - (δ + K) / 2 = -K by ring, abs_neg, abs_of_pos hKpos]
    · rintro d ⟨x, ⟨hxP, hxc⟩, y, ⟨hyP, hyc⟩, hx, hy, rfl⟩
      rw [vsub_eq_sub, l15_inner_u hu he_def] at hx hy
      have hnu := norm_pos_iff.2 hu
      have hx' : 0 < inner ℝ (x - V) e := pos_of_mul_pos_right hx hnu.le
      have hy' : inner ℝ (y - V) e < 0 := by
        by_contra h; push_neg at h; nlinarith
      have ex := hup x hxP (l15_cone_of_double hk (to2 x hxc) hx')
      have ey := hlo y hyP (l15_cone_of_double_neg hk (to2 y hyc) hy')
      have t1 := dist_triangle y x G₁
      have t2 := dist_triangle x y G₂
      rw [dist_comm y x] at t1
      show K ≤ dist x y
      linarith
  rcases (hiffS S₁).1 D₁ with h1 | h1 <;> rcases (hiffS S₂).1 D₂ with h2 | h2
  · exact absurd (h1.trans h2.symm) hS
  · obtain ⟨eF₁, eC₁⟩ := l15_data' hu hα0 hα1 hn hPn he_def hσ he' S₁ C₁ F₁ hC₁ hF₁ d₁ h1
    obtain ⟨eF₂, eC₂⟩ := l15_data' hu hα0 hα1 hn hPn he_def hσ he' S₂ C₂ F₂ hC₂ hF₂ d₂ h2
    refine ⟨K, fun X hX => ?_, fun g hg Y₁ hY₁ Y₂ hY₂ => ?_, least⟩
    · rw [eF₁, eF₂, ← hp₁, ← hp₂]; exact (hiff X hX.1).1 hX.2
    · rw [gen d₁ d₂ C₁ C₂ eC₁ eC₂ g hg Y₁ hY₁ Y₂ hY₂, hK1]
  · obtain ⟨eF₁, eC₁⟩ := l15_data' hu hα0 hα1 hn hPn he_def hσ he' S₁ C₁ F₁ hC₁ hF₁ d₂ h1
    obtain ⟨eF₂, eC₂⟩ := l15_data' hu hα0 hα1 hn hPn he_def hσ he' S₂ C₂ F₂ hC₂ hF₂ d₁ h2
    refine ⟨K, fun X hX => ?_, fun g hg Y₁ hY₁ Y₂ hY₂ => ?_, least⟩
    · rw [eF₁, eF₂, ← hp₁, ← hp₂, abs_sub_comm]; exact (hiff X hX.1).1 hX.2
    · rw [gen d₂ d₁ C₁ C₂ eC₁ eC₂ g hg Y₁ hY₁ Y₂ hY₂, hK2]
  · exact absurd (h1.trans h2.symm) hS

/-! ### Conics3 -/

/-- A generator point on the contact circle.-/
lemma l15_circle_pt {V u e w : E3} (hu : u ≠ 0) (he_def : e = ‖u‖⁻¹ • u) (he : ‖e‖ = 1)
    {α d : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2) (hw : ‖w‖ = 1)
    (hwe : inner ℝ w e = Real.cos α) :
    V + (d * Real.cos α) • w ∈
      Metric.sphere (V + d • e) (|d| * Real.sin α) ∩ cone V u α := by
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  have hαI1 : α ≤ π := by linarith [Real.pi_pos]
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_sphere, dist_eq_norm,
      show V + (d * Real.cos α) • w - (V + d • e) = (d * Real.cos α) • w - d • e by abel]
    have h2 : ‖(d * Real.cos α) • w - d • e‖ ^ 2 = (|d| * Real.sin α) ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, norm_smul, hw, he, real_inner_smul_left,
        real_inner_smul_right, hwe, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
        mul_pow, sq_abs, sq_abs]
      linear_combination (-d ^ 2) * hks
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  · rw [l15_cone_eq hu hα0.le hαI1, ← he_def]
    show inner ℝ (V + (d * Real.cos α) • w - V) e ^ 2 =
      Real.cos α ^ 2 * ‖V + (d * Real.cos α) • w - V‖ ^ 2
    rw [add_sub_cancel_left, real_inner_smul_left, hwe, norm_smul, hw, Real.norm_eq_abs,
      mul_one, mul_pow, sq_abs]
    ring

/-- The affine span of the contact circle is the plane of the circle.-/
lemma l15_span_circle {V u e : E3} (hu : u ≠ 0) (he_def : e = ‖u‖⁻¹ • u) (he : ‖e‖ = 1)
    {α d : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2) (hd : d ≠ 0) :
    ((affineSpan ℝ (Metric.sphere (V + d • e) (|d| * Real.sin α) ∩ cone V u α) :
      AffineSubspace ℝ E3) : Set E3) = Dandelin.axisPlane V e (d * Real.cos α ^ 2) := by
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  have hαI1 : α ≤ π := by linarith [Real.pi_pos]
  set C := Metric.sphere (V + d • e) (|d| * Real.sin α) ∩ cone V u α
  set k := Real.cos α
  set s := Real.sin α
  have hee : inner ℝ e e = 1 := by rw [l15_inner_self, he]; norm_num
  set c := V + (d * k ^ 2) • e
  set PiC : AffineSubspace ℝ E3 := AffineSubspace.mk' c (ℝ ∙ e)ᗮ
  have hPiC : ∀ Y : E3, Y ∈ PiC ↔ inner ℝ (Y - V) e = d * k ^ 2 := by
    intro Y
    rw [AffineSubspace.mem_mk', vsub_eq_sub, Submodule.mem_orthogonal_singleton_iff_inner_left,
      show Y - c = (Y - V) - (d * k ^ 2) • e by simp only [c]; abel, inner_sub_left,
      real_inner_smul_left, hee, mul_one, sub_eq_zero]
  have hsub : C ⊆ (PiC : Set E3) := by
    rintro X ⟨hXs, hXc⟩
    rw [SetLike.mem_coe, hPiC]
    rw [l15_cone_eq hu hα0.le hαI1, ← he_def] at hXc
    have hc2 : inner ℝ (X - V) e ^ 2 = k ^ 2 * ‖X - V‖ ^ 2 := hXc
    rw [Metric.mem_sphere, dist_eq_norm, show X - (V + d • e) = (X - V) - d • e by abel] at hXs
    have h2 : ‖(X - V) - d • e‖ ^ 2 = (|d| * s) ^ 2 := by rw [hXs]
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, he, Real.norm_eq_abs, mul_one,
      mul_pow, sq_abs] at h2
    set y := inner ℝ (X - V) e
    have : (y - d * k ^ 2) ^ 2 = 0 := by linear_combination hc2 + k ^ 2 * h2 + d ^ 2 * k ^ 2 * hks
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  have hle : affineSpan ℝ C ≤ PiC := affineSpan_le.2 hsub
  have hge : PiC ≤ affineSpan ℝ C := by
    intro Y hY
    have hY' := (hPiC Y).1 hY
    have hc0 : inner ℝ (c - c) e = 0 := by rw [sub_self, inner_zero_left]
    have hYc : inner ℝ (Y - c) e = 0 := by
      rw [show Y - c = (Y - V) - (d * k ^ 2) • e by simp only [c]; abel, inner_sub_left,
        real_inner_smul_left, hee, hY']; ring
    obtain ⟨f, hf, hfe, hz⟩ := l15_plane_dir he hc0 hYc
    set r := d * k * s
    have hr : r ≠ 0 := by simp only [r]; exact mul_ne_zero (mul_ne_zero hd hk.ne') hs.ne'
    have g₁ := Dandelin.gen_dir (k := k) (s := s) he hf hfe hks
    have g₂ := Dandelin.gen_dir (k := k) (s := -s) he hf hfe (by rw [neg_sq]; exact hks)
    have p₁ := l15_circle_pt (V := V) (d := d) hu he_def he hα0 hα1 g₁.1 g₁.2
    have p₂ := l15_circle_pt (V := V) (d := d) hu he_def he hα0 hα1 g₂.1 g₂.2
    have q₁ : V + (d * k) • (k • e + s • f) = c + r • f := by
      simp only [c, r, smul_add, smul_smul]; rw [add_assoc]; congr 2 <;> ring_nf
    have q₂ : V + (d * k) • (k • e + (-s) • f) = c - r • f := by
      simp only [c, r, smul_add, smul_smul]
      rw [sub_eq_add_neg, ← neg_smul, add_assoc]; congr 2 <;> ring_nf
    rw [q₁] at p₁; rw [q₂] at p₂
    have hsub2 : ({c - r • f, c + r • f} : Set E3) ⊆ C := by
      intro x hx
      rcases hx with rfl | rfl
      · exact p₂
      · exact p₁
    have hmem := AffineMap.lineMap_mem_affineSpan_pair (k := ℝ)
      ((‖Y - c‖ / r + 1) / 2) (c - r • f) (c + r • f)
    have heq : AffineMap.lineMap (c - r • f) (c + r • f) ((‖Y - c‖ / r + 1) / 2) = Y := by
      rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
        show c + r • f - (c - r • f) = (2 * r) • f by rw [two_mul, add_smul]; abel, smul_smul,
        show (‖Y - c‖ / r + 1) / 2 * (2 * r) = ‖Y - c‖ + r by field_simp, add_smul, ← hz]
      abel
    rw [heq] at hmem
    exact affineSpan_mono ℝ hsub2 hmem
  have := le_antisymm hle hge
  rw [this]
  ext Y
  rw [SetLike.mem_coe, hPiC]
  rfl
lemma l15_directrix_eq {V u e : E3} (hu : u ≠ 0) (he_def : e = ‖u‖⁻¹ • u) (he : ‖e‖ = 1)
    {α d : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2) (hd : d ≠ 0) {P : AffineSubspace ℝ E3} {p₀ n : E3}
    (hPn : ∀ X : E3, X ∈ P ↔ inner ℝ (X - p₀) n = 0) :
    ((P ⊓ affineSpan ℝ (Metric.sphere (V + d • e) (|d| * Real.sin α) ∩ cone V u α) :
      AffineSubspace ℝ E3) : Set E3) = Dandelin.directrix V e n p₀ (d * Real.cos α ^ 2) := by
  ext Y
  have hs := l15_span_circle (V := V) hu he_def he hα0 hα1 hd
  have h2 : ∀ Y : E3, Y ∈ affineSpan ℝ (Metric.sphere (V + d • e) (|d| * Real.sin α) ∩
      cone V u α) ↔ Y ∈ Dandelin.axisPlane V e (d * Real.cos α ^ 2) := by
    intro Y; rw [← hs]; rfl
  rw [SetLike.mem_coe, AffineSubspace.mem_inf_iff, h2, hPn]
  rfl

theorem cov_Conics3_obligation : classical_Conics3_obligation := by
  intro V u hu α hα0 hα1 P hP hVP hβ S C F hC hF
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  obtain ⟨p₀, n, e, hn, hp₀, hPn, he_def, he, hc0, hcos, hβ0, hβ1, hm1⟩ := l15_setup hu P hP hVP
  have hm := l15_noncirc hcos hβ0 hβ
  obtain ⟨d, hd, -, -, -, hCe⟩ := l15_dandelin_data hu hα0 hα1 hn hPn he_def S C F hC hF
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = d * Real.cos α ^ 2 := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = inner ℝ e n := ⟨_, rfl⟩
  rw [← hmdef] at hm
  obtain ⟨a, hadef⟩ : ∃ a : E3, a = e - m • n := ⟨_, rfl⟩
  have hnn : inner ℝ n n = 1 := by rw [l15_inner_self, hn]; norm_num
  have han : inner ℝ a n = 0 := by
    rw [hadef, inner_sub_left, real_inner_smul_left, hnn, hmdef]; ring
  have ha2 : ‖a‖ ^ 2 = 1 - m ^ 2 := by rw [hadef, hmdef]; exact Dandelin.norm_sub_inner_smul_sq he hn
  have hae : inner ℝ a e = 1 - m ^ 2 := by
    rw [hadef, inner_sub_left, real_inner_smul_left, l15_inner_self e, he, real_inner_comm,
      ← hmdef]; ring
  have ha0 : a ≠ 0 := by
    intro h; rw [h, norm_zero] at ha2; nlinarith
  obtain ⟨f, hf, hfS⟩ := Dandelin.exists_unit_orth ({e, n} : Finset E3)
    (by
      calc ({e, n} : Finset E3).card ≤ 2 := Finset.card_le_two
        _ < Module.finrank ℝ E3 := by rw [finrank_euclideanSpace_fin]; norm_num)
  have hfe : inner ℝ f e = 0 := hfS e (by simp)
  have hfn : inner ℝ f n = 0 := hfS n (by simp)
  have haf : inner ℝ a f = 0 := by
    rw [hadef, inner_sub_left, real_inner_smul_left, real_inner_comm, hfe,
      real_inner_comm, hfn]; ring
  have hn0 : n ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  have hm2 : 1 - m ^ 2 ≠ 0 := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (b - inner ℝ (p₀ - V) e) / (1 - m ^ 2) := ⟨_, rfl⟩
  obtain ⟨p, hpdef⟩ : ∃ p : E3, p = p₀ + t • a := ⟨_, rfl⟩
  have hpP : inner ℝ (p - p₀) n = 0 := by
    rw [hpdef, add_sub_cancel_left, real_inner_smul_left, han, mul_zero]
  have hpe : inner ℝ (p - V) e = b := by
    rw [hpdef, show p₀ + t • a - V = (p₀ - V) + t • a by abel, inner_add_left,
      real_inner_smul_left, hae, ht, div_mul_cancel₀ _ hm2]; ring
  refine ⟨p, f +ᵥ p, ?_, ?_⟩
  · intro h
    have : f = 0 := by
      have h' := congrArg (· -ᵥ p) h
      simp only [vsub_self, vadd_vsub] at h'
      exact h'.symm
    rw [this, norm_zero] at hf; norm_num at hf
  · rw [hCe]
    apply SetLike.coe_injective
    rw [l15_directrix_eq hu he_def he hα0 hα1 hd hPn]
    ext Y
    rw [SetLike.mem_coe, l15_line_mem]
    show (inner ℝ (Y - p₀) n = 0 ∧ inner ℝ (Y - V) e = d * Real.cos α ^ 2) ↔ _
    rw [← hb]
    constructor
    · rintro ⟨h1, h2⟩
      have hYn : inner ℝ (Y - p) n = 0 := by
        rw [show Y - p = (Y - p₀) - (p - p₀) by abel, inner_sub_left, h1, hpP, sub_zero]
      have hYe : inner ℝ (Y - p) e = 0 := by
        rw [show Y - p = (Y - V) - (p - V) by abel, inner_sub_left, h2, hpe, sub_self]
      have hdec := Dandelin.decomp_of_finrank_le_three
        (by rw [finrank_euclideanSpace_fin]) hn0 ha0 hf han hfn haf hYn
      have hYa : inner ℝ (Y - p) a = 0 := by
        rw [hadef, inner_sub_right, real_inner_smul_right, hYe, hYn]; ring
      rw [hYa, zero_div, zero_smul, zero_add] at hdec
      exact ⟨inner ℝ (Y - p) f, by rw [← hdec]; abel⟩
    · rintro ⟨r, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [show p + r • f - p₀ = (p - p₀) + r • f by abel, inner_add_left, hpP,
          real_inner_smul_left, hfn]; ring
      · rw [show p + r • f - V = (p - V) + r • f by abel, inner_add_left, hpe,
          real_inner_smul_left, hfe]; ring

lemma l15_ecc_eq {α β m : ℝ} (hcos : Real.cos β = √(1 - m ^ 2)) :
    Dandelin.ecc m (Real.cos α) = Real.cos β / Real.cos α := by
  rw [Dandelin.ecc, hcos]

theorem cov_Conics3_a : classical_Conics3_a := by
  intro V u hu α hα0 hα1 P hP hVP hβ S C F hC hF X hX
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  have hαI1 : α ≤ π := by linarith [Real.pi_pos]
  obtain ⟨p₀, n, e, hn, hp₀, hPn, he_def, he, hc0, hcos, hβ0, hβ1, hm1⟩ := l15_setup hu P hP hVP
  have hm := l15_noncirc hcos hβ0 hβ
  obtain ⟨d, hd, -, htan, hFe, hCe⟩ := l15_dandelin_data hu hα0 hα1 hn hPn he_def S C F hC hF
  have hXP := (hPn X).1 hX.1
  have hX2 : X ∈ Dandelin.cone2 V e (Real.cos α) := by
    rw [he_def]; exact (l15_cone_eq hu hα0.le hαI1 X).1 hX.2
  have htan' : |inner ℝ ((V + d • e) - p₀) n| = |d| * Real.sin α := by
    rw [Dandelin.inner_center_sub]; exact htan
  obtain ⟨h1, h2⟩ := Dandelin.tangent_of_proj hn hFe htan' hXP
    (by rw [hFe]; exact Dandelin.proj_mem_plane hn)
  have := (Dandelin.mem_cone2_iff_focal_directrix he hn hks hk hm hXP h1 h2).1 hX2
  rw [dist_eq_norm, this, hCe, l15_directrix_eq hu he_def he hα0 hα1 hd hPn, l15_ecc_eq hcos]

theorem cov_Conics3_b : classical_Conics3_b := by
  intro V u hu α hα0 hα1 P hP hVP hβ S C F hC hF
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  have hαI1 : α ≤ π := by linarith [Real.pi_pos]
  obtain ⟨p₀, n, e, hn, hp₀, hPn, he_def, he, hc0, hcos, hβ0, hβ1, hm1⟩ := l15_setup hu P hP hVP
  refine ⟨fun h => ?_, fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · rw [div_lt_one hk]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hα0.le (by linarith [Real.pi_pos]) h
  · rw [h, div_self hk.ne']
  · have hcov := cov_Conics3_a V u hu α hα0 hα1 P hP hVP hβ S C F hC hF
    have he1 : Real.cos (planeAxisAngle u P) / Real.cos α = 1 := by rw [h, div_self hk.ne']
    ext X
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hXP, hXc⟩
      refine ⟨hXP, ?_⟩
      have := hcov X ⟨hXP, hXc⟩
      rwa [he1, one_mul] at this
    · rintro ⟨hXP, hXd⟩
      refine ⟨hXP, ?_⟩
      have hm := l15_noncirc hcos hβ0 hβ
      obtain ⟨d, hd, -, htan, hFe, hCe⟩ := l15_dandelin_data hu hα0 hα1 hn hPn he_def S C F hC hF
      have hXP' := (hPn X).1 hXP
      have htan' : |inner ℝ ((V + d • e) - p₀) n| = |d| * Real.sin α := by
        rw [Dandelin.inner_center_sub]; exact htan
      obtain ⟨h1, h2⟩ := Dandelin.tangent_of_proj hn hFe htan' hXP'
        (by rw [hFe]; exact Dandelin.proj_mem_plane hn)
      have h3 : ‖X - F‖ = Dandelin.ecc (inner ℝ e n) (Real.cos α) *
          Metric.infDist X (Dandelin.directrix V e n p₀ (d * Real.cos α ^ 2)) := by
        rw [l15_ecc_eq hcos, he1, one_mul, ← dist_eq_norm, hXd, hCe,
          l15_directrix_eq hu he_def he hα0 hα1 hd hPn]
      have := Dandelin.directrix_converse he hn hks hk hm hXP' h1 h2 h3
      rw [l15_cone_eq hu hα0.le hαI1, ← he_def]; exact this
  · rw [one_lt_div hk]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hβ0 hαI1 h

theorem cov_Conics3_parabola_unique : classical_Conics3_parabola_unique := by
  intro V u hu α hα0 hα1 P hP hVP hβ
  obtain ⟨hk, hs, hks⟩ := l15_ks hα0 hα1
  obtain ⟨p₀, n, e, hn, hp₀, hPn, he_def, he, hc0, hcos, hβ0, hβ1, hm1⟩ := l15_setup hu P hP hVP
  have hreg := l15_regime_par hα0 hα1 hm1 hcos hβ
  have hm0 : inner ℝ e n ≠ 0 := by intro h; rw [h, abs_zero] at hreg; linarith
  have hσ : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have he' : e = (1 : ℝ) • e := (one_smul ℝ e).symm
  have hiff := l15_dandelin_iff (V := V) hu hα0 hα1 hn hPn he_def hσ he'
  have root : ∀ d : ℝ, |d * inner ℝ e n - inner ℝ (p₀ - V) n| = |d| * Real.sin α ↔
      d = inner ℝ (p₀ - V) n / (2 * inner ℝ e n) := by
    intro d
    rw [← hreg, ← abs_mul, abs_eq_abs]
    constructor
    · rintro (h | h)
      · exact absurd (by linarith : inner ℝ (p₀ - V) n = 0) hc0
      · field_simp; linarith
    · intro h; right; rw [h]; field_simp; ring
  set d₀ := inner ℝ (p₀ - V) n / (2 * inner ℝ e n)
  have hd₀ : d₀ ≠ 0 := div_ne_zero hc0 (mul_ne_zero two_ne_zero hm0)
  refine ⟨l15_S V e (Real.sin α) d₀, (hiff _).2 ⟨d₀, hd₀, rfl, (root d₀).2 rfl⟩, fun S hS => ?_⟩
  obtain ⟨d, -, rfl, h⟩ := (hiff S).1 hS
  rw [(root d).1 h]

end Dandelin.Classical
