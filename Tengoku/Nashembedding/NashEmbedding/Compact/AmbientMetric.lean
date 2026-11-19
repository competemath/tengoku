/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ambient metric along an immersion

Let `u : M → E'` be a smooth immersion of a manifold `M` (modelled on `E`) into a
finite-dimensional real inner-product space `E'`, and `g` a smooth Riemannian
metric on `M`.  At each `x`, with `L = mfderiv u x : T_xM → E'` injective, put

    P := (L† ∘ L)⁻¹ ∘ L†   (left inverse of `L`),   Q := L ∘ P   (projection onto `range L`),
    G x a b := g_x (P a) (P b) + ⟪(1 - Q) a, (1 - Q) b⟫.

Then `G x` is a positive-definite symmetric bilinear form on `E'` with
`G x (L v) (L w) = g_x v w`, and `x ↦ G x` is smooth `M → (E' →L E' →L ℝ)`.

**Theorem** (`exists_ambient_metric`): such a `G` exists.  It is the input to the
Whitney-extension step (`WhitneyExtension.lean`), which extends `G ∘ u⁻¹`
from `u '' M` to a smooth matrix field on `E'`.

Smoothness.  `T_xM` is definitionally `E`, but `x ↦ mfderiv u x` is not
continuous as a raw map `M → (E →L E')` (the chart at `x` jumps).  Mathlib's
invariant form is `inTangentCoordinates`: near `x₀`,
    L̃ x := mfderiv u x ∘L S x,   S x := (trivializationAt E (TangentSpace I) x₀).symmL ℝ x,
is smooth (`ContMDiffAt.mfderiv_const`), and similarly
    g̃ x a b := g.inner x (S x a) (S x b)
is smooth (section smoothness of `g` in the trivialization at `x₀`).  Since
`S x` is a linear isomorphism, `pinv (L ∘L S) = S⁻¹ ∘L pinv L`, so
    G x a b = g̃ x (pinv (L̃ x) a) (pinv (L̃ x) b) + ⟪(1 - L̃ x ∘L pinv (L̃ x)) a, …⟫,
a smooth expression in `L̃ x` and `g̃ x` (leaves L1–L4 for `pinv`).

Leaves L1–L7 and the assembly L8 were proved by Aristotle (project 6f927eaf, 2026-08-30).
-/

open scoped Manifold ContDiff Topology InnerProduct
open Set Function ContinuousLinearMap Bundle

noncomputable section

namespace NashEmbedding

/-! ## Pseudo-inverse of an injective linear map between inner-product spaces -/

section Pinv

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

/-- The Moore–Penrose left inverse `(L† ∘ L)⁻¹ ∘ L†` (with `inverse 0 = 0` if `L† ∘ L`
  is not invertible).-/
def pinv (L : E →L[ℝ] E') : E' →L[ℝ] E :=
  (ContinuousLinearMap.inverse (L.adjoint ∘L L)) ∘L L.adjoint

/-- **L1.** The adjoint is smooth (it is a linear isometry equivalence).
@isnad1 id=contdiff.0h2v.s11.68f6eedb84e4 from=translated src=- shape=bb4aae86 vocab=b9584a6f
-/
theorem contDiff_adjoint :
    ContDiff ℝ ∞ (fun L : E →L[ℝ] E' => L.adjoint) := by
  have h1 : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h2 : CompleteSpace E' := FiniteDimensional.complete ℝ E'
  let f : (E →L[ℝ] E') →ₗ[ℝ] (E' →L[ℝ] E) :=
    { toFun := fun L => L.adjoint
      map_add' := fun L L' => map_add ContinuousLinearMap.adjoint L L'
      map_smul' := fun c L => by simp }
  have hb : ∀ L : E →L[ℝ] E', ‖f L‖ ≤ 1 * ‖L‖ := by
    intro L
    simp only [one_mul]
    exact le_of_eq (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E') |>.norm_map L)
  exact (f.mkContinuous 1 hb).contDiff

/-- **L2.** For injective `L`, `L† ∘ L` is invertible.
@isnad1 id=isinvert.1h3v.s11.0efda3207709 from=translated src=- shape=80818cb8 vocab=63eba807
-/
theorem isInvertible_adjoint_comp_self {L : E →L[ℝ] E'} (hL : Injective L) :
    (L.adjoint ∘L L).IsInvertible := by
  have h1 : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h2 : CompleteSpace E' := FiniteDimensional.complete ℝ E'
  have hker : (L.adjoint ∘L L : E →L[ℝ] E).toLinearMap.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx0 : (L.adjoint ∘L L) x = 0 := hx
    have h3 : ‖L x‖ ^ 2 = RCLike.re (inner ℝ ((L.adjoint ∘L L) x) x) :=
      ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left L x
    rw [hx0] at h3
    simp at h3
    exact hL (by rw [h3, map_zero])
  have hrange : (L.adjoint ∘L L : E →L[ℝ] E).toLinearMap.range = ⊤ :=
    LinearMap.range_eq_top.mpr
      ((LinearMap.injective_iff_surjective).1 (LinearMap.ker_eq_bot.mp hker))
  exact ⟨ContinuousLinearEquiv.ofBijective (L.adjoint ∘L L) hker hrange, rfl⟩

/-- **L3.** `pinv` is a left inverse on injective maps.
@isnad1 id=eq.1h3v.s9.13b67065a075 from=translated src=- shape=96c3749f vocab=d4d796b1
-/
theorem pinv_comp {L : E →L[ℝ] E'} (hL : Injective L) :
    pinv L ∘L L = ContinuousLinearMap.id ℝ E := by
  have h := isInvertible_adjoint_comp_self hL
  rw [pinv, ContinuousLinearMap.comp_assoc, h.inverse_comp_self]

/-- **L4.** `pinv` is smooth at injective maps.
@isnad1 id=contdiff.1h3v.s9.06186baf4b30 from=translated src=- shape=5301e85e vocab=26c0a8fd
-/
theorem contDiffAt_pinv {L : E →L[ℝ] E'} (hL : Injective L) :
    ContDiffAt ℝ ∞ (pinv : (E →L[ℝ] E') → (E' →L[ℝ] E)) L := by
  have h1 : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hA : ContDiffAt ℝ ∞ (fun M : E →L[ℝ] E' => M.adjoint ∘L M) L :=
    (contDiff_adjoint.clm_comp contDiff_id).contDiffAt
  have hinv : ContDiffAt ℝ ∞ (ContinuousLinearMap.inverse : (E →L[ℝ] E) → (E →L[ℝ] E))
      (L.adjoint ∘L L) := (isInvertible_adjoint_comp_self hL).contDiffAt_map_inverse
  have hcomp : ContDiffAt ℝ ∞
      (fun M : E →L[ℝ] E' => ContinuousLinearMap.inverse (M.adjoint ∘L M)) L :=
    ContDiffAt.comp (𝕜 := ℝ) (n := ∞) (x := L)
      (g := (ContinuousLinearMap.inverse : (E →L[ℝ] E) → (E →L[ℝ] E)))
      (f := fun M : E →L[ℝ] E' => M.adjoint ∘L M) hinv hA
  exact hcomp.clm_comp contDiff_adjoint.contDiffAt

end Pinv

/-! ## Smoothness of the differential and of the metric in tangent coordinates

  `TangentSpace I x` is definitionally `E` but carries no norm, so `mfderiv` and
  `g.inner x` cannot be composed with `∘L` in statements.  We use Mathlib's
  invariant forms (`inTangentCoordinates`, the trivialization at `x₀`) for the
  smoothness leaves, and explicit definitional casts `diff`, `metricAt` for the
  pointwise algebra. -/

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- The differential `mfderiv u x`, read as a map `E →L E'` (definitional cast).-/
def diff (u : M → E') (x : M) : E →L[ℝ] E' := mfderiv I 𝓘(ℝ, E') u x

/-- The metric at `x`, read as a bilinear form on `E` (definitional cast).-/
def metricAt (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) (x : M) :
    E →L[ℝ] E →L[ℝ] ℝ := g.inner x

/-- Coordinate change from the model fibre to `T_xM ≅ E`, in the trivialization at `x₀`
  (definitional cast of `symmL`).-/
def tcoord (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] (x₀ x : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x₀).symmL ℝ x

omit [FiniteDimensional ℝ E] in
/-- **L6.** The differential in tangent coordinates at `x₀` is smooth near `x₀`
  (`ContMDiffAt.mfderiv_const`).
@isnad1 id=contmdif.1h7v.s10.634114a92c64 from=translated src=- shape=b550b562 vocab=745ca75c
-/
theorem contMDiffAt_inTangentCoordinates_mfderiv {u : M → E'} (hu : ContMDiff I 𝓘(ℝ, E') ∞ u)
    (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞
      (inTangentCoordinates I 𝓘(ℝ, E') id u (mfderiv I 𝓘(ℝ, E') u) x₀) x₀ :=
  (hu x₀).mfderiv_const (m := ∞) (n := ∞) (by simp)

omit [FiniteDimensional ℝ E] in
/-- **L7.** The metric, read in the trivialization at `x₀`, is smooth near `x₀`
  (unfold `g.contMDiff` with `contMDiffAt_section`).
@isnad1 id=contmdif.0h6v.s13.8d4f3899ddbd from=translated src=- shape=8860a8be vocab=b28faa9d
-/
theorem contMDiffAt_metric_trivialization
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨x, g.inner x⟩).2) x₀ :=
  -- `(contMDiffAt_section x₀).1 (g.contMDiff x₀)`, up to unfolding `TotalSpace.mk'`.
  (contMDiffAt_section (F := E →L[ℝ] E →L[ℝ] ℝ) x₀).1 (g.contMDiff x₀)

end Coordinates

/-! ## The ambient metric -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

/-- The Euclidean inner product of `E'` as a real bilinear form (over `ℝ` the conjugate
  linearity of `innerSL` is trivial).-/
def innerBilin (E' : Type*) [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] :
    E' →L[ℝ] E' →L[ℝ] ℝ :=
  innerSL ℝ

/-- The ambient metric along `u` at `x`, as a bilinear form on `E'`:
  `G x a b = g_x (P a) (P b) + ⟪(1 - L P) a, (1 - L P) b⟫` with `L = diff u x`, `P = pinv L`.-/
def ambientMetric (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (u : M → E') (x : M) : E' →L[ℝ] E' →L[ℝ] ℝ :=
  let L : E →L[ℝ] E' := diff (I := I) u x
  let P : E' →L[ℝ] E := pinv L
  let R : E' →L[ℝ] E' := ContinuousLinearMap.id ℝ E' - L ∘L P
  (metricAt g x).bilinearComp P P + (innerBilin E').bilinearComp R R

end Main

end NashEmbedding

end
