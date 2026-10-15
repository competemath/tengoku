/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import Tengoku.LeanPool.LeanPool.PLAcceleratedNesterovLean.MorseBott.TubularProjection.Defs
public import Tengoku

/-!
# Tubular Neighborhood Projection -- IFT-Based C¹ Regularity

IFT-based proof that the nearest-point projection is C¹ at every point of
the submanifold S.
-/

@[expose] public section

open Filter Topology Metric NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace PLAcceleratedNesterovLean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private lemma isInvertible_of_bijective_finiteDimensional
    {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : A →L[ℝ] B) (hL : Function.Bijective L) :
    L.IsInvertible := by
  refine ⟨(LinearEquiv.ofBijective L.toLinearMap ?_).toContinuousLinearEquiv, ?_⟩
  · exact hL
  · ext x
    rfl

-- ════════════════════════════════════════════════════════════════════════════
-- § IFT-based local C¹ regularity of the tubular projection
-- ════════════════════════════════════════════════════════════════════════════

/-! ### Analysis of `fderiv ℝ π x` for `x ∉ S`

At `m ∈ S`, `fderiv ℝ π m = V_m.starProjection` (Property 9). But for
`x ∈ U \ S`, the derivative is **not** simply the orthogonal projection
onto the tangent space at `π(x)`. In chart coordinates at `m = π(x)`:

  `π(y) = m + v*(y − m) + φ(v*(y − m))`

where `v* : E → V` is the IFT solution to the first-order optimality
equation `F(r, v) = 0`. The derivative is:

  `fderiv ℝ π x = (ι_V + ι_{V⊥} ∘ Dφ(v₀)) ∘ Dv*(r₀)`

where `v₀ = v*(x − m)`, `r₀ = x − m`, and `Dv*` is given by the
implicit derivative formula `Dv* = −(∂F/∂v)⁻¹ ∘ (∂F/∂r)`.

At `v₀ = 0` (i.e., `x = m ∈ S`), `Dφ(0) = 0` and `Dv*(0) = proj_V`,
recovering `fderiv ℝ π m = V.starProjection`.

At `v₀ ≠ 0`, `Dφ(v₀) ≠ 0`, and the derivative depends on second-order
geometry (D²φ) of the submanifold. Continuity of `x ↦ fderiv ℝ π x`
follows from the IFT giving C¹ regularity of `v*`.

**Why the IFT is essential:** To determine `fderiv ℝ π x` at `x ∉ S`,
one must solve the optimality equation (which IS the IFT). Composing
`x ↦ π(x) ↦ V_{π(x)} ↦ V_{π(x)}.starProjection` only gives the
derivative on `S`; the IFT extends it to all of `U`. -/

/-- The optimality equation `F` is C¹ when `φ` is C².
This follows because `F` involves `φ`, `fderiv ℝ φ`, and the
continuous linear maps `V.orthogonalProjectionOnto`, `V⊥.orthogonalProjectionOnto`,
and the adjoint operation. Since `φ` is C², `fderiv ℝ φ` is C¹,
and the adjoint is a continuous linear operation. -/
private lemma contDiff_adjoint
    {n : WithTop ℕ∞}
    {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂] [FiniteDimensional ℝ F₂] :
    ContDiff ℝ n
      (ContinuousLinearMap.adjoint : (F₁ →L[ℝ] F₂) → (F₂ →L[ℝ] F₁)) :=
  IsBoundedLinearMap.contDiff {
    map_add := fun A B => by
      simp_all
    map_smul := fun c A => by
      simp_all
    bound := ⟨1, one_pos, fun A => by
      simp_all⟩
  }

/--
@isnad1 id=contdiff.1h4v.s10.af55923ac8f6 from=translated src=- shape=6cc83242 vocab=8944dabb
-/
lemma optimalityEqn_contDiff
    {V : Submodule ℝ E} {φ : V → V.orthogonal}
    (hφ : ContDiff ℝ 2 φ) (m : E) :
    ContDiff ℝ 1 (optimalityEqn φ m) := by
  unfold optimalityEqn
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  -- The residual r - v - φ(v) is C¹ as a function of (r, v)
  have hres : ContDiff ℝ 1 fun p : E × V =>
      p.1 - (V.subtypeL p.2 : E) - (V.orthogonal.subtypeL (φ p.2) : E) :=
    (contDiff_fst.sub (V.subtypeL.contDiff.comp contDiff_snd)).sub
      (V.orthogonal.subtypeL.contDiff.comp (hφ1.comp contDiff_snd))
  -- fderiv ℝ φ is C¹ (since φ is C²)
  have hDφ : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_cast)
  -- The adjoint of (fderiv ℝ φ v) is C¹ in v
  have hDφ_adj : ContDiff ℝ 1 fun v : V =>
      (ContinuousLinearMap.adjoint (fderiv ℝ φ v) : V.orthogonal →L[ℝ] V) :=
    contDiff_adjoint.comp hDφ
  -- Sum: projV(res) + (Dφ(v))†(projW(res))
  exact ((V.orthogonalProjectionOnto : E →L[ℝ] V).contDiff.comp hres).add
    ((hDφ_adj.comp contDiff_snd).clm_apply
      ((V.orthogonal.orthogonalProjectionOnto : E →L[ℝ] V.orthogonal).contDiff.comp hres))

/-- If v' locally minimizes g(v) = ‖r - v↑ - (φ v)↑‖², then F(r, v') = 0.
@isnad1 id=eq.2h6v.s10.8d79bd371fcf from=translated src=- shape=73f7ea47 vocab=adc42254
-/
lemma localMin_sq_dist_implies_optimalityEqn
    {V : Submodule ℝ E} {φ : V → V.orthogonal}
    (hφC2 : ContDiff ℝ 2 φ) (m : E) {r : E} {v' : V}
    (h_min : IsLocalMin (fun v : V => ‖r - (v : E) - (φ v : E)‖ ^ 2) v') :
    optimalityEqn φ m (r, v') = 0 := by
  set g : V → ℝ := fun v => ‖r - (v : E) - (φ v : E)‖ ^ 2
  set res : V → E := fun v => r - (v : E) - (φ v : E)
  set ιV := V.subtypeL
  set ιW := V.orthogonal.subtypeL
  set Dφ := fderiv ℝ φ v'
  have hφ_diff : Differentiable ℝ φ := hφC2.differentiable two_ne_zero
  set res' : V →L[ℝ] E := -(ιV + ιW.comp Dφ)
  have hres_fda : HasFDerivAt res res' v' := by
    have h1 : HasFDerivAt (fun v : V => (v : E)) ιV v' := ιV.hasFDerivAt
    have h2 : HasFDerivAt (fun v : V => (φ v : E)) (ιW.comp Dφ) v' :=
      ιW.hasFDerivAt.comp v' (hφ_diff.differentiableAt.hasFDerivAt)
    have h3 := ((hasFDerivAt_const r v').sub h1).sub h2
    have : (0 : V →L[ℝ] E) - ιV - ιW.comp Dφ = res' :=
      ContinuousLinearMap.ext fun w => by
        simp only [zero_sub,
          FunLike.coe_sub,
          ContinuousLinearMap.coe_comp,
          Pi.sub_apply,
          neg_apply,
          Function.comp_apply, neg_add_rev,
          add_apply, res']
        abel
    rwa [this] at h3
  have hg_fda : HasFDerivAt g (2 • (innerSL ℝ (res v')).comp res') v' :=
    hres_fda.norm_sq
  have h_fderiv_zero : fderiv ℝ g v' = 0 := h_min.fderiv_eq_zero
  have h_deriv_eq : (2 • (innerSL ℝ (res v')).comp res') = (0 : V →L[ℝ] ℝ) := by
    rw [← h_fderiv_zero]; exact hg_fda.fderiv.symm
  have h_res_inner : ∀ w : V, @inner ℝ E _ (res v') (res' w) = 0 := by
    intro w
    have hw := ContinuousLinearMap.ext_iff.mp h_deriv_eq w
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
               zero_apply, innerSL_apply_apply] at hw
    rw [two_smul] at hw; linarith
  have h_sum_zero : ∀ w : V,
      @inner ℝ E _ (res v') (w : E) +
      @inner ℝ E _ (res v') ((Dφ w : V.orthogonal) : E) = 0 := by
    intro w
    have := h_res_inner w
    simp only [res', neg_apply, add_apply,
               ContinuousLinearMap.comp_apply] at this
    rw [inner_neg_right, neg_eq_zero, inner_add_right] at this
    exact this
  set F := optimalityEqn φ m (r, v')
  suffices h_F_inner : ∀ w : V, @inner ℝ V _ F w = 0 by
    have := h_F_inner F; rwa [inner_self_eq_zero] at this
  intro w
  change @inner ℝ V _ (V.orthogonalProjectionOnto (res v') +
    Dφ.adjoint (V.orthogonal.orthogonalProjectionOnto (res v'))) w = 0
  rw [inner_add_left]
  have hterm1 : @inner ℝ V _ (V.orthogonalProjectionOnto (res v')) w =
      @inner ℝ E _ (res v') (w : E) :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right w (res v')
  have hterm2 : @inner ℝ V _
      (Dφ.adjoint (V.orthogonal.orthogonalProjectionOnto (res v'))) w =
      @inner ℝ E _ (res v') ((Dφ w : V.orthogonal) : E) := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (Dφ w) (res v')
  rw [hterm1, hterm2]; exact h_sum_zero w

end PLAcceleratedNesterovLean
