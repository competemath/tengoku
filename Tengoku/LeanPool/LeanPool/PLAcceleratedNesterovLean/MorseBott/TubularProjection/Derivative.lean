/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import Tengoku.LeanPool.LeanPool.PLAcceleratedNesterovLean.MorseBott.TubularProjection.Defs
import Tengoku.LeanPool.LeanPool.PLAcceleratedNesterovLean.MorseBott.TubularProjection.IFT

/-!
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tubular Neighborhood Projection — Derivative and Main Theorem

Proof that `fderiv ℝ π m = V.starProjection` at each `m ∈ S`, and
the main theorem assembling all 10 properties of the projection.
-/

@[expose] public section

open Filter Topology Metric NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace PLAcceleratedNesterovLean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- ════════════════════════════════════════════════════════════════════════════
-- § Derivative of projection equals orthogonal projection onto tangent space
-- ════════════════════════════════════════════════════════════════════════════

omit [FiniteDimensional ℝ E] in
/-- Transfer `HasFDerivAt` from `g` to `f` when `f − g = o(· − a)` and `f(a) = g(a)`.
    This is weaker than `EventuallyEq.hasFDerivAt_iff` but covers perturbation estimates
    on curved submanifolds where π ≠ χ exactly but π − χ = O(‖x−m‖²) = o(‖x−m‖). -/
private abbrev hasFDerivAt_of_isLittleO_sub
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {f g : E → F'} {L : E →L[ℝ] F'} {a : E}
    (hg : HasFDerivAt g L a) (hfa : f a = g a)
    (hfg : (fun x => f x - g x) =o[𝓝 a] (fun x => x - a)) :
    HasFDerivAt f L a :=
  HasFDerivAt.of_isLittleO <|
    (hfg.add hg.isLittleO).congr_left fun _ => by rw [hfa]; abel
 -- Needed: nlinarith/linarith proofs exceed default heartbeat limit

-- Needed: nlinarith/linarith proofs exceed default heartbeat limit
omit [FiniteDimensional ℝ E] in
/-- φ is ε-Lipschitz on a ball around 0 for any ε > 0, since Dφ(0) = 0 and φ is C². -/
private abbrev phi_lipschitzOn_near_zero
    {V : Submodule ℝ E} {φ : V → V.orthogonal}
    (hφC2 : ContDiff ℝ 2 φ) (hDφ0 : fderiv ℝ φ 0 = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r > 0, ∀ a ∈ Metric.ball (0 : V) r, ∀ b ∈ Metric.ball (0 : V) r,
      ‖φ a - φ b‖ ≤ ε * ‖a - b‖ := by
  have hφ_diff : Differentiable ℝ φ := hφC2.differentiable two_ne_zero
  have hcd : ContDiff ℝ 1 (fderiv ℝ φ) := hφC2.fderiv_right (by norm_cast)
  have hDφ_cont : Continuous (fderiv ℝ φ) := hcd.continuous
  -- Step 1: fderiv ℝ φ 0 = 0 and continuity ⇒ ‖fderiv ℝ φ v‖ ≤ ε on ball(0, r₁)
  obtain ⟨r₁, hr₁_pos, hDφ_small⟩ : ∃ r₁ > 0, ∀ v : V,
      v ∈ Metric.ball (0 : V) r₁ → ‖fderiv ℝ φ v‖ ≤ ε := by
    have hball_open : @IsOpen (V →L[ℝ] V.orthogonal)
        ContinuousLinearMap.topologicalSpace (Metric.ball 0 ε) :=
      Metric.isOpen_ball
    have h0_in : fderiv ℝ φ 0 ∈ Metric.ball (0 : V →L[ℝ] V.orthogonal) ε := by
      rw [hDφ0]; exact Metric.mem_ball_self hε
    have hpre := hball_open.preimage hDφ_cont
    obtain ⟨r₁, hr₁_pos, hr₁⟩ := Metric.isOpen_iff.mp hpre 0 h0_in
    refine ⟨r₁, hr₁_pos, fun v hv => ?_⟩
    have h1 : fderiv ℝ φ v ∈ Metric.ball (0 : V →L[ℝ] V.orthogonal) ε :=
      hr₁ (Metric.mem_ball.mp hv)
    simp only [Metric.mem_ball] at h1
    change @dist _ (@PseudoMetricSpace.toDist _
      ContinuousLinearMap.seminorm.toSeminormedAddCommGroup.toPseudoMetricSpace)
      (fderiv ℝ φ v) 0 < ε at h1
    rw [dist_eq_norm, sub_zero] at h1
    exact le_of_lt h1
  -- Step 2: MVT on closedBall(0, r₁/2) ⊆ ball(0, r₁) gives the Lipschitz bound
  refine ⟨r₁ / 2, by positivity, fun a ha b hb => ?_⟩
  have hsub : Metric.closedBall (0 : V) (r₁ / 2) ⊆ Metric.ball (0 : V) r₁ :=
    Metric.closedBall_subset_ball (by linarith)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun v _ => hφ_diff.differentiableAt)
    (fun v hv => hDφ_small v (hsub hv))
    (convex_closedBall _ _)
    (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hb)))
    -- Needed: nlinarith/linarith proofs exceed default heartbeat limit
    (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp ha)))
 -- Needed: nlinarith/linarith proofs exceed default heartbeat limit

/-- At each point `m ∈ S`, the Fréchet derivative of the tubular projection
    equals `V.starProjection` (the orthogonal projection `E → E` onto the
    tangent space `V`).

    The proof is decomposed into two steps:
    1. `h_diff`: π and χ differ by `o(‖x − m‖)` near `m` (Pythagorean + small
       Lipschitz estimate from C² bounds on φ and nearest-point optimality).
    2. `h_chartHasFDeriv`: `χ` has Fréchet derivative `V.starProjection` at `m`,
       which follows from `φ 0 = 0`, `Dφ(0) = 0`, and the chain rule.
    These combine via `hasFDerivAt_of_isLittleO_sub`. -/
private abbrev tubularProj_hasFDerivAt_starProjection {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U) (hne : S.Nonempty)
    (m : E) (hm : m ∈ S) :
    ∃ V : Submodule ℝ E,
      HasFDerivAt (tubularProj hTN hne) V.starProjection m := by
  obtain ⟨V, φ, δ, hδ, hφC2, hφ0, hDφ0, hchart⟩ := hTN.submanifold_chart m hm
  refine ⟨V, ?_⟩
  -- The chart projection: nearest-point projection expressed via the local chart
  let χ : E → E := fun x =>
    m + (V.starProjection (x - m) : E) + ((φ (V.orthogonalProjectionOnto (x - m))) : E)
  -- Step 1: χ(m) = m = tubularProj(m) (both fix S)
  have h_base_eq : χ m = m := by
    simp only [χ, sub_self, map_zero, hφ0, Submodule.coe_zero, add_zero]
  have h_base : tubularProj hTN hne m = χ m := by
    rw [h_base_eq, tubularProj_fixes_S hTN hne m hm]
  -- Step 1b: π agrees with χ to first order near m.
  -- Pythagorean + small Lipschitz argument:
  --   For any c > 0, since Dφ(0) = 0, get L s.t. φ is L-Lip on ball(0,r).
  --   For x near m, decompose x − m = v + w (v ∈ V, w ∈ V⊥).
  --   χ(x) = m + v + φ(v), π(x) = m + v* + φ(v*) where v* minimizes distance.
  --   Nearest-point optimality + Pythagoras on V ⊕ V⊥:
  --     ‖v−v*‖² + ‖w−φ(v*)‖² ≤ ‖w−φ(v)‖²
  --   Expand: ‖v−v*‖ ≤ 2L(1+L)‖x−m‖ → 0, hence ‖π(x)−χ(x)‖ = o(‖x−m‖).
  have h_diff : (fun x => tubularProj hTN hne x - χ x) =o[𝓝 m]
      (fun x => x - m) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    -- Step 1: Choose ε and get Lipschitz ball for φ near 0
    have hε_pos : (0 : ℝ) < min (1 / 4) (c / 12) := lt_min (by positivity) (by linarith)
    set ε := min (1 / 4 : ℝ) (c / 12) with hε_def
    have hε_le : ε ≤ 1 / 4 := min_le_left _ _
    have hε_le_c : ε ≤ c / 12 := min_le_right _ _
    obtain ⟨r₁, hr₁, hLip_on⟩ := phi_lipschitzOn_near_zero hφC2 hDφ0 ε hε_pos
    -- Step 2: m ∈ U (since m ∈ S ⊆ U)
    have hm_U : m ∈ U := hTN.subset hm
    obtain ⟨r_U, hr_U, hball_U⟩ := isOpen_iff.mp (U_isOpen hTN) m hm_U
    -- Step 3: Choose radius ensuring x ∈ U, π(x) in chart, v/v* in Lipschitz ball
    set r := min (min (δ / 3) (r₁ / 3)) r_U with hr_def
    have hr_pos : 0 < r := lt_min (lt_min (by linarith) (by linarith)) hr_U
    have hr_le_δ3 : r ≤ δ / 3 := le_trans (min_le_left _ _) (min_le_left _ _)
    have hr_le_r13 : r ≤ r₁ / 3 := le_trans (min_le_left _ _) (min_le_right _ _)
    -- Step 4: Prove the bound on ball(m, r)
    apply Metric.eventually_nhds_iff_ball.mpr
    refine ⟨r, hr_pos, fun x hx_ball => ?_⟩
    have hx_norm : ‖x - m‖ < r := by rwa [mem_ball, dist_eq_norm] at hx_ball
    have hx_U : x ∈ U := hball_U (mem_ball.mpr (lt_of_lt_of_le
      (show dist x m < r by rwa [dist_eq_norm]) (min_le_right _ _)))
    set π_x := tubularProj hTN hne x with hπ_def
    obtain ⟨hπ_S, hπ_dist⟩ := tubularProj_mem hTN hne x hx_U
    -- ‖π(x) - m‖ ≤ 2‖x - m‖ (nearest point + triangle inequality)
    have hπ_opt : ‖x - π_x‖ ≤ ‖x - m‖ := by
      calc ‖x - π_x‖ = dist x π_x := (dist_eq_norm x π_x).symm
        _ = Metric.infDist x S := hπ_dist
        _ ≤ dist x m := Metric.infDist_le_dist_of_mem hm
        _ = ‖x - m‖ := dist_eq_norm x m
    have hπ_near : ‖π_x - m‖ ≤ 2 * ‖x - m‖ := by
      have h2 : ‖π_x - m‖ ≤ ‖π_x - x‖ + ‖x - m‖ := by
        calc ‖π_x - m‖ = ‖(π_x - x) + (x - m)‖ := by congr 1; abel
          _ ≤ ‖π_x - x‖ + ‖x - m‖ := norm_add_le _ _
      have h3 : ‖π_x - x‖ = ‖x - π_x‖ := (norm_sub_rev x π_x).symm
      linarith
    -- π(x) ∈ ball(m, δ), so we can use the chart
    have hπ_in_ball : π_x ∈ ball m δ := by
      rw [mem_ball, dist_comm, dist_eq_norm, norm_sub_rev]; linarith
    obtain ⟨v_star, hπ_eq⟩ := (hchart π_x hπ_in_ball).mp hπ_S
    -- Define v = V-component of (x - m)
    set v := V.orthogonalProjectionOnto (x - m) with hv_def
    set w := V.orthogonal.orthogonalProjectionOnto (x - m) with hw_def
    -- x - m = (v : E) + (w : E) (orthogonal decomposition)
    have hxm_decomp : x - m = (v : E) + (w : E) := by
      have h := (V.starProjection_add_starProjection_orthogonal (x - m)).symm
      rwa [Submodule.starProjection_apply, Submodule.starProjection_apply] at h
    -- π_x - m = (v_star : E) + (φ v_star : E)
    have hπ_sub : π_x - m = (v_star : E) + (φ v_star : E) := by
      rw [hπ_eq]; abel
    -- V.orthogonalProjectionOnto(π_x - m) = v_star
    have hπ_proj : V.orthogonalProjectionOnto (π_x - m) = v_star := by
      have hφ_proj : V.orthogonalProjectionOnto (φ v_star : E) = 0 :=
        Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
          (V.orthogonal.coe_mem (φ v_star))
      rw [hπ_sub, map_add,
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v_star,
        hφ_proj, add_zero]
    -- Norm bounds
    have hv_norm : ‖(v : E)‖ ≤ ‖x - m‖ :=
      Submodule.norm_orthogonalProjectionOnto_apply_le V (x - m)
    have hvs_norm : ‖(v_star : E)‖ ≤ 2 * ‖x - m‖ := by
      have h := Submodule.norm_orthogonalProjectionOnto_apply_le V (π_x - m)
      rw [hπ_proj] at h; exact le_trans h hπ_near
    -- v and v_star are in the Lipschitz ball
    have hv_ball : v ∈ ball (0 : V) r₁ := by
      rw [mem_ball, dist_zero_right]; exact lt_of_le_of_lt hv_norm (by linarith)
    have hvs_ball : v_star ∈ ball (0 : V) r₁ := by
      rw [mem_ball, dist_zero_right]; exact lt_of_le_of_lt hvs_norm (by linarith)
    have h0_ball : (0 : V) ∈ ball (0 : V) r₁ := mem_ball_self hr₁
    -- Lipschitz bounds (in subtype norms, which equal ambient norms)
    have hLip_diff : ‖φ v_star - φ v‖ ≤ ε * ‖v_star - v‖ :=
      hLip_on v_star hvs_ball v hv_ball
    have hLip_v : ‖φ v‖ ≤ ε * ‖v‖ := by
      have h := hLip_on v hv_ball 0 h0_ball
      simp only [sub_zero, hφ0] at h; exact h
    have hLip_vs : ‖φ v_star‖ ≤ ε * ‖v_star‖ := by
      have h := hLip_on v_star hvs_ball 0 h0_ball
      simp only [sub_zero, hφ0] at h; exact h
    -- χ(x) ∈ S: need m + v + φ(v) ∈ ball(m, δ) and use chart
    have h_star_eq : V.starProjection (x - m) = (v : E) :=
      Submodule.starProjection_apply V (x - m)
    have hχ_sub_m : χ x - m = (v : E) + (φ v : E) := by
      change m + V.starProjection (x - m) + (φ (V.orthogonalProjectionOnto (x - m)) : E) - m =
        (v : E) + (φ v : E)
      rw [h_star_eq]; abel
    have hχ_in_ball : χ x ∈ ball m δ := by
      rw [mem_ball, dist_comm, dist_eq_norm, norm_sub_rev,
        show χ x - m = (v : E) + (φ v : E) from hχ_sub_m]
      calc ‖(v : E) + (φ v : E)‖ ≤ ‖(v : E)‖ + ‖(φ v : E)‖ := norm_add_le _ _
        _ ≤ ‖x - m‖ + ε * ‖x - m‖ := by
            have h1 : ‖(φ v : E)‖ ≤ ε * ‖(v : E)‖ := hLip_v
            have h2 : ε * ‖(v : E)‖ ≤ ε * ‖x - m‖ :=
              mul_le_mul_of_nonneg_left hv_norm hε_pos.le
            linarith
        _ < δ := by
          have h_xm_lt : ‖x - m‖ < δ / 3 := lt_of_lt_of_le hx_norm hr_le_δ3
          have h_eps_bound : ε * ‖x - m‖ ≤ (1 / 4) * ‖x - m‖ :=
            mul_le_mul_of_nonneg_right hε_le (norm_nonneg _)
          linarith
    have hχ_S : χ x ∈ S :=
      (hchart (χ x) hχ_in_ball).mpr ⟨v, by
        have := sub_eq_iff_eq_add.mp hχ_sub_m; rw [this]; abel⟩
    -- Optimality: ‖x - π_x‖ ≤ ‖x - χ(x)‖ (nearest point)
    have hopt : ‖x - π_x‖ ≤ ‖x - χ x‖ := by
      calc ‖x - π_x‖ = dist x π_x := (dist_eq_norm x π_x).symm
        _ = Metric.infDist x S := hπ_dist
        _ ≤ dist x (χ x) := Metric.infDist_le_dist_of_mem hχ_S
        _ = ‖x - χ x‖ := dist_eq_norm x (χ x)
    -- Decompose x - π_x and x - χ(x)
    have hxπ_eq : x - π_x = ((v : E) - (v_star : E)) + ((w : E) - (φ v_star : E)) := by
      have : x - π_x = (x - m) - (π_x - m) := by abel
      rw [this, hxm_decomp, hπ_sub]; abel
    have hxχ_eq : x - χ x = (w : E) - (φ v : E) := by
      have : x - χ x = (x - m) - (χ x - m) := by abel
      rw [this, hxm_decomp, hχ_sub_m]; abel
    -- Pythagorean theorem: V-component ⊥ V⊥-component of (x - π_x)
    set a_vec := (v : E) - (v_star : E) with ha_def
    set b_vec := (w : E) - (φ v_star : E) with hb_def
    have ha_mem : a_vec ∈ V := V.sub_mem (Submodule.coe_mem v) (Submodule.coe_mem v_star)
    have hb_mem : b_vec ∈ V.orthogonal :=
      V.orthogonal.sub_mem (Submodule.coe_mem w) (Submodule.coe_mem (φ v_star))
    have hortho : @inner ℝ E _ a_vec b_vec = 0 :=
      Submodule.inner_right_of_mem_orthogonal ha_mem hb_mem
    -- ‖x - π_x‖² = ‖a_vec‖² + ‖b_vec‖² (Pythagoras)
    have hpyth : ‖x - π_x‖ * ‖x - π_x‖ = ‖a_vec‖ * ‖a_vec‖ + ‖b_vec‖ * ‖b_vec‖ := by
      rw [hxπ_eq]
      exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a_vec b_vec hortho
    -- ‖x - χ(x)‖² = ‖w - φ(v)‖² (entirely in V⊥, no V-component)
    -- From optimality: ‖a_vec‖² + ‖b_vec‖² ≤ ‖x - χ(x)‖²
    have hopt_sq : ‖a_vec‖ * ‖a_vec‖ + ‖b_vec‖ * ‖b_vec‖ ≤
        ‖x - χ x‖ * ‖x - χ x‖ := by
      rw [← hpyth]; exact mul_self_le_mul_self (norm_nonneg _) hopt
    -- Triangle: ‖w - φ(v)‖ ≤ ‖w - φ(v*)‖ + ‖φ(v*) - φ(v)‖ ≤ ‖b_vec‖ + ε‖v* - v‖
    have coe_sub_W : ∀ a b : V.orthogonal, ((a - b : V.orthogonal) : E) = (a : E) - (b : E) :=
      fun a b => AddSubgroupClass.coe_sub a b
    have coe_sub_V : ∀ a b : V, ((a - b : V) : E) = (a : E) - (b : E) :=
      fun a b => AddSubgroupClass.coe_sub a b
    have htri : ‖x - χ x‖ ≤ ‖b_vec‖ + ε * ‖a_vec‖ := by
      rw [hxχ_eq]
      have hsplit : (w : E) - (φ v : E) = b_vec + ((φ v_star : E) - (φ v : E)) := by
        rw [hb_def]; abel
      rw [hsplit]
      refine le_trans (norm_add_le _ _) (add_le_add le_rfl ?_)
      calc ‖(φ v_star : E) - (φ v : E)‖
          = ‖((φ v_star - φ v : V.orthogonal) : E)‖ := by rw [coe_sub_W]
        _ = ‖φ v_star - φ v‖ := rfl
        _ ≤ ε * ‖v_star - v‖ := hLip_diff
        _ = ε * ‖((v_star - v : V) : E)‖ := by rfl
        _ = ε * ‖(v_star : E) - (v : E)‖ := by rw [coe_sub_V]
        _ = ε * ‖a_vec‖ := by congr 1; exact norm_sub_rev _ _
    -- Core algebraic bound: a² + b² ≤ (b + εa)² gives a(1-ε²) ≤ 2bε
    set a := ‖a_vec‖ with ha_norm_def
    set b := ‖b_vec‖ with hb_norm_def
    have ha_nn : 0 ≤ a := norm_nonneg _
    have hb_nn : 0 ≤ b := norm_nonneg _
    have hcore : a * a + b * b ≤ (b + ε * a) * (b + ε * a) := by
      calc a * a + b * b ≤ ‖x - χ x‖ * ‖x - χ x‖ := hopt_sq
        _ ≤ (b + ε * a) * (b + ε * a) := mul_self_le_mul_self (norm_nonneg _) htri
    have hcore2 : a * a * (1 - ε * ε) ≤ 2 * b * ε * a := by
      have hexp : (b + ε * a) * (b + ε * a) =
          b * b + 2 * b * (ε * a) + ε * a * (ε * a) := by ring
      have key : a * a ≤ 2 * b * (ε * a) + ε * a * (ε * a) := by
        have h_combined := le_trans hcore (le_of_eq hexp)
        linarith
      have factored : a * a * (1 - ε * ε) = a * a - ε * ε * (a * a) := by ring
      have rearranged : ε * a * (ε * a) = ε * ε * (a * a) := by ring
      linarith
    have hε_sq : 1 - ε * ε ≥ 15 / 16 := by
      have := mul_self_le_mul_self hε_pos.le hε_le
      linarith
    have ha_bound : a ≤ 3 * b * ε := by
      by_cases ha0 : a = 0
      · rw [ha0]; positivity
      · have ha_pos : 0 < a := lt_of_le_of_ne ha_nn (Ne.symm ha0)
        have h_cancel : a * (1 - ε * ε) ≤ 2 * b * ε := by
          by_contra h; push Not at h
          have h1 := mul_lt_mul_of_pos_right h ha_pos
          have : a * (1 - ε * ε) * a = a * a * (1 - ε * ε) := by ring
          linarith [hcore2]
        have h_step : a * (15 / 16) ≤ 2 * b * ε :=
          le_trans (mul_le_mul_of_nonneg_left (by linarith : (15:ℝ)/16 ≤ 1 - ε * ε) ha_nn)
                   h_cancel
        have h_bε_nn : 0 ≤ b * ε := mul_nonneg hb_nn hε_pos.le
        linarith
    -- Bound b ≤ 2‖x-m‖
    have hw_norm : ‖(w : E)‖ ≤ ‖x - m‖ :=
      Submodule.norm_orthogonalProjectionOnto_apply_le V.orthogonal (x - m)
    have hb_bound : b ≤ 2 * ‖x - m‖ := by
      have hφvs_coe : ‖(φ v_star : E)‖ ≤ ε * ‖(v_star : E)‖ := hLip_vs
      have hvs_coe : ‖(v_star : E)‖ ≤ 2 * ‖x - m‖ := hvs_norm
      calc b ≤ ‖(w : E)‖ + ‖(φ v_star : E)‖ := norm_sub_le _ _
        _ ≤ ‖x - m‖ + ε * ‖(v_star : E)‖ := by
            have h5 := hw_norm; have h6 := hφvs_coe; linarith
        _ ≤ ‖x - m‖ + (1/4) * (2 * ‖x - m‖) := by
            have := mul_le_mul hε_le hvs_coe (norm_nonneg _) (by positivity : (0:ℝ) ≤ 1/4)
            linarith
        _ ≤ 2 * ‖x - m‖ := by linarith [norm_nonneg (x - m)]
    -- ‖π(x) - χ(x)‖ ≤ (1 + ε) * a
    have hdiff_bound : ‖tubularProj hTN hne x - χ x‖ ≤ (1 + ε) * a := by
      have h_eq : π_x - χ x = ((v_star : E) - (v : E)) + ((φ v_star : E) - (φ v : E)) := by
        have : π_x - χ x = (π_x - m) - (χ x - m) := by abel
        rw [this, hπ_sub, hχ_sub_m]; abel
      have h_lip_coe : ‖(φ v_star : E) - (φ v : E)‖ ≤ ε * a := by
        calc ‖(φ v_star : E) - (φ v : E)‖
            = ‖((φ v_star - φ v : V.orthogonal) : E)‖ := by rw [coe_sub_W]
          _ = ‖φ v_star - φ v‖ := rfl
          _ ≤ ε * ‖v_star - v‖ := hLip_diff
          _ = ε * ‖((v_star - v : V) : E)‖ := by rfl
          _ = ε * ‖(v_star : E) - (v : E)‖ := by rw [coe_sub_V]
          _ = ε * ‖a_vec‖ := by congr 1; exact norm_sub_rev _ _
      have h_vs_norm : ‖(v_star : E) - (v : E)‖ = a := by
        change ‖(v_star : E) - (v : E)‖ = ‖a_vec‖
        exact norm_sub_rev _ _
      calc ‖tubularProj hTN hne x - χ x‖ = ‖π_x - χ x‖ := rfl
        _ = ‖((v_star : E) - (v : E)) + ((φ v_star : E) - (φ v : E))‖ := by rw [h_eq]
        _ ≤ ‖(v_star : E) - (v : E)‖ + ‖(φ v_star : E) - (φ v : E)‖ := norm_add_le _ _
        _ ≤ a + ε * a := add_le_add (le_of_eq h_vs_norm) h_lip_coe
        _ = (1 + ε) * a := by ring
    -- Final: (1+ε) * 3bε ≤ (5/4) * 6ε * ‖x-m‖ ≤ c * ‖x-m‖
    have hxm_nn : 0 ≤ ‖x - m‖ := norm_nonneg _
    have h1 : (1 + ε) * a ≤ (1 + ε) * (3 * b * ε) :=
      mul_le_mul_of_nonneg_left ha_bound (by linarith)
    have h2 : (1 + ε) * (3 * b * ε) ≤ (1 + ε) * (3 * (2 * ‖x - m‖) * ε) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ 1 + ε)
      apply mul_le_mul_of_nonneg_right _ hε_pos.le
      have h_bb := hb_bound
      linarith
    have h3 : (1 + ε) * (3 * (2 * ‖x - m‖) * ε) = (1 + ε) * 6 * ε * ‖x - m‖ := by ring
    have h4 : (1 + ε) * 6 * ε * ‖x - m‖ ≤ c * ‖x - m‖ := by
      apply mul_le_mul_of_nonneg_right _ hxm_nn
      have h_1e : (1 : ℝ) + ε ≤ 5 / 4 := by linarith
      have h_6e : 6 * ε ≤ c / 2 := by linarith
      calc (1 + ε) * 6 * ε = (1 + ε) * (6 * ε) := by ring
        _ ≤ (5 / 4) * (c / 2) :=
            mul_le_mul h_1e h_6e (by positivity) (by positivity)
        _ = 5 * c / 8 := by ring
        _ ≤ c := by linarith
    have h5 := hdiff_bound
    linarith
  -- Step 2: χ has Fréchet derivative V.starProjection at m
  -- (The φ-term vanishes because Dφ(0) = 0; the starProjection term is linear.)
  have h_chartHasFDeriv : HasFDerivAt χ V.starProjection m := by
    -- HasFDerivAt (· - m) at m
    have h_sub : HasFDerivAt (· - m) (.id ℝ E) m := hasFDerivAt_sub_const m
    -- HasFDerivAt (V.starProjection ∘ (· - m)) at m
    have h_star : HasFDerivAt (fun x => V.starProjection (x - m)) V.starProjection m := by
      have := V.starProjection.hasFDerivAt.comp m h_sub
      rwa [ContinuousLinearMap.comp_id] at this
    -- φ is differentiable at 0 with derivative 0
    have hφ_fd : HasFDerivAt φ (0 : V →L[ℝ] V.orthogonal) (0 : V) := by
      have hd : Differentiable ℝ φ := hφC2.differentiable two_ne_zero
      have h := (hd (0 : V)).hasFDerivAt
      rw [hDφ0] at h; exact h
    -- V.orthogonalProjectionOnto evaluates to 0 at (m - m)
    have h_proj_zero : V.orthogonalProjectionOnto (m - m) = 0 := by rw [sub_self, map_zero]
    -- HasFDerivAt (V.orthogonalProjectionOnto ∘ (· - m)) at m
    have h_proj : HasFDerivAt (fun x => V.orthogonalProjectionOnto (x - m))
        (V.orthogonalProjectionOnto.comp (.id ℝ E)) m :=
      (V.orthogonalProjectionOnto : E →L[ℝ] V).hasFDerivAt.comp m h_sub
    -- HasFDerivAt (φ ∘ V.orthogonalProjectionOnto ∘ (· - m)) at m with derivative 0
    have h_phi : HasFDerivAt (fun x => φ (V.orthogonalProjectionOnto (x - m)))
        (0 : E →L[ℝ] V.orthogonal) m := by
      have h1 : HasFDerivAt φ (0 : V →L[ℝ] V.orthogonal)
          (V.orthogonalProjectionOnto (m - m)) := by
        rw [h_proj_zero]; exact hφ_fd
      have h2 := h1.comp m h_proj
      rwa [ContinuousLinearMap.zero_comp] at h2
    -- Coerce φ-term to E; derivative is still 0
    have h_coe : HasFDerivAt (fun x => (φ (V.orthogonalProjectionOnto (x - m)) : E))
        (0 : E →L[ℝ] E) m := by
      have := V.orthogonal.subtypeL.hasFDerivAt.comp m h_phi
      rwa [ContinuousLinearMap.comp_zero] at this
    -- Combine: χ = (m + star_part) + coe_part, derivative = V.starProjection + 0
    have h_all := (h_star.const_add m).add h_coe
    rwa [add_zero] at h_all
  -- Combine: transfer HasFDerivAt from χ to π via Lipschitz perturbation.
  -- Since π(m) = χ(m) and (π − χ) = o(‖· − m‖), HasFDerivAt χ L m ⟹ HasFDerivAt π L m.
  exact hasFDerivAt_of_isLittleO_sub h_chartHasFDeriv h_base h_diff

-- ════════════════════════════════════════════════════════════════════════════
-- § Main theorem: 10 properties
-- ════════════════════════════════════════════════════════════════════════════

end PLAcceleratedNesterovLean
