/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Analytic.SimpleRootCover
import Tengoku.LanaOka.Oka.Topology.Algebra.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Holomorphic branches of simple roots

Let `Q` be a monic polynomial whose coefficients are holomorphic functions on an open subset `V`
of a complex normed space, and let `a` be a simple root of `Q(c)`, `c ∈ V`. Then near `c` the
roots of `Q(y)` near `a` are given by a single holomorphic function `φ` with `φ(c) = a`
(`ComplexAnalytic.exists_simpleRoot_branch`): existence of roots near `a` is the continuity of
roots (`Polynomial.eventually_exists_isRoot_near_of_continuous`), uniqueness follows from the mean
value inequality since `∂Q/∂v` stays close to `Q(c)'(a) ≠ 0`, and holomorphy is
`Polynomial.differentiableAt_of_isRoot_of_differentiableAt_coeff`.
-/

open Filter Topology Metric Polynomial

namespace ComplexAnalytic

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The polynomial `Q(y)` obtained by evaluating the coefficients of `Q` at `y`. -/
abbrev evalPoly (Q : Polynomial (E → ℂ)) (y : E) : ℂ[X] :=
  Q.map (Pi.evalRingHom (fun _ ↦ ℂ) y)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma coeff_evalPoly (Q : Polynomial (E → ℂ)) (y : E) (k : ℕ) :
    (evalPoly Q y).coeff k = Q.coeff k y := by
  simp [evalPoly, coeff_map]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma natDegree_evalPoly_le (Q : Polynomial (E → ℂ)) (y : E) :
    (evalPoly Q y).natDegree ≤ Q.natDegree :=
  natDegree_map_le

omit [NormedSpace ℂ E] in
lemma continuousOn_eval_evalPoly {Q : Polynomial (E → ℂ)} {V : Set E}
    (hc : ∀ k, ContinuousOn (Q.coeff k) V) :
    ContinuousOn (fun q : E × ℂ ↦ (evalPoly Q q.1).eval q.2) (V ×ˢ Set.univ) := by
  have h : ∀ q : E × ℂ, (evalPoly Q q.1).eval q.2 =
      ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i q.1 * q.2 ^ i := fun q ↦ by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_evalPoly_le Q q.1))]
    simp
  simp only [h]
  exact continuousOn_finsetSum _ fun i _ ↦ ((hc i).comp continuousOn_fst fun q hq ↦ hq.1).mul
    (continuous_snd.pow i).continuousOn

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma derivative_evalPoly (Q : Polynomial (E → ℂ)) (y : E) :
    (evalPoly Q y).derivative = evalPoly (derivative Q) y :=
  derivative_map _ _

lemma differentiableOn_coeff_derivative {Q : Polynomial (E → ℂ)} {V : Set E}
    (hd : ∀ k, DifferentiableOn ℂ (Q.coeff k) V) (k : ℕ) :
    DifferentiableOn ℂ ((derivative Q).coeff k) V := by
  have h : (derivative Q).coeff k = fun y ↦ Q.coeff (k + 1) y * ((k : ℂ) + 1) := by
    ext y
    simp [coeff_derivative]
  rw [h]
  exact (hd (k + 1)).mul (differentiableOn_const _)

/-- **A holomorphic branch of a simple root.** Let `Q` be monic with coefficients holomorphic on
an open `V`, and let `a` be a simple root of `Q(c)`, `c ∈ V`. Then there are `r, ε > 0` with
`B(c, r) ⊆ V` and a holomorphic `φ` on `B(c, r)` with `φ(c) = a` such that for `y ∈ B(c, r)` the
only root of `Q(y)` in `B(a, ε)` is `φ(y)`. -/
theorem exists_simpleRoot_branch {Q : Polynomial (E → ℂ)} (hQ : Q.Monic) {V : Set E}
    (hV : IsOpen V) (hd : ∀ k, DifferentiableOn ℂ (Q.coeff k) V) {c : E} (hc : c ∈ V) {a : ℂ}
    (ha : (evalPoly Q c).IsRoot a) (hsimple : (evalPoly Q c).derivative.eval a ≠ 0) :
    ∃ r > 0, ∃ ε > 0, ball c r ⊆ V ∧ ∃ φ : E → ℂ, DifferentiableOn ℂ φ (ball c r) ∧ φ c = a ∧
      ∀ y ∈ ball c r, ‖φ y - a‖ < ε ∧
        ∀ v : ℂ, ‖v - a‖ < ε → ((evalPoly Q y).IsRoot v ↔ v = φ y) := by
  classical
  set D := ‖(evalPoly Q c).derivative.eval a‖ with hD
  have hDpos : 0 < D := norm_pos_iff.2 hsimple
  -- the derivative in `v` stays close to `Q(c)'(a)`
  have hcont : ContinuousAt (fun q : E × ℂ ↦ (evalPoly (derivative Q) q.1).eval q.2) (c, a) := by
    refine (continuousOn_eval_evalPoly (fun k ↦ (differentiableOn_coeff_derivative hd k)
      |>.continuousOn)).continuousAt ?_
    exact prod_mem_nhds (hV.mem_nhds hc) univ_mem
  have hev : ∀ᶠ q : E × ℂ in 𝓝 (c, a),
      ‖(evalPoly (derivative Q) q.1).eval q.2 - (evalPoly Q c).derivative.eval a‖ < D / 2 := by
    have h := Metric.continuousAt_iff'.1 hcont (D / 2) (half_pos hDpos)
    rw [derivative_evalPoly]
    simpa [dist_eq_norm] using h
  obtain ⟨U, hU, T, hT, hUT⟩ := mem_nhds_prod_iff.1 (hev.and
    (prod_mem_nhds (hV.mem_nhds hc) univ_mem))
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.1 hT
  have hbound : ∀ y ∈ ball c r₀, ∀ v ∈ ball a ε,
      ‖(evalPoly (derivative Q) y).eval v - (evalPoly Q c).derivative.eval a‖ < D / 2 ∧ y ∈ V :=
    fun y hy v hv ↦ by
      have := hUT (Set.mk_mem_prod (hr₀U hy) (hεT hv))
      exact ⟨this.1, this.2.1⟩
  -- uniqueness of roots in `B(a, ε)`
  have huniq : ∀ y ∈ ball c r₀, ∀ v₁ v₂, v₁ ∈ ball a ε → v₂ ∈ ball a ε →
      (evalPoly Q y).IsRoot v₁ → (evalPoly Q y).IsRoot v₂ → v₁ = v₂ := by
    intro y hy v₁ v₂ hv₁ hv₂ h₁ h₂
    set L := (evalPoly Q c).derivative.eval a
    set g : ℂ → ℂ := fun v ↦ (evalPoly Q y).eval v - L * v
    have hg : ∀ v ∈ ball a ε, HasDerivWithinAt g ((evalPoly Q y).derivative.eval v - L)
        (ball a ε) v := fun v _ ↦
      ((((evalPoly Q y).hasDerivAt v).sub ((hasDerivAt_id v).const_mul L)).hasDerivWithinAt
        |>.congr_deriv (by ring))
    have hg' : ∀ v ∈ ball a ε, ‖(evalPoly Q y).derivative.eval v - L‖ ≤ D / 2 := fun v hv ↦ by
      rw [derivative_evalPoly]
      exact (hbound y hy v hv).1.le
    have := (convex_ball a ε).norm_image_sub_le_of_norm_hasDerivWithin_le hg hg' hv₁ hv₂
    have hgv : g v₂ - g v₁ = -(L * (v₂ - v₁)) := by
      simp only [g, h₁.eq_zero, h₂.eq_zero]
      ring
    rw [hgv, norm_neg, norm_mul] at this
    by_contra hne
    have hpos : 0 < ‖v₂ - v₁‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
    have : D * ‖v₂ - v₁‖ ≤ D / 2 * ‖v₂ - v₁‖ := this
    nlinarith
  -- existence of roots near roots
  have hexist : ∀ y₀ ∈ ball c r₀, ∀ τ, (evalPoly Q y₀).IsRoot τ → ∀ δ > 0,
      ∀ᶠ y in 𝓝 y₀, ∃ σ, (evalPoly Q y).IsRoot σ ∧ ‖σ - τ‖ < δ := by
    intro y₀ hy₀ τ hτ δ hδ
    have hZ : IsOpen (ball c r₀) := isOpen_ball
    have h := Polynomial.eventually_exists_isRoot_near_of_continuous (Z := ball c r₀)
      (p := fun y ↦ evalPoly Q y.1) (d := Q.natDegree) (fun y ↦ hQ.map _)
      (fun y ↦ (hQ.natDegree_map _)) (fun i ↦ by
        simp only [coeff_evalPoly]
        exact ((hd i).continuousOn.mono fun y hy ↦ (hbound y hy a (mem_ball_self hε)).2)
          |>.domRestrict) (x₀ := ⟨y₀, hy₀⟩) hτ hδ
    rw [hZ.isOpenEmbedding_subtypeVal.nhds_eq_comap, eventually_comap] at h
    filter_upwards [h, hZ.mem_nhds hy₀] with y hy hyZ
    exact hy ⟨y, hyZ⟩ rfl
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.mem_nhds_iff.1
    (hexist c (mem_ball_self hr₀) a ha ε hε)
  set r := min r₀ r₁
  have hr : 0 < r := lt_min hr₀ hr₁
  have hrr₀ : ball c r ⊆ ball c r₀ := ball_subset_ball (min_le_left _ _)
  set φ : E → ℂ := fun y ↦
    if h : ∃ σ, (evalPoly Q y).IsRoot σ ∧ ‖σ - a‖ < ε then h.choose else a
  have hφ : ∀ y ∈ ball c r, (evalPoly Q y).IsRoot (φ y) ∧ ‖φ y - a‖ < ε := fun y hy ↦ by
    have h : ∃ σ, (evalPoly Q y).IsRoot σ ∧ ‖σ - a‖ < ε :=
      hr₁sub (ball_subset_ball (min_le_right _ _) hy)
    simp only [φ, dite_eq_left h]
    exact h.choose_spec
  have hiff : ∀ y ∈ ball c r, ∀ v : ℂ, ‖v - a‖ < ε →
      ((evalPoly Q y).IsRoot v ↔ v = φ y) := fun y hy v hv ↦
    ⟨fun h ↦ huniq y (hrr₀ hy) v (φ y) (by simpa [dist_eq_norm] using hv)
      (by simpa [dist_eq_norm] using (hφ y hy).2) h (hφ y hy).1,
      fun h ↦ h ▸ (hφ y hy).1⟩
  have hφc : φ c = a :=
    ((hiff c (mem_ball_self hr) a (by simpa using hε)).1 ha).symm
  have hφcont : ∀ y₀ ∈ ball c r, ContinuousAt φ y₀ := by
    intro y₀ hy₀
    rw [Metric.continuousAt_iff']
    intro δ hδ
    have hδ' : 0 < min δ (ε - ‖φ y₀ - a‖) := lt_min hδ (sub_pos.2 (hφ y₀ hy₀).2)
    filter_upwards [hexist y₀ (hrr₀ hy₀) (φ y₀) (hφ y₀ hy₀).1 _ hδ',
      isOpen_ball.mem_nhds hy₀] with y ⟨σ, hσ, hσd⟩ hy
    have hσa : ‖σ - a‖ < ε := by
      calc ‖σ - a‖ = ‖(σ - φ y₀) + (φ y₀ - a)‖ := by ring_nf
        _ ≤ ‖σ - φ y₀‖ + ‖φ y₀ - a‖ := norm_add_le _ _
        _ < (ε - ‖φ y₀ - a‖) + ‖φ y₀ - a‖ := by
          linarith [hσd.trans_le (min_le_right _ _)]
        _ = ε := by ring
    rw [← (hiff y hy σ hσa).1 hσ, dist_eq_norm]
    exact hσd.trans_le (min_le_left _ _)
  refine ⟨r, hr, ε, hε, fun y hy ↦ (hbound y (hrr₀ hy) a (mem_ball_self hε)).2, φ,
    fun y₀ hy₀ ↦ ?_, hφc, fun y hy ↦ ⟨(hφ y hy).2, hiff y hy⟩⟩
  refine (Polynomial.differentiableAt_of_isRoot_of_differentiableAt_coeff
    (p := evalPoly Q) (n := Q.natDegree) (natDegree_evalPoly_le Q) (fun i ↦ ?_)
    (hφcont y₀ hy₀) ?_ ?_).differentiableWithinAt
  · have : (fun y ↦ (evalPoly Q y).coeff i) = Q.coeff i := funext fun y ↦ coeff_evalPoly Q y i
    rw [this]
    exact (hd i).differentiableAt (hV.mem_nhds (hbound y₀ (hrr₀ hy₀) a (mem_ball_self hε)).2)
  · filter_upwards [isOpen_ball.mem_nhds hy₀] with y hy
    exact (hφ y hy).1
  · intro h0
    have := (hbound y₀ (hrr₀ hy₀) (φ y₀) (by simpa [dist_eq_norm] using (hφ y₀ hy₀).2)).1
    rw [← derivative_evalPoly, h0, zero_sub, norm_neg] at this
    linarith

end

end ComplexAnalytic
