/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Analysis.Analytic.Polynomial
import Tengoku.Seed.Analysis.Analytic.Uniqueness
import Tengoku.Seed.Analysis.Calculus.FDeriv.Mul
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic
import Tengoku.Seed.Algebra.MvPolynomial.Funext
import Tengoku.Seed.Topology.Algebra.MvPolynomial
import Tengoku.LanaOka.Oka.Analysis.Complex.LiouvillePolynomial
import Tengoku.LanaOka.Oka.Nullstellensatz.CommonRoot
import Tengoku.LanaOka.Oka.Analytic.RiemannExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The root cover of an irreducible polynomial is connected

Let `P ∈ ℂ[x₁, …, x_d][T]` be monic and irreducible, and let `δ ∈ ℂ[x₁, …, x_d]` be nonzero such
that `P(w, ·)` is separable whenever `δ(w) ≠ 0`. Then the root cover
`{(w, τ) ∈ ℂ^d × ℂ | δ(w) ≠ 0, P(w, τ) = 0}` is connected
(`ComplexAnalytic.isPreconnected_rootCover`).

Suppose that the root cover is split by two open sets `u` and `v`. For `w` with `δ(w) ≠ 0` let
`Q_w = ∏ (T - τ)`, the product over the roots `τ` of `P(w, ·)` with `(w, τ) ∈ u`. Simple roots
depend holomorphically on the parameters, so the coefficients of `Q_w` are holomorphic, and they
are bounded near every point since the roots of a monic polynomial are bounded in terms of its
coefficients. By the Riemann extension theorem they extend to entire functions of polynomial
growth, which are polynomials. The degree of `Q_w` is constant since the complement of `δ = 0` is
connected, so `Q` is a monic factor of `P` of degree strictly between `0` and `deg P`.

## Main results

- `ComplexAnalytic.exists_differentiable_eq_of_locally_bounded`: Riemann extension across a
  polynomial hypersurface in `ℂ^d`.
- `ComplexAnalytic.isPreconnected_setOf_eval_ne_zero`: the complement of a polynomial
  hypersurface in `ℂ^d` is connected.
- `ComplexAnalytic.differentiableAt_of_isRoot`: a continuous simple root of a polynomial with
  polynomial coefficients is holomorphic.
- `ComplexAnalytic.isPreconnected_rootCover`: the root cover of an irreducible polynomial is
  connected.

## References

- David Mumford, *Algebraic Geometry I: Complex Projective Varieties*, (4.16)
-/

open Polynomial Filter Topology Asymptotics

namespace ComplexAnalytic

noncomputable section

variable {d : ℕ}

/-! ### Polynomials in `ℂ^d` -/

/-- Evaluating a polynomial with polynomial coefficients is jointly continuous. -/
theorem continuous_eval_map_eval (D : (MvPolynomial (Fin d) ℂ)[X]) :
    Continuous fun q : (Fin d → ℂ) × ℂ ↦ (D.map (MvPolynomial.eval q.1)).eval q.2 := by
  have e : (fun q : (Fin d → ℂ) × ℂ ↦ (D.map (MvPolynomial.eval q.1)).eval q.2) =
      fun q ↦ ∑ i ∈ Finset.range (D.natDegree + 1),
        MvPolynomial.eval q.1 (D.coeff i) * q.2 ^ i := by
    funext q
    rw [eval_map, eval₂_eq_sum_range]
  rw [e]
  exact continuous_finsetSum _ fun i _ ↦
    ((MvPolynomial.continuous_eval _).comp continuous_fst).mul (continuous_snd.pow i)

/-- A polynomial on `ℂ^d` has polynomial growth. -/
theorem exists_norm_eval_le (p : MvPolynomial (Fin d) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w, ‖MvPolynomial.eval w p‖ ≤ C * (1 + ‖w‖) ^ N := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, norm_nonneg _, 0, fun w ↦ by simp⟩
  | add p q hp hq =>
    obtain ⟨C₁, hC₁, N₁, h₁⟩ := hp
    obtain ⟨C₂, hC₂, N₂, h₂⟩ := hq
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, max N₁ N₂, fun w ↦ ?_⟩
    have hw : 1 ≤ 1 + ‖w‖ := le_add_of_nonneg_right (norm_nonneg w)
    have e₁ := pow_le_pow_right₀ hw (le_max_left N₁ N₂)
    have e₂ := pow_le_pow_right₀ hw (le_max_right N₁ N₂)
    rw [map_add]
    calc ‖MvPolynomial.eval w p + MvPolynomial.eval w q‖
        ≤ ‖MvPolynomial.eval w p‖ + ‖MvPolynomial.eval w q‖ := norm_add_le _ _
      _ ≤ C₁ * (1 + ‖w‖) ^ N₁ + C₂ * (1 + ‖w‖) ^ N₂ := add_le_add (h₁ w) (h₂ w)
      _ ≤ C₁ * (1 + ‖w‖) ^ max N₁ N₂ + C₂ * (1 + ‖w‖) ^ max N₁ N₂ :=
          add_le_add (mul_le_mul_of_nonneg_left e₁ hC₁) (mul_le_mul_of_nonneg_left e₂ hC₂)
      _ = (C₁ + C₂) * (1 + ‖w‖) ^ max N₁ N₂ := by ring
  | mul_X p i hp =>
    obtain ⟨C, hC, N, h⟩ := hp
    refine ⟨C, hC, N + 1, fun w ↦ ?_⟩
    have hi : ‖w i‖ ≤ 1 + ‖w‖ :=
      (norm_le_pi_norm w i).trans (le_add_of_nonneg_left zero_le_one)
    rw [map_mul, MvPolynomial.eval_X, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (h w) hi (norm_nonneg _) (by positivity)

/-- The complement of the zero set of a nonzero polynomial on `ℂ^d` is dense. -/
theorem dense_setOf_eval_ne_zero {δ : MvPolynomial (Fin d) ℂ} (hδ : δ ≠ 0) :
    Dense {w : Fin d → ℂ | MvPolynomial.eval w δ ≠ 0} := by
  intro w₀
  rw [mem_closure_iff_frequently]
  by_contra h
  rw [not_frequently] at h
  have hz : (fun w ↦ MvPolynomial.eval w δ) =ᶠ[𝓝 w₀] 0 := by
    filter_upwards [h] with w hw
    simpa using hw
  have heq := (AnalyticOnNhd.eval_mvPolynomial δ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ w₀) hz
  exact hδ (MvPolynomial.funext fun w ↦ by simpa using heq (Set.mem_univ w))

/-- The zero set of a nonzero polynomial on `ℂ^d` has empty interior. -/
theorem interior_setOf_eval_eq_zero {δ : MvPolynomial (Fin d) ℂ} (hδ : δ ≠ 0) :
    interior (Set.univ ∩ (fun w ↦ MvPolynomial.eval w δ) ⁻¹' {0}) = ∅ := by
  obtain ⟨z, hz⟩ := (dense_setOf_eval_ne_zero hδ).nonempty
  exact (AnalyticOnNhd.eval_mvPolynomial δ).interior_inter_preimage_zero_eq_empty
    isPreconnected_univ (Set.mem_univ z) hz

/-- **Riemann extension across a polynomial hypersurface**: a function on `ℂ^d` which is
holomorphic off the zero set of a nonzero polynomial `δ` and locally bounded there agrees off
`δ = 0` with an entire function. -/
theorem exists_differentiable_eq_of_locally_bounded {δ : MvPolynomial (Fin d) ℂ} (hδ : δ ≠ 0)
    {f : (Fin d → ℂ) → ℂ} (hf : DifferentiableOn ℂ f {w | MvPolynomial.eval w δ ≠ 0})
    (hb : ∀ w, ∃ U ∈ 𝓝 w, ∃ M : ℝ, ∀ w' ∈ U, MvPolynomial.eval w' δ ≠ 0 → ‖f w'‖ ≤ M) :
    ∃ F : (Fin d → ℂ) → ℂ, Differentiable ℂ F ∧ ∀ w, MvPolynomial.eval w δ ≠ 0 → F w = f w := by
  have hset : Set.univ \ (fun w ↦ MvPolynomial.eval w δ) ⁻¹' {0} =
      {w : Fin d → ℂ | MvPolynomial.eval w δ ≠ 0} := by
    ext
    simp
  have hbdd : ∀ z ∈ Set.univ, IsBoundedUnder (· ≤ ·)
      (𝓝[Set.univ \ (fun w ↦ MvPolynomial.eval w δ) ⁻¹' {0}] z) fun w ↦ ‖f w‖ := by
    intro z _
    obtain ⟨U, hU, M, hM⟩ := hb z
    refine isBoundedUnder_of_eventually_le (a := M) ?_
    rw [hset, eventually_nhdsWithin_iff]
    filter_upwards [hU] with w hw hw' using hM w hw hw'
  obtain ⟨F, hF, hFf⟩ := exists_differentiableOn_eqOn_of_isBoundedUnder isOpen_univ
    (AnalyticOnNhd.eval_mvPolynomial δ).differentiableOn (interior_setOf_eval_eq_zero hδ)
    (hset ▸ hf) hbdd
  exact ⟨F, differentiableOn_univ.1 hF, fun w hw ↦ hFf (by rw [hset]; exact hw)⟩

/-- **The complement of a polynomial hypersurface in `ℂ^d` is connected.** -/
theorem isPreconnected_setOf_eval_ne_zero {δ : MvPolynomial (Fin d) ℂ} (hδ : δ ≠ 0) :
    IsPreconnected {w : Fin d → ℂ | MvPolynomial.eval w δ ≠ 0} := by
  have hset : Set.univ \ (fun w ↦ MvPolynomial.eval w δ) ⁻¹' {0} =
      {w : Fin d → ℂ | MvPolynomial.eval w δ ≠ 0} := by
    ext
    simp
  rw [← hset]
  exact isPreconnected_univ.diff_zero isOpen_univ
    (AnalyticOnNhd.eval_mvPolynomial δ).differentiableOn (interior_setOf_eval_eq_zero hδ)

/-! ### Simple roots -/

/-- If `a` is differentiable at `x` with `a x = 0` and `k` is continuous at `x`, then `a * k` is
differentiable at `x`. -/
theorem hasFDerivAt_mul_of_continuousAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a k : E → ℂ} {a' : E →L[ℂ] ℂ} {x : E} (ha : HasFDerivAt a a' x) (ha0 : a x = 0)
    (hk : ContinuousAt k x) : HasFDerivAt (fun y ↦ a y * k y) (k x • a') x := by
  refine HasFDerivAt.of_isLittleO ?_
  have h₁ : (fun y ↦ k y • (a y - a x - a' (y - x))) =o[𝓝 x] fun y ↦ (1 : ℂ) • (y - x) :=
    (hk.tendsto.isBigO_one ℂ).smul_isLittleO ha.isLittleO
  have h₂ : (fun y ↦ (k y - k x) • a' (y - x)) =o[𝓝 x] fun y ↦ (1 : ℂ) • (y - x) := by
    refine IsLittleO.smul_isBigO ?_ (a'.isBigO_sub _ x)
    rw [isLittleO_one_iff]
    simpa using hk.tendsto.sub_const (k x)
  refine ((h₁.add h₂).congr_left fun y ↦ ?_).congr_right fun y ↦ one_smul ℂ _
  simp only [smul_eq_mul, ha0, FunLike.coe_smul, Pi.smul_apply]
  ring

/-- **A continuous simple root of a polynomial with polynomial coefficients is holomorphic.** -/
theorem differentiableAt_of_isRoot {P : (MvPolynomial (Fin d) ℂ)[X]} {ρ : (Fin d → ℂ) → ℂ}
    {w₀ : Fin d → ℂ} (hρ : ContinuousAt ρ w₀)
    (hroot : ∀ᶠ w in 𝓝 w₀, (P.map (MvPolynomial.eval w)).IsRoot (ρ w))
    (hsimple : (P.map (MvPolynomial.eval w₀)).derivative.eval (ρ w₀) ≠ 0) :
    DifferentiableAt ℂ ρ w₀ := by
  set τ₀ := ρ w₀
  set c : MvPolynomial (Fin d) ℂ := P.eval (MvPolynomial.C τ₀)
  set D := (P - C c) /ₘ (X - C (MvPolynomial.C τ₀))
  have hD : (X - C (MvPolynomial.C τ₀)) * D = P - C c :=
    mul_divByMonic_eq_iff_isRoot.2 (by simp [c])
  have hmap (w : Fin d → ℂ) : P.map (MvPolynomial.eval w) =
      C (MvPolynomial.eval w c) + (X - C τ₀) * D.map (MvPolynomial.eval w) := by
    have := congrArg (Polynomial.map (MvPolynomial.eval w)) hD
    simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, MvPolynomial.eval_C] at this
    rw [this]
    ring
  have hev (w : Fin d → ℂ) (T : ℂ) : (P.map (MvPolynomial.eval w)).eval T =
      MvPolynomial.eval w c + (T - τ₀) * (D.map (MvPolynomial.eval w)).eval T := by
    rw [hmap w]
    simp
  have hder : (P.map (MvPolynomial.eval w₀)).derivative.eval τ₀ =
      (D.map (MvPolynomial.eval w₀)).eval τ₀ := by
    rw [hmap w₀]
    simp
  have ha0 : MvPolynomial.eval w₀ c = 0 := by
    have := hev w₀ τ₀
    rw [(hroot.self_of_nhds).eq_zero] at this
    simpa using this.symm
  set b : (Fin d → ℂ) → ℂ := fun w ↦ (D.map (MvPolynomial.eval w)).eval (ρ w)
  have hb : ContinuousAt b w₀ :=
    (continuous_eval_map_eval D).continuousAt.comp (continuousAt_id.prodMk hρ)
  have hb0 : b w₀ ≠ 0 := by
    change (D.map (MvPolynomial.eval w₀)).eval τ₀ ≠ 0
    rwa [← hder]
  have ha : HasFDerivAt (fun w ↦ MvPolynomial.eval w c) _ w₀ :=
    ((AnalyticOnNhd.eval_mvPolynomial c) w₀ trivial).differentiableAt.hasFDerivAt
  have hk : ContinuousAt (fun w ↦ -(b w)⁻¹) w₀ := (hb.inv₀ hb0).neg
  have hmul := (hasFDerivAt_mul_of_continuousAt ha ha0 hk).differentiableAt.const_add τ₀
  refine hmul.congr_of_eventuallyEq ?_
  filter_upwards [hroot, hb.eventually_ne hb0] with w hw hbw
  have := hev w (ρ w)
  rw [hw.eq_zero] at this
  change ρ w = τ₀ + MvPolynomial.eval w c * -(b w)⁻¹
  field_simp
  linear_combination -this

/-- The coefficients of `∏ (T - fᵢ(w))` are differentiable where the `fᵢ` are. -/
theorem differentiableAt_coeff_prod {ι : Type*} (s : Finset ι) {f : ι → (Fin d → ℂ) → ℂ}
    {w₀ : Fin d → ℂ} (hf : ∀ i ∈ s, DifferentiableAt ℂ (f i) w₀) (j : ℕ) :
    DifferentiableAt ℂ (fun w ↦ (∏ i ∈ s, (X - C (f i w))).coeff j) w₀ := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty => simp only [Finset.prod_empty]; exact differentiableAt_const _
  | insert i s hi ih =>
    have hs : ∀ i ∈ s, DifferentiableAt ℂ (f i) w₀ := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    simp_rw [Finset.prod_insert hi, sub_mul, coeff_sub, coeff_C_mul]
    refine DifferentiableAt.sub ?_ ((hf i (Finset.mem_insert_self i s)).mul (ih hs j))
    cases j with
    | zero => simp only [coeff_X_mul_zero]; exact differentiableAt_const _
    | succ j => simp only [coeff_X_mul]; exact ih hs j

/-- The coefficients of `∏ (T - τ)` over roots `τ` of norm at most `B` are bounded by
`(1 + B)` to the number of factors. -/
theorem norm_coeff_prod_le {s : Finset ℂ} {B : ℝ} (hB : 0 ≤ B) (hs : ∀ τ ∈ s, ‖τ‖ ≤ B)
    (j : ℕ) : ‖(∏ τ ∈ s, (X - C τ)).coeff j‖ ≤ (1 + B) ^ s.card := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty =>
    simp only [Finset.prod_empty, coeff_one, Finset.card_empty, pow_zero]
    split_ifs <;> simp
  | insert i s hi ih =>
    have hs' : ∀ τ ∈ s, ‖τ‖ ≤ B := fun τ hτ ↦ hs τ (Finset.mem_insert_of_mem hτ)
    have hi' : ‖i‖ ≤ B := hs i (Finset.mem_insert_self i s)
    rw [Finset.prod_insert hi, sub_mul, coeff_sub, coeff_C_mul, Finset.card_insert_of_notMem hi,
      pow_succ]
    have h₁ : ‖(X * ∏ τ ∈ s, (X - C τ)).coeff j‖ ≤ (1 + B) ^ s.card := by
      cases j with
      | zero => simp only [coeff_X_mul_zero, norm_zero]; positivity
      | succ j => rw [coeff_X_mul]; exact ih hs' j
    have h₂ : ‖i * (∏ τ ∈ s, (X - C τ)).coeff j‖ ≤ B * (1 + B) ^ s.card := by
      rw [norm_mul]
      exact mul_le_mul hi' (ih hs' j) (norm_nonneg _) hB
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ (1 + B) ^ s.card + B * (1 + B) ^ s.card := add_le_add h₁ h₂
      _ = (1 + B) ^ s.card * (1 + B) := by ring

/-- A root of a monic complex polynomial is bounded by one plus the sum of the norms of the lower
coefficients. -/
theorem norm_le_of_isRoot {q : ℂ[X]} (hq : q.Monic) {σ : ℂ} (hσ : q.IsRoot σ) :
    ‖σ‖ ≤ 1 + ∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖ := by
  set S := ∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  refine (Polynomial.norm_lt_of_isRoot hq (by positivity) ?_ hσ).le
  have hn : q.natDegree ≠ 0 := by
    intro h
    have := (Multiset.card_pos_iff_exists_mem.2 ⟨σ, (mem_roots hq.ne_zero).2 hσ⟩).trans_le
      (card_roots' q)
    omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h1 : (1 : ℝ) ≤ 1 + S := le_add_of_nonneg_right hS
  calc ∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖ * (1 + S) ^ i
      ≤ ∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖ * (1 + S) ^ n := by
        refine Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ h1 ?_) (norm_nonneg _)
        rw [Finset.mem_range, hn] at hi
        omega
    _ = S * (1 + S) ^ n := by rw [← Finset.sum_mul]
    _ < (1 + S) * (1 + S) ^ n := by
        have : 0 < (1 + S) ^ n := by positivity
        nlinarith
    _ = (1 + S) ^ q.natDegree := by rw [hn, pow_succ']

/-- A product of reals which are all at least `a ≥ 0` is at least `a` to the number of factors. -/
private lemma pow_card_le_prod_of_le {s : Multiset ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ x ∈ s, a ≤ x) : a ^ Multiset.card s ≤ s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.prod_cons, mul_comm]
    have hx := h x (Multiset.mem_cons_self x s)
    exact mul_le_mul hx (ih fun y hy ↦ h y (Multiset.mem_cons_of_mem hy)) (by positivity)
      (ha.trans hx)

/-- A monic polynomial whose coefficients are polynomials has, for parameters near `w₀`, a root
near each root at `w₀`. -/
theorem eventually_exists_isRoot_near {P : (MvPolynomial (Fin d) ℂ)[X]} (hP : P.Monic)
    {w₀ : Fin d → ℂ} {τ : ℂ} (hτ : (P.map (MvPolynomial.eval w₀)).IsRoot τ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 w₀, ∃ σ, (P.map (MvPolynomial.eval w)).IsRoot σ ∧ ‖σ - τ‖ < ε := by
  have hc : Tendsto (fun w ↦ (P.map (MvPolynomial.eval w)).eval τ) (𝓝 w₀) (𝓝 0) := by
    have := ((continuous_eval_map_eval P).comp
      (continuous_id.prodMk (continuous_const (y := τ)))).tendsto w₀
    rw [Function.comp_def] at this
    simpa [hτ.eq_zero] using this
  filter_upwards [(tendsto_norm_zero.comp hc).eventually
    (eventually_lt_nhds (show (0 : ℝ) < ε ^ P.natDegree by positivity))] with w hw
  by_contra! h
  set q := P.map (MvPolynomial.eval w)
  have hq : q.Monic := hP.map _
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hq
    IsAlgClosed.card_roots_eq_natDegree
  have hev : ‖q.eval τ‖ = (q.roots.map fun σ ↦ ‖τ - σ‖).prod := by
    conv_lhs => rw [← hprod]
    rw [eval_multiset_prod, Multiset.map_map]
    change (normHom : ℂ →*₀ ℝ) _ = _
    rw [map_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hle : ε ^ P.natDegree ≤ ‖q.eval τ‖ := by
    rw [hev, ← hP.natDegree_map (MvPolynomial.eval w), ← IsAlgClosed.card_roots_eq_natDegree,
      ← Multiset.card_map (fun σ ↦ ‖τ - σ‖)]
    refine pow_card_le_prod_of_le hε.le fun x hx ↦ ?_
    obtain ⟨σ, hσ, rfl⟩ := Multiset.mem_map.1 hx
    rw [norm_sub_rev]
    exact h σ (isRoot_of_mem_roots hσ)
  exact (lt_irrefl _ (hle.trans_lt hw))

/-! ### The local structure of the roots -/

/-- The number of distinct roots of a separable fibre of a monic polynomial is its degree. -/
theorem card_roots_toFinset_of_separable {P : (MvPolynomial (Fin d) ℂ)[X]} (hP : P.Monic)
    {w : Fin d → ℂ} (hsep : (P.map (MvPolynomial.eval w)).Separable) :
    (P.map (MvPolynomial.eval w)).roots.toFinset.card = P.natDegree := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
    hP.natDegree_map]

/-- A separable fibre of a monic polynomial is the product of `T - τ` over its roots. -/
theorem prod_roots_toFinset_of_separable {P : (MvPolynomial (Fin d) ℂ)[X]} (hP : P.Monic)
    {w : Fin d → ℂ} (hsep : (P.map (MvPolynomial.eval w)).Separable) :
    ∏ τ ∈ (P.map (MvPolynomial.eval w)).roots.toFinset, (X - C τ) =
      P.map (MvPolynomial.eval w) := by
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.2 (nodup_roots hsep)]
  exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hP.map _)
    IsAlgClosed.card_roots_eq_natDegree

/-- **Local roots.** Near a parameter `w₀` over which the fibres of a monic polynomial are
separable, the roots are given by functions `ρ τ` indexed by the roots `τ` at `w₀`, each
continuous at `w₀` with value `τ`. -/
theorem exists_local_roots {P : (MvPolynomial (Fin d) ℂ)[X]} (hP : P.Monic) {w₀ : Fin d → ℂ}
    (hsep : ∀ᶠ w in 𝓝 w₀, (P.map (MvPolynomial.eval w)).Separable) :
    ∃ ρ : ℂ → (Fin d → ℂ) → ℂ,
      (∀ τ ∈ (P.map (MvPolynomial.eval w₀)).roots.toFinset,
        ρ τ w₀ = τ ∧ ContinuousAt (ρ τ) w₀ ∧
          ∀ᶠ w in 𝓝 w₀, (P.map (MvPolynomial.eval w)).IsRoot (ρ τ w)) ∧
      ∀ᶠ w in 𝓝 w₀,
        Set.InjOn (fun τ ↦ ρ τ w) (P.map (MvPolynomial.eval w₀)).roots.toFinset ∧
        (P.map (MvPolynomial.eval w)).roots.toFinset =
          (P.map (MvPolynomial.eval w₀)).roots.toFinset.image fun τ ↦ ρ τ w := by
  classical
  set T₀ := (P.map (MvPolynomial.eval w₀)).roots.toFinset
  obtain ⟨ε, hsepT, hε⟩ : ∃ ε : ℝ,
      (∀ τ ∈ T₀, ∀ τ' ∈ T₀, τ ≠ τ' → 2 * ε ≤ ‖τ - τ'‖) ∧ 0 < ε := by
    have h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ τ ∈ T₀, ∀ τ' ∈ T₀, τ ≠ τ' → 2 * ε ≤ ‖τ - τ'‖ := by
      refine (eventually_all_finset _).2 fun τ _ ↦ (eventually_all_finset _).2 fun τ' _ ↦ ?_
      by_cases hne : τ = τ'
      · exact Eventually.of_forall fun _ h ↦ absurd hne h
      have ht : Tendsto (fun ε : ℝ ↦ 2 * ε) (𝓝[>] 0) (𝓝 0) :=
        ((continuous_const_mul (2 : ℝ)).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      filter_upwards [ht.eventually
        (eventually_le_nhds (norm_pos_iff.2 (sub_ne_zero.2 hne)))] with ε hε _ using hε
    exact (h.and self_mem_nhdsWithin).exists
  let ρ : ℂ → (Fin d → ℂ) → ℂ := fun τ w ↦
    if h : ∃ σ, (P.map (MvPolynomial.eval w)).IsRoot σ ∧ ‖σ - τ‖ < ε then h.choose else τ
  have hρ (τ : ℂ) {w : Fin d → ℂ}
      (h : ∃ σ, (P.map (MvPolynomial.eval w)).IsRoot σ ∧ ‖σ - τ‖ < ε) :
      (P.map (MvPolynomial.eval w)).IsRoot (ρ τ w) ∧ ‖ρ τ w - τ‖ < ε := by
    simp only [ρ, dite_eq_left h]
    exact h.choose_spec
  have hclose {τ τ' σ : ℂ} (hτ : τ ∈ T₀) (hτ' : τ' ∈ T₀) (h₁ : ‖σ - τ‖ < ε)
      (h₂ : ‖σ - τ'‖ < ε) : τ = τ' := by
    by_contra hne
    have := hsepT τ hτ τ' hτ' hne
    have : ‖τ - τ'‖ ≤ ‖σ - τ'‖ + ‖σ - τ‖ := by
      calc ‖τ - τ'‖ = ‖(σ - τ') - (σ - τ)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  let good : (Fin d → ℂ) → Prop := fun w ↦ (P.map (MvPolynomial.eval w)).Separable ∧
      ∀ τ ∈ T₀, ∃ σ, (P.map (MvPolynomial.eval w)).IsRoot σ ∧ ‖σ - τ‖ < ε
  have hG : ∀ᶠ w in 𝓝 w₀, good w :=
    hsep.and ((eventually_all_finset _).2 fun τ hτ ↦
      eventually_exists_isRoot_near hP (isRoot_of_mem_roots (Multiset.mem_toFinset.1 hτ)) hε)
  have hgood (w : Fin d → ℂ) (hw : good w) : Set.InjOn (fun τ ↦ ρ τ w) T₀ ∧
      (P.map (MvPolynomial.eval w)).roots.toFinset = T₀.image fun τ ↦ ρ τ w := by
    have hinj : Set.InjOn (fun τ ↦ ρ τ w) T₀ := fun τ hτ τ' hτ' h ↦
      hclose hτ hτ' (hρ τ (hw.2 τ hτ)).2 ((congrArg (· - τ') h).symm ▸ (hρ τ' (hw.2 τ' hτ')).2)
    refine ⟨hinj, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
    · intro σ hσ
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hσ
      exact Multiset.mem_toFinset.2 ((mem_roots (hP.map _).ne_zero).2 (hρ τ (hw.2 τ hτ)).1)
    · rw [Finset.card_image_of_injOn hinj, card_roots_toFinset_of_separable hP hw.1,
        card_roots_toFinset_of_separable hP hsep.self_of_nhds]
  have huniq (w : Fin d → ℂ) (hw : good w) {τ : ℂ} (hτ : τ ∈ T₀) {σ : ℂ}
      (hσ : (P.map (MvPolynomial.eval w)).IsRoot σ) (hστ : ‖σ - τ‖ < ε) : σ = ρ τ w := by
    have hmem : σ ∈ T₀.image fun τ ↦ ρ τ w := by
      rw [← (hgood w hw).2]
      exact Multiset.mem_toFinset.2 ((mem_roots (hP.map _).ne_zero).2 hσ)
    obtain ⟨τ', hτ', rfl⟩ := Finset.mem_image.1 hmem
    rw [hclose hτ' hτ (hρ τ' (hw.2 τ' hτ')).2 hστ]
  refine ⟨ρ, fun τ hτ ↦ ?_, hG.mono hgood⟩
  have hroot : (P.map (MvPolynomial.eval w₀)).IsRoot τ :=
    isRoot_of_mem_roots (Multiset.mem_toFinset.1 hτ)
  have h0 : ρ τ w₀ = τ := (huniq w₀ hG.self_of_nhds hτ hroot (by simpa using hε)).symm
  refine ⟨h0, ?_, hG.mono fun w hw ↦ (hρ τ (hw.2 τ hτ)).1⟩
  rw [ContinuousAt, h0, Metric.tendsto_nhds]
  intro ε' hε'
  filter_upwards [hG, eventually_exists_isRoot_near hP hroot (lt_min hε' hε)] with w hw hex
  obtain ⟨σ, hσ, hστ⟩ := hex
  rw [dist_eq_norm, ← huniq w hw hτ hσ (hστ.trans_le (min_le_right _ _))]
  exact hστ.trans_le (min_le_left _ _)
/-- The coefficients of `T ^ k + ∑_{i < k} aᵢ T ^ i`. -/
private lemma coeff_X_pow_add_sum {R : Type*} [Semiring R] {k : ℕ} (a : ℕ → R) (j : ℕ) :
    (X ^ k + ∑ i : Fin k, C (a i) * X ^ (i : ℕ)).coeff j =
      if j < k then a j else if j = k then 1 else 0 := by
  rw [coeff_add, coeff_X_pow, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases h₁ : j < k
  · rw [ite_eq_left h₁, ite_eq_right (by omega), zero_add, Finset.sum_eq_single ⟨j, h₁⟩
      (fun i _ hi ↦ ite_eq_right fun h ↦ hi (Fin.ext h.symm)) (by simp), ite_eq_left rfl]
  · rw [ite_eq_right h₁, Finset.sum_eq_zero fun i _ ↦ ite_eq_right (by have := i.2; omega), add_zero]

/-! ### The root cover -/

open scoped Classical in
/-- The roots `τ` of `P(w, ·)` with `(w, τ) ∈ u`. -/
def rootsIn (P : (MvPolynomial (Fin d) ℂ)[X]) (u : Set ((Fin d → ℂ) × ℂ)) (w : Fin d → ℂ) :
    Finset ℂ :=
  (P.map (MvPolynomial.eval w)).roots.toFinset.filter fun τ ↦ (w, τ) ∈ u

/-- An element of `rootsIn P u w` is a root of `P(w, ·)`. -/
lemma isRoot_of_mem_rootsIn {P : (MvPolynomial (Fin d) ℂ)[X]} {u : Set ((Fin d → ℂ) × ℂ)}
    {w : Fin d → ℂ} {τ : ℂ} (h : τ ∈ rootsIn P u w) : (P.map (MvPolynomial.eval w)).IsRoot τ := by
  classical
  unfold rootsIn at h
  exact isRoot_of_mem_roots (Multiset.mem_toFinset.1 (Finset.mem_filter.1 h).1)

/-- Near a parameter `w₀` with `δ(w₀) ≠ 0`, the product of `T - τ` over the roots `τ` of `P(w, ·)`
lying in one of two open sets separating the root cover is a product of `T - ρ(w)` for finitely
many functions `ρ` holomorphic at `w₀`. -/
theorem exists_local_prod_rootsIn {P : (MvPolynomial (Fin d) ℂ)[X]} (hP : P.Monic)
    {δ : MvPolynomial (Fin d) ℂ}
    (hsep : ∀ w, MvPolynomial.eval w δ ≠ 0 → (P.map (MvPolynomial.eval w)).Separable)
    {u v : Set ((Fin d → ℂ) × ℂ)} (hu : IsOpen u) (hv : IsOpen v)
    (huv : ∀ w τ, MvPolynomial.eval w δ ≠ 0 → (P.map (MvPolynomial.eval w)).IsRoot τ →
      (w, τ) ∈ u ∨ (w, τ) ∈ v)
    (hdisj : ∀ w τ, MvPolynomial.eval w δ ≠ 0 → (P.map (MvPolynomial.eval w)).IsRoot τ →
      (w, τ) ∈ u → (w, τ) ∉ v)
    {w₀ : Fin d → ℂ} (hw₀ : MvPolynomial.eval w₀ δ ≠ 0) :
    ∃ (I₀ : Finset ℂ) (ρ : ℂ → (Fin d → ℂ) → ℂ),
      (∀ τ ∈ I₀, DifferentiableAt ℂ (ρ τ) w₀) ∧
      ∀ᶠ w in 𝓝 w₀, ∏ τ ∈ rootsIn P u w, (X - C τ) = ∏ τ ∈ I₀, (X - C (ρ τ w)) ∧
        (rootsIn P u w).card = I₀.card := by
  classical
  have hWn : ∀ᶠ w in 𝓝 w₀, MvPolynomial.eval w δ ≠ 0 :=
    (MvPolynomial.continuous_eval δ).continuousAt.eventually_ne hw₀
  obtain ⟨ρ, hρ, hev⟩ := exists_local_roots hP (hWn.mono fun w hw ↦ hsep w hw)
  refine ⟨(P.map (MvPolynomial.eval w₀)).roots.toFinset.filter fun τ ↦ (w₀, τ) ∈ u, ρ,
    fun τ hτ ↦ ?_, ?_⟩
  · obtain ⟨h0, hc, hr⟩ := hρ τ (Finset.mem_filter.1 hτ).1
    refine differentiableAt_of_isRoot hc hr ?_
    rw [h0]
    have hτr : (P.map (MvPolynomial.eval w₀)).IsRoot τ :=
      isRoot_of_mem_roots (Multiset.mem_toFinset.1 (Finset.mem_filter.1 hτ).1)
    have := (hsep w₀ hw₀).aeval_derivative_ne_zero (x := τ) (by simpa using hτr.eq_zero)
    simpa using this
  have hmem : ∀ τ ∈ (P.map (MvPolynomial.eval w₀)).roots.toFinset,
      ∀ᶠ w in 𝓝 w₀, ((w, ρ τ w) ∈ u ↔ (w₀, τ) ∈ u) := by
    intro τ hτ
    obtain ⟨h0, hc, hr⟩ := hρ τ hτ
    have hcont : ContinuousAt (fun w ↦ (w, ρ τ w)) w₀ := continuousAt_id.prodMk hc
    have hroot₀ : (P.map (MvPolynomial.eval w₀)).IsRoot τ :=
      isRoot_of_mem_roots (Multiset.mem_toFinset.1 hτ)
    by_cases hτu : (w₀, τ) ∈ u
    · have : ∀ᶠ w in 𝓝 w₀, (w, ρ τ w) ∈ u :=
        hcont.preimage_mem_nhds (by rw [h0]; exact hu.mem_nhds hτu)
      filter_upwards [this] with w hw
      simp [hw, hτu]
    · have hτv : (w₀, τ) ∈ v := (huv w₀ τ hw₀ hroot₀).resolve_left hτu
      have : ∀ᶠ w in 𝓝 w₀, (w, ρ τ w) ∈ v :=
        hcont.preimage_mem_nhds (by rw [h0]; exact hv.mem_nhds hτv)
      filter_upwards [this, hr, hWn] with w hw hrw hww
      simp only [hτu, iff_false]
      exact fun hwu ↦ hdisj w _ hww hrw hwu hw
  filter_upwards [hev, (eventually_all_finset _).2 hmem] with w hw hwu
  obtain ⟨hinj, himg⟩ := hw
  have hS : rootsIn P u w = ((P.map (MvPolynomial.eval w₀)).roots.toFinset.filter
      fun τ ↦ (w₀, τ) ∈ u).image fun τ ↦ ρ τ w := by
    unfold rootsIn
    rw [himg, Finset.filter_image]
    congr 1
    exact Finset.filter_congr fun τ hτ ↦ hwu τ hτ
  have hinj' := hinj.mono (Finset.coe_subset.2 (Finset.filter_subset
    (fun τ ↦ (w₀, τ) ∈ u) (P.map (MvPolynomial.eval w₀)).roots.toFinset))
  exact ⟨by rw [hS, Finset.prod_image hinj'], by rw [hS, Finset.card_image_of_injOn hinj']⟩

/-- The coefficients of `∏ (T - τ)` over the roots `τ` of `P(w, ·)` in `u` are bounded by a
continuous function of `w` of polynomial growth. -/
theorem exists_bound_coeff_prod_rootsIn {P : (MvPolynomial (Fin d) ℂ)[X]} (hP : P.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) :
    ∃ B : (Fin d → ℂ) → ℝ, Continuous B ∧ (∀ w, 0 ≤ B w) ∧
      (∀ w j, ‖(∏ τ ∈ rootsIn P u w, (X - C τ)).coeff j‖ ≤ B w) ∧
      ∃ K : ℝ, ∃ M : ℕ, ∀ w, B w ≤ K * (1 + ‖w‖) ^ M := by
  classical
  set e := P.natDegree
  let A : (Fin d → ℂ) → ℝ := fun w ↦ 1 + ∑ i ∈ Finset.range e, ‖MvPolynomial.eval w (P.coeff i)‖
  have hA0 (w : Fin d → ℂ) : 0 ≤ A w := by positivity
  have hAc : Continuous A := continuous_const.add (continuous_finsetSum _ fun i _ ↦
    (MvPolynomial.continuous_eval _).norm)
  have hroots (w : Fin d → ℂ) (τ : ℂ) (hτ : (P.map (MvPolynomial.eval w)).IsRoot τ) :
      ‖τ‖ ≤ A w := by
    have := norm_le_of_isRoot (hP.map (MvPolynomial.eval w)) hτ
    simpa [hP.natDegree_map, coeff_map, A, e] using this
  refine ⟨fun w ↦ (1 + A w) ^ e, (continuous_const.add hAc).pow e, fun w ↦ by positivity,
    fun w j ↦ ?_, ?_⟩
  · refine (norm_coeff_prod_le (hA0 w) (fun τ hτ ↦ hroots w τ (isRoot_of_mem_rootsIn hτ)) j).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_right (hA0 w)) ?_)
    unfold rootsIn
    refine (Finset.card_filter_le _ _).trans ((Multiset.toFinset_card_le _).trans
      ((card_roots' _).trans ?_))
    rw [hP.natDegree_map]
  choose Cc hCc Nc hNc using fun i ↦ exists_norm_eval_le (P.coeff i)
  set N := ∑ i ∈ Finset.range e, Nc i
  set C₀ := ∑ i ∈ Finset.range e, Cc i
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun i _ ↦ hCc i
  refine ⟨(2 + C₀) ^ e, N * e, fun w ↦ ?_⟩
  have h1 : 1 ≤ (1 + ‖w‖) ^ N := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg w))
  have h2 : ∑ i ∈ Finset.range e, ‖MvPolynomial.eval w (P.coeff i)‖ ≤ C₀ * (1 + ‖w‖) ^ N := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi ↦ (hNc i w).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg w))
        (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi)) (hCc i))
  change (1 + (1 + _)) ^ e ≤ _
  rw [pow_mul, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  nlinarith

/-- **The root cover of an irreducible polynomial is connected.** Let `P ∈ ℂ[x₁, …, x_d][T]` be
monic and irreducible and let `δ ≠ 0` be such that `P(w, ·)` is separable whenever `δ(w) ≠ 0`.
Then `{(w, τ) | δ(w) ≠ 0, P(w, τ) = 0}` is preconnected. -/
theorem isPreconnected_rootCover {P : (MvPolynomial (Fin d) ℂ)[X]} (hP : P.Monic)
    (hirr : Irreducible P) {δ : MvPolynomial (Fin d) ℂ} (hδ : δ ≠ 0)
    (hsep : ∀ w, MvPolynomial.eval w δ ≠ 0 → (P.map (MvPolynomial.eval w)).Separable) :
    IsPreconnected {q : (Fin d → ℂ) × ℂ |
      MvPolynomial.eval q.1 δ ≠ 0 ∧ (P.map (MvPolynomial.eval q.1)).IsRoot q.2} := by
  classical
  rintro u v hu hv hEuv ⟨⟨w₁, τ₁⟩, ⟨hw₁, hτ₁⟩, hu₁⟩ ⟨⟨w₂, τ₂⟩, ⟨hw₂, hτ₂⟩, hv₂⟩
  by_contra hne
  have hdisj (w : Fin d → ℂ) (τ : ℂ) (h₁ : MvPolynomial.eval w δ ≠ 0)
      (h₂ : (P.map (MvPolynomial.eval w)).IsRoot τ) (h₃ : (w, τ) ∈ u) : (w, τ) ∉ v :=
    fun h₄ ↦ hne ⟨(w, τ), ⟨h₁, h₂⟩, h₃, h₄⟩
  have huv (w : Fin d → ℂ) (τ : ℂ) (h₁ : MvPolynomial.eval w δ ≠ 0)
      (h₂ : (P.map (MvPolynomial.eval w)).IsRoot τ) : (w, τ) ∈ u ∨ (w, τ) ∈ v :=
    hEuv (a := (w, τ)) ⟨h₁, h₂⟩
  have hloc (w₀ : Fin d → ℂ) (hw₀ : MvPolynomial.eval w₀ δ ≠ 0) :=
    exists_local_prod_rootsIn hP hsep hu hv huv hdisj hw₀
  -- the coefficients are holomorphic off `δ = 0`
  have hdiff (j : ℕ) : DifferentiableOn ℂ (fun w ↦ (∏ τ ∈ rootsIn P u w, (X - C τ)).coeff j)
      {w | MvPolynomial.eval w δ ≠ 0} := by
    intro w₀ hw₀
    obtain ⟨I₀, ρ, hd, hev⟩ := hloc w₀ hw₀
    exact ((differentiableAt_coeff_prod I₀ hd j).congr_of_eventuallyEq
      (hev.mono fun w hw ↦ by simp only [hw.1])).differentiableWithinAt
  -- the degree is constant off `δ = 0`
  have hcard {w : Fin d → ℂ} (hw : MvPolynomial.eval w δ ≠ 0) :
      (rootsIn P u w).card = (rootsIn P u w₁).card := by
    refine (isPreconnected_setOf_eval_ne_zero hδ).constant (f := fun w ↦ (rootsIn P u w).card)
      (fun w₀ hw₀ ↦ ?_) hw hw₁
    obtain ⟨I₀, ρ, -, hev⟩ := hloc w₀ hw₀
    refine ContinuousAt.continuousWithinAt (tendsto_nhds_of_eventually_eq ?_)
    filter_upwards [hev] with w hw
    rw [hw.2, hev.self_of_nhds.2]
  have hk1 : 1 ≤ (rootsIn P u w₁).card := by
    refine Finset.card_pos.2 ⟨τ₁, ?_⟩
    unfold rootsIn
    exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ((mem_roots (hP.map _).ne_zero).2 hτ₁), hu₁⟩
  have hke : (rootsIn P u w₁).card < P.natDegree := by
    rw [← hcard hw₂, ← card_roots_toFinset_of_separable hP (hsep w₂ hw₂)]
    unfold rootsIn
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2
      ⟨τ₂, Multiset.mem_toFinset.2 ((mem_roots (hP.map _).ne_zero).2 hτ₂), fun h ↦ ?_⟩)
    exact hdisj w₂ τ₂ hw₂ hτ₂ (Finset.mem_filter.1 h).2 hv₂
  -- extension to polynomials
  obtain ⟨B, hBc, -, hQb, K, M, hBg⟩ := exists_bound_coeff_prod_rootsIn hP u
  have hbdd (j : ℕ) (w₀ : Fin d → ℂ) : ∃ U ∈ 𝓝 w₀, ∃ M : ℝ, ∀ w ∈ U,
      MvPolynomial.eval w δ ≠ 0 → ‖(∏ τ ∈ rootsIn P u w, (X - C τ)).coeff j‖ ≤ M :=
    ⟨{w | B w < B w₀ + 1}, (isOpen_lt hBc continuous_const).mem_nhds (by simp), B w₀ + 1,
      fun w hw _ ↦ (hQb w j).trans (le_of_lt hw)⟩
  choose F hF using fun j ↦ exists_differentiable_eq_of_locally_bounded hδ (hdiff j) (hbdd j)
  have hFb (j : ℕ) (w : Fin d → ℂ) : ‖F j w‖ ≤ K * (1 + ‖w‖) ^ M := by
    have hcl : IsClosed {w : Fin d → ℂ | ‖F j w‖ ≤ K * (1 + ‖w‖) ^ M} :=
      isClosed_le (hF j).1.continuous.norm
        (continuous_const.mul ((continuous_const.add continuous_norm).pow _))
    have hsub : {w | MvPolynomial.eval w δ ≠ 0} ⊆
        {w : Fin d → ℂ | ‖F j w‖ ≤ K * (1 + ‖w‖) ^ M} := fun w hw ↦ by
      change ‖F j w‖ ≤ _
      rw [(hF j).2 w hw]
      exact (hQb w j).trans (hBg w)
    have := closure_minimal hsub hcl
    rw [(dense_setOf_eval_ne_zero hδ).closure_eq] at this
    exact this (Set.mem_univ w)
  choose p hp using fun j ↦ Differentiable.exists_mvPolynomial_eq_of_norm_le_pow (hF j).1 (hFb j)
  -- the factor
  obtain ⟨k, hk⟩ : ∃ k, k = (rootsIn P u w₁).card := ⟨_, rfl⟩
  rw [← hk] at hk1 hke
  have hQ'm : (X ^ k + ∑ i : Fin k, C (p i) * X ^ (i : ℕ)).Monic :=
    monic_X_pow_add (degree_sum_fin_lt _)
  have hQ'deg : (X ^ k + ∑ i : Fin k, C (p i) * X ^ (i : ℕ)).natDegree = k := by
    rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]
    exact degree_sum_fin_lt _
  have hQm (w : Fin d → ℂ) : (∏ τ ∈ rootsIn P u w, (X - C τ)).Monic :=
    monic_prod_of_monic _ _ fun τ _ ↦ monic_X_sub_C τ
  have hQmap (w : Fin d → ℂ) (hw : MvPolynomial.eval w δ ≠ 0) :
      (X ^ k + ∑ i : Fin k, C (p i) * X ^ (i : ℕ)).map (MvPolynomial.eval w) =
        ∏ τ ∈ rootsIn P u w, (X - C τ) := by
    have hdeg : (∏ τ ∈ rootsIn P u w, (X - C τ)).natDegree = k := by
      rw [hk, ← hcard hw]
      exact natDegree_finsetProd_X_sub_C_eq_card _ _
    ext j
    rw [coeff_map, coeff_X_pow_add_sum]
    split_ifs with h₁ h₂
    · rw [← hp, (hF j).2 w hw]
    · subst h₂
      rw [map_one, ← hdeg]
      exact (hQm w).coeff_natDegree.symm
    · rw [map_zero, coeff_eq_zero_of_natDegree_lt]
      omega
  have hmod (w : Fin d → ℂ) (hw : MvPolynomial.eval w δ ≠ 0) :
      (P %ₘ (X ^ k + ∑ i : Fin k, C (p i) * X ^ (i : ℕ))).map (MvPolynomial.eval w) = 0 := by
    rw [map_modByMonic _ hQ'm, hQmap w hw, modByMonic_eq_zero_iff_dvd (hQm w),
      ← prod_roots_toFinset_of_separable hP (hsep w hw)]
    unfold rootsIn
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  have hmod0 : P %ₘ (X ^ k + ∑ i : Fin k, C (p i) * X ^ (i : ℕ)) = 0 := by
    refine Polynomial.ext fun j ↦ ?_
    have h : δ * (P %ₘ (X ^ k + ∑ i : Fin k, C (p i) * X ^ (i : ℕ))).coeff j = 0 :=
      MvPolynomial.funext fun w ↦ by
        by_cases hw : MvPolynomial.eval w δ = 0
        · simp [hw]
        · have := congrArg (coeff · j) (hmod w hw)
          simp only [coeff_map, coeff_zero] at this
          simp [this]
    simpa [hδ] using h
  obtain ⟨D, hD⟩ := (modByMonic_eq_zero_iff_dvd hQ'm).1 hmod0
  rcases hirr.isUnit_or_isUnit hD with h | h
  · have := natDegree_eq_zero_of_isUnit h
    omega
  · have hD0 : D ≠ 0 := by
      rintro rfl
      exact hP.ne_zero (by simpa using hD)
    have := congrArg natDegree hD
    rw [hQ'm.natDegree_mul' hD0, natDegree_eq_zero_of_isUnit h, hQ'deg] at this
    omega

end

end ComplexAnalytic
