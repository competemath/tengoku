/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Analysis.Complex.Schwarz
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.LogDeriv
import Tengoku.Seed.LinearAlgebra.Lagrange
import Tengoku.Seed.RingTheory.RootsOfUnity.Complex
import Tengoku.LanaOka.Oka.Analytic.RiemannExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded holomorphic functions on a Kummer covering

Let `E` be a finite-dimensional complex normed space, `k > 0` and `κ : E × ℂ → E × ℂ` the map
`(b, u) ↦ (b, uᵏ)`. Let `V ⊆ E × ℂ` be open and write `Z = {u = 0}`. A holomorphic function `f`
on `κ⁻¹(V) \ Z` which is bounded near every point of `Z` can be written uniquely as
`f(b, u) = ∑_{j < k} uʲ gⱼ(b, uᵏ)` with `gⱼ` holomorphic on `V`. In other words, the bounded
holomorphic functions on `κ⁻¹(V) \ Z` form the free module over the holomorphic functions on `V`
with basis `1, u, …, uᵏ⁻¹`, and they are exactly the restrictions of the holomorphic functions on
`κ⁻¹(V)`.

## Proof

For `0 ≤ j < k` let `Hⱼ(b, t) = k⁻¹ ∑_{rᵏ = t} rᵏ⁻ʲ f(b, r)`, the sum over the `k`-th roots of `t`
counted with multiplicity. Near a point with `t ≠ 0` the roots are `ζⁱ ρ(t)` for a holomorphic
branch `ρ` of the `k`-th root, so `Hⱼ` is holomorphic off `Z`; near `Z` it is bounded and tends
to zero. By the Riemann extension theorem `Hⱼ` extends holomorphically to `V` and vanishes on `Z`,
so by the Schwarz lemma `Hⱼ / t` is bounded near `Z` and extends to a holomorphic `gⱼ`. The
orthogonality of the characters of the `k`-th roots of unity gives `f = ∑ uʲ gⱼ ∘ κ`.

## Main definitions

- `Kummer.powMap k`: the map `(b, u) ↦ (b, uᵏ)` on `E × ℂ`.
- `Kummer.trace k j f`: the function `(b, t) ↦ k⁻¹ ∑_{rᵏ = t} rᵏ⁻ʲ f(b, r)`.

## Main results

- `Kummer.exists_eqOn_sum_pow_mul_comp_powMap`: a holomorphic function on `κ⁻¹(V) \ Z` bounded
  near `Z` is `∑ uʲ gⱼ ∘ κ` with `gⱼ` holomorphic on `V`.
- `Kummer.eqOn_zero_of_sum_pow_mul_comp_powMap`: the `gⱼ` are unique.
- `Kummer.differentiableOn_sum_pow_mul_comp_powMap`: conversely such sums are holomorphic on
  `κ⁻¹(V)`.
- `Kummer.exists_differentiableOn_powMap_eqOn`: a holomorphic function on
  `κ⁻¹(V) \ Z` which is bounded near `Z` extends holomorphically to `κ⁻¹(V)`.
- `Kummer.isBoundedUnder_of_pow_add_sum_eq_zero`: a function satisfying a monic equation with
  bounded coefficients is bounded; in particular integral functions are bounded near `Z`.
-/

open Set Filter Topology Metric Complex

namespace Kummer

noncomputable section

variable {E : Type*}

/-- The map `(b, u) ↦ (b, uᵏ)` on `E × ℂ`. -/
def powMap (k : ℕ) (x : E × ℂ) : E × ℂ := (x.1, x.2 ^ k)

@[simp]
lemma powMap_apply (k : ℕ) (x : E × ℂ) : powMap k x = (x.1, x.2 ^ k) :=
  rfl

@[fun_prop]
lemma continuous_powMap [NormedAddCommGroup E] (k : ℕ) : Continuous (powMap (E := E) k) := by
  unfold powMap
  fun_prop

@[fun_prop]
lemma differentiable_powMap [NormedAddCommGroup E] [NormedSpace ℂ E] (k : ℕ) :
    Differentiable ℂ (powMap (E := E) k) := by
  unfold powMap
  fun_prop

/-- The primitive `k`-th root of unity `exp(2πi / k)`. -/
def zeta (k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / k)

lemma isPrimitiveRoot_zeta {k : ℕ} (hk : 0 < k) : IsPrimitiveRoot (zeta k) k :=
  Complex.isPrimitiveRoot_exp k hk.ne'

/-- The function `(b, t) ↦ k⁻¹ ∑_{rᵏ = t} rᵏ⁻ʲ f(b, r)`, the sum running over the `k`-th roots of
`t` with multiplicity. -/
def trace (k j : ℕ) (f : E × ℂ → ℂ) (x : E × ℂ) : ℂ :=
  (k : ℂ)⁻¹ * ((Polynomial.nthRoots k x.2).map fun r ↦ r ^ (k - j) * f (x.1, r)).sum

lemma trace_eq {k : ℕ} (hk : 0 < k) (j : ℕ) (f : E × ℂ → ℂ) {x : E × ℂ} {r : ℂ}
    (hr : r ^ k = x.2) :
    trace k j f x = (k : ℂ)⁻¹ *
      ∑ i ∈ Finset.range k, (zeta k ^ i * r) ^ (k - j) * f (x.1, zeta k ^ i * r) := by
  rw [trace, (isPrimitiveRoot_zeta hk).nthRoots_eq hr, Multiset.map_map, Finset.sum_eq_multiset_sum,
    Finset.range_val]
  rfl

lemma exists_pow_eq (t : ℂ) {k : ℕ} (hk : 0 < k) : ∃ r : ℂ, r ^ k = t :=
  ⟨t ^ ((k : ℂ)⁻¹), Complex.cpow_nat_inv_pow t hk.ne'⟩

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The zero set of the second coordinate has empty interior in any subset of `E × ℂ`. -/
lemma interior_inter_preimage_snd_eq_empty (U : Set (E × ℂ)) :
    interior (U ∩ Prod.snd ⁻¹' {0}) = ∅ := by
  have h : interior (univ ∩ (Prod.snd : E × ℂ → ℂ) ⁻¹' {0}) = ∅ :=
    AnalyticOnNhd.interior_inter_preimage_zero_eq_empty
      (fun x _ ↦ (ContinuousLinearMap.snd ℂ E ℂ).analyticAt x) isPreconnected_univ
      (z := (0, 1)) trivial one_ne_zero
  exact subset_empty_iff.1 (h ▸ interior_mono (inter_subset_inter_left _ (subset_univ U)))

variable [FiniteDimensional ℂ E]

/-- The Riemann extension theorem across `u = 0`, with boundedness required only at the points
of `u = 0`. -/
lemma exists_differentiableOn_eqOn_diff_snd {V : Set (E × ℂ)} (hV : IsOpen V) {F : E × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (V \ Prod.snd ⁻¹' {0}))
    (hb : ∀ x ∈ V, x.2 = 0 → IsBoundedUnder (· ≤ ·) (𝓝[V \ Prod.snd ⁻¹' {0}] x) (‖F ·‖)) :
    ∃ F' : E × ℂ → ℂ, DifferentiableOn ℂ F' V ∧ EqOn F' F (V \ Prod.snd ⁻¹' {0}) := by
  refine exists_differentiableOn_eqOn_of_isBoundedUnder hV differentiable_snd.differentiableOn
    (interior_inter_preimage_snd_eq_empty V) hF fun x hx ↦ ?_
  by_cases hx0 : x.2 = 0
  · exact hb x hx hx0
  · have hW : IsOpen (V \ Prod.snd ⁻¹' {0}) :=
      hV.sdiff (isClosed_singleton.preimage continuous_snd)
    exact ((hF.differentiableAt (hW.mem_nhds ⟨hx, hx0⟩)).continuousAt.norm.tendsto
      |>.isBoundedUnder_le).mono nhdsWithin_le_nhds

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- The bound on `trace k j f` near `u = 0`: if `‖t‖ < ηᵏ` with `η ≤ 1` and `f` is bounded by `M`
at all points `(b, r)` with `rᵏ = t`, then the trace is bounded by `M η` at `(b, t)`. -/
lemma norm_trace_le {k j : ℕ} (hk : 0 < k) (hj : j < k) {f : E × ℂ → ℂ} {M η : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1) {y : E × ℂ} (hy : ‖y.2‖ < η ^ k)
    (hf : ∀ r : ℂ, r ^ k = y.2 → ‖f (y.1, r)‖ ≤ M) : ‖trace k j f y‖ ≤ M * η := by
  obtain ⟨r, hr⟩ := exists_pow_eq y.2 hk
  have hζ := isPrimitiveRoot_zeta hk
  have hnorm (i : ℕ) : ‖zeta k ^ i * r‖ = ‖r‖ := by
    rw [norm_mul, norm_pow, hζ.norm'_eq_one hk.ne', one_pow, one_mul]
  have hr1 : ‖r‖ < η := by
    refine lt_of_pow_lt_pow_left₀ k hη0 ?_
    rw [← norm_pow, hr]
    exact hy
  have hpow (i : ℕ) : (zeta k ^ i * r) ^ k = y.2 := by
    rw [mul_pow, ← pow_mul, mul_comm i k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hr]
  rw [trace_eq hk j f hr]
  calc ‖(k : ℂ)⁻¹ * ∑ i ∈ Finset.range k, (zeta k ^ i * r) ^ (k - j) * f (y.1, zeta k ^ i * r)‖
      ≤ (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k,
          ‖(zeta k ^ i * r) ^ (k - j) * f (y.1, zeta k ^ i * r)‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        gcongr
        exact norm_sum_le _ _
    _ ≤ (k : ℝ)⁻¹ * ∑ _i ∈ Finset.range k, η * M := by
        gcongr with i hi
        rw [norm_mul, norm_pow, hnorm]
        refine mul_le_mul ?_ (hf _ (hpow i)) (norm_nonneg _) hη0
        exact (pow_le_of_le_one (norm_nonneg _) (hr1.le.trans hη) (by omega)).trans hr1.le
    _ = M * η := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
lemma setOf_norm_lt_mem_nhds {x : E × ℂ} (hx : x.2 = 0) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    {y : E × ℂ | ‖y.1 - x.1‖ < a ∧ ‖y.2‖ < c} ∈ 𝓝 x := by
  refine mem_of_superset (ball_mem_nhds x (lt_min ha hc)) fun y hy ↦ ?_
  rw [mem_ball, Prod.dist_eq, max_lt_iff, lt_min_iff, lt_min_iff] at hy
  refine ⟨?_, ?_⟩
  · rw [← dist_eq_norm]
    exact hy.1.1
  · have := hy.2.2
    rwa [hx, dist_zero_right] at this

/-- For `j < k`, the function `trace k j f / t` extends holomorphically over `V`. -/
theorem exists_differentiableOn_eqOn_trace_div {k j : ℕ} (hk : 0 < k) (hj : j < k)
    {V : Set (E × ℂ)} (hV : IsOpen V) {f : E × ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (powMap k ⁻¹' V \ Prod.snd ⁻¹' {0}))
    (hbdd : ∀ x ∈ V, x.2 = 0 →
      IsBoundedUnder (· ≤ ·) (𝓝[powMap k ⁻¹' V \ Prod.snd ⁻¹' {0}] x) (‖f ·‖)) :
    ∃ g : E × ℂ → ℂ, DifferentiableOn ℂ g V ∧
      EqOn g (fun y ↦ trace k j f y / y.2) (V \ Prod.snd ⁻¹' {0}) := by
  set Z : Set (E × ℂ) := Prod.snd ⁻¹' {0}
  have hZ : IsClosed Z := isClosed_singleton.preimage continuous_snd
  have hVZ : IsOpen (V \ Z) := hV.sdiff hZ
  have hVZ' : IsOpen (powMap k ⁻¹' V \ Z) := (hV.preimage (continuous_powMap k)).sdiff hZ
  have hζ := isPrimitiveRoot_zeta hk
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  -- The trace is holomorphic off `Z`.
  have hH : DifferentiableOn ℂ (trace k j f) (V \ Z) := by
    rintro ⟨b₁, t₁⟩ ⟨hV₁, ht₁⟩
    have ht₁ : t₁ ≠ 0 := ht₁
    obtain ⟨r₁, hr₁⟩ := exists_pow_eq t₁ hk
    have hr₁0 : r₁ ≠ 0 := by
      rintro rfl
      exact ht₁ (hr₁ ▸ zero_pow hk.ne')
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℂ → ℂ, ρ = fun t ↦ r₁ * Complex.exp (Complex.log (t / t₁) / k) :=
      ⟨_, rfl⟩
    have hslit : ∀ᶠ y : E × ℂ in 𝓝 (b₁, t₁), y.2 / t₁ ∈ slitPlane :=
      (continuous_snd.div_const t₁).continuousAt.preimage_mem_nhds
        (isOpen_slitPlane.mem_nhds (by simp [div_self ht₁, one_mem_slitPlane]))
    have hρ : ∀ᶠ y : E × ℂ in 𝓝 (b₁, t₁), ρ y.2 ^ k = y.2 := by
      filter_upwards [hslit] with y hy
      simp only [hρdef, mul_pow, ← Complex.exp_nat_mul]
      rw [mul_div_cancel₀ _ hk0, Complex.exp_log (slitPlane_ne_zero hy), hr₁,
        mul_div_cancel₀ _ ht₁]
    have hρd : DifferentiableAt ℂ ρ t₁ := by
      have : DifferentiableAt ℂ Complex.log (t₁ / t₁) :=
        differentiableAt_log (by simp [div_self ht₁, one_mem_slitPlane])
      have h1 : DifferentiableAt ℂ (fun t : ℂ ↦ t / t₁) t₁ := differentiableAt_id.div_const t₁
      have h2 : DifferentiableAt ℂ (fun t : ℂ ↦ Complex.log (t / t₁)) t₁ :=
        DifferentiableAt.comp (g := Complex.log) (f := fun t : ℂ ↦ t / t₁) t₁ this h1
      rw [hρdef]
      exact (differentiableAt_const r₁).mul ((h2.div_const (k : ℂ)).cexp)
    have hρ₁ : ρ t₁ = r₁ := by simp [hρdef, div_self ht₁]
    refine (DifferentiableAt.congr_of_eventuallyEq (f := fun y : E × ℂ ↦ (k : ℂ)⁻¹ *
      ∑ i ∈ Finset.range k, (zeta k ^ i * ρ y.2) ^ (k - j) * f (y.1, zeta k ^ i * ρ y.2))
      ?_ ?_).differentiableWithinAt
    · refine (differentiableAt_const _).mul (DifferentiableAt.fun_sum fun i _ ↦ ?_)
      have hρ' : DifferentiableAt ℂ (fun y : E × ℂ ↦ zeta k ^ i * ρ y.2) (b₁, t₁) :=
        (differentiableAt_const _).mul (hρd.comp (b₁, t₁) differentiableAt_snd)
      refine (hρ'.pow _).mul ?_
      have hmem : (b₁, zeta k ^ i * ρ t₁) ∈ powMap k ⁻¹' V \ Z := by
        refine ⟨?_, ?_⟩
        · change (b₁, (zeta k ^ i * ρ t₁) ^ k) ∈ V
          rw [hρ₁, mul_pow, ← pow_mul, mul_comm i k, pow_mul, hζ.pow_eq_one, one_pow, one_mul,
            hr₁]
          exact hV₁
        · change zeta k ^ i * ρ t₁ ≠ 0
          rw [hρ₁]
          exact mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hk.ne')) hr₁0
      exact (hf.differentiableAt (hVZ'.mem_nhds hmem)).comp (b₁, t₁)
        (differentiableAt_fst.prodMk hρ')
    · filter_upwards [hρ] with y hy
      exact trace_eq hk j f hy
  -- Near a point of `Z`, the trace is bounded by `M η` where `‖t‖ < ηᵏ`.
  have hest : ∀ x ∈ V, x.2 = 0 → ∃ M ≥ 0, ∃ δ > 0, δ ≤ 1 ∧ ∀ η, 0 ≤ η → η ≤ δ →
      ∀ y ∈ V \ Z, ‖y.1 - x.1‖ < δ → ‖y.2‖ < η ^ k → ‖trace k j f y‖ ≤ M * η := by
    intro x hx hx0
    obtain ⟨M, hM⟩ := hbdd x hx hx0
    have hM' := eventually_nhdsWithin_iff.1 (eventually_map.1 hM)
    obtain ⟨δ, hδ, hδM⟩ := Metric.eventually_nhds_iff.1 hM'
    refine ⟨max M 0, le_max_right _ _, min δ 1, lt_min hδ one_pos, min_le_right _ _,
      fun η hη0 hηδ y hy hy1 hy2 ↦ ?_⟩
    refine norm_trace_le hk hj hη0 (hηδ.trans (min_le_right _ _)) hy2
      fun r hr ↦ (hδM ?_ ⟨?_, ?_⟩).trans (le_max_left _ _)
    · have hr' : ‖r‖ < η := by
        refine lt_of_pow_lt_pow_left₀ k hη0 ?_
        rw [← norm_pow, hr]
        exact hy2
      rw [Prod.dist_eq, max_lt_iff, hx0, dist_zero_right, dist_eq_norm]
      exact ⟨hy1.trans_le (min_le_left _ _), hr'.trans_le (hηδ.trans (min_le_left _ _))⟩
    · change (y.1, r ^ k) ∈ V
      rw [hr]
      exact hy.1
    · change r ≠ 0
      rintro rfl
      exact hy.2 (show y.2 = 0 by rw [← hr, zero_pow hk.ne'])
  -- The trace extends holomorphically over `V`.
  obtain ⟨H, hHd, hHeq⟩ := exists_differentiableOn_eqOn_diff_snd hV hH fun x hx hx0 ↦ by
    obtain ⟨M, -, δ, hδ, hδ1, hMδ⟩ := hest x hx hx0
    refine ⟨M * δ, eventually_map.2 ?_⟩
    filter_upwards [nhdsWithin_le_nhds (setOf_norm_lt_mem_nhds hx0 hδ (pow_pos hδ k)),
      self_mem_nhdsWithin] with y hy hyV using hMδ δ hδ.le le_rfl y hyV hy.1 hy.2
  -- The extension vanishes on `Z`.
  have hH0 : ∀ x ∈ V, x.2 = 0 → H x = 0 := by
    intro x hx hx0
    obtain ⟨M, hM0, δ, hδ, hδ1, hMδ⟩ := hest x hx hx0
    haveI : (𝓝[V \ Z] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1
      (subset_closure_diff_zero hV (interior_inter_preimage_snd_eq_empty V) hx)
    have h₁ : Tendsto H (𝓝[V \ Z] x) (𝓝 (H x)) :=
      ((hHd.differentiableAt (hV.mem_nhds hx)).continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    have h₂ : Tendsto H (𝓝[V \ Z] x) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      set η := min δ (ε / (2 * (M + 1)))
      have hη : 0 < η := lt_min hδ (by positivity)
      filter_upwards [nhdsWithin_le_nhds (setOf_norm_lt_mem_nhds hx0 hδ (pow_pos hη k)),
        self_mem_nhdsWithin] with y hy hyV
      rw [dist_zero_right, hHeq hyV]
      calc ‖trace k j f y‖ ≤ M * η := hMδ η hη.le (min_le_left _ _) y hyV hy.1 hy.2
        _ ≤ (M + 1) * (ε / (2 * (M + 1))) :=
          mul_le_mul (by linarith) (min_le_right _ _) hη.le (by linarith)
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    exact tendsto_nhds_unique h₁ h₂
  -- By the Schwarz lemma `H / t` is bounded near `Z`.
  have hG : DifferentiableOn ℂ (fun y : E × ℂ ↦ H y / y.2) (V \ Z) := by
    simp_rw [div_eq_mul_inv]
    exact (hHd.mono sdiff_subset).mul
      (differentiable_snd.differentiableOn.inv fun y (hy : y ∈ V \ Z) ↦ hy.2)
  obtain ⟨G, hGd, hGeq⟩ := exists_differentiableOn_eqOn_diff_snd hV hG fun x hx hx0 ↦ by
    obtain ⟨δ₁, hδ₁, hδ₁H⟩ := Metric.continuousAt_iff.1
      (hHd.differentiableAt (hV.mem_nhds hx)).continuousAt 1 one_pos
    obtain ⟨δ₂, hδ₂, hδ₂V⟩ := Metric.isOpen_iff.1 hV x hx
    set δ := min δ₁ δ₂
    have hδ : 0 < δ := lt_min hδ₁ hδ₂
    refine ⟨1 / δ, eventually_map.2 ?_⟩
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds x hδ), self_mem_nhdsWithin]
      with y hy hyV
    have hball (t : ℂ) (ht : t ∈ ball (0 : ℂ) δ) : (y.1, t) ∈ ball x δ := by
      rw [mem_ball] at hy ht ⊢
      rw [Prod.dist_eq] at hy ⊢
      refine max_lt ((le_max_left _ _).trans_lt hy) ?_
      simpa [hx0] using ht
    have hφd : DifferentiableOn ℂ (fun t ↦ H (y.1, t)) (ball 0 δ) := fun t ht ↦
      ((hHd.differentiableAt (hV.mem_nhds (hδ₂V ((ball_subset_ball (min_le_right _ _))
        (hball t ht))))).comp t ((differentiableAt_const _).prodMk differentiableAt_id))
        |>.differentiableWithinAt
    have hφ0 : H (y.1, 0) = 0 :=
      hH0 _ (hδ₂V ((ball_subset_ball (min_le_right _ _)) (hball 0 (mem_ball_self hδ)))) rfl
    have hmaps : MapsTo (fun t ↦ H (y.1, t)) (ball 0 δ) (closedBall (H (y.1, 0)) 1) := by
      intro t ht
      rw [hφ0, mem_closedBall, dist_zero_right]
      have := hδ₁H ((ball_subset_ball (min_le_left _ _)) (hball t ht))
      rw [hH0 x hx hx0, dist_zero_right] at this
      exact this.le
    have hyδ : y.2 ∈ ball (0 : ℂ) δ := by
      rw [mem_ball] at hy ⊢
      rw [Prod.dist_eq] at hy
      have := (le_max_right _ _).trans_lt hy
      rwa [hx0] at this
    have := Complex.norm_dslope_le_div_of_mapsTo_ball hφd hmaps hyδ
    rw [dslope_of_ne _ hyV.2, slope_def_module, hφ0, sub_zero, sub_zero, smul_eq_mul] at this
    simpa [div_eq_inv_mul] using this
  refine ⟨G, hGd, fun y hy ↦ ?_⟩
  rw [hGeq hy]
  change H y / y.2 = trace k j f y / y.2
  rw [hHeq hy]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- The orthogonality relation behind the decomposition. -/
lemma sum_pow_mul_div {k : ℕ} (hk : 0 < k) {u : ℂ} (hu : u ≠ 0) (F : ℂ → ℂ) :
    ∑ j : Fin k, u ^ (j : ℕ) * (((k : ℂ)⁻¹ *
      ∑ i ∈ Finset.range k, (zeta k ^ i * u) ^ (k - j) * F (zeta k ^ i * u)) / u ^ k) = F u := by
  have hζ := isPrimitiveRoot_zeta hk
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have h₁ (j : Fin k) : u ^ (j : ℕ) * (((k : ℂ)⁻¹ *
      ∑ i ∈ Finset.range k, (zeta k ^ i * u) ^ (k - j) * F (zeta k ^ i * u)) / u ^ k) =
      (k : ℂ)⁻¹ * ∑ i ∈ Finset.range k, (zeta k ^ i) ^ (k - j) * F (zeta k ^ i * u) := by
    rw [← mul_div_assoc, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have : u ^ (j : ℕ) * u ^ (k - j) = u ^ k := by rw [← pow_add, Nat.add_sub_cancel' j.2.le]
    rw [mul_pow, div_eq_iff (pow_ne_zero _ hu)]
    linear_combination (zeta k ^ i) ^ (k - j) * F (zeta k ^ i * u) * (k : ℂ)⁻¹ * this
  have h₂ (i : ℕ) : ∑ j : Fin k, (zeta k ^ i) ^ (k - j) = zeta k ^ i *
      ∑ j ∈ Finset.range k, (zeta k ^ i) ^ j := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ (zeta k ^ i) ^ (k - j)), ← Finset.sum_range_reflect,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    rw [← pow_succ']
    congr 1
    omega
  simp_rw [h₁]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, h₂]
  rw [Finset.sum_eq_single 0]
  · simp [hk0]
  · intro i hi hi0
    rw [Finset.mem_range] at hi
    have hne : zeta k ^ i ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hi0 hi
    rw [geom_sum_eq hne, ← pow_mul, mul_comm i k, pow_mul, hζ.pow_eq_one, one_pow, sub_self,
      zero_div, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 hk) h

/-- **Bounded holomorphic functions on a Kummer covering.** A holomorphic function on
`κ⁻¹(V) \ {u = 0}` which is bounded near `u = 0` is `∑_{j < k} uʲ gⱼ(b, uᵏ)` with `gⱼ` holomorphic
on `V`, where `κ(b, u) = (b, uᵏ)`. -/
theorem exists_eqOn_sum_pow_mul_comp_powMap {k : ℕ} (hk : 0 < k) {V : Set (E × ℂ)}
    (hV : IsOpen V) {f : E × ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (powMap k ⁻¹' V \ Prod.snd ⁻¹' {0}))
    (hbdd : ∀ x ∈ V, x.2 = 0 →
      IsBoundedUnder (· ≤ ·) (𝓝[powMap k ⁻¹' V \ Prod.snd ⁻¹' {0}] x) (‖f ·‖)) :
    ∃ g : Fin k → E × ℂ → ℂ, (∀ j, DifferentiableOn ℂ (g j) V) ∧
      EqOn f (fun x ↦ ∑ j : Fin k, x.2 ^ (j : ℕ) * g j (powMap k x))
        (powMap k ⁻¹' V \ Prod.snd ⁻¹' {0}) := by
  choose g hgd hgeq using fun j : Fin k ↦
    exists_differentiableOn_eqOn_trace_div hk j.2 hV hf hbdd
  refine ⟨g, hgd, fun x hx ↦ ?_⟩
  have hx0 : x.2 ≠ 0 := hx.2
  have hmem : powMap k x ∈ V \ Prod.snd ⁻¹' {0} := ⟨hx.1, pow_ne_zero k hx0⟩
  simp only
  simp_rw [hgeq _ hmem]
  simp only [powMap_apply]
  simp_rw [trace_eq hk _ f (x := (x.1, x.2 ^ k)) (r := x.2) rfl]
  exact (sum_pow_mul_div hk hx0 fun r ↦ f (x.1, r)).symm

omit [FiniteDimensional ℂ E] in
/-- **Uniqueness of the decomposition**: if `∑_{j < k} uʲ gⱼ(b, uᵏ)` vanishes on
`κ⁻¹(V) \ {u = 0}` for continuous `gⱼ`, then every `gⱼ` vanishes on `V`. -/
theorem eqOn_zero_of_sum_pow_mul_comp_powMap {k : ℕ} (hk : 0 < k) {V : Set (E × ℂ)}
    (hV : IsOpen V) {g : Fin k → E × ℂ → ℂ} (hg : ∀ j, ContinuousOn (g j) V)
    (h : EqOn (fun x ↦ ∑ j : Fin k, x.2 ^ (j : ℕ) * g j (powMap k x)) 0
      (powMap k ⁻¹' V \ Prod.snd ⁻¹' {0})) (j : Fin k) :
    EqOn (g j) 0 V := by
  have hζ := isPrimitiveRoot_zeta hk
  refine EqOn.of_eqOn_diff_zero hV (interior_inter_preimage_snd_eq_empty V) (hg j)
    continuousOn_const fun y hy ↦ ?_
  have hy0 : y.2 ≠ 0 := hy.2
  obtain ⟨r, hr⟩ := exists_pow_eq y.2 hk
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hy0 (hr ▸ zero_pow hk.ne')
  set p : Polynomial ℂ := ∑ l : Fin k, Polynomial.C (g l y) * Polynomial.X ^ (l : ℕ)
  have hp : p = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (v := fun i : Fin k ↦
      zeta k ^ (i : ℕ) * r) Finset.univ ?_ ?_ fun i _ ↦ ?_
    · intro i _ i' _ hii'
      exact Fin.ext (hζ.pow_inj i.2 i'.2 (mul_right_cancel₀ hr0 hii'))
    · rw [Finset.card_univ, Fintype.card_fin]
      exact Polynomial.degree_sum_fin_lt _
    · have hpow : (zeta k ^ (i : ℕ) * r) ^ k = y.2 := by
        rw [mul_pow, ← pow_mul, mul_comm (i : ℕ) k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hr]
      have hmem : (y.1, zeta k ^ (i : ℕ) * r) ∈ powMap k ⁻¹' V \ Prod.snd ⁻¹' {0} := by
        refine ⟨?_, mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hk.ne')) hr0⟩
        change (y.1, (zeta k ^ (i : ℕ) * r) ^ k) ∈ V
        rw [hpow]
        exact hy.1
      have := h hmem
      simp only [powMap_apply, hpow, Pi.zero_apply] at this
      simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [← this]
      exact Finset.sum_congr rfl fun l _ ↦ mul_comm _ _
  have := congrArg (Polynomial.coeff · j) hp
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single j (fun l _ hl ↦ ite_eq_right fun h ↦ hl (Fin.ext h.symm))
    (fun h ↦ absurd (Finset.mem_univ j) h), ite_eq_left rfl] at this
  exact this

omit [FiniteDimensional ℂ E] in
/-- Conversely, `∑_{j < k} uʲ gⱼ(b, uᵏ)` is holomorphic on `κ⁻¹(V)` for `gⱼ` holomorphic on `V`. -/
theorem differentiableOn_sum_pow_mul_comp_powMap {k : ℕ} {V : Set (E × ℂ)}
    {g : Fin k → E × ℂ → ℂ} (hg : ∀ j, DifferentiableOn ℂ (g j) V) :
    DifferentiableOn ℂ (fun x ↦ ∑ j : Fin k, x.2 ^ (j : ℕ) * g j (powMap k x))
      (powMap k ⁻¹' V) :=
  DifferentiableOn.fun_sum fun j _ ↦ (differentiable_snd.differentiableOn.pow _).mul
    ((hg j).comp (differentiable_powMap k).differentiableOn fun _ hx ↦ hx)

/-- **Riemann extension on a Kummer covering**: a holomorphic function on `κ⁻¹(V) \ {u = 0}`
which is bounded near `u = 0` extends holomorphically to `κ⁻¹(V)`. -/
theorem exists_differentiableOn_powMap_eqOn {k : ℕ} (hk : 0 < k) {V : Set (E × ℂ)}
    (hV : IsOpen V) {f : E × ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (powMap k ⁻¹' V \ Prod.snd ⁻¹' {0}))
    (hbdd : ∀ x ∈ V, x.2 = 0 →
      IsBoundedUnder (· ≤ ·) (𝓝[powMap k ⁻¹' V \ Prod.snd ⁻¹' {0}] x) (‖f ·‖)) :
    ∃ F : E × ℂ → ℂ, DifferentiableOn ℂ F (powMap k ⁻¹' V) ∧
      EqOn F f (powMap k ⁻¹' V \ Prod.snd ⁻¹' {0}) := by
  obtain ⟨g, hgd, hgeq⟩ := exists_eqOn_sum_pow_mul_comp_powMap hk hV hf hbdd
  exact ⟨_, differentiableOn_sum_pow_mul_comp_powMap hgd, hgeq.symm⟩
omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- A root of a monic polynomial is bounded in terms of its coefficients: if
`zⁿ + ∑_{i < n} aᵢ zⁱ = 0` with `‖aᵢ‖ ≤ A`, then `‖z‖ ≤ max 1 (n A)`. -/
lemma norm_le_of_pow_add_sum_eq_zero {n : ℕ} {z : ℂ} {a : ℕ → ℂ} {A : ℝ}
    (ha : ∀ i < n, ‖a i‖ ≤ A) (h : z ^ n + ∑ i ∈ Finset.range n, a i * z ^ i = 0) :
    ‖z‖ ≤ max 1 (n * A) := by
  by_contra hz
  push Not at hz
  have h1 : 1 < ‖z‖ := (le_max_left _ _).trans_lt hz
  have h2 : n * A < ‖z‖ := (le_max_right _ _).trans_lt hz
  cases n with
  | zero => simp at h
  | succ n =>
    have hA : 0 ≤ A := (norm_nonneg _).trans (ha 0 (Nat.succ_pos n))
    have heq : z ^ (n + 1) = -∑ i ∈ Finset.range (n + 1), a i * z ^ i :=
      eq_neg_of_add_eq_zero_left h
    have hle : ‖z‖ ^ n * ‖z‖ ≤ ‖z‖ ^ n * ((n + 1) * A) := by
      calc ‖z‖ ^ n * ‖z‖ = ‖∑ i ∈ Finset.range (n + 1), a i * z ^ i‖ := by
            rw [← pow_succ, ← norm_pow, heq, norm_neg]
        _ ≤ ∑ i ∈ Finset.range (n + 1), ‖a i‖ * ‖z‖ ^ i := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
            rw [norm_mul, norm_pow]
        _ ≤ ∑ _i ∈ Finset.range (n + 1), A * ‖z‖ ^ n := by
            refine Finset.sum_le_sum fun i hi ↦ mul_le_mul (ha i (Finset.mem_range.1 hi))
              (pow_le_pow_right₀ h1.le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
              (by positivity) hA
        _ = ‖z‖ ^ n * ((n + 1) * A) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have := le_of_mul_le_mul_left hle (pow_pos (by linarith) n)
    push_cast at h2
    linarith

/-- **Integral functions are bounded**: if `f` satisfies eventually along `l` a monic equation
`fⁿ + ∑_{i < n} aᵢ fⁱ = 0` whose coefficients are bounded along `l`, then `f` is bounded along
`l`. -/
theorem isBoundedUnder_of_pow_add_sum_eq_zero {α : Type*} {l : Filter α} {f : α → ℂ} {n : ℕ}
    {a : ℕ → α → ℂ} (ha : ∀ i < n, IsBoundedUnder (· ≤ ·) l (‖a i ·‖))
    (h : ∀ᶠ x in l, f x ^ n + ∑ i ∈ Finset.range n, a i x * f x ^ i = 0) :
    IsBoundedUnder (· ≤ ·) l (‖f ·‖) := by
  have : ∀ i ∈ Finset.range n, ∃ A : ℝ, ∀ᶠ x in l, ‖a i x‖ ≤ A := fun i hi ↦ by
    obtain ⟨A, hA⟩ := ha i (Finset.mem_range.1 hi)
    exact ⟨A, eventually_map.1 hA⟩
  choose! A hA using this
  set A' := ∑ i ∈ Finset.range n, max (A i) 0
  have hev : ∀ᶠ x in l, ∀ i ∈ Finset.range n, ‖a i x‖ ≤ A' :=
    (Filter.eventually_all_finset _).2 fun i hi ↦ (hA i hi).mono fun x hx ↦
      hx.trans ((le_max_left _ _).trans
        (Finset.single_le_sum (f := fun j ↦ max (A j) 0) (fun j _ ↦ le_max_right _ _) hi))
  refine ⟨max 1 (n * A'), eventually_map.2 ?_⟩
  filter_upwards [h, hev] with x hx hx'
  exact norm_le_of_pow_add_sum_eq_zero (fun i hi ↦ hx' i (Finset.mem_range.2 hi)) hx

end

end Kummer
