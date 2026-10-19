/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Algebra.Ring.GeomSum
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic
import Tengoku.Seed.Topology.Covering.Basic
import Tengoku.LanaOka.Oka.Analytification.RET.RootCover
import Tengoku.LanaOka.Oka.Topology.Algebra.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Simple roots of families of polynomials

Let `p : X → ℂ[X]` be a family of monic polynomials of fixed degree whose coefficients depend
continuously on the parameter. If every member is separable, the zero locus
`{(x, w) | p x (w) = 0}` is a finite covering of `X`: near every parameter the roots are given by
continuous functions, one near each root of the central member. If the parameter space is a
complex normed space and the coefficients are holomorphic, continuous simple roots are
holomorphic.

## Main results

- `Polynomial.eventually_exists_isRoot_near_of_continuous`: roots move continuously in the
  sense that a root at `x₀` is approximated by roots at nearby parameters.
- `Polynomial.isCoveringMap_fst_zeroLocus`: the zero locus of a continuous separable family of
  monic polynomials of fixed degree is a covering of the parameter space.
- `Polynomial.differentiableAt_of_isRoot_of_differentiableAt_coeff`: a continuous simple root of a
  family with holomorphic coefficients is holomorphic.
-/

open Filter Topology Finset Metric

namespace Polynomial

noncomputable section

section Topological

variable {Z : Type*} [TopologicalSpace Z] {d : ℕ} {p : Z → ℂ[X]}

/-- A product of reals which are all at least `a ≥ 0` is at least `a` to the number of factors. -/
private lemma pow_card_le_multiset_prod {s : Multiset ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ x ∈ s, a ≤ x) : a ^ Multiset.card s ≤ s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.prod_cons, mul_comm]
    have hx := h x (Multiset.mem_cons_self x s)
    exact mul_le_mul hx (ih fun y hy ↦ h y (Multiset.mem_cons_of_mem hy)) (by positivity)
      (ha.trans hx)

/-- For parameters near `x₀`, a continuous family of monic polynomials of fixed degree has a root
near each root of `p x₀`. -/
theorem eventually_exists_isRoot_near_of_continuous (hm : ∀ x, (p x).Monic)
    (hd : ∀ x, (p x).natDegree = d) (hc : ∀ i, Continuous fun x ↦ (p x).coeff i) {x₀ : Z}
    {τ : ℂ} (hτ : (p x₀).IsRoot τ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ σ, (p x).IsRoot σ ∧ ‖σ - τ‖ < ε := by
  have hc' : Tendsto (fun x ↦ (p x).eval τ) (𝓝 x₀) (𝓝 0) := by
    have := ((continuous_eval_of_continuous_coeff (fun x ↦ (hd x).le) hc).comp
      (continuous_id.prodMk (continuous_const (y := τ)))).tendsto x₀
    rw [Function.comp_def] at this
    simpa [hτ.eq_zero] using this
  filter_upwards [(tendsto_norm_zero.comp hc').eventually
    (eventually_lt_nhds (show (0 : ℝ) < ε ^ d by positivity))] with x hx
  by_contra! h
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hm x)
    IsAlgClosed.card_roots_eq_natDegree
  have hev : ‖(p x).eval τ‖ = ((p x).roots.map fun σ ↦ ‖τ - σ‖).prod := by
    conv_lhs => rw [← hprod]
    rw [eval_multiset_prod, Multiset.map_map]
    change (normHom : ℂ →*₀ ℝ) _ = _
    rw [map_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hle : ε ^ d ≤ ‖(p x).eval τ‖ := by
    rw [hev, ← hd x, ← IsAlgClosed.card_roots_eq_natDegree,
      ← Multiset.card_map (fun σ ↦ ‖τ - σ‖)]
    refine pow_card_le_multiset_prod hε.le fun y hy ↦ ?_
    obtain ⟨σ, hσ, rfl⟩ := Multiset.mem_map.1 hy
    rw [norm_sub_rev]
    exact h σ (isRoot_of_mem_roots hσ)
  exact lt_irrefl _ (hle.trans_lt hx)

/-- A separable monic complex polynomial is the product of `X - C τ` over its roots. -/
theorem prod_roots_toFinset_of_separable {q : ℂ[X]} (hm : q.Monic) (hs : q.Separable) :
    ∏ τ ∈ q.roots.toFinset, (X - C τ) = q := by
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.2 (nodup_roots hs)]
  exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm IsAlgClosed.card_roots_eq_natDegree

/-- A separable complex polynomial has as many distinct roots as its degree. -/
theorem card_roots_toFinset_of_separable {q : ℂ[X]} (hs : q.Separable) :
    q.roots.toFinset.card = q.natDegree := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), IsAlgClosed.card_roots_eq_natDegree]

/-- **The zero locus of a continuous separable family of monic polynomials of fixed degree is a
covering of the parameter space.** -/
theorem isCoveringMap_fst_zeroLocus (hm : ∀ x, (p x).Monic) (hd : ∀ x, (p x).natDegree = d)
    (hc : ∀ i, Continuous fun x ↦ (p x).coeff i) (hs : ∀ x, (p x).Separable) :
    IsCoveringMap fun q : {q : Z × ℂ // (p q.1).eval q.2 = 0} ↦ (q : Z × ℂ).1 := by
  classical
  intro x₀
  set f := fun q : {q : Z × ℂ // (p q.1).eval q.2 = 0} ↦ (q : Z × ℂ).1
  set T₀ := (p x₀).roots.toFinset
  -- Separate the roots of `p x₀` by discs of radius `ε`.
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
  have hclose {τ τ' σ : ℂ} (hτ : τ ∈ T₀) (hτ' : τ' ∈ T₀) (h₁ : ‖σ - τ‖ < ε)
      (h₂ : ‖σ - τ'‖ < ε) : τ = τ' := by
    by_contra hne
    have := hsepT τ hτ τ' hτ' hne
    have : ‖τ - τ'‖ ≤ ‖σ - τ'‖ + ‖σ - τ‖ := by
      calc ‖τ - τ'‖ = ‖(σ - τ') - (σ - τ)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  -- An open neighbourhood `U` of `x₀` over which every disc contains a root.
  obtain ⟨U, hUex, hUo, hxU⟩ := eventually_nhds_iff.1 ((eventually_all_finset T₀).2 fun τ hτ ↦
    eventually_exists_isRoot_near_of_continuous hm hd hc
      (isRoot_of_mem_roots (Multiset.mem_toFinset.1 hτ)) hε)
  let ρ : ℂ → Z → ℂ := fun τ x ↦
    if h : ∃ σ, (p x).IsRoot σ ∧ ‖σ - τ‖ < ε then h.choose else τ
  have hρ {τ : ℂ} (hτ : τ ∈ T₀) {x : Z} (hx : x ∈ U) :
      (p x).IsRoot (ρ τ x) ∧ ‖ρ τ x - τ‖ < ε := by
    have h := hUex x hx τ hτ
    simp only [ρ, dite_eq_left h]
    exact h.choose_spec
  have hcardT : T₀.card = d := by rw [card_roots_toFinset_of_separable (hs x₀), hd]
  -- Every root over `U` is one of the chosen roots.
  have hkey {x : Z} (hx : x ∈ U) {σ : ℂ} (hσ : (p x).IsRoot σ) : ∃ τ ∈ T₀, σ = ρ τ x := by
    have hinj : Set.InjOn (fun τ ↦ ρ τ x) T₀ := fun τ hτ τ' hτ' h ↦
      hclose hτ hτ' (hρ hτ hx).2 ((congrArg (· - τ') h).symm ▸ (hρ hτ' hx).2)
    have heq : T₀.image (fun τ ↦ ρ τ x) = (p x).roots.toFinset := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro σ hσ
        obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hσ
        exact Multiset.mem_toFinset.2 ((mem_roots (hm x).ne_zero).2 (hρ hτ hx).1)
      · rw [Finset.card_image_of_injOn hinj, card_roots_toFinset_of_separable (hs x), hd,
          hcardT]
    have hmem : σ ∈ T₀.image fun τ ↦ ρ τ x := by
      rw [heq]
      exact Multiset.mem_toFinset.2 ((mem_roots (hm x).ne_zero).2 hσ)
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hmem
    exact ⟨τ, hτ, rfl⟩
  have huniq {x : Z} (hx : x ∈ U) {τ : ℂ} (hτ : τ ∈ T₀) {σ : ℂ} (hσ : (p x).IsRoot σ)
      (hστ : ‖σ - τ‖ < ε) : σ = ρ τ x := by
    obtain ⟨τ', hτ', rfl⟩ := hkey hx hσ
    rw [hclose hτ' hτ (hρ hτ' hx).2 hστ]
  -- The chosen roots are continuous on `U`.
  have hcont {τ : ℂ} (hτ : τ ∈ T₀) : ContinuousOn (ρ τ) U := by
    intro x₁ hx₁
    refine (ContinuousAt.continuousWithinAt ?_)
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε' hε'
    have hδ : 0 < min ε' (ε - ‖ρ τ x₁ - τ‖) := lt_min hε' (by linarith [(hρ hτ hx₁).2])
    filter_upwards [hUo.mem_nhds hx₁, eventually_exists_isRoot_near_of_continuous hm hd hc
      (hρ hτ hx₁).1 hδ] with x hx ⟨σ, hσ, hσ'⟩
    have h₁ : ‖σ - τ‖ < ε := by
      calc ‖σ - τ‖ = ‖(σ - ρ τ x₁) + (ρ τ x₁ - τ)‖ := by ring_nf
        _ ≤ ‖σ - ρ τ x₁‖ + ‖ρ τ x₁ - τ‖ := norm_add_le _ _
        _ < ε := by linarith [hσ'.trans_le (min_le_right _ _)]
    rw [dist_eq_norm, ← huniq hx hτ hσ h₁]
    exact hσ'.trans_le (min_le_left _ _)
  -- The trivialisation over `U`.
  have hroot (q : {q : Z × ℂ // (p q.1).eval q.2 = 0}) : (p q.1.1).IsRoot q.1.2 := q.2
  let idx : f ⁻¹' U → T₀ := fun q ↦
    ⟨(hkey q.2 (hroot q.1)).choose, (hkey q.2 (hroot q.1)).choose_spec.1⟩
  have hidx (q : f ⁻¹' U) : q.1.1.2 = ρ (idx q) q.1.1.1 :=
    (hkey q.2 (hroot q.1)).choose_spec.2
  have hidx_eq (q : f ⁻¹' U) {τ : ℂ} (hτ : τ ∈ T₀) (h : ‖q.1.1.2 - τ‖ < ε) : (idx q : ℂ) = τ :=
    hclose (idx q).2 hτ (by rw [hidx q]; exact (hρ (idx q).2 q.2).2) h
  have hidx_cont : Continuous idx := by
    refine continuous_discrete_rng.2 fun τ ↦ ?_
    have : idx ⁻¹' {τ} = {q : f ⁻¹' U | ‖q.1.1.2 - τ‖ < ε} := by
      ext q
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      refine ⟨fun h ↦ ?_, fun h ↦ Subtype.ext (hidx_eq q τ.2 h)⟩
      rw [hidx q, h]
      exact (hρ τ.2 q.2).2
    rw [this]
    exact isOpen_lt (by fun_prop) continuous_const
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage (I := T₀) ⟨inferInstance, U, hxU, hUo,
    hUo.preimage (continuous_fst.comp continuous_subtype_val),
    { toFun q := (⟨f q, q.2⟩, idx q)
      invFun y := ⟨⟨(y.1.1, ρ y.2 y.1.1), (hρ y.2.2 y.1.2).1⟩, y.1.2⟩
      left_inv q := by
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext rfl (hidx q).symm
      right_inv y := by
        refine Prod.ext rfl (Subtype.ext (hidx_eq _ y.2.2 (hρ y.2.2 y.1.2).2))
      continuous_toFun := by
        refine Continuous.prodMk ?_ hidx_cont
        exact (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
          _
      continuous_invFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        refine (continuous_subtype_val.comp continuous_fst).prodMk ?_
        refine continuous_prod_of_discrete_right.2 fun τ ↦ ?_
        exact (continuousOn_iff_continuous_domRestrict.1 (hcont τ.2)) }, fun _ ↦ rfl⟩

end Topological

section Holomorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : E → ℂ[X]} {n : ℕ} {x₀ : E}

/-- **A continuous simple root of a family of polynomials with holomorphic coefficients is
holomorphic.** -/
theorem differentiableAt_of_isRoot_of_differentiableAt_coeff (hd : ∀ x, (p x).natDegree ≤ n)
    (hdiff : ∀ i, DifferentiableAt ℂ (fun x ↦ (p x).coeff i) x₀) {ρ : E → ℂ}
    (hρ : ContinuousAt ρ x₀) (hroot : ∀ᶠ x in 𝓝 x₀, (p x).IsRoot (ρ x))
    (hsimple : (p x₀).derivative.eval (ρ x₀) ≠ 0) : DifferentiableAt ℂ ρ x₀ := by
  set τ₀ := ρ x₀
  set c : E → ℂ := fun x ↦ (p x).eval τ₀
  set g : ℂ → ℕ → ℂ := fun w i ↦ ∑ j ∈ range i, w ^ j * τ₀ ^ (i - 1 - j)
  set b : E → ℂ := fun x ↦ ∑ i ∈ range (n + 1), (p x).coeff i * g (ρ x) i
  have hev (x : E) (w : ℂ) : (p x).eval w =
      c x + (w - τ₀) * ∑ i ∈ range (n + 1), (p x).coeff i * g w i := by
    simp only [c]
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (hd x)) w,
      eval_eq_sum_range' (Nat.lt_succ_of_le (hd x)) τ₀, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := geom_sum₂_mul w τ₀ i
    simp only [g]
    linear_combination (-(p x).coeff i) * this
  have hc : DifferentiableAt ℂ c x₀ := by
    simp only [c, eval_eq_sum_range' (Nat.lt_succ_of_le (hd _))]
    exact DifferentiableAt.fun_sum fun i _ ↦ (hdiff i).mul_const _
  have hc0 : c x₀ = 0 := hroot.self_of_nhds
  have hb : ContinuousAt b x₀ := by
    refine tendsto_finsetSum _ fun i _ ↦ (hdiff i).continuousAt.mul ?_
    exact tendsto_finsetSum _ fun j _ ↦ (hρ.pow j).mul continuousAt_const
  have hb0 : b x₀ ≠ 0 := by
    have : b x₀ = (p x₀).derivative.eval τ₀ := by
      simp only [b, g, geom_sum₂_self, τ₀]
      rw [eval_eq_sum_range' (n := n + 1)
        (lt_of_le_of_lt (natDegree_derivative_le _) (by have := hd x₀; omega)),
        Finset.sum_range_succ', Finset.sum_range_succ]
      rw [coeff_derivative (p x₀) n,
        coeff_eq_zero_of_natDegree_lt (p := p x₀) (n := n + 1) (by have := hd x₀; omega)]
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [coeff_derivative, Nat.add_sub_cancel]
      push_cast
      ring
    rwa [this]
  have ha : HasFDerivAt c (fderiv ℂ c x₀) x₀ := hc.hasFDerivAt
  have hk : ContinuousAt (fun x ↦ -(b x)⁻¹) x₀ := (hb.inv₀ hb0).neg
  have hmul :=
    (ComplexAnalytic.hasFDerivAt_mul_of_continuousAt ha hc0 hk).differentiableAt.const_add τ₀
  refine hmul.congr_of_eventuallyEq ?_
  filter_upwards [hroot, hb.eventually_ne hb0] with x hx hbx
  have := hev x (ρ x)
  rw [hx.eq_zero] at this
  change ρ x = τ₀ + c x * -(b x)⁻¹
  field_simp
  linear_combination -this

end Holomorphic

end

end Polynomial
