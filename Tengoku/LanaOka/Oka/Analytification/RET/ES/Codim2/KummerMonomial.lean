/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.LanaOka.Oka.Analysis.Complex.KummerExtension
import Tengoku.LanaOka.Oka.Analysis.Complex.KummerExtensionPi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Holomorphic functions on a Kummer covering along a normal crossings divisor

Let `E` be a finite-dimensional complex normed space, `M > 0` and `κ : E × ℂʳ → E × ℂʳ` the map
`(b, u) ↦ (b, u₁ᴹ, …, uᵣᴹ)` (`KummerPi.powMap M`). For an open `V ⊆ E × ℂʳ`, every holomorphic
function on `κ⁻¹(V)` is uniquely of the form `∑_j uʲ gⱼ(κ(b, u))`, the sum over the exponents
`j ∈ {0, …, M - 1}ʳ`, with `gⱼ` holomorphic on `V`
(`KummerPi.exists_eqOn_sum_monomial_mul_comp_powMap`,
`KummerPi.eqOn_zero_of_sum_monomial_mul_comp_powMap`). This follows from the one-variable case
`Kummer.exists_eqOn_sum_pow_mul_comp_powMap` by induction on `r`.

The multiplication of the coordinates by `M`-th roots of unity `KummerPi.rotMap M a` multiplies
`uʲ` by the character value `KummerPi.rotChar M a j`. Hence a function invariant under
`KummerPi.rotMap M a` has `gⱼ = 0` unless `rotChar M a j = 1`
(`KummerPi.eqOn_zero_of_comp_rotMap_eq`). By `KummerPi.exists_differentiableOn_powMap_eqOn` and
`KummerPi.eqOn_comp_rotMap`, the bounded holomorphic functions on the quotient of a Kummer
covering of `B × (Δ*)ʳ` by a group `Γ` of rotations are the invariant holomorphic functions on
`κ⁻¹(V)`; so they form the free module over the holomorphic functions on `V` with basis the
monomials `uʲ` with `rotChar M a j = 1` for all `a ∈ Γ`.

## Main definitions

- `KummerPi.monomial j`: the function `(b, u) ↦ uʲ = ∏ᵢ uᵢ ^ jᵢ`.
- `KummerPi.rotChar M a j`: the scalar by which `KummerPi.rotMap M a` multiplies `uʲ`.

## Main results

- `KummerPi.exists_eqOn_sum_monomial_mul_comp_powMap`: the decomposition `∑_j uʲ gⱼ ∘ κ`.
- `KummerPi.eqOn_zero_of_sum_monomial_mul_comp_powMap`: uniqueness of the `gⱼ`.
- `KummerPi.differentiableOn_sum_monomial_mul_comp_powMap`: such sums are holomorphic.
- `KummerPi.eqOn_zero_of_comp_rotMap_eq`: invariant functions only involve invariant monomials.
-/

open Set Filter Topology

namespace KummerPi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℕ}

/-- The monomial `(b, u) ↦ uʲ = ∏ᵢ uᵢ ^ jᵢ` on `E × ℂʳ`. -/
def monomial (j : Fin r → ℕ) (x : E × (Fin r → ℂ)) : ℂ :=
  ∏ i, x.2 i ^ j i

/-- The scalar `∏ᵢ exp(2πi aᵢ / M) ^ jᵢ` by which `KummerPi.rotMap M a` multiplies `uʲ`. -/
noncomputable def rotChar (M : ℕ) (a : Fin r → ℤ) (j : Fin r → ℕ) : ℂ :=
  ∏ i, Complex.exp (2 * Real.pi * Complex.I * a i / M) ^ j i

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma monomial_rotMap (M : ℕ) (a : Fin r → ℤ) (j : Fin r → ℕ) (x : E × (Fin r → ℂ)) :
    monomial j (rotMap M a x) = rotChar M a j * monomial j x := by
  simp only [monomial, rotMap, rotChar, mul_pow, Finset.prod_mul_distrib]

@[fun_prop]
lemma differentiable_monomial (j : Fin r → ℕ) :
    Differentiable ℂ (monomial (E := E) j) := by
  unfold monomial
  fun_prop

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma monomial_succ (j : Fin (r + 1) → ℕ) (x : E × (Fin (r + 1) → ℂ)) {F : Type*} (b : F) :
    monomial j x = x.2 0 ^ j 0 * monomial (Fin.tail j) (b, Fin.tail x.2) := by
  simp only [monomial, Fin.prod_univ_succ, Fin.tail]

/-! ### Splitting off the first coordinate -/

/-- The map `((b, u), t) ↦ (b, (t, u))`, inserting the coordinate `t` in front. -/
def consMap (p : (E × (Fin r → ℂ)) × ℂ) : E × (Fin (r + 1) → ℂ) :=
  (p.1.1, Fin.cons p.2 p.1.2)

lemma differentiable_consMap : Differentiable ℂ (consMap (E := E) (r := r)) := by
  refine (differentiable_fst.comp differentiable_fst).prodMk (differentiable_pi.2 fun i ↦ ?_)
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simp only [Fin.cons_zero]
    fun_prop
  · simp only [Fin.cons_succ]
    fun_prop

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma consMap_tail (x : E × (Fin (r + 1) → ℂ)) : consMap ((x.1, Fin.tail x.2), x.2 0) = x :=
  Prod.ext rfl (Fin.cons_self_tail x.2)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma powMap_consMap (M : ℕ) (p : (E × (Fin r → ℂ)) × ℂ) :
    powMap M (consMap p) = consMap ((p.1.1, fun i ↦ p.1.2 i ^ M), p.2 ^ M) := by
  refine Prod.ext rfl (funext fun i ↦ ?_)
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simp [powMap, consMap]
  · simp [powMap, consMap]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma powMap_zero (M : ℕ) (x : E × (Fin 0 → ℂ)) : powMap M x = x :=
  Prod.ext rfl (funext fun i ↦ Fin.elim0 i)

/-! ### The decomposition -/

/-- Sums `∑_j uʲ gⱼ ∘ κ` with `gⱼ` holomorphic on `V` are holomorphic on `κ⁻¹(V)`. -/
theorem differentiableOn_sum_monomial_mul_comp_powMap {M : ℕ} {V : Set (E × (Fin r → ℂ))}
    {g : (Fin r → Fin M) → E × (Fin r → ℂ) → ℂ} (hg : ∀ j, DifferentiableOn ℂ (g j) V) :
    DifferentiableOn ℂ (fun x ↦ ∑ j, monomial (fun i ↦ (j i : ℕ)) x * g j (powMap M x))
      (powMap M ⁻¹' V) :=
  DifferentiableOn.fun_sum fun j _ ↦ (differentiable_monomial _).differentiableOn.mul
    ((hg j).comp (differentiable_powMap M).differentiableOn fun _ hx ↦ hx)

variable [FiniteDimensional ℂ E]

/-- **Holomorphic functions on a Kummer covering along a normal crossings divisor.** A
holomorphic function on `κ⁻¹(V)` is `∑_j uʲ gⱼ(κ(b, u))`, the sum over `j ∈ {0, …, M - 1}ʳ`, with
`gⱼ` holomorphic on `V`. -/
theorem exists_eqOn_sum_monomial_mul_comp_powMap {M : ℕ} (hM : 0 < M)
    {V : Set (E × (Fin r → ℂ))} (hV : IsOpen V) {F : E × (Fin r → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (powMap M ⁻¹' V)) :
    ∃ g : (Fin r → Fin M) → E × (Fin r → ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (g j) V) ∧
      EqOn F (fun x ↦ ∑ j, monomial (fun i ↦ (j i : ℕ)) x * g j (powMap M x))
        (powMap M ⁻¹' V) := by
  induction r generalizing E with
  | zero =>
    refine ⟨fun _ ↦ F, fun _ ↦ ?_, fun x _ ↦ ?_⟩
    · have : powMap M ⁻¹' V = V := by ext x; simp [powMap_zero]
      rwa [this] at hF
    · simp [monomial, powMap_zero]
  | succ r ih =>
    -- First the Kummer decomposition in the coordinate `u₀`, with parameters `(b, u')`.
    set V₁ : Set ((E × (Fin r → ℂ)) × ℂ) :=
      (fun p ↦ consMap ((p.1.1, fun i ↦ p.1.2 i ^ M), p.2)) ⁻¹' V
    have hV₁ : IsOpen V₁ := hV.preimage (differentiable_consMap.continuous.comp (by fun_prop))
    have hpre₁ (p : (E × (Fin r → ℂ)) × ℂ) :
        p ∈ Kummer.powMap M ⁻¹' V₁ ↔ consMap p ∈ powMap M ⁻¹' V := by
      simp only [mem_preimage, V₁, powMap_consMap, Kummer.powMap_apply]
    have hf₁ : DifferentiableOn ℂ (F ∘ consMap) (Kummer.powMap M ⁻¹' V₁) :=
      hF.comp differentiable_consMap.differentiableOn fun p hp ↦ (hpre₁ p).1 hp
    have hVo₁ : IsOpen (Kummer.powMap M ⁻¹' V₁) :=
      hV₁.preimage (Kummer.continuous_powMap M)
    obtain ⟨g₁, hg₁, hfg₁⟩ := Kummer.exists_eqOn_sum_pow_mul_comp_powMap hM hV₁
      (hf₁.mono sdiff_subset) fun p hp hp0 ↦ by
        have hp' : p ∈ Kummer.powMap M ⁻¹' V₁ := by
          change (p.1, p.2 ^ M) ∈ V₁
          rwa [hp0, zero_pow hM.ne', ← hp0]
        exact ((hf₁.differentiableAt (hVo₁.mem_nhds hp')).continuousAt.norm.tendsto
          |>.isBoundedUnder_le).mono nhdsWithin_le_nhds
    have hfg₁' := EqOn.of_eqOn_diff_zero hVo₁ (Kummer.interior_inter_preimage_snd_eq_empty _)
      hf₁.continuousOn (Kummer.differentiableOn_sum_pow_mul_comp_powMap hg₁).continuousOn hfg₁
    -- Then the induction hypothesis for the coefficients, with parameters `(b, t₀)`.
    set V₂ : Set ((E × ℂ) × (Fin r → ℂ)) := (fun q ↦ consMap ((q.1.1, q.2), q.1.2)) ⁻¹' V
    have hsw : Differentiable ℂ fun q : (E × ℂ) × (Fin r → ℂ) ↦
        (((q.1.1, q.2), q.1.2) : (E × (Fin r → ℂ)) × ℂ) := by fun_prop
    have hV₂ : IsOpen V₂ := hV.preimage (differentiable_consMap.continuous.comp hsw.continuous)
    have hpre₂ (j₀ : Fin M) : DifferentiableOn ℂ (fun q ↦ g₁ j₀ ((q.1.1, q.2), q.1.2))
        (powMap M ⁻¹' V₂) :=
      (hg₁ j₀).comp hsw.differentiableOn fun q hq ↦ hq
    choose k hk hkeq using fun j₀ ↦ ih hV₂ (hpre₂ j₀)
    have hsplit : Differentiable ℂ fun x : E × (Fin (r + 1) → ℂ) ↦
        (((x.1, x.2 0), Fin.tail x.2) : (E × ℂ) × (Fin r → ℂ)) := by
      refine (differentiable_fst.prodMk ?_).prodMk ?_
      · fun_prop
      · refine differentiable_pi.2 fun i ↦ ?_
        change Differentiable ℂ fun x : E × (Fin (r + 1) → ℂ) ↦ x.2 i.succ
        fun_prop
    refine ⟨fun j x ↦ k (j 0) (Fin.tail j) ((x.1, x.2 0), Fin.tail x.2), fun j ↦ ?_,
      fun x hx ↦ ?_⟩
    · refine (hk (j 0) (Fin.tail j)).comp hsplit.differentiableOn fun x hx ↦ ?_
      change consMap ((x.1, Fin.tail x.2), x.2 0) ∈ V
      rwa [consMap_tail]
    have hx₁ : ((x.1, Fin.tail x.2), x.2 0) ∈ Kummer.powMap M ⁻¹' V₁ := by
      rw [hpre₁, consMap_tail]
      exact hx
    have h₁ := hfg₁' hx₁
    simp only [Function.comp_apply, consMap_tail, Kummer.powMap_apply] at h₁
    rw [h₁]
    have hx₂ : ((x.1, x.2 0 ^ M), Fin.tail x.2) ∈ powMap M ⁻¹' V₂ := by
      have h := powMap_consMap M ((x.1, Fin.tail x.2), x.2 0)
      rw [consMap_tail] at h
      change consMap ((x.1, fun i ↦ Fin.tail x.2 i ^ M), x.2 0 ^ M) ∈ V
      rw [← h]
      exact hx
    have h₂ (j₀ : Fin M) := hkeq j₀ hx₂
    simp only at h₂
    simp_rw [h₂]
    rw [← (Fin.consEquiv fun _ : Fin (r + 1) ↦ Fin M).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j₀ _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ ↦ ?_
    rw [show (Fin.consEquiv fun _ : Fin (r + 1) ↦ Fin M) (j₀, j') = Fin.cons j₀ j' from rfl]
    simp only [monomial_succ _ x x.1, Fin.cons_zero, Fin.tail_cons]
    have hpow : powMap M ((x.1, x.2 0 ^ M), Fin.tail x.2) =
        (((powMap M x).1, (powMap M x).2 0), Fin.tail (powMap M x).2) := rfl
    rw [hpow, mul_assoc]
    rfl

omit [FiniteDimensional ℂ E] in
/-- **Uniqueness of the decomposition.** If `∑_j uʲ gⱼ ∘ κ` vanishes on `κ⁻¹(V)` for `gⱼ`
continuous on `V`, then every `gⱼ` vanishes on `V`. -/
theorem eqOn_zero_of_sum_monomial_mul_comp_powMap {M : ℕ} (hM : 0 < M)
    {V : Set (E × (Fin r → ℂ))} (hV : IsOpen V) {g : (Fin r → Fin M) → E × (Fin r → ℂ) → ℂ}
    (hg : ∀ j, ContinuousOn (g j) V)
    (h : EqOn (fun x ↦ ∑ j, monomial (fun i ↦ (j i : ℕ)) x * g j (powMap M x)) 0
      (powMap M ⁻¹' V)) (j : Fin r → Fin M) : EqOn (g j) 0 V := by
  induction r generalizing E with
  | zero =>
    intro x hx
    have hx' : x ∈ powMap M ⁻¹' V := by rwa [mem_preimage, powMap_zero]
    have := h hx'
    simp only [Fintype.sum_unique, monomial, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
      powMap_zero, Pi.zero_apply] at this
    rw [Subsingleton.elim j default]
    exact this
  | succ r ih =>
    set V₁ : Set ((E × (Fin r → ℂ)) × ℂ) :=
      (fun p ↦ consMap ((p.1.1, fun i ↦ p.1.2 i ^ M), p.2)) ⁻¹' V
    have hV₁ : IsOpen V₁ := hV.preimage (differentiable_consMap.continuous.comp (by fun_prop))
    have hsw : Continuous fun p : (E × (Fin r → ℂ)) × ℂ ↦
        (((p.1.1, p.2), p.1.2) : (E × ℂ) × (Fin r → ℂ)) := by fun_prop
    -- The coefficient of `u₀ ^ j₀`, as a function of `((b, u'), t₀)`.
    set G : Fin M → (E × (Fin r → ℂ)) × ℂ → ℂ := fun j₀ p ↦
      ∑ j' : Fin r → Fin M, monomial (fun i ↦ (j' i : ℕ)) ((p.1.1, p.2), p.1.2) *
        g (Fin.cons j₀ j') (consMap ((p.1.1, fun i ↦ p.1.2 i ^ M), p.2))
    have hG (j₀ : Fin M) : ContinuousOn (G j₀) V₁ := by
      refine continuousOn_finsetSum _ fun j' _ ↦ ?_
      refine ((differentiable_monomial _).continuous.comp hsw).continuousOn.mul ?_
      exact (hg _).comp (differentiable_consMap.continuous.comp (by fun_prop)).continuousOn
        fun p hp ↦ hp
    have hG0 (j₀ : Fin M) : EqOn (G j₀) 0 V₁ := by
      refine Kummer.eqOn_zero_of_sum_pow_mul_comp_powMap hM hV₁ hG (fun p hp ↦ ?_) j₀
      have hp' : consMap p ∈ powMap M ⁻¹' V := by
        change powMap M (consMap p) ∈ V
        rw [powMap_consMap]
        exact hp.1
      have := h hp'
      simp only [Pi.zero_apply] at this ⊢
      rw [← this, ← (Fin.consEquiv fun _ : Fin (r + 1) ↦ Fin M).sum_comp,
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j₀ _ ↦ ?_
      simp only [G, Kummer.powMap_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ ↦ ?_
      rw [show (Fin.consEquiv fun _ : Fin (r + 1) ↦ Fin M) (j₀, j') = Fin.cons j₀ j' from rfl]
      simp only [monomial_succ _ (consMap p) p.1.1, powMap_consMap]
      simp only [consMap, Fin.cons_zero, monomial, Fin.tail, Fin.cons_succ]
      ring
    -- Apply the induction hypothesis to the coefficients.
    set V₂ : Set ((E × ℂ) × (Fin r → ℂ)) := (fun q ↦ consMap ((q.1.1, q.2), q.1.2)) ⁻¹' V
    have hsw₂ : Continuous fun q : (E × ℂ) × (Fin r → ℂ) ↦
        (((q.1.1, q.2), q.1.2) : (E × (Fin r → ℂ)) × ℂ) := by fun_prop
    have hV₂ : IsOpen V₂ := hV.preimage (differentiable_consMap.continuous.comp hsw₂)
    have hcons : Continuous fun q : (E × ℂ) × (Fin r → ℂ) ↦ consMap ((q.1.1, q.2), q.1.2) :=
      differentiable_consMap.continuous.comp hsw₂
    have hih := ih (E := E × ℂ) hV₂
      (g := fun j' q ↦ g (Fin.cons (j 0) j') (consMap ((q.1.1, q.2), q.1.2)))
      (fun j' ↦ (hg _).comp hcons.continuousOn fun q hq ↦ hq) (fun q hq ↦ ?_) (Fin.tail j)
    · intro x hx
      have hx' : ((x.1, x.2 0), Fin.tail x.2) ∈ V₂ := by
        change consMap ((x.1, Fin.tail x.2), x.2 0) ∈ V
        rwa [consMap_tail]
      have := hih hx'
      simp only [Fin.cons_self_tail, consMap_tail] at this
      exact this
    · have hq' : ((q.1.1, q.2), q.1.2) ∈ V₁ := by
        change consMap ((q.1.1, fun i ↦ q.2 i ^ M), q.1.2) ∈ V
        exact hq
      have := hG0 (j 0) hq'
      simp only [G, Pi.zero_apply] at this ⊢
      rw [← this]
      rfl

omit [FiniteDimensional ℂ E] in
/-- **Invariant functions only involve invariant monomials.** If `∑_j uʲ gⱼ ∘ κ` is invariant on
`κ⁻¹(V)` under the rotation `KummerPi.rotMap M a`, then `gⱼ` vanishes on `V` for every `j` with
`rotChar M a j ≠ 1`. -/
theorem eqOn_zero_of_comp_rotMap_eq {M : ℕ} (hM : 0 < M) {V : Set (E × (Fin r → ℂ))}
    (hV : IsOpen V) {g : (Fin r → Fin M) → E × (Fin r → ℂ) → ℂ}
    (hg : ∀ j, ContinuousOn (g j) V) (a : Fin r → ℤ)
    (h : ∀ x ∈ powMap M ⁻¹' V,
      ∑ j, monomial (fun i ↦ (j i : ℕ)) (rotMap M a x) * g j (powMap M (rotMap M a x)) =
        ∑ j, monomial (fun i ↦ (j i : ℕ)) x * g j (powMap M x))
    {j : Fin r → Fin M} (hj : rotChar M a (fun i ↦ (j i : ℕ)) ≠ 1) : EqOn (g j) 0 V := by
  have h' := eqOn_zero_of_sum_monomial_mul_comp_powMap hM hV
    (g := fun j x ↦ (rotChar M a (fun i ↦ (j i : ℕ)) - 1) * g j x)
    (fun j ↦ continuousOn_const.mul (hg j)) (fun x hx ↦ ?_) j
  · intro x hx
    have := h' hx
    simp only [Pi.zero_apply, mul_eq_zero, sub_eq_zero, hj, false_or] at this
    exact this
  · have := h x hx
    simp only [powMap_rotMap hM.ne', monomial_rotMap] at this
    simp only [Pi.zero_apply]
    rw [← sub_eq_zero.2 this, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring

end KummerPi
