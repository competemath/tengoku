/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.RelativeRiemannRoch.WeightAlgebraRG6B
import Tengoku.Seed.RingTheory.PowerSeries.Exp
import Tengoku.Seed.RingTheory.PowerSeries.Inverse
import Tengoku.Seed.RingTheory.PowerSeries.Trunc
import Tengoku.Seed.RingTheory.PowerSeries.NoZeroDivisors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RG6B, part B: the Todd class `td_K = ∏ Td(log L)` from the recursion `ψ τ = s τ`

Evaluation of `ℚ⟦X⟧` at an element `a` with `a^(D+1) = 0`, the series
`P = (1 - e^{-X}) / X`, `Td = P⁻¹ = X/(1 - e^{-X})`, `Θ_j = ∑_{m<j} e^{-mX}`, and the identity
`Θ_j(X) · Td(jX) = j · Td(X)`.  Hence for `a` of weight one (`ψ a = j a`),
`θ(a) · ψ Td(a) = j · Td(a)`, and the recursion element `τ` of part A equals
`∏ Td(a_i) / ∏ Td(b_k)` when `s = j^d θ(Ω_f)^{-1}`, `θ(Ω_f) = ∏ θ(a_i) / ∏ θ(b_k)`.
-/

namespace RG6B

open PowerSeries

section Series

/-- `P = (1 - e^{-X}) / X = ∑ (-1)^k X^k / (k+1)!`-/
noncomputable def Pser : ℚ⟦X⟧ := PowerSeries.mk fun k => (-1 : ℚ) ^ k / ((k + 1).factorial : ℚ)

/-- `e^{-X}`-/
noncomputable def expNeg : ℚ⟦X⟧ := rescale (-1 : ℚ) (exp ℚ)

/-- `Θ_j = ∑_{m<j} e^{-mX}`-/
noncomputable def Theta (j : ℕ) : ℚ⟦X⟧ := ∑ m ∈ Finset.range j, expNeg ^ m

/-- the Todd series `Td = X / (1 - e^{-X}) = P⁻¹`-/
noncomputable def Tdser : ℚ⟦X⟧ := (Pser)⁻¹

theorem constantCoeff_Pser : constantCoeff Pser = 1 := by
  simp [Pser, ← coeff_zero_eq_constantCoeff_apply]

theorem coeff_expNeg (n : ℕ) : coeff n expNeg = (-1 : ℚ) ^ n / (n.factorial : ℚ) := by
  simp [expNeg, coeff_rescale, coeff_exp, div_eq_mul_inv]

theorem constantCoeff_expNeg : constantCoeff expNeg = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_expNeg]; simp

theorem X_mul_Pser : X * Pser = 1 - expNeg := by
  ext n
  rcases n with _ | n
  · rw [coeff_zero_X_mul, map_sub, coeff_zero_one, coeff_expNeg]; simp
  · rw [coeff_succ_X_mul, map_sub, coeff_one, coeff_expNeg]
    simp only [Pser, coeff_mk, Nat.succ_ne_zero, ite_false, zero_sub]
    rw [pow_succ]
    ring

theorem rescale_expNeg (j : ℕ) : rescale (j : ℚ) expNeg = expNeg ^ j := by
  have h1 : expNeg ^ j = rescale (-1 : ℚ) (exp ℚ ^ j) := by rw [expNeg, map_pow]
  rw [h1, exp_pow_eq_rescale_exp, expNeg]
  rw [← RingHom.comp_apply, ← rescale_mul, ← RingHom.comp_apply, ← rescale_mul, mul_comm]

theorem Pser_scale (j : ℕ) : C (j : ℚ) * rescale (j : ℚ) Pser = Pser * Theta j := by
  apply mul_left_cancel₀ (X_ne_zero (R := ℚ))
  have e1 : X * (C (j : ℚ) * rescale (j : ℚ) Pser) = 1 - expNeg ^ j := by
    have := congrArg (rescale (j : ℚ)) X_mul_Pser
    rw [map_mul, rescale_X, map_sub, map_one, rescale_expNeg] at this
    rw [← this]; ring
  have e2 : X * (Pser * Theta j) = 1 - expNeg ^ j := by
    rw [← mul_assoc, X_mul_Pser, Theta, mul_neg_geom_sum]
  rw [e1, e2]

theorem Pser_mul_Tdser : Pser * Tdser = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_Pser]; exact one_ne_zero)

theorem constantCoeff_Tdser : constantCoeff Tdser = 1 := by
  have := congrArg constantCoeff Pser_mul_Tdser
  rwa [map_mul, constantCoeff_Pser, one_mul, map_one] at this

/-- `Θ_j(X) · Td(jX) = j · Td(X)`-/
theorem Theta_mul_rescale_Tdser (j : ℕ) :
    Theta j * rescale (j : ℚ) Tdser = C (j : ℚ) * Tdser := by
  have h4 := Pser_scale j
  have hPT := Pser_mul_Tdser
  have hRR : rescale (j : ℚ) Pser * rescale (j : ℚ) Tdser = 1 := by
    rw [← map_mul, hPT, map_one]
  linear_combination (-(Theta j * rescale (j : ℚ) Tdser)) * hPT +
    (-(Tdser * rescale (j : ℚ) Tdser)) * h4 + (C (j : ℚ) * Tdser) * hRR

theorem constantCoeff_Theta (j : ℕ) : constantCoeff (Theta j) = (j : ℚ) := by
  simp [Theta, map_sum, constantCoeff_expNeg]

end Series

section Eval

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- evaluation of a power series at `a`, truncated at order `D + 1`-/
noncomputable def ev (D : ℕ) (a : K) (f : ℚ⟦X⟧) : K := Polynomial.aeval a (trunc (D + 1) f)

theorem ev_eq_sum (D : ℕ) (a : K) (f : ℚ⟦X⟧) :
    ev D a f = ∑ i ∈ Finset.range (D + 1), coeff i f • a ^ i := by
  unfold ev
  rw [Polynomial.aeval_eq_sum_range' (n := D + 1) (natDegree_trunc_lt f D)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [coeff_trunc, ite_eq_left (Finset.mem_range.1 hi)]

theorem ev_add (D : ℕ) (a : K) (f g : ℚ⟦X⟧) : ev D a (f + g) = ev D a f + ev D a g := by
  simp only [ev_eq_sum, map_add, add_smul, Finset.sum_add_distrib]

theorem ev_zero (D : ℕ) (a : K) : ev D a (0 : ℚ⟦X⟧) = 0 := by simp [ev_eq_sum]

theorem ev_one (D : ℕ) (a : K) : ev D a (1 : ℚ⟦X⟧) = 1 := by
  rw [ev, trunc_one, map_one]

theorem aeval_trunc_coe {N : ℕ} {a : K} (ha : a ^ N = 0) (r : Polynomial ℚ) :
    Polynomial.aeval a (trunc N (r : ℚ⟦X⟧)) = Polynomial.aeval a r := by
  have hdvd : (Polynomial.X : Polynomial ℚ) ^ N ∣ r - trunc N (r : ℚ⟦X⟧) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, coeff_trunc, ite_eq_left hd, Polynomial.coeff_coe, sub_self]
  obtain ⟨q, hq⟩ := hdvd
  have := congrArg (Polynomial.aeval a) hq
  rw [map_sub, map_mul, map_pow, Polynomial.aeval_X, ha, zero_mul] at this
  exact (sub_eq_zero.1 this).symm

theorem ev_mul {D : ℕ} {a : K} (ha : a ^ (D + 1) = 0) (f g : ℚ⟦X⟧) :
    ev D a (f * g) = ev D a f * ev D a g := by
  unfold ev
  rw [← trunc_trunc_mul_trunc, ← Polynomial.coe_mul, aeval_trunc_coe ha, map_mul]

/-- evaluation at a nilpotent element as a ring homomorphism-/
noncomputable def evHom (D : ℕ) (a : K) (ha : a ^ (D + 1) = 0) : ℚ⟦X⟧ →+* K where
  toFun := ev D a
  map_one' := ev_one D a
  map_mul' := ev_mul ha
  map_zero' := ev_zero D a
  map_add' := ev_add D a

theorem ev_C (D : ℕ) (a : K) (c : ℚ) : ev D a (C c) = algebraMap ℚ K c := by
  rw [ev, trunc_C, Polynomial.aeval_C]

theorem psi_ev (psi : K →+* K) {a : K} (j D : ℕ) (hpsi : psi a = (j : ℚ) • a) (f : ℚ⟦X⟧) :
    psi (ev D a f) = ev D a (rescale (j : ℚ) f) := by
  rw [ev_eq_sum, ev_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_rat_smul, map_pow, hpsi, smul_pow, coeff_rescale, smul_smul, mul_comm]

end Eval

section Weighted

variable {K : Type*} [CommRing K] [Algebra ℚ K] {W : ℕ → Submodule ℚ K} [GradedAlgebra W]
  {psi : K →+* K} {j D : ℕ}

theorem pow_succ_eq_zero (H : WeightHyp W psi j D) {a : K} (ha : a ∈ Fil W 1) :
    a ^ (D + 1) = 0 :=
  Fil_bot H le_rfl (Fil_pow H ha (D + 1))

theorem pr_zero_ev (H : WeightHyp W psi j D) {a : K} (ha : a ∈ Fil W 1) (f : ℚ⟦X⟧) :
    pr W 0 (ev D a f) = constantCoeff f • (1 : K) := by
  rw [ev_eq_sum, map_sum, Finset.sum_eq_single 0]
  · rw [map_smul, pow_zero, pr_one_zero, coeff_zero_eq_constantCoeff_apply]
  · intro i _ hi
    rw [map_smul, Fil_one_iff.1 (Fil_mono (Nat.one_le_iff_ne_zero.2 hi) (Fil_pow H ha i)),
      smul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos D)) h

theorem isUnit_ev (H : WeightHyp W psi j D) {a : K} (ha : a ∈ Fil W 1) {f : ℚ⟦X⟧}
    (hf : constantCoeff f ≠ 0) : IsUnit (ev D a f) := by
  have h1 : pr W 0 ((constantCoeff f)⁻¹ • ev D a f) = 1 := by
    rw [map_smul, pr_zero_ev H ha, smul_smul, inv_mul_cancel₀ hf, one_smul]
  have h2 := isUnit_of_pr_zero H h1
  have h3 : ev D a f = algebraMap ℚ K (constantCoeff f) * ((constantCoeff f)⁻¹ • ev D a f) := by
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hf, one_smul]
  rw [h3]
  exact ((isUnit_iff_ne_zero.2 hf).map (algebraMap ℚ K)).mul h2

theorem pr_zero_mul (H : WeightHyp W psi j D) (x y : K) :
    pr W 0 (x * y) = pr W 0 x * pr W 0 y := by
  have hx' : x - pr W 0 x ∈ Fil W 1 := by
    rw [Fil_one_iff, map_sub, pr_of_mem_same (pr_mem 0 x), sub_self]
  have hy' : y - pr W 0 y ∈ Fil W 1 := by
    rw [Fil_one_iff, map_sub, pr_of_mem_same (pr_mem 0 y), sub_self]
  have e : x * y = pr W 0 x * pr W 0 y +
      (pr W 0 x * (y - pr W 0 y) + (x - pr W 0 x) * y) := by ring
  have h1 : pr W 0 x * (y - pr W 0 y) ∈ Fil W 1 := by
    simpa using Fil_mul H (Fil_zero_all (W := W) (pr W 0 x)) hy'
  have h2 : (x - pr W 0 x) * y ∈ Fil W 1 := by
    simpa using Fil_mul H hx' (Fil_zero_all (W := W) y)
  have h3 : pr W 0 x * pr W 0 y ∈ W 0 := by
    simpa using SetLike.mul_mem_graded (pr_mem (W := W) 0 x) (pr_mem (W := W) 0 y)
  rw [e, map_add, pr_of_mem_same h3, Fil_one_iff.1 (add_mem h1 h2), add_zero]

/-- the weight-zero projection as a monoid homomorphism-/
noncomputable def pr0Hom (H : WeightHyp W psi j D) : K →* K where
  toFun := pr W 0
  map_one' := pr_one_zero
  map_mul' := pr_zero_mul H

/-- the Todd element of a root `a`-/
noncomputable def Td (D : ℕ) (a : K) : K := ev D a Tdser

/-- `θ_j(a) = ∑_{m<j} e^{-m a}`-/
noncomputable def th (j D : ℕ) (a : K) : K := ev D a (Theta j)

theorem pr_zero_Td (H : WeightHyp W psi j D) {a : K} (ha : a ∈ Fil W 1) :
    pr W 0 (Td D a) = 1 := by
  rw [Td, pr_zero_ev H ha, constantCoeff_Tdser, one_smul]

theorem isUnit_Td (H : WeightHyp W psi j D) {a : K} (ha : a ∈ Fil W 1) : IsUnit (Td D a) :=
  isUnit_of_pr_zero H (pr_zero_Td H ha)

theorem isUnit_th (H : WeightHyp W psi j D) {a : K} (ha : a ∈ Fil W 1) : IsUnit (th j D a) :=
  isUnit_ev H ha (by rw [constantCoeff_Theta]; exact_mod_cast (by have := H.hj; omega))

/-- **Key identity** for a weight-one root `a` (`ψ a = j a`): `θ_j(a) · ψ Td(a) = j · Td(a)`,
i.e. `ψ Td(a) / Td(a) = j / θ_j(a)`.-/
theorem th_mul_psi_Td (H : WeightHyp W psi j D) {a : K} (ha : a ∈ W 1) :
    th j D a * psi (Td D a) = algebraMap ℚ K (j : ℚ) * Td D a := by
  have ha1 : a ∈ Fil W 1 := Fil_of_mem ha le_rfl
  have hn := pow_succ_eq_zero H ha1
  have hpsi : psi a = (j : ℚ) • a := by rw [H.psi_eq ha, pow_one]
  have h := congrArg (evHom D a hn) (Theta_mul_rescale_Tdser j)
  change ev D a (Theta j * rescale (j : ℚ) Tdser) = ev D a (C (j : ℚ) * Tdser) at h
  rw [ev_mul hn, ev_mul hn, ev_C, ← psi_ev psi j D hpsi] at h
  exact h

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem isUnit_prod' {R : Type*} [CommRing R] {α : Type*} [Fintype α] (f : α → R)
    (h : ∀ i, IsUnit (f i)) : IsUnit (∏ i, f i) :=
  Finset.prod_induction f IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => h i)

theorem prod_th_psi_Td (H : WeightHyp W psi j D) (a : ι → K) (ha : ∀ i, a i ∈ W 1) :
    (∏ i, th j D (a i)) * psi (∏ i, Td D (a i)) =
      algebraMap ℚ K (j : ℚ) ^ Fintype.card ι * ∏ i, Td D (a i) := by
  rw [map_prod, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl (fun i _ => th_mul_psi_Td H (ha i)), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

theorem pr_zero_prod_Td (H : WeightHyp W psi j D) (a : ι → K) (ha : ∀ i, a i ∈ W 1) :
    pr W 0 (∏ i, Td D (a i)) = 1 := by
  have : pr W 0 (∏ i, Td D (a i)) = ∏ i, pr W 0 (Td D (a i)) :=
    map_prod (pr0Hom H) (fun i => Td D (a i)) Finset.univ
  rw [this]
  exact Finset.prod_eq_one fun i _ => pr_zero_Td H (Fil_of_mem (ha i) le_rfl)

/-- **`τ = td_K`**: the element `τ` of the recursion `ψ τ = s τ`, `τ₀ = 1` is the Todd class
`∏ Td(a_i) / ∏ Td(b_k)` when `s = j^d θ(Ω_f)^{-1}` and `θ(Ω_f) = ∏ θ(a_i) / ∏ θ(b_k)`
(`t * ∏ θ(a_i) = ∏ θ(b_k)`, `|ι| = d + |κ|`).-/
theorem tau_mul_prod_Td (H : WeightHyp W psi j D) (a : ι → K) (b : κ → K)
    (ha : ∀ i, a i ∈ W 1) (hb : ∀ k, b k ∈ W 1) {t s : K} {d : ℕ}
    (hd : Fintype.card ι = d + Fintype.card κ)
    (ht : t * ∏ i, th j D (a i) = ∏ k, th j D (b k))
    (hs : s = (j : ℚ) ^ d • t) (hs0 : pr W 0 s = 1)
    {τ : K} (h0 : pr W 0 τ = 1) (hτ : psi τ = s * τ) :
    τ * ∏ k, Td D (b k) = ∏ i, Td D (a i) := by
  have hV := prod_th_psi_Td H a ha
  have hU := prod_th_psi_Td H b hb
  rw [hd, pow_add] at hV
  have hUu : IsUnit (∏ k, Td D (b k)) :=
    isUnit_prod' _ fun k => isUnit_Td H (Fil_of_mem (hb k) le_rfl)
  have hTp : IsUnit (∏ i, th j D (a i)) :=
    isUnit_prod' _ fun i => isUnit_th H (Fil_of_mem (ha i) le_rfl)
  have hTm : IsUnit (∏ k, th j D (b k)) :=
    isUnit_prod' _ fun k => isUnit_th H (Fil_of_mem (hb k) le_rfl)
  obtain ⟨u, hu⟩ := hUu
  have hUi : (∏ k, Td D (b k)) * ↑u⁻¹ = 1 := by rw [← hu]; exact u.mul_inv
  have hpsiUUi : psi (∏ k, Td D (b k)) * psi ↑u⁻¹ = 1 := by rw [← map_mul, hUi, map_one]
  have hs' : s = algebraMap ℚ K (j : ℚ) ^ d * t := by
    rw [hs, Algebra.smul_def, map_pow]
  have hpr_Ui : pr W 0 (↑u⁻¹ : K) = 1 := by
    have h1 := pr_zero_mul H (∏ k, Td D (b k)) ↑u⁻¹
    rw [hUi, pr_one_zero, pr_zero_prod_Td H b hb, one_mul] at h1
    exact h1.symm
  have hτ' : psi ((∏ i, Td D (a i)) * ↑u⁻¹) = s * ((∏ i, Td D (a i)) * ↑u⁻¹) := by
    have hQ : IsUnit ((∏ i, th j D (a i)) * (∏ k, th j D (b k)) *
        psi (∏ k, Td D (b k))) :=
      (hTp.mul hTm).mul ((hu ▸ u.isUnit).map psi)
    refine hQ.mul_left_cancel ?_
    rw [map_mul, hs']
    linear_combination
      ((∏ k, th j D (b k)) * psi (∏ k, Td D (b k)) * psi ↑u⁻¹) * hV +
      ((∏ k, th j D (b k)) * (algebraMap ℚ K (j : ℚ) ^ d * algebraMap ℚ K (j : ℚ) ^
        Fintype.card κ) * (∏ i, Td D (a i))) * hpsiUUi -
      ((∏ k, th j D (b k)) * psi (∏ k, Td D (b k)) * algebraMap ℚ K (j : ℚ) ^ d *
        (∏ i, Td D (a i)) * ↑u⁻¹) * ht -
      ((∏ k, th j D (b k)) * algebraMap ℚ K (j : ℚ) ^ d * (∏ i, Td D (a i)) * ↑u⁻¹) * hU -
      ((∏ k, th j D (b k)) * (algebraMap ℚ K (j : ℚ) ^ d * algebraMap ℚ K (j : ℚ) ^
        Fintype.card κ) * (∏ i, Td D (a i))) * hUi
  have hpr' : pr W 0 ((∏ i, Td D (a i)) * ↑u⁻¹) = 1 := by
    rw [pr_zero_mul H, pr_zero_prod_Td H a ha, hpr_Ui, one_mul]
  have := tau_unique H hs0 h0 hτ hpr' hτ'
  rw [this, mul_assoc, mul_comm (↑u⁻¹ : K), hUi, mul_one]

/-- **Fulton–Lang `gr_γ` form (packaged)**.  From (E1) `χ x = χ (t * ψ x)` with
`s = j^d • t` of weight-0 part `1`, `t * ∏ θ(a_i) = ∏ θ(b_k)` (i.e. `t = θ^j(Ω_f)^{-1}` with
`Ω_f` of tangent roots `a_i` minus `b_k`) and `|ι| = d + |κ|` we get `τ = td_K` with
`τ * ∏ Td(b_k) = ∏ Td(a_i)`, `ψ τ = s τ`, `ν = χ(· τ⁻¹)` of `ν ∘ ψ = j^d ν`, vanishing off
weight `d`, and `χ x = ν ((x τ)_{(d)})`.-/
theorem E1_to_E2_todd (H : WeightHyp W psi j D) (chi : K →ₗ[ℚ] ℚ) (a : ι → K) (b : κ → K)
    (ha : ∀ i, a i ∈ W 1) (hb : ∀ k, b k ∈ W 1) {t s : K} {d : ℕ}
    (hd : Fintype.card ι = d + Fintype.card κ)
    (ht : t * ∏ i, th j D (a i) = ∏ k, th j D (b k))
    (hs : s = (j : ℚ) ^ d • t) (hs0 : pr W 0 s = 1)
    (hE1 : ∀ x, chi x = chi (t * psi x)) :
    ∃ τ τi : K, τ * ∏ k, Td D (b k) = ∏ i, Td D (a i) ∧ pr W 0 τ = 1 ∧ psi τ = s * τ ∧
      τ * τi = 1 ∧ (∀ {p : ℕ} {w : K}, w ∈ W p → p ≠ d → chi (w * τi) = 0) ∧
      (∀ w, chi (psi w * τi) = (j : ℚ) ^ d * chi (w * τi)) ∧
      (∀ x, chi x = chi (pr W d (x * τ) * τi)) := by
  obtain ⟨τ, τi, h0, hτ, hi, h1, h2, h3⟩ := E1_to_E2 H chi hs hs0 hE1
  exact ⟨τ, τi, tau_mul_prod_Td H a b ha hb hd ht hs hs0 h0 hτ, h0, hτ, hi, h1, h2, h3⟩

end Weighted

end RG6B
