/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.GradedAlgebra.Basic
import Tengoku.Seed.RingTheory.Nilpotent.Exp
import Tengoku.Seed.Algebra.Ring.GeomSum
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RG6B: the weight-algebra step E1 -> E2 (Fulton–Lang `gr_γ` form of GRR)

Pure algebra.  `K` plays `K₀(X) ⊗ ℚ`, `psi` plays `ψ^j`, and `W p` the weight-`p` (γ-graded)
piece on which `ψ^j = j^p`.  The weight decomposition is an abstract hypothesis `WeightHyp`.
Given the identity (E1) `χ x = χ (t * ψ x)` with `j^d • t = s`, `s` of weight-0 part `1`, we
show: there is a unique `τ` (Todd class) with `τ₀ = 1`, `ψ τ = s τ`; `ν w := χ (w * τ⁻¹)`
satisfies `ν ∘ ψ = j^d ν`, hence is concentrated in weight `d`; and `χ x = ν (x τ)_{(d)}`.
-/

namespace RG6B

open DirectSum

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- Hypotheses for the weight decomposition: `ψ = j^p` on `W p`, and weights are `≤ D`.-/
structure WeightHyp (W : ℕ → Submodule ℚ K) [GradedAlgebra W] (psi : K →+* K) (j D : ℕ) :
    Prop where
  /-- the Adams index is at least `2`-/
  hj : 2 ≤ j
  /-- `ψ^j = j^p` on weight `p`-/
  psi_eq : ∀ {p : ℕ} {x : K}, x ∈ W p → psi x = (j : ℚ) ^ p • x
  /-- weights beyond `D` vanish (γ-nilpotence)-/
  bound : ∀ {p : ℕ}, D < p → W p = ⊥

section Basic

variable {W : ℕ → Submodule ℚ K} [GradedAlgebra W] {psi : K →+* K} {j D : ℕ}

/-- the weight-`p` projection-/
noncomputable abbrev pr (W : ℕ → Submodule ℚ K) [GradedAlgebra W] (p : ℕ) : K →ₗ[ℚ] K :=
  GradedAlgebra.proj W p

theorem pr_mem (p : ℕ) (x : K) : pr W p x ∈ W p := by
  rw [pr, GradedAlgebra.proj_apply]
  exact (DirectSum.decompose W x p).2

theorem pr_of_mem_same {p : ℕ} {x : K} (hx : x ∈ W p) : pr W p x = x := by
  rw [pr, GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same W hx]

theorem pr_of_mem_ne {p q : ℕ} {x : K} (hx : x ∈ W q) (h : p ≠ q) : pr W p x = 0 := by
  rw [pr, GradedAlgebra.proj_apply]
  exact DirectSum.decompose_of_mem_ne W hx (Ne.symm h)

theorem pr_one_zero : pr W 0 (1 : K) = 1 :=
  pr_of_mem_same (SetLike.one_mem_graded W)

theorem pr_one_ne {p : ℕ} (hp : p ≠ 0) : pr W p (1 : K) = 0 :=
  pr_of_mem_ne (SetLike.one_mem_graded W) hp

theorem pr_eq_zero_of_bound (H : WeightHyp W psi j D) {p : ℕ} (hp : D < p) (x : K) :
    pr W p x = 0 := by
  have := pr_mem (W := W) p x
  rw [H.bound hp] at this
  simpa using this

theorem sum_pr (H : WeightHyp W psi j D) (x : K) :
    x = ∑ p ∈ Finset.range (D + 1), pr W p x := by
  classical
  calc x = ∑ i ∈ (DirectSum.decompose W x).support, (DirectSum.decompose W x i : K) :=
        (DirectSum.sum_support_decompose W x).symm
    _ = ∑ p ∈ Finset.range (D + 1), (DirectSum.decompose W x p : K) := by
        apply Finset.sum_subset
        · intro p hp
          rw [Finset.mem_range, Nat.lt_succ_iff]
          by_contra hlt
          have hlt : D < p := by omega
          have h0 : pr W p x = 0 := pr_eq_zero_of_bound H hlt x
          rw [pr, GradedAlgebra.proj_apply] at h0
          have : DirectSum.decompose W x p = 0 := Subtype.ext h0
          exact (DFinsupp.mem_support_iff).1 hp this
        · intro p _ hp
          by_contra hne
          exact hp ((DFinsupp.mem_support_iff).2 fun h => hne (by simp [h]))
    _ = _ := by simp [pr, GradedAlgebra.proj_apply]

theorem eq_of_pr_eq (H : WeightHyp W psi j D) {x y : K} (h : ∀ p, pr W p x = pr W p y) :
    x = y := by
  rw [sum_pr H x, sum_pr H y]
  exact Finset.sum_congr rfl fun p _ => h p

theorem pr_psi (H : WeightHyp W psi j D) (p : ℕ) (x : K) :
    pr W p (psi x) = (j : ℚ) ^ p • pr W p x := by
  conv_lhs => rw [sum_pr H x]
  rw [map_sum, map_sum]
  rw [Finset.sum_eq_single p]
  · rw [H.psi_eq (pr_mem p x), map_smul, pr_of_mem_same (pr_mem p x)]
  · intro q _ hqp
    rw [H.psi_eq (pr_mem q x), map_smul, pr_of_mem_ne (pr_mem q x) (Ne.symm hqp), smul_zero]
  · intro hp
    have hp' : D < p := by simpa [Finset.mem_range] using hp
    rw [pr_eq_zero_of_bound H hp' x]
    simp

/-- the weight filtration `F^m`: elements with no component in weight `< m`-/
def Fil (W : ℕ → Submodule ℚ K) [GradedAlgebra W] (m : ℕ) : Submodule ℚ K where
  carrier := {x | ∀ p < m, pr W p x = 0}
  add_mem' := by
    intro x y hx hy p hp
    have h1 : pr W p x = 0 := hx p hp
    have h2 : pr W p y = 0 := hy p hp
    rw [map_add, h1, h2, add_zero]
  zero_mem' := by intro p _; simp
  smul_mem' := by
    intro c x hx p hp
    have h1 : pr W p x = 0 := hx p hp
    rw [map_smul, h1, smul_zero]

theorem mem_Fil {m : ℕ} {x : K} : x ∈ Fil W m ↔ ∀ p < m, pr W p x = 0 := Iff.rfl

theorem Fil_zero_all (x : K) : x ∈ Fil W 0 := fun p hp => absurd hp (by omega)

theorem Fil_mono {m n : ℕ} (h : m ≤ n) {x : K} (hx : x ∈ Fil W n) : x ∈ Fil W m :=
  fun p hp => hx p (lt_of_lt_of_le hp h)

theorem Fil_one_iff {x : K} : x ∈ Fil W 1 ↔ pr W 0 x = 0 := by
  constructor
  · intro h; exact h 0 (by omega)
  · intro h p hp
    have : p = 0 := by omega
    subst this; exact h

theorem Fil_of_mem {m p : ℕ} {x : K} (hx : x ∈ W p) (h : m ≤ p) : x ∈ Fil W m := by
  intro q hq
  exact pr_of_mem_ne hx (by omega)

theorem Fil_bot (H : WeightHyp W psi j D) {m : ℕ} (hm : D + 1 ≤ m) {x : K} (hx : x ∈ Fil W m) :
    x = 0 := by
  rw [sum_pr H x]
  exact Finset.sum_eq_zero fun p hp => hx p (by simp at hp; omega)

theorem Fil_mul (H : WeightHyp W psi j D) {m n : ℕ} {x y : K} (hx : x ∈ Fil W m)
    (hy : y ∈ Fil W n) : x * y ∈ Fil W (m + n) := by
  intro p hp
  rw [sum_pr H x, sum_pr H y, Finset.sum_mul_sum, map_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases ha : a < m
  · rw [hx a ha, zero_mul, map_zero]
  by_cases hb : b < n
  · rw [hy b hb, mul_zero, map_zero]
  exact pr_of_mem_ne (SetLike.mul_mem_graded (pr_mem a x) (pr_mem b y)) (by omega)

theorem Fil_pow (H : WeightHyp W psi j D) {x : K} (hx : x ∈ Fil W 1) (k : ℕ) :
    x ^ k ∈ Fil W k := by
  induction k with
  | zero => exact Fil_zero_all _
  | succ k ih => rw [pow_succ]; exact Fil_mul H ih hx

theorem isUnit_of_pr_zero (H : WeightHyp W psi j D) {a : K} (h : pr W 0 a = 1) : IsUnit a := by
  have hn : a - 1 ∈ Fil W 1 := by
    rw [Fil_one_iff, map_sub, h, pr_one_zero, sub_self]
  have hnil : IsNilpotent (a - 1) := ⟨D + 1, Fil_bot H le_rfl (Fil_pow H hn (D + 1))⟩
  simpa using hnil.isUnit_add_one

/-- the inverse of `ψ - 1` on positive weights, killing weight `0`-/
noncomputable def Rop (W : ℕ → Submodule ℚ K) [GradedAlgebra W] (j D : ℕ) : K →ₗ[ℚ] K :=
  ∑ p ∈ Finset.range (D + 1), (((j : ℚ) ^ p - 1)⁻¹) • pr W p

theorem pr_Rop (H : WeightHyp W psi j D) (p : ℕ) (x : K) :
    pr W p (Rop W j D x) = (((j : ℚ) ^ p - 1)⁻¹) • pr W p x := by
  unfold Rop
  rw [LinearMap.sum_apply, map_sum]
  rw [Finset.sum_eq_single p]
  · simp only [LinearMap.smul_apply, map_smul]
    rw [pr_of_mem_same (pr_mem p x)]
  · intro q _ hqp
    simp only [LinearMap.smul_apply, map_smul]
    rw [pr_of_mem_ne (pr_mem q x) (Ne.symm hqp), smul_zero]
  · intro hp
    have hp' : D < p := by simpa [Finset.mem_range] using hp
    simp [pr_eq_zero_of_bound H hp' x]

theorem Rop_mem_Fil (H : WeightHyp W psi j D) {m : ℕ} {x : K} (hx : x ∈ Fil W m) :
    Rop W j D x ∈ Fil W m := by
  intro p hp
  rw [pr_Rop H, hx p hp, smul_zero]

theorem Rop_mem_Fil_one (H : WeightHyp W psi j D) (x : K) : Rop W j D x ∈ Fil W 1 := by
  rw [Fil_one_iff, pr_Rop H]
  simp

theorem one_lt_pow_cast (H : WeightHyp W psi j D) {p : ℕ} (hp : p ≠ 0) : (1 : ℚ) < (j : ℚ) ^ p := by
  have : (1 : ℚ) < j := by exact_mod_cast H.hj
  exact one_lt_pow₀ this hp

theorem psi_Rop_sub (H : WeightHyp W psi j D) (x : K) :
    psi (Rop W j D x) - Rop W j D x = x - pr W 0 x := by
  apply eq_of_pr_eq H
  intro p
  rw [map_sub, pr_psi H, pr_Rop H, map_sub]
  by_cases hp : p = 0
  · subst hp
    simp
  · have hne : (j : ℚ) ^ p - 1 ≠ 0 := by
      have := one_lt_pow_cast H hp
      linarith
    rw [pr_of_mem_ne (pr_mem 0 x) hp, sub_zero, smul_smul, ← sub_smul,
      show ((j : ℚ) ^ p * ((j : ℚ) ^ p - 1)⁻¹ - ((j : ℚ) ^ p - 1)⁻¹) = 1 by field_simp, one_smul]

theorem Rop_psi_sub (H : WeightHyp W psi j D) {v : K} (hv : v ∈ Fil W 1) :
    Rop W j D (psi v - v) = v := by
  apply eq_of_pr_eq H
  intro p
  rw [pr_Rop H, map_sub, pr_psi H]
  by_cases hp : p = 0
  · subst hp
    have : pr W 0 v = 0 := Fil_one_iff.1 hv
    simp [this]
  · have hne : (j : ℚ) ^ p - 1 ≠ 0 := by
      have := one_lt_pow_cast H hp
      linarith
    rw [show ((j : ℚ) ^ p • pr W p v - pr W p v) = ((j : ℚ) ^ p - 1) • pr W p v by
      rw [sub_smul, one_smul], smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- the recursion operator `y ↦ R ((s - 1) y)` raising the weight filtration-/
noncomputable def Aop (W : ℕ → Submodule ℚ K) [GradedAlgebra W] (j D : ℕ) (s : K) :
    Module.End ℚ K :=
  Rop W j D ∘ₗ LinearMap.mulLeft ℚ (s - 1)

theorem Aop_apply (s y : K) : Aop W j D s y = Rop W j D ((s - 1) * y) := rfl

theorem Aop_mem (H : WeightHyp W psi j D) {s : K} (hs : s - 1 ∈ Fil W 1) {m : ℕ} {y : K}
    (hy : y ∈ Fil W m) : Aop W j D s y ∈ Fil W (m + 1) := by
  rw [Aop_apply]
  have := Fil_mul H hs hy
  rw [add_comm] at this
  exact Rop_mem_Fil H this

theorem Aop_pow_mem (H : WeightHyp W psi j D) {s : K} (hs : s - 1 ∈ Fil W 1) {m : ℕ} {y : K}
    (hy : y ∈ Fil W m) (k : ℕ) : ((Aop W j D s) ^ k) y ∈ Fil W (m + k) := by
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact Aop_mem H hs ih

theorem sub_one_mem_Fil {s : K} (hs : pr W 0 s = 1) : s - 1 ∈ Fil W 1 := by
  rw [Fil_one_iff, map_sub, hs, pr_one_zero, sub_self]

/-- existence of the Todd-type element `τ` with `τ₀ = 1`, `ψ τ = s τ`-/
theorem exists_tau (H : WeightHyp W psi j D) {s : K} (hs : pr W 0 s = 1) :
    ∃ τ : K, pr W 0 τ = 1 ∧ psi τ = s * τ := by
  have hs1 := sub_one_mem_Fil (W := W) hs
  have hw0 : Rop W j D (s - 1) ∈ Fil W 1 := Rop_mem_Fil_one H _
  have hAw : ((Aop W j D s) ^ (D + 1)) (Rop W j D (s - 1)) = 0 :=
    Fil_bot H (m := 1 + (D + 1)) (by omega) (Aop_pow_mem H hs1 hw0 (D + 1))
  obtain ⟨u, hu1, hfix⟩ : ∃ u : K, u ∈ Fil W 1 ∧
      u - Aop W j D s u = Rop W j D (s - 1) := by
    refine ⟨(∑ k ∈ Finset.range (D + 1), (Aop W j D s) ^ k) (Rop W j D (s - 1)), ?_, ?_⟩
    · rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun k _ => Fil_mono (by omega) (Aop_pow_mem H hs1 hw0 k)
    · have h := congrArg (fun T : Module.End ℚ K => T (Rop W j D (s - 1)))
        (mul_neg_geom_sum (Aop W j D s) (D + 1))
      simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, hAw,
        sub_zero] at h
      exact h
  have hu_eq : u = Rop W j D ((s - 1) * (1 + u)) := by
    rw [mul_add, mul_one, map_add]
    change u = Rop W j D (s - 1) + Aop W j D s u
    rw [← hfix]; abel
  have hy : (s - 1) * (1 + u) ∈ Fil W 1 := by
    have := Fil_mul H hs1 (Fil_zero_all (W := W) (1 + u))
    simpa using this
  have key := psi_Rop_sub H ((s - 1) * (1 + u))
  rw [← hu_eq, Fil_one_iff.1 hy, sub_zero] at key
  refine ⟨1 + u, ?_, ?_⟩
  · rw [map_add, pr_one_zero, Fil_one_iff.1 hu1, add_zero]
  · rw [map_add, map_one]
    linear_combination key

theorem tau_unique (H : WeightHyp W psi j D) {s : K} (hs : pr W 0 s = 1) {τ τ' : K}
    (h1 : pr W 0 τ = 1) (h2 : psi τ = s * τ) (h1' : pr W 0 τ' = 1) (h2' : psi τ' = s * τ') :
    τ = τ' := by
  have hs1 := sub_one_mem_Fil (W := W) hs
  have hv : τ - τ' ∈ Fil W 1 := by rw [Fil_one_iff, map_sub, h1, h1', sub_self]
  have hA : Aop W j D s (τ - τ') = τ - τ' := by
    have hpsi : psi (τ - τ') - (τ - τ') = (s - 1) * (τ - τ') := by
      rw [map_sub, h2, h2']; ring
    rw [Aop_apply, ← hpsi]
    exact Rop_psi_sub H hv
  have hk : ∀ k : ℕ, ((Aop W j D s) ^ k) (τ - τ') = τ - τ' := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, hA]
  have := Fil_bot H (m := 1 + (D + 1)) (by omega) (Aop_pow_mem H hs1 hv (D + 1))
  rw [hk] at this
  exact sub_eq_zero.1 this

end Basic

section E2

variable {W : ℕ → Submodule ℚ K} [GradedAlgebra W] {psi : K →+* K} {j D : ℕ}

omit [Algebra ℚ K] in
theorem s_mul_psi_inv {s τ τi : K} (hτ : psi τ = s * τ) (hi : τ * τi = 1) :
    s * psi τi = τi := by
  have h1 : psi τ * psi τi = 1 := by rw [← map_mul, hi, map_one]
  calc s * psi τi = (τ * τi) * (s * psi τi) := by rw [hi, one_mul]
    _ = τi * (s * τ * psi τi) := by ring
    _ = τi := by rw [← hτ, h1, mul_one]

/-- `ν ∘ ψ = j^d ν` for `ν w = χ (w τ⁻¹)`: the rewriting of (E1).-/
theorem nu_psi (chi : K →ₗ[ℚ] ℚ) {t s τ τi : K} {d : ℕ} (hs : s = (j : ℚ) ^ d • t)
    (hE1 : ∀ x, chi x = chi (t * psi x)) (hτ : psi τ = s * τ) (hi : τ * τi = 1) (w : K) :
    chi (psi w * τi) = (j : ℚ) ^ d * chi (w * τi) := by
  have e := s_mul_psi_inv hτ hi
  have h := hE1 (w * τi)
  rw [RingHom.map_mul] at h
  have h2 : (j : ℚ) ^ d • (t * (psi w * psi τi)) = psi w * τi :=
    calc (j : ℚ) ^ d • (t * (psi w * psi τi)) = psi w * (((j : ℚ) ^ d • t) * psi τi) := by
          rw [smul_mul_assoc, mul_smul_comm]; congr 1; ring
      _ = psi w * (s * psi τi) := by rw [hs]
      _ = psi w * τi := by rw [e]
  rw [← h2, map_smul, smul_eq_mul, ← h]

/-- converse: `ν ∘ ψ = j^d ν` gives back (E1)-/
theorem E1_of_nu_psi (chi : K →ₗ[ℚ] ℚ) {t s τ τi : K} {d : ℕ} (hjd : (j : ℚ) ^ d ≠ 0)
    (hs : s = (j : ℚ) ^ d • t) (hτ : psi τ = s * τ) (hi : τ * τi = 1)
    (hν : ∀ w, chi (psi w * τi) = (j : ℚ) ^ d * chi (w * τi)) (x : K) :
    chi x = chi (t * psi x) := by
  have hx : x = (x * τ) * τi := by rw [mul_assoc, hi, mul_one]
  have e := s_mul_psi_inv hτ hi
  have h2 : (j : ℚ) ^ d • (t * psi x) = psi (x * τ) * τi := by
    have hpx : psi x = psi (x * τ) * psi τi := by
      rw [← RingHom.map_mul, mul_assoc, hi, mul_one]
    calc (j : ℚ) ^ d • (t * psi x) = psi (x * τ) * (((j : ℚ) ^ d • t) * psi τi) := by
          rw [hpx, smul_mul_assoc, mul_smul_comm]; congr 1; ring
      _ = psi (x * τ) * (s * psi τi) := by rw [hs]
      _ = psi (x * τ) * τi := by rw [e]
  have h3 : (j : ℚ) ^ d * chi (t * psi x) = (j : ℚ) ^ d * chi x := by
    rw [← smul_eq_mul, ← map_smul, h2, hν, ← hx]
  exact (mul_left_cancel₀ hjd h3).symm

/-- `ν` is concentrated in weight `d`.-/
theorem nu_eq_zero_of_mem (H : WeightHyp W psi j D) (chi : K →ₗ[ℚ] ℚ) {t s τ τi : K} {d : ℕ}
    (hs : s = (j : ℚ) ^ d • t) (hE1 : ∀ x, chi x = chi (t * psi x)) (hτ : psi τ = s * τ)
    (hi : τ * τi = 1) {p : ℕ} {w : K} (hw : w ∈ W p) (hp : p ≠ d) : chi (w * τi) = 0 := by
  have h := nu_psi chi hs hE1 hτ hi w
  rw [H.psi_eq hw, smul_mul_assoc, map_smul, smul_eq_mul] at h
  have hne : (j : ℚ) ^ p ≠ (j : ℚ) ^ d := fun h' =>
    hp (Nat.pow_right_injective H.hj (by exact_mod_cast h'))
  have h4 : ((j : ℚ) ^ p - (j : ℚ) ^ d) * chi (w * τi) = 0 := by rw [sub_mul]; linarith
  rcases mul_eq_zero.1 h4 with h5 | h5
  · exact absurd (sub_eq_zero.1 h5) hne
  · exact h5

/-- (E2): `χ x = ν ((x τ)_{(d)})`.-/
theorem chi_eq_proj (H : WeightHyp W psi j D) (chi : K →ₗ[ℚ] ℚ) {t s τ τi : K} {d : ℕ}
    (hs : s = (j : ℚ) ^ d • t) (hE1 : ∀ x, chi x = chi (t * psi x)) (hτ : psi τ = s * τ)
    (hi : τ * τi = 1) (x : K) : chi x = chi (pr W d (x * τ) * τi) := by
  have h1 : x = (x * τ) * τi := by rw [mul_assoc, hi, mul_one]
  calc chi x = chi ((x * τ) * τi) := by rw [← h1]
    _ = ∑ p ∈ Finset.range (D + 1), chi (pr W p (x * τ) * τi) := by
        conv_lhs => rw [sum_pr H (x * τ)]
        rw [Finset.sum_mul, map_sum]
    _ = chi (pr W d (x * τ) * τi) := by
        refine Finset.sum_eq_single d (fun p _ hp => ?_) (fun hd => ?_)
        · exact nu_eq_zero_of_mem H chi hs hE1 hτ hi (pr_mem p _) hp
        · have hd' : D < d := by simpa [Finset.mem_range] using hd
          rw [pr_eq_zero_of_bound H hd', zero_mul, map_zero]

/-- if the weight `d_f` exceeds the bound, `χ` vanishes.-/
theorem chi_eq_zero_of_lt (H : WeightHyp W psi j D) (chi : K →ₗ[ℚ] ℚ) {t s τ τi : K} {d : ℕ}
    (hs : s = (j : ℚ) ^ d • t) (hE1 : ∀ x, chi x = chi (t * psi x)) (hτ : psi τ = s * τ)
    (hi : τ * τi = 1) (hd : D < d) (x : K) : chi x = 0 := by
  rw [chi_eq_proj H chi hs hE1 hτ hi x, pr_eq_zero_of_bound H hd, zero_mul, map_zero]

/-- **E1 ⇒ E2 (packaged)**: for `s = j^d • t` of weight-0 part `1` and (E1), there are `τ`, `τ⁻¹`
with `τ₀ = 1`, `ψ τ = s τ`, `ν = χ(· τ⁻¹)` vanishing off weight `d` and `χ x = ν ((x τ)_{(d)})`.-/
theorem E1_to_E2 (H : WeightHyp W psi j D) (chi : K →ₗ[ℚ] ℚ) {t s : K} {d : ℕ}
    (hs : s = (j : ℚ) ^ d • t) (hs0 : pr W 0 s = 1) (hE1 : ∀ x, chi x = chi (t * psi x)) :
    ∃ τ τi : K, pr W 0 τ = 1 ∧ psi τ = s * τ ∧ τ * τi = 1 ∧
      (∀ {p : ℕ} {w : K}, w ∈ W p → p ≠ d → chi (w * τi) = 0) ∧
      (∀ w, chi (psi w * τi) = (j : ℚ) ^ d * chi (w * τi)) ∧
      (∀ x, chi x = chi (pr W d (x * τ) * τi)) := by
  obtain ⟨τ, h0, hτ⟩ := exists_tau H hs0
  obtain ⟨u, hu⟩ := isUnit_of_pr_zero H h0
  refine ⟨τ, ↑u⁻¹, h0, hτ, ?_, ?_, nu_psi chi hs hE1 hτ ?_, chi_eq_proj H chi hs hE1 hτ ?_⟩
  · rw [← hu]; exact u.mul_inv
  · intro p w hw hp
    exact nu_eq_zero_of_mem H chi hs hE1 hτ (by rw [← hu]; exact u.mul_inv) hw hp
  · rw [← hu]; exact u.mul_inv
  · rw [← hu]; exact u.mul_inv

end E2

end RG6B
