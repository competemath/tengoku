/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.Polynomial.Vieta
import Tengoku.Seed.Algebra.Polynomial.Eval.Defs
import Tengoku.Seed.Algebra.Algebra.Rat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Route CII-L1 (CASEII leaf 1): the algebra of the zero-section computation `ZSCore`

Pure algebra, Mathlib only.  Plan and honest blockers: `notes/agents/CIIL1-status.md`.

Geometric setting (paper).  `N` has rank `r` on `X`, `E = ℙ(N ⊕ 1) →π X`, `ξ = c₁ O(1)`,
`V = π^*N ⊗ O(1)`, `s : X ↪ E` the zero locus of the tautological section of `V` (normal bundle `N`,
**not** `N^∨`).  The leaf is `π_*(ch(λ_{-1} V^∨) ∩ [E]) = td(N)⁻¹ ∩ [X]`.

Three facts reduce it to the polynomial identity proved here.

1. `ch(λ_{-1} V^∨) = ∏ᵢ (1 - e^{-(nᵢ + ξ)})` (splitting principle, `ch_line`).
2. `π_*(ξ^k ∩ π^*α) = s_{k-r}(N ⊕ 1) ∩ α` for `k ≥ r`, and `= 0` for `k < r`
   (`segreOn`, `segreOn_zero`, `sandwichOn_eq_zero_of_lt` in K5), with `c(N) · s(N) = 1`
   (`chernOfCoverOn` is defined by this).
3. Projection formula for `π` applied to the coefficients (symmetric functions of the `nᵢ`).

So `ZSCore` is `φ(∏ᵢ (1 - e^{-(nᵢ+ξ)})) = ∏ᵢ (1 - e^{-nᵢ})/nᵢ`, where `φ : R[ξ] → R`,
`φ(ξ^k) = s_{k-r}` (`0` for `k < r`).  **No relation in `A_*(E)` is used** (no `ξ · ∏(ξ + nᵢ) = 0`,
no Whitney for `E`): `ξ^k` is only ever pushed forward.

Proof: `1 - e^{-z} = z · u(z)` (exact for the truncated exponential), hence `g(ξ) = P(ξ) · U(ξ)` with
`P = ∏(ξ + nᵢ) = Σ eⱼ ξ^{r-j}` and `U = ∏ u(ξ + nᵢ)`.  Now `φ(P · ξⁱ) = Σⱼ eⱼ s_{i-j} = [i = 0]`
(this is `c · s = 1`), so `φ(P · U) = U(0) = ∏ u(nᵢ)`.
-/

set_option autoImplicit false

open Polynomial

namespace ChowZeroSectionCIIL1

noncomputable section

section Core

variable {R : Type*} [CommRing R]

/-- The pushforward functional `φ(ξ^k) = s_{k-r}` (`0` for `k < r`), `R`-linear on `R[ξ]`.-/
def phi (r : ℕ) (s : ℕ → R) : R[X] →ₗ[R] R :=
  Polynomial.lsum fun k => (if r ≤ k then s (k - r) else 0) • (LinearMap.id : R →ₗ[R] R)

/--
@isnad1 id=eq.0h5v.s8.ed25b0fd4ba6 from=translated src=- shape=ebadf35f vocab=b57fff5f
-/
theorem phi_monomial (r : ℕ) (s : ℕ → R) (k : ℕ) (a : R) :
    phi r s (monomial k a) = a * (if r ≤ k then s (k - r) else 0) := by
  simp only [phi, Polynomial.lsum_apply]
  rw [Polynomial.sum_monomial_index]
  · split_ifs <;> simp [mul_comm]
  · simp

/--
@isnad1 id=eq.0h5v.s8.d8d699ebeda4 from=translated src=- shape=4979631b vocab=06270542
-/
theorem phi_C_mul_X_pow (r : ℕ) (s : ℕ → R) (k : ℕ) (a : R) :
    phi r s (C a * X ^ k) = a * (if r ≤ k then s (k - r) else 0) := by
  rw [C_mul_X_pow_eq_monomial, phi_monomial]

/-- The polynomial `P(ξ) = Σⱼ eⱼ ξ^{r-j}` (`= c_r(π^*N ⊗ O(1))`).-/
def chernPoly (r : ℕ) (e : ℕ → R) : R[X] :=
  ∑ j ∈ Finset.range (r + 1), C (e j) * X ^ (r - j)

/-- `c · s = 1`, in the form used by `chernOfCoverOn` (`c = s⁻¹` as power series), with `c` of
rank `r` (`c_j = 0` for `j > r`).-/
def SegreInv (r : ℕ) (e s : ℕ → R) : Prop :=
  (∀ j, r < j → e j = 0) ∧
    ∀ m, ∑ a ∈ Finset.range (m + 1), e a * s (m - a) = if m = 0 then 1 else 0

/--
@isnad1 id=eq.1h5v.s8.cbb37ddd200b from=translated src=- shape=d917a3ea vocab=4c6e40ce
-/
theorem phi_chernPoly_mul_X_pow {r : ℕ} {e s : ℕ → R} (h : SegreInv r e s) (i : ℕ) :
    phi r s (chernPoly r e * X ^ i) = if i = 0 then 1 else 0 := by
  obtain ⟨hz, hs⟩ := h
  have step : phi r s (chernPoly r e * X ^ i) =
      ∑ j ∈ Finset.range (r + 1), (if j ≤ i then e j * s (i - j) else 0) := by
    simp only [chernPoly, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [mul_assoc, ← pow_add, phi_C_mul_X_pow]
    by_cases hji : j ≤ i
    · have h1 : r ≤ r - j + i := by omega
      have h2 : r - j + i - r = i - j := by omega
      simp [hji, h1, h2]
    · have h1 : ¬ r ≤ r - j + i := by omega
      simp [hji, h1]
  rw [step, ← hs i, ← Finset.sum_filter]
  refine Finset.sum_subset ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    omega
  · intro a ha hna
    simp only [Finset.mem_range] at ha
    have : ¬ a < r + 1 := by
      intro hlt
      exact hna (by simp only [Finset.mem_filter, Finset.mem_range]; omega)
    rw [hz a (by omega), zero_mul]

/-- **Key identity** `φ(P · U) = U(0)`: the whole content of `ZSCore` modulo `P · U = g`.
@isnad1 id=eq.1h5v.s8.522092c1fcec from=translated src=- shape=1f025ab6 vocab=7e632db8
-/
theorem phi_chernPoly_mul {r : ℕ} {e s : ℕ → R} (h : SegreInv r e s) (U : R[X]) :
    phi r s (chernPoly r e * U) = U.coeff 0 := by
  induction U using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, hp, hq, coeff_add]
  | monomial i a =>
    have : chernPoly r e * monomial i a = a • (chernPoly r e * X ^ i) := by
      rw [← C_mul_X_pow_eq_monomial, smul_eq_C_mul]; ring
    rw [this, map_smul, phi_chernPoly_mul_X_pow h, coeff_monomial, smul_eq_mul]
    by_cases hi : i = 0 <;> simp [hi]

end Core

section Roots

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Truncated exponential `Σ_{k ≤ D} z^k / k!`.-/
def expT {A : Type*} [CommRing A] [Algebra ℚ A] (D : ℕ) (z : A) : A :=
  ∑ k ∈ Finset.range (D + 1), algebraMap ℚ A (1 / (k.factorial : ℚ)) * z ^ k

/-- Truncated `u(z) = (1 - e^{-z}) / z = Σ_{k < D} (-1)^k z^k / (k+1)!`.-/
def uT {A : Type*} [CommRing A] [Algebra ℚ A] (D : ℕ) (z : A) : A :=
  ∑ k ∈ Finset.range D, algebraMap ℚ A (1 / ((k + 1).factorial : ℚ)) * ((-1) ^ k * z ^ k)

/--
@isnad1 id=eq.0h3v.s6.21932906b520 from=translated src=- shape=c1ac8ce6 vocab=ad88f7da
-/
theorem one_sub_expT_neg {A : Type*} [CommRing A] [Algebra ℚ A] (D : ℕ) (z : A) :
    1 - expT D (-z) = z * uT D z := by
  induction D with
  | zero => simp [expT, uT]
  | succ D ih =>
    simp only [expT, uT, Finset.sum_range_succ] at ih ⊢
    have h0 : (algebraMap ℚ A) (1 / ((0 : ℕ).factorial : ℚ)) = 1 := by simp
    rw [mul_add, ← ih]
    have : (-z) ^ (D + 1) = (-1) ^ (D + 1) * z ^ (D + 1) := by rw [neg_eq_neg_one_mul, mul_pow]
    rw [this]
    have h3 : (-1 : A) ^ (D + 1) = - (-1) ^ D := by rw [pow_succ]; ring
    rw [h3]
    ring

/--
@isnad1 id=eq.0h3v.s7.922d97659ff5 from=translated src=- shape=f2930c65 vocab=828705c3
-/
theorem eval_zero_uT (D : ℕ) (n : R) : (uT D (X + C n)).eval 0 = uT D n := by
  simp only [uT, eval_finsetSum, eval_mul, eval_pow, eval_add, eval_X, eval_C, zero_add,
    eval_neg, eval_one, Polynomial.algebraMap_apply]

/-- **ZSCore, splitting-principle form.**  For roots `n₁..n_r` (a multiset `m`), Segre classes
`s` with `c(m) · s = 1`, and every truncation order `D`:
`φ(∏ᵢ (1 - e^{-(ξ + nᵢ)})) = ∏ᵢ u(nᵢ)` (`= td(N)⁻¹`).
@isnad1 id=eq.1h4v.s8.e36956e8b0bf from=translated src=- shape=513b757c vocab=e677729f
-/
theorem zscore_roots (m : Multiset R) (s : ℕ → R)
    (hs : SegreInv (Multiset.card m) (fun j => m.esymm j) s) (D : ℕ) :
    phi (Multiset.card m) s
        ((m.map fun n => 1 - expT D (-(X + C n))).prod) =
      (m.map fun n => uT D n).prod := by
  have hP : (m.map fun n => X + C n).prod = chernPoly (Multiset.card m) (fun j => m.esymm j) := by
    rw [Multiset.prod_X_add_C_eq_sum_esymm]; rfl
  have hg : (m.map fun n => 1 - expT D (-(X + C n))).prod =
      chernPoly (Multiset.card m) (fun j => m.esymm j) *
        (m.map fun n => uT D (X + C n)).prod := by
    rw [← hP, ← Multiset.prod_map_mul]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun n _ => one_sub_expT_neg D _)
  rw [hg, phi_chernPoly_mul hs]
  have : ((m.map fun n => uT D (X + C n)).prod).coeff 0 =
      Polynomial.eval 0 ((m.map fun n => uT D (X + C n)).prod) := by
    rw [coeff_zero_eq_eval_zero]
  rw [this, Polynomial.eval_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun n _ => eval_zero_uT D n)

end Roots

end

end ChowZeroSectionCIIL1
