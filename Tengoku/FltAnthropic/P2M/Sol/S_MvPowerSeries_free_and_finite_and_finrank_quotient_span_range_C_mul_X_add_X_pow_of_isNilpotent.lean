import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_C_mul_X_add_X_pow_of_isNilpotent.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_C_mul_X_add_X_pow_of_isNilpotent.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_C_mul_X_add_X_pow_of_isNilpotent

set_option autoImplicit false

universe u

noncomputable section

open MvPowerSeries

namespace P2mKcWeierSep

section OneVariable

variable {σ : Type*} {R : Type*} [CommRing R]

abbrev sepPoly (i : σ) (N : ℕ) (c : R) : MvPowerSeries σ R := C c * X i + X i ^ N

def lowSub (i : σ) (N : ℕ) : Submodule R (MvPowerSeries σ R) where
  carrier := {φ | ∀ m : σ →₀ ℕ, N ≤ m i → coeff m φ = 0}
  zero_mem' := fun m _ => map_zero _
  add_mem' := by
    intro a b ha hb m hm
    rw [map_add, ha m hm, hb m hm, add_zero]
  smul_mem' := by
    intro a φ hφ m hm
    rw [map_smul, hφ m hm, smul_zero]

/--
@isnad1 id=mem.1h6v.s8.1848f5700db3 from=translated src=- shape=e4c626fe vocab=e20b15d3
-/
theorem C_mul_mem {i : σ} {N : ℕ} {φ : MvPowerSeries σ R} (a : R) (h : φ ∈ lowSub i N) :
    C a * φ ∈ lowSub i N := by
  rw [← smul_eq_C_mul]
  exact (lowSub i N).smul_mem a h

/--
@isnad1 id=mem.2h6v.s8.05c7151e3445 from=translated src=- shape=05b5f755 vocab=5e2aebf3
-/
theorem X_mul_mem_of_ne {i j : σ} (hij : i ≠ j) {N : ℕ} {φ : MvPowerSeries σ R}
    (h : φ ∈ lowSub j N) : X i * φ ∈ lowSub j N := by
  intro m hm
  rw [X_def, coeff_monomial_mul, one_mul]
  split_ifs with hle
  · apply h
    rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hij.symm, Nat.sub_zero]
    exact hm
  · rfl

def low (i : σ) (N : ℕ) (φ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun m => if m i < N then coeff m φ else 0

def high (i : σ) (N : ℕ) (φ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun m => coeff (m + Finsupp.single i N) φ

/--
@isnad1 id=eq.0h6v.s8.64e9a1bbb7ec from=translated src=- shape=a29fa7f4 vocab=d6f47c5e
-/
theorem coeff_low (i : σ) (N : ℕ) (φ : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff m (low i N φ) = if m i < N then coeff m φ else 0 := rfl

/--
@isnad1 id=eq.0h6v.s8.6da897aa47e1 from=translated src=- shape=11a8c5c7 vocab=88edbd3a
-/
theorem coeff_high (i : σ) (N : ℕ) (φ : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff m (high i N φ) = coeff (m + Finsupp.single i N) φ := rfl

/--
@isnad1 id=mem.0h5v.s7.6c307ba73c96 from=translated src=- shape=f6b1f059 vocab=118e66ba
-/
theorem low_mem (i : σ) (N : ℕ) (φ : MvPowerSeries σ R) : low i N φ ∈ lowSub i N := by
  intro m hm
  rw [coeff_low, ite_eq_right (not_lt.mpr hm)]

/--
@isnad1 id=mem.1h7v.s8.c905bd31cb09 from=translated src=- shape=21730ede vocab=118e66ba
-/
theorem low_mem_of_mem (i : σ) (N : ℕ) {j : σ} {N' : ℕ} {φ : MvPowerSeries σ R}
    (h : φ ∈ lowSub j N') : low i N φ ∈ lowSub j N' := by
  intro m hm
  rw [coeff_low]
  split_ifs
  · exact h m hm
  · rfl

/--
@isnad1 id=mem.2h7v.s8.6a0c3a28b140 from=translated src=- shape=ae0aca6a vocab=a75a8c10
-/
theorem high_mem_of_ne {i j : σ} (hij : i ≠ j) (N : ℕ) {N' : ℕ} {φ : MvPowerSeries σ R}
    (h : φ ∈ lowSub j N') : high i N φ ∈ lowSub j N' := by
  intro m hm
  rw [coeff_high]
  apply h
  show N' ≤ (m + Finsupp.single i N) j
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hij.symm, add_zero]
  exact hm

/--
@isnad1 id=eq.0h6v.s7.b3bc96d644e7 from=translated src=- shape=12cf458d vocab=a6d6eb80
-/
theorem high_C_mul (i : σ) (N : ℕ) (a : R) (φ : MvPowerSeries σ R) :
    high i N (C a * φ) = C a * high i N φ := by
  refine MvPowerSeries.ext fun m => ?_
  rw [coeff_high, coeff_C_mul, coeff_C_mul, coeff_high]

/--
@isnad1 id=eq.0h5v.s7.fe7433831f25 from=translated src=- shape=8a75b993 vocab=96c77fc7
-/
theorem low_add_X_pow_mul_high (i : σ) (N : ℕ) (φ : MvPowerSeries σ R) :
    low i N φ + X i ^ N * high i N φ = φ := by
  refine MvPowerSeries.ext fun m => ?_
  rw [map_add, coeff_low, X_pow_eq, coeff_monomial_mul, one_mul]
  by_cases h : m i < N
  · rw [ite_eq_left h, ite_eq_right (fun hle => absurd (Finsupp.single_le_iff.mp hle) (not_le.mpr h)), add_zero]
  · have hle : Finsupp.single i N ≤ m := Finsupp.single_le_iff.mpr (not_lt.mp h)
    rw [ite_eq_right h, ite_eq_left hle, zero_add, coeff_high, tsub_add_cancel_of_le hle]

def lowL (i : σ) (N : ℕ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun := low i N
  map_add' φ ψ := by
    refine MvPowerSeries.ext fun m => ?_
    rw [map_add, coeff_low, coeff_low, coeff_low, map_add]
    split_ifs
    · rfl
    · rw [add_zero]
  map_smul' a φ := by
    refine MvPowerSeries.ext fun m => ?_
    rw [RingHom.id_apply, map_smul, coeff_low, coeff_low, map_smul]
    split_ifs
    · rfl
    · rw [smul_zero]

def highL (i : σ) (N : ℕ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun := high i N
  map_add' φ ψ := by
    refine MvPowerSeries.ext fun m => ?_
    rw [map_add, coeff_high, coeff_high, coeff_high, map_add]
  map_smul' a φ := by
    refine MvPowerSeries.ext fun m => ?_
    rw [RingHom.id_apply, map_smul, coeff_high, coeff_high, map_smul]

def stepL (i : σ) (N : ℕ) (c : R) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R :=
  -(LinearMap.mulLeft R (C c * X i) ∘ₗ highL i N)

/--
@isnad1 id=eq.0h6v.s8.aa635b4ea08d from=translated src=- shape=46a66465 vocab=edfd7d2d
-/
theorem stepL_apply (i : σ) (N : ℕ) (c : R) (φ : MvPowerSeries σ R) :
    stepL i N c φ = -(C c * X i * high i N φ) := rfl

/--
@isnad1 id=eq.0h6v.s8.22b1f6a51855 from=translated src=- shape=535ca580 vocab=fe80f08e
-/
theorem high_mul_add_low (i : σ) (N : ℕ) (c : R) (φ : MvPowerSeries σ R) :
    high i N φ * sepPoly i N c + low i N φ = φ - stepL i N c φ := by
  have h := low_add_X_pow_mul_high i N φ
  rw [stepL_apply]
  linear_combination h

/--
@isnad1 id=ex.0h7v.s8.c0b21b511958 from=translated src=- shape=3dbb9ea8 vocab=cc0f46e0
-/
theorem iterate_stepL (i : σ) (N : ℕ) (c : R) :
    ∀ (k : ℕ) (φ : MvPowerSeries σ R), ∃ ψ : MvPowerSeries σ R,
      (⇑(stepL i N c))^[k] φ = C (c ^ k) * ψ := by
  intro k
  induction k with
  | zero => intro φ; exact ⟨φ, by rw [Function.iterate_zero, id_eq, pow_zero, map_one, one_mul]⟩
  | succ k ih =>
    intro φ
    obtain ⟨ψ, hψ⟩ := ih φ
    refine ⟨-(X i * high i N ψ), ?_⟩
    rw [Function.iterate_succ_apply', hψ, stepL_apply, high_C_mul, pow_succ, map_mul]
    ring

def remL (i : σ) (N : ℕ) (c : R) : ℕ → (MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R)
  | 0 => 0
  | k + 1 => lowL i N + remL i N c k ∘ₗ stepL i N c

def quoL (i : σ) (N : ℕ) (c : R) : ℕ → (MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R)
  | 0 => 0
  | k + 1 => highL i N + quoL i N c k ∘ₗ stepL i N c

/--
@isnad1 id=eq.0h6v.s7.c284efa27644 from=translated src=- shape=e84cd7bf vocab=d13351c2
-/
theorem remL_zero_apply (i : σ) (N : ℕ) (c : R) (φ : MvPowerSeries σ R) :
    remL i N c 0 φ = 0 := rfl

/--
@isnad1 id=eq.0h6v.s7.f74f26ab2f09 from=translated src=- shape=e84cd7bf vocab=0aabb748
-/
theorem quoL_zero_apply (i : σ) (N : ℕ) (c : R) (φ : MvPowerSeries σ R) :
    quoL i N c 0 φ = 0 := rfl

/--
@isnad1 id=eq.0h7v.s9.6cd5913c1f88 from=translated src=- shape=7cbd57dc vocab=36d31f82
-/
theorem remL_succ_apply (i : σ) (N : ℕ) (c : R) (k : ℕ) (φ : MvPowerSeries σ R) :
    remL i N c (k + 1) φ = low i N φ + remL i N c k (stepL i N c φ) := rfl

/--
@isnad1 id=eq.0h7v.s9.24947cffa9d5 from=translated src=- shape=7cbd57dc vocab=d6ba05e1
-/
theorem quoL_succ_apply (i : σ) (N : ℕ) (c : R) (k : ℕ) (φ : MvPowerSeries σ R) :
    quoL i N c (k + 1) φ = high i N φ + quoL i N c k (stepL i N c φ) := rfl

/--
@isnad1 id=eq.0h7v.s9.d10d9f647722 from=translated src=- shape=524f41a6 vocab=0c55f827
-/
theorem quoL_mul_add_remL (i : σ) (N : ℕ) (c : R) :
    ∀ (k : ℕ) (φ : MvPowerSeries σ R),
      quoL i N c k φ * sepPoly i N c + remL i N c k φ = φ - (⇑(stepL i N c))^[k] φ := by
  intro k
  induction k with
  | zero =>
    intro φ
    rw [quoL_zero_apply, remL_zero_apply, zero_mul, add_zero, Function.iterate_zero, id_eq, sub_self]
  | succ k ih =>
    intro φ
    have h1 := ih (stepL i N c φ)
    have h2 := high_mul_add_low i N c φ
    rw [quoL_succ_apply, remL_succ_apply, Function.iterate_succ_apply]
    linear_combination h1 + h2

/--
@isnad1 id=mem.0h7v.s8.b91e95fd650d from=translated src=- shape=dd1d6805 vocab=fd28fc1c
-/
theorem remL_mem (i : σ) (N : ℕ) (c : R) :
    ∀ (k : ℕ) (φ : MvPowerSeries σ R), remL i N c k φ ∈ lowSub i N := by
  intro k
  induction k with
  | zero => intro φ; rw [remL_zero_apply]; exact Submodule.zero_mem _
  | succ k ih =>
    intro φ
    rw [remL_succ_apply]
    exact Submodule.add_mem _ (low_mem i N φ) (ih _)

/--
@isnad1 id=mem.2h8v.s9.e0599606afcf from=translated src=- shape=924d4428 vocab=18684dfe
-/
theorem stepL_mem_of_ne {i j : σ} (hij : i ≠ j) (N : ℕ) (c : R) {N' : ℕ} {φ : MvPowerSeries σ R}
    (h : φ ∈ lowSub j N') : stepL i N c φ ∈ lowSub j N' := by
  rw [stepL_apply, mul_assoc]
  exact Submodule.neg_mem _ (C_mul_mem c (X_mul_mem_of_ne hij (high_mem_of_ne hij N h)))

/--
@isnad1 id=mem.2h9v.s9.6d79e98c18f7 from=translated src=- shape=70662854 vocab=fd28fc1c
-/
theorem remL_mem_of_ne {i j : σ} (hij : i ≠ j) (N : ℕ) (c : R) {N' : ℕ} :
    ∀ (k : ℕ) {φ : MvPowerSeries σ R}, φ ∈ lowSub j N' → remL i N c k φ ∈ lowSub j N' := by
  intro k
  induction k with
  | zero => intro φ _; rw [remL_zero_apply]; exact Submodule.zero_mem _
  | succ k ih =>
    intro φ h
    rw [remL_succ_apply]
    exact Submodule.add_mem _ (low_mem_of_mem i N h) (ih (stepL_mem_of_ne hij N c h))

theorem eq_zero_of_mul_sep_mem {i : σ} {N : ℕ} {c : R} {n : ℕ} (hn : c ^ n = 0)
    {q : MvPowerSeries σ R} (hq : q * sepPoly i N c ∈ lowSub i N) : q = 0 := by

  have key : ∀ m : σ →₀ ℕ,
      coeff m q = -(c * coeff (m + Finsupp.single i N) (q * X i)) := by
    intro m
    have h0 : coeff (m + Finsupp.single i N) (q * sepPoly i N c) = 0 :=
      hq _ (by rw [Finsupp.add_apply, Finsupp.single_eq_same]; exact Nat.le_add_left _ _)
    have hle : Finsupp.single i N ≤ m + Finsupp.single i N :=
      Finsupp.single_le_iff.mpr (by rw [Finsupp.add_apply, Finsupp.single_eq_same]; omega)
    rw [mul_add, map_add, X_pow_eq, coeff_mul_monomial, ite_eq_left hle, add_tsub_cancel_right, mul_one,
      show q * (C c * X i) = C c * (q * X i) by ring, coeff_C_mul] at h0
    linear_combination h0

  have hk : ∀ k : ℕ, ∃ ψ : MvPowerSeries σ R, q = C (c ^ k) * ψ := by
    intro k
    induction k with
    | zero => exact ⟨q, by rw [pow_zero, map_one, one_mul]⟩
    | succ k ih =>
      obtain ⟨ψ, hψ⟩ := ih
      refine ⟨-(high i N (ψ * X i)), MvPowerSeries.ext fun m => ?_⟩
      have h1 : q * X i = C (c ^ k) * (ψ * X i) := by rw [hψ, mul_assoc]
      rw [key m, h1, coeff_C_mul, coeff_C_mul, map_neg, coeff_high, pow_succ]
      ring
  obtain ⟨ψ, hψ⟩ := hk n
  rw [hψ, hn, map_zero, zero_mul]

/--
@isnad1 id=and.4h10v.s8.0a93e6334b4f from=translated src=- shape=eff6b16e vocab=1f6dcc3a
-/
theorem unique_div {i : σ} {N : ℕ} {c : R} {n : ℕ} (hn : c ^ n = 0)
    {q q' r r' : MvPowerSeries σ R} (hr : r ∈ lowSub i N) (hr' : r' ∈ lowSub i N)
    (h : q * sepPoly i N c + r = q' * sepPoly i N c + r') : q = q' ∧ r = r' := by
  have h1 : (q - q') * sepPoly i N c = r' - r := by linear_combination h
  have h2 : q - q' = 0 :=
    eq_zero_of_mul_sep_mem hn (by rw [h1]; exact Submodule.sub_mem _ hr' hr)
  have hq : q = q' := sub_eq_zero.mp h2
  refine ⟨hq, ?_⟩
  rw [hq] at h
  exact add_left_cancel h

section Rem

variable {i : σ} {N : ℕ} {c : R} {n : ℕ}

/--
@isnad1 id=eq.1h7v.s9.06a56da3bbb3 from=translated src=- shape=e9d069bb vocab=56893381
-/
theorem quo_mul_add_rem (hn : c ^ n = 0) (φ : MvPowerSeries σ R) :
    quoL i N c n φ * sepPoly i N c + remL i N c n φ = φ := by
  obtain ⟨ψ, hψ⟩ := iterate_stepL i N c n φ
  rw [quoL_mul_add_remL, hψ, hn, map_zero, zero_mul, sub_zero]

/--
@isnad1 id=mem.1h7v.s8.aa87ef60f4f5 from=translated src=- shape=9d3305c0 vocab=14dc3afb
-/
theorem sub_rem_mem (hn : c ^ n = 0) (φ : MvPowerSeries σ R) :
    φ - remL i N c n φ ∈ Ideal.span ({sepPoly i N c} : Set (MvPowerSeries σ R)) :=
  Ideal.mem_span_singleton'.mpr ⟨quoL i N c n φ, by
    have h := quo_mul_add_rem (i := i) (N := N) hn φ
    linear_combination h⟩

/--
@isnad1 id=eq.2h7v.s8.7796d94d7a73 from=translated src=- shape=d81f01a8 vocab=ea49e529
-/
theorem rem_eq_self (hn : c ^ n = 0) {φ : MvPowerSeries σ R} (hφ : φ ∈ lowSub i N) :
    remL i N c n φ = φ :=
  (unique_div hn (remL_mem i N c n φ) hφ
    (by rw [quo_mul_add_rem hn φ, zero_mul, zero_add])).2

/--
@isnad1 id=eq.1h7v.s8.d1d20f78850a from=translated src=- shape=5d0b4225 vocab=99ec1907
-/
theorem rem_mul_sep (hn : c ^ n = 0) (q : MvPowerSeries σ R) :
    remL i N c n (q * sepPoly i N c) = 0 :=
  (unique_div hn (remL_mem i N c n _) (Submodule.zero_mem _)
    (by rw [quo_mul_add_rem hn, add_zero])).2

/--
@isnad1 id=eq.0h8v.s9.92f879568c6d from=translated src=- shape=247a4c56 vocab=5b793ee5
-/
theorem rem_C_mul (a : R) (φ : MvPowerSeries σ R) :
    remL i N c n (C a * φ) = C a * remL i N c n φ := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul]

/--
@isnad1 id=eq.2h8v.s9.f066b71b8eda from=translated src=- shape=bae3b12e vocab=0ccbf6a0
-/
theorem rem_X_mul (hn : c ^ n = 0) {j : σ} (hji : j ≠ i) (φ : MvPowerSeries σ R) :
    remL i N c n (X j * φ) = X j * remL i N c n φ := by
  have e1 := quo_mul_add_rem (i := i) (N := N) hn (X j * φ)
  have e2 := quo_mul_add_rem (i := i) (N := N) hn φ
  exact (unique_div (q := quoL i N c n (X j * φ)) (q' := X j * quoL i N c n φ) hn (remL_mem i N c n _)
    (X_mul_mem_of_ne hji (remL_mem i N c n φ))
    (by simp only [sepPoly] at e1 e2 ⊢; linear_combination e1 - X j * e2)).2

/--
@isnad1 id=eq.2h9v.s9.7c8a3c6a697a from=translated src=- shape=9b7b548f vocab=0ccbf6a0
-/
theorem rem_X_pow_mul (hn : c ^ n = 0) {j : σ} (hji : j ≠ i) (φ : MvPowerSeries σ R) :
    ∀ k : ℕ, remL i N c n (X j ^ k * φ) = X j ^ k * remL i N c n φ := by
  intro k
  induction k with
  | zero => rw [pow_zero, one_mul, one_mul]
  | succ k ih =>
    rw [pow_succ', mul_assoc, rem_X_mul hn hji, mul_assoc, ← ih]

/--
@isnad1 id=eq.2h10v.s9.2b97a6717b8c from=translated src=- shape=5af8bb73 vocab=99ec1907
-/
theorem rem_sep_mul (hn : c ^ n = 0) {j : σ} (hji : j ≠ i) (N' : ℕ) (a : R)
    (φ : MvPowerSeries σ R) :
    remL i N c n (sepPoly j N' a * φ) = sepPoly j N' a * remL i N c n φ := by
  rw [show sepPoly j N' a * φ = C a * (X j * φ) + X j ^ N' * φ by
      simp only [sepPoly]; ring,
    map_add, rem_C_mul, rem_X_mul hn hji, rem_X_pow_mul hn hji]
  simp only [sepPoly]
  ring

end Rem

end OneVariable

section Global

variable {R : Type*} [CommRing R] {g : ℕ}

abbrev sep (N : Fin g → ℕ) (c : Fin g → R) (i : Fin g) : MvPowerSeries (Fin g) R :=
  C (c i) * X i + X i ^ N i

abbrev sepIdeal (N : Fin g → ℕ) (c : Fin g → R) : Ideal (MvPowerSeries (Fin g) R) :=
  Ideal.span (Set.range fun i : Fin g => C (c i) * X i + (X i : MvPowerSeries (Fin g) R) ^ N i)

/--
@isnad1 id=mem.0h5v.s6.dc323f866217 from=translated src=- shape=5eb40d8b vocab=90a2ae53
-/
theorem sep_mem_sepIdeal (N : Fin g → ℕ) (c : Fin g → R) (i : Fin g) : sep N c i ∈ sepIdeal N c :=
  Ideal.subset_span ⟨i, rfl⟩

/--
@isnad1 id=le.0h5v.s7.6bef26d3efe2 from=translated src=- shape=87f28ced vocab=50e8536e
-/
theorem span_sep_le (N : Fin g → ℕ) (c : Fin g → R) (i : Fin g) :
    Ideal.span ({sepPoly i (N i) (c i)} : Set (MvPowerSeries (Fin g) R)) ≤ sepIdeal N c :=
  (Ideal.span_singleton_le_iff_mem _).mpr (sep_mem_sepIdeal N c i)

variable (N : Fin g → ℕ) (c : Fin g → R) (n : Fin g → ℕ)

def RedUpTo : ℕ → (MvPowerSeries (Fin g) R →ₗ[R] MvPowerSeries (Fin g) R)
  | 0 => LinearMap.id
  | k + 1 =>
    if h : k < g then remL (⟨k, h⟩ : Fin g) (N ⟨k, h⟩) (c ⟨k, h⟩) (n ⟨k, h⟩) ∘ₗ RedUpTo k
    else RedUpTo k

/--
@isnad1 id=eq.0h6v.s8.12d07c0283d3 from=translated src=- shape=7d2abc18 vocab=d26dd29c
-/
theorem RedUpTo_zero_apply (φ : MvPowerSeries (Fin g) R) : RedUpTo N c n 0 φ = φ := rfl

/--
@isnad1 id=eq.1h7v.s9.73092a6ef753 from=translated src=- shape=1d45ffdf vocab=c2b52132
-/
theorem RedUpTo_succ_of_lt {k : ℕ} (h : k < g) (φ : MvPowerSeries (Fin g) R) :
    RedUpTo N c n (k + 1) φ =
      remL (⟨k, h⟩ : Fin g) (N ⟨k, h⟩) (c ⟨k, h⟩) (n ⟨k, h⟩) (RedUpTo N c n k φ) := by
  simp only [RedUpTo, dite_eq_left h, LinearMap.comp_apply]

/--
@isnad1 id=eq.1h7v.s8.86bed0daa4bc from=translated src=- shape=e0da8946 vocab=083ba3c5
-/
theorem RedUpTo_succ_of_not_lt {k : ℕ} (h : ¬ k < g) (φ : MvPowerSeries (Fin g) R) :
    RedUpTo N c n (k + 1) φ = RedUpTo N c n k φ := by
  simp only [RedUpTo, dite_eq_right h]

abbrev Red : MvPowerSeries (Fin g) R →ₗ[R] MvPowerSeries (Fin g) R := RedUpTo N c n g

variable {N c n} (hn : ∀ i, c i ^ n i = 0)
include hn

/--
@isnad1 id=mem.1h7v.s8.35c8a8e0fea4 from=translated src=- shape=d0427af3 vocab=d282e36f
-/
theorem sub_RedUpTo_mem :
    ∀ (k : ℕ) (φ : MvPowerSeries (Fin g) R), φ - RedUpTo N c n k φ ∈ sepIdeal N c := by
  intro k
  induction k with
  | zero => intro φ; rw [RedUpTo_zero_apply, sub_self]; exact Submodule.zero_mem _
  | succ k ih =>
    intro φ
    by_cases h : k < g
    · rw [RedUpTo_succ_of_lt N c n h,
        show ∀ a b : MvPowerSeries (Fin g) R, φ - b = (φ - a) + (a - b) from fun a b => by ring]
      exact Submodule.add_mem _ (ih φ) (span_sep_le N c ⟨k, h⟩ (sub_rem_mem (hn ⟨k, h⟩) _))
    · rw [RedUpTo_succ_of_not_lt N c n h]
      exact ih φ

omit hn in
/--
@isnad1 id=mem.1h8v.s8.7042f810e710 from=translated src=- shape=79cb5a90 vocab=0c8acce3
-/
theorem RedUpTo_mem :
    ∀ (k : ℕ) (φ : MvPowerSeries (Fin g) R) (j : Fin g), (j : ℕ) < k →
      RedUpTo N c n k φ ∈ lowSub j (N j) := by
  intro k
  induction k with
  | zero => intro φ j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    intro φ j hj
    by_cases h : k < g
    · rw [RedUpTo_succ_of_lt N c n h]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
      · have hne : (⟨k, h⟩ : Fin g) ≠ j := fun e => by
          have := congrArg Fin.val e; simp only at this; omega
        exact remL_mem_of_ne hne _ _ _ (ih φ j hj')
      · have hje : j = ⟨k, h⟩ := Fin.ext hj'
        subst hje
        exact remL_mem _ _ _ _ _
    · rw [RedUpTo_succ_of_not_lt N c n h]
      exact ih φ j (by omega)

/--
@isnad1 id=eq.2h7v.s8.c0292d8f644e from=translated src=- shape=e5cf29b0 vocab=a9ba1e57
-/
theorem RedUpTo_eq_self :
    ∀ (k : ℕ) {φ : MvPowerSeries (Fin g) R}, (∀ j : Fin g, φ ∈ lowSub j (N j)) →
      RedUpTo N c n k φ = φ := by
  intro k
  induction k with
  | zero => intro φ _; rfl
  | succ k ih =>
    intro φ hφ
    by_cases h : k < g
    · rw [RedUpTo_succ_of_lt N c n h, ih hφ]
      exact rem_eq_self (hn ⟨k, h⟩) (hφ ⟨k, h⟩)
    · rw [RedUpTo_succ_of_not_lt N c n h, ih hφ]

/--
@isnad1 id=eq.2h8v.s9.3d466bb44e34 from=translated src=- shape=a5f709d4 vocab=050297f4
-/
theorem RedUpTo_sep_mul :
    ∀ (k : ℕ) (i : Fin g), k ≤ (i : ℕ) → ∀ φ : MvPowerSeries (Fin g) R,
      RedUpTo N c n k (sep N c i * φ) = sep N c i * RedUpTo N c n k φ := by
  intro k
  induction k with
  | zero => intro i _ φ; rfl
  | succ k ih =>
    intro i hi φ
    by_cases h : k < g
    · have hne : i ≠ (⟨k, h⟩ : Fin g) := fun e => by
        have := congrArg Fin.val e; simp only at this; omega
      rw [RedUpTo_succ_of_lt N c n h, RedUpTo_succ_of_lt N c n h, ih i (by omega) φ]
      exact rem_sep_mul (hn ⟨k, h⟩) hne (N i) (c i) _
    · rw [RedUpTo_succ_of_not_lt N c n h, RedUpTo_succ_of_not_lt N c n h]
      exact ih i (by omega) φ

/--
@isnad1 id=eq.2h8v.s8.f877f65848c6 from=translated src=- shape=770b5db0 vocab=eb5eefca
-/
theorem RedUpTo_mul_sep :
    ∀ (k : ℕ) (i : Fin g), (i : ℕ) < k → ∀ q : MvPowerSeries (Fin g) R,
      RedUpTo N c n k (q * sep N c i) = 0 := by
  intro k
  induction k with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hi q
    by_cases h : k < g
    · rw [RedUpTo_succ_of_lt N c n h]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
      · rw [ih i hi' q, map_zero]
      · have hie : i = ⟨k, h⟩ := Fin.ext hi'
        subst hie
        rw [mul_comm, RedUpTo_sep_mul hn k _ le_rfl q, mul_comm]
        exact rem_mul_sep (hn _) _
    · rw [RedUpTo_succ_of_not_lt N c n h]
      exact ih i (by omega) q

/--
@isnad1 id=mem.1h6v.s8.3baa3d99cad4 from=translated src=- shape=f843f3fa vocab=883cb0ce
-/
theorem sub_Red_mem (φ : MvPowerSeries (Fin g) R) : φ - Red N c n φ ∈ sepIdeal N c :=
  sub_RedUpTo_mem hn g φ

omit hn in
/--
@isnad1 id=mem.0h7v.s8.138f37a672df from=translated src=- shape=a0dc1807 vocab=0f90a490
-/
theorem Red_mem (φ : MvPowerSeries (Fin g) R) (j : Fin g) : Red N c n φ ∈ lowSub j (N j) :=
  RedUpTo_mem g φ j j.isLt

/--
@isnad1 id=eq.2h6v.s8.1749b2f54ee8 from=translated src=- shape=043b7848 vocab=6bb65185
-/
theorem Red_eq_self {φ : MvPowerSeries (Fin g) R} (hφ : ∀ j : Fin g, φ ∈ lowSub j (N j)) :
    Red N c n φ = φ :=
  RedUpTo_eq_self hn g hφ

/--
@isnad1 id=eq.2h6v.s8.7163a5d31283 from=translated src=- shape=5ca2ade7 vocab=756530ae
-/
theorem Red_eq_zero_of_mem {φ : MvPowerSeries (Fin g) R} (hφ : φ ∈ sepIdeal N c) :
    Red N c n φ = 0 := by
  obtain ⟨q, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hφ
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  exact RedUpTo_mul_sep hn g i i.isLt (q i)

end Global

section Box

variable {R : Type*} [CommRing R] {g : ℕ} {N : Fin g → ℕ}

def InBox (N : Fin g → ℕ) (d : Fin g →₀ ℕ) : Prop := ∀ i, d i < N i

scoped instance instDecidableInBox (N : Fin g → ℕ) (d : Fin g →₀ ℕ) : Decidable (InBox N d) := by
  unfold InBox; infer_instance

/--
@isnad1 id=eq.2h5v.s8.0533dbf4e90c from=translated src=- shape=01b7b9bf vocab=91e81dd9
-/
theorem coeff_eq_zero_of_not_inBox {φ : MvPowerSeries (Fin g) R} (hφ : ∀ j : Fin g, φ ∈ lowSub j (N j))
    {d : Fin g →₀ ℕ} (hd : ¬ InBox N d) : coeff d φ = 0 := by
  obtain ⟨j, hj⟩ := not_forall.mp hd
  exact hφ j d (not_lt.mp hj)

def toFinsupp (u : (i : Fin g) → Fin (N i)) : Fin g →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (u i : ℕ)

/--
@isnad1 id=eq.0h4v.s5.0d8159242fbd from=translated src=- shape=8f433d38 vocab=7f283d1e
-/
@[scoped simp] theorem toFinsupp_apply (u : (i : Fin g) → Fin (N i)) (i : Fin g) : toFinsupp u i = u i := rfl

/--
@isnad1 id=inbox.0h3v.s4.5a27b50d73d9 from=translated src=- shape=8360a44a vocab=86b087b0
-/
theorem inBox_toFinsupp (u : (i : Fin g) → Fin (N i)) : InBox N (toFinsupp u) := fun i => (u i).isLt

/--
@isnad1 id=eq.1h3v.s6.f54a8816b20b from=translated src=- shape=6af75a1d vocab=3e92f7be
-/
theorem toFinsupp_mk {d : Fin g →₀ ℕ} (h : InBox N d) :
    toFinsupp (fun i => (⟨d i, h i⟩ : Fin (N i))) = d := by
  ext i
  rfl

def extend (v : ((i : Fin g) → Fin (N i)) → R) : MvPowerSeries (Fin g) R :=
  fun d => if h : InBox N d then v (fun i => ⟨d i, h i⟩) else 0

/--
@isnad1 id=eq.0h5v.s8.f078ed60d275 from=translated src=- shape=b6a30862 vocab=5bf6bd56
-/
theorem coeff_extend (v : ((i : Fin g) → Fin (N i)) → R) (d : Fin g →₀ ℕ) :
    coeff d (extend v) = if h : InBox N d then v (fun i => ⟨d i, h i⟩) else 0 :=
  rfl

/--
@isnad1 id=eq.0h5v.s7.7dd67953f43a from=translated src=- shape=2244f7bb vocab=e41e9047
-/
theorem coeff_extend_toFinsupp (v : ((i : Fin g) → Fin (N i)) → R) (u : (i : Fin g) → Fin (N i)) :
    coeff (toFinsupp u) (extend v) = v u := by
  rw [coeff_extend, dite_eq_left (inBox_toFinsupp u)]
  rfl

/--
@isnad1 id=mem.0h5v.s7.6687107efe40 from=translated src=- shape=859edae9 vocab=79a4f1fe
-/
theorem extend_mem (v : ((i : Fin g) → Fin (N i)) → R) (j : Fin g) : extend v ∈ lowSub j (N j) := by
  intro d hd
  rw [coeff_extend, dite_eq_right]
  exact fun h => absurd (h j) (not_lt.mpr hd)

variable (N) (c : Fin g → R) (n : Fin g → ℕ)

def extendLin : (((i : Fin g) → Fin (N i)) → R) →ₗ[R] (MvPowerSeries (Fin g) R ⧸ sepIdeal N c) :=
  (Ideal.Quotient.mkₐ R (sepIdeal N c)).toLinearMap ∘ₗ
    { toFun := extend
      map_add' := fun v w => by
        refine MvPowerSeries.ext fun d => ?_
        rw [map_add, coeff_extend, coeff_extend, coeff_extend]
        split_ifs <;> simp
      map_smul' := fun a v => by
        refine MvPowerSeries.ext fun d => ?_
        rw [map_smul, coeff_extend, coeff_extend, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp }

/--
@isnad1 id=eq.0h5v.s10.9f0dd26eeca7 from=translated src=- shape=50efae97 vocab=6c977ddf
-/
theorem extendLin_apply (v : ((i : Fin g) → Fin (N i)) → R) :
    extendLin N c v = Ideal.Quotient.mk (sepIdeal N c) (extend v) := rfl

variable {N c n} (hn : ∀ i, c i ^ n i = 0)
include hn

/--
@isnad1 id=injectiv.1h5v.s9.8f76a82794e9 from=translated src=- shape=047e6eaf vocab=b381b596
-/
theorem extendLin_injective : Function.Injective (extendLin N c) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  rw [extendLin_apply, Ideal.Quotient.eq_zero_iff_mem] at hv
  have h0 : extend v = 0 := by
    rw [← Red_eq_self (n := n) hn (extend_mem v)]
    exact Red_eq_zero_of_mem hn hv
  funext u
  rw [← coeff_extend_toFinsupp v u, h0, map_zero]
  rfl

/--
@isnad1 id=surjecti.1h5v.s9.f8201e672381 from=translated src=- shape=047e6eaf vocab=193cd176
-/
theorem extendLin_surjective : Function.Surjective (extendLin N c) := by
  intro x
  obtain ⟨θ, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨fun u => coeff (toFinsupp u) (Red N c n θ), ?_⟩
  have hext : extend (N := N) (fun u => coeff (toFinsupp u) (Red N c n θ)) = Red N c n θ := by
    refine MvPowerSeries.ext fun d => ?_
    rw [coeff_extend]
    split_ifs with hd
    · rw [toFinsupp_mk hd]
    · exact (coeff_eq_zero_of_not_inBox (Red_mem θ) hd).symm
  rw [extendLin_apply, Ideal.Quotient.eq, hext,
    show Red N c n θ - θ = -(θ - Red N c n θ) by ring]
  exact Submodule.neg_mem _ (sub_Red_mem hn θ)

def boxEquiv :
    (((i : Fin g) → Fin (N i)) → R) ≃ₗ[R] (MvPowerSeries (Fin g) R ⧸ sepIdeal N c) :=
  LinearEquiv.ofBijective (extendLin N c) ⟨extendLin_injective hn, extendLin_surjective hn⟩

end Box

end P2mKcWeierSep
open scoped _root_.P2MW.S_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_C_mul_X_add_X_pow_of_isNilpotent.P2mKcWeierSep

end
open scoped _root_.P2MW.S_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_C_mul_X_add_X_pow_of_isNilpotent.P2mKcWeierSep

open P2mKcWeierSep in
/--
@isnad1 id=and.1h4v.s11.189001164f2d from=translated src=- shape=8794b2fd vocab=ed0d0715
-/
theorem solution
    (R : Type u) [CommRing R] [Nontrivial R] (g : ℕ) (N : Fin g → ℕ) (c : Fin g → R)
    (hc : ∀ i, IsNilpotent (c i)) :
    Module.Free R (MvPowerSeries (Fin g) R ⧸
        Ideal.span (Set.range fun i : Fin g =>
          MvPowerSeries.C (c i) * MvPowerSeries.X i + (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N i)) ∧
      Module.Finite R (MvPowerSeries (Fin g) R ⧸
        Ideal.span (Set.range fun i : Fin g =>
          MvPowerSeries.C (c i) * MvPowerSeries.X i + (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N i)) ∧
      Module.finrank R (MvPowerSeries (Fin g) R ⧸
        Ideal.span (Set.range fun i : Fin g =>
          MvPowerSeries.C (c i) * MvPowerSeries.X i + (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N i))
          = ∏ i, N i := by
  choose n hn using hc
  refine ⟨Module.Free.of_equiv (boxEquiv hn), Module.Finite.equiv (boxEquiv hn), ?_⟩
  rw [← (boxEquiv hn).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_pi]
  simp only [Fintype.card_fin]
