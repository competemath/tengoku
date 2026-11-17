/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.QuantumGroup.ModuleSymmetry.Rank1

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A formula for `T''` on short strings

Let `M` be an integrable `U_q(𝔰𝔩₂)`-module (`QuantumGroup.IntegrableSl2`) with `q` nonzero and not
a root of unity, and let `T = T''_q` (`QuantumGroup.IntegrableSl2.T`). For `p, r ∈ ℕ` put
`Ψ_{p,r} = Σ_{s ≤ min(r, p)} (-1)^s q^{-s} E^{(r-s)} F^{(p-s)}` (`IntegrableSl2.psi`). We show
`T(w) = (-1)^p q^p Ψ_{p,r}(w)` for every `w ∈ M^{p-r}` in the span of the vectors `F^{(k)} ζ` with
`ζ` primitive and `k ≤ r` (`IntegrableSl2.T_eq_psi_of_mem`). On such a vector both sides are
multiples of `F^{(p+k-r)} ζ`, and the coefficients agree by the identity
`Σ_c (-1)^c q^c [h+c, c] [h, k-c] = (-q^{h+1})^k` of `QuantumGroup.QBinomialSeries`.

This is the rank-one computation behind the compatibility `T(Eⱼ m) = Tᵢ(Eⱼ) T(m)` of Lusztig's
symmetries of `U` and of its integrable modules ([Lus] 37.1.2; [Jan] 8.10, whose proof is
different): for a primitive vector `η ∈ Mᵖ` of an integrable `U`-module, `Tᵢ(Eⱼ) T(η)` equals
`(-1)^p q^p Ψ_{p,r}(Eⱼ η)` with `r = -aᵢⱼ`, and `Eⱼ η` lies in the span above. To control the
lengths of the strings we also show that a vector of `Mⁿ` killed by `E^N` (if `n ≥ 0`), resp. by
`F^N` (if `n ≤ 0`), is a sum of vectors `F^{(k)} ζ` with `k < N`, resp. `k < N - n`
(`IntegrableSl2.mem_stringsLT_of_nonneg`, `IntegrableSl2.mem_stringsLT_of_nonpos`).

The arguments are our own.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §5.2, §37.1.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, §8.10.
-/

open Finset

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  (V : IntegrableSl2 q M)

/-! ### Strings of bounded length -/

/-- The span of the vectors `F^{(j)} η` with `j < N` and `η ∈ M^{n+2j}` primitive.-/
def stringsLT (n : ℤ) (N : ℕ) : Submodule k M :=
  Submodule.span k
    {x | ∃ (j : ℕ) (η : M), j < N ∧ η ∈ V.wt (n + 2 * j) ∧ V.E η = 0 ∧ x = V.dF j η}

variable {V}

variable (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq0 hq

/-! ### The operator `Ψ_{p,r}` -/

omit hq0 hq in
/--
@isnad1 id=eq.3h5v.s6.6a5ae253492b from=translated src=- shape=3098d027 vocab=65971565
-/
lemma qBinomial_mul_qBinomial_eq' {a kk u : ℕ} (hka : kk ≤ a) (hu : u ≤ kk)
    (hf : ∀ n, qFactorial q n ≠ 0) :
    qBinomial q a kk * qBinomial q kk u = qBinomial q a u * qBinomial q (a - u) (kk - u) := by
  have h1 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) hka
  have h2 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) hu
  have h3 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (show u ≤ a by omega)
  have h4 := qBinomial_mul_qFactorial_mul_qFactorial (v := q) (show kk - u ≤ a - u by omega)
  rw [show a - u - (kk - u) = a - kk by omega] at h4
  have hX : qFactorial q u * qFactorial q (kk - u) * qFactorial q (a - kk) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hf _) (hf _)) (hf _)
  apply mul_right_cancel₀ hX
  linear_combination (qBinomial q a kk * qFactorial q (a - kk)) * h2 + h1 -
    (qBinomial q a u * qFactorial q u) * h4 - h3

/-- `[a, k] [k, u] = [a, u] [a - u, k - u]` for `u ≤ k`.
@isnad1 id=eq.3h5v.s7.e0b43e1b5ce3 from=translated src=- shape=6ba2bc44 vocab=3e15718c
-/
lemma qBinomial_mul_qBinomial_eq {a kk u : ℕ} (hu : u ≤ kk) :
    qBinomial q a kk * qBinomial q kk u = qBinomial q a u * qBinomial q (a - u) (kk - u) := by
  rcases le_or_gt kk a with hka | hka
  · exact qBinomial_mul_qBinomial_eq' hka hu (qFactorial_ne_zero_of_pow_ne_one hq0 hq)
  · rcases le_or_gt u a with hua | hua
    · rw [qBinomial_eq_zero_of_lt q hka,
        qBinomial_eq_zero_of_lt q (show a - u < kk - u by omega), zero_mul, mul_zero]
    · rw [qBinomial_eq_zero_of_lt q hka, qBinomial_eq_zero_of_lt q hua, zero_mul, zero_mul]

omit hq0 hq in
/--
@isnad1 id=eq.1h3v.s7.4f4f2f8d5623 from=translated src=- shape=eb4076fd vocab=90e5a5f2
-/
lemma neg_one_pow_sub {r u : ℕ} (h : u ≤ r) : (-1 : k) ^ (r - u) = (-1) ^ r * (-1) ^ u := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add, mul_comm ((-1 : k) ^ u), mul_assoc, ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]

omit hq in
/--
@isnad1 id=eq.2h4v.s7.190a1c5eb3fc from=translated src=- shape=72e072c7 vocab=497e8d54
-/
lemma inv_pow_sub {r u : ℕ} (h : u ≤ r) : q⁻¹ ^ (r - u) = q⁻¹ ^ r * q ^ u := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have := pow_ne_zero u hq0
  simp only [Nat.add_sub_cancel_left, pow_add, inv_pow]
  field_simp

/-- The coefficient identity behind `T_eq_psi_of_mem`.
@isnad1 id=eq.4h5v.s9.daa5272c1914 from=translated src=- shape=cfcd1016 vocab=8bbf2861
-/
lemma psi_coeff {p r kk : ℕ} (hk : kk ≤ r) (hh : r ≤ p + kk) :
    (-1) ^ p * q ^ p * ∑ s ∈ range (r + 1), (if s ≤ p then (-1) ^ s * q⁻¹ ^ s else 0) *
      (qBinomial q (p - s + kk) (p - s) * qBinomial q kk (r - s)) =
      (-1) ^ (p + kk - r) * q ^ ((p + kk - r) * (kk + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨h, rfl⟩ : ∃ h, p = h + d := ⟨p - d, by omega⟩
  rw [show h + d + kk - (kk + d) = h by omega]
  -- reverse the summation: `s = r - u`
  rw [← sum_range_reflect]
  simp only [Nat.add_sub_cancel]
  -- only `u ≤ kk` contributes
  rw [← sum_subset (range_subset_range.2 (show kk + 1 ≤ kk + d + 1 by omega))]
  swap
  · intro u hu hu'
    simp only [mem_range, not_lt] at hu hu'
    rw [show kk + d - (kk + d - u) = u by omega, qBinomial_eq_zero_of_lt q (by omega : kk < u),
      mul_zero, mul_zero]
  have hterm : ∀ u ∈ range (kk + 1), (if kk + d - u ≤ h + d then
      (-1) ^ (kk + d - u) * q⁻¹ ^ (kk + d - u) else 0) *
      (qBinomial q (h + d - (kk + d - u) + kk) (h + d - (kk + d - u)) *
        qBinomial q kk (kk + d - (kk + d - u))) =
      (-1) ^ (kk + d) * q⁻¹ ^ (kk + d) *
        ((-1) ^ u * q ^ u * qBinomial q (h + u) u * qBinomial q h (kk - u)) := by
    intro u hu
    simp only [mem_range] at hu
    rw [show kk + d - (kk + d - u) = u by omega]
    split_ifs with hs
    · rw [show h + d - (kk + d - u) + kk = h + u by omega,
        show h + d - (kk + d - u) = h + u - kk by omega,
        qBinomial_symm q (show kk ≤ h + u by omega),
        qBinomial_mul_qBinomial_eq hq0 hq (show u ≤ kk by omega), Nat.add_sub_cancel,
        neg_one_pow_sub (show u ≤ kk + d by omega), inv_pow_sub hq0 (show u ≤ kk + d by omega)]
      ring
    · rw [qBinomial_eq_zero_of_lt q (show h < kk - u by omega)]
      ring
  rw [sum_congr rfl hterm, ← mul_sum, sum_qBinomial_mul_qBinomial_zero hq0 h kk]
  rw [inv_pow, neg_pow (q ^ (h + 1)), ← pow_mul]
  have hqd : q ^ (kk + d) ≠ 0 := pow_ne_zero _ hq0
  field_simp
  have e1 : ((-1 : k) ^ d) ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  have e2 : ((-1 : k) ^ kk) ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  rw [pow_add (-1 : k) h d, pow_add (-1 : k) kk d]
  linear_combination ((-1 : k) ^ h * q ^ (h + d) * q ^ ((h + 1) * kk) * ((-1) ^ kk) ^ 2) * e1 +
    ((-1 : k) ^ h * q ^ (h + d) * q ^ ((h + 1) * kk)) * e2

variable (V) in
/-- `Ψ_{p,r} = Σ_{s ≤ min(r, p)} (-1)^s q^{-s} E^{(r-s)} F^{(p-s)}`.-/
noncomputable def psi (p r : ℕ) : Module.End k M :=
  ∑ s ∈ range (r + 1), (if s ≤ p then (-1) ^ s * q⁻¹ ^ s else 0) • (V.dE (r - s) * V.dF (p - s))

omit hq0 hq in
/--
@isnad1 id=eq.0h7v.s8.f88527360bb6 from=translated src=- shape=be1031c4 vocab=0ab59384
-/
lemma psi_apply (p r : ℕ) (w : M) : V.psi p r w = ∑ s ∈ range (r + 1),
    (if s ≤ p then (-1) ^ s * q⁻¹ ^ s else 0) • V.dE (r - s) (V.dF (p - s) w) := by
  rw [psi, LinearMap.sum_apply]
  rfl

/-- `T''_q(w) = (-1)^p q^p Ψ_{p,r}(w)` for `w ∈ M^{p-r}` in the span of the vectors `F^{(k)} ζ`,
`ζ` primitive, `k ≤ r`.
@isnad1 id=eq.3h7v.s8.c53a6887ba65 from=translated src=- shape=585e29cb vocab=668c8711
-/
theorem T_eq_psi_of_mem {p r : ℕ} {w : M} (hw : w ∈ V.stringsLT ((p : ℤ) - r) (r + 1)) :
    V.T q w = ((-1) ^ p * q ^ p) • V.psi p r w := by
  induction hw using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, map_smul, hx, smul_comm]
  | mem x hx =>
    obtain ⟨kk, ζ, hkk, hζ, hE, rfl⟩ := hx
    rcases lt_or_ge ((p : ℤ) - r + 2 * kk) 0 with hneg | hnn
    · rw [eq_zero_of_primitive_of_neg hq0 hq hζ hE hneg]
      simp
    obtain ⟨P, hP⟩ : ∃ P : ℕ, (P : ℤ) = p - r + 2 * kk := ⟨_, Int.toNat_of_nonneg hnn⟩
    rw [← hP] at hζ
    by_cases hkP : kk ≤ P
    swap
    · rw [dF_eq_zero_of_primitive hq0 hq hζ hE (by omega)]
      simp
    have hh : r ≤ p + kk := by omega
    rw [T_dF_of_primitive hq0 hq hq0 (fun _ _ ↦ rfl) hζ hE hkP, psi_apply]
    have hterm : ∀ s ∈ range (r + 1), (if s ≤ p then (-1) ^ s * q⁻¹ ^ s else 0) •
        V.dE (r - s) (V.dF (p - s) (V.dF kk ζ)) =
        ((if s ≤ p then (-1) ^ s * q⁻¹ ^ s else 0) *
          (qBinomial q (p - s + kk) (p - s) * qBinomial q kk (r - s))) • V.dF (P - kk) ζ := by
      intro s hs
      simp only [mem_range] at hs
      split_ifs with hsp
      swap
      · simp
      rw [dF_dF hq0 hq, map_smul]
      rcases le_or_gt (r - s) kk with hrs | hrs
      · rw [dE_dF_of_primitive hq0 hq hζ hE (show r - s ≤ p - s + kk by omega)
          (show p - s + kk ≤ P by omega), show P - (p - s + kk) + (r - s) = kk by omega,
          show p - s + kk - (r - s) = P - kk by omega, smul_smul, smul_smul, mul_assoc]
      · rw [dF_eq_zero_of_primitive hq0 hq hζ hE (show (P : ℤ) < (p - s + kk : ℕ) by omega),
          map_zero, smul_zero, smul_zero, qBinomial_eq_zero_of_lt q hrs, mul_zero, mul_zero,
          zero_smul]
    rw [sum_congr rfl hterm, ← sum_smul, smul_smul, psi_coeff hq0 hq (by omega) hh,
      show p + kk - r = P - kk by omega]

end IntegrableSl2

end LieLean.QuantumGroup
