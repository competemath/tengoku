import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.CoefficientDegree
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.QuotientOrbit
import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.FieldTheory.RatFunc.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# The reduction from LN97 (6.19) to (6.20)

For `g = f^((q-1)/m)`, a first-block relation modulo `X^q` makes the
orbit product vanish in that quotient.  Multiplying by `f^(m-1)` and
using Frobenius gives the polynomial `firstBlockCleared`.  Its degree
bound lifts the quotient identity to a polynomial identity, and then
to the rational-function identity (6.20).

The numerical hypothesis is stated first as the exact degree budget
`m * D + (m - 1) * f.natDegree < q`; no irreducibility is needed here.
-/

variable {F : Type*} [Field F]

/-- The polynomial obtained by clearing denominators in (6.20).-/
noncomputable def firstBlockCleared {m : ℕ}
    (zeta : F) (a : Fin m → Polynomial F) (f : Polynomial F) : Polynomial F :=
  ∑ i ∈ Finset.range m,
    (firstBlockSymmetric zeta a).coeff i * C (f.eval 0) ^ i * f ^ (m - 1 - i)

theorem firstBlockCleared_natDegree_le
    {m D : ℕ} (hm : 0 < m) (zeta : F)
    (a : Fin m → Polynomial F) (ha : ∀ i, (a i).natDegree ≤ D)
    (f : Polynomial F) :
    (firstBlockCleared zeta a f).natDegree ≤ m * D + (m - 1) * f.natDegree := by
  unfold firstBlockCleared
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  calc
    _ ≤ ((firstBlockSymmetric zeta a).coeff i * C (f.eval 0) ^ i).natDegree +
        (f ^ (m - 1 - i)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ m * D + (m - 1 - i) * f.natDegree := by
      apply Nat.add_le_add
      · rw [← map_pow]
        exact (Polynomial.natDegree_mul_C_le _ _).trans
          (firstBlockSymmetric_coeff_natDegree_le hm zeta a ha i)
      · exact Polynomial.natDegree_pow_le
    _ ≤ m * D + (m - 1) * f.natDegree :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _

/-- The exponent rearrangement used before applying Frobenius.  This
identity holds in the quotient ring even when `x` is not a unit.-/
theorem pow_mul_card_sub_one_pow
    {R : Type*} [CommMonoid R] (x : R) {q n i : ℕ}
    (hq : 0 < q) (hi : i ≤ n) :
    x ^ n * (x ^ (q - 1)) ^ i = (x ^ q) ^ i * x ^ (n - i) := by
  simp only [← pow_mul, ← pow_add]
  congr 1
  have hq' : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hi' : n - i + i = n := Nat.sub_add_cancel hi
  nlinarith

/-- The degree budget in the book, with natural-number subtraction made
explicit: `k` must fit in `q / m` and must be positive.-/
theorem firstBlock_degree_budget {q m k : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hkq : k ≤ q / m) :
    m * (q / m - k) + (m - 1) * k < q := by
  have hdiv : m * (q / m) ≤ q := Nat.mul_div_le q m
  have hsub : q / m - k + k = q / m := Nat.sub_add_cancel hkq
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  nlinarith

/-- Clearing denominators commutes with mapping into any field.-/
theorem firstBlockCleared_map_eq_mul_eval₂
    {K : Type*} [Field K] (phi : Polynomial F →+* K)
    {m : ℕ} (hm : 0 < m) {zeta : F} (hzeta : IsPrimitiveRoot zeta m)
    (a : Fin m → Polynomial F) (f : Polynomial F) (hf : phi f ≠ 0) :
    phi (firstBlockCleared zeta a f) =
      (phi f) ^ (m - 1) *
        (firstBlockSymmetric zeta a).eval₂ phi (phi (C (f.eval 0)) / phi f) := by
  have hdeg : (firstBlockSymmetric zeta a).natDegree < m :=
    lt_of_le_of_lt (firstBlockSymmetric_natDegree_le hm hzeta a) (by omega)
  rw [eval₂_eq_sum_range' phi hdeg]
  simp only [firstBlockCleared, map_sum, map_mul, map_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ m - 1 := by have := Finset.mem_range.mp hi; omega
  rw [div_pow, pow_sub₀ (phi f) hf hi']
  ring

variable [Fintype F]

/-- Frobenius in `F[X]/(X^q)`: `f(X)^q` reduces to `f(0)`.-/
theorem XCardMk_pow_card (f : Polynomial F) :
    (XCardMk F) (f ^ Fintype.card F) = (XCardMk F) (C (f.eval 0)) := by
  have hh :
      (XCardMk F).comp (FiniteField.frobeniusAlgHom F (Polynomial F)).toRingHom =
        (XCardMk F).comp (Polynomial.C.comp (Polynomial.evalRingHom 0)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [RingHom.comp_apply, FiniteField.frobeniusAlgHom_apply,
        ← map_pow, FiniteField.pow_card]
    · change (XCardMk F) (X ^ Fintype.card F) = (XCardMk F) (C (eval 0 X))
      simp [XCardMk]
  exact DFunLike.congr_fun hh f

/-- Contracting the orbit identity turns the first-block quotient relation
into an evaluation of `G` at `g^m`.-/
theorem firstBlockSymmetric_quotient_eval_eq_zero
    {m : ℕ} (hm : 0 < m) {zeta : F} (hzeta : IsPrimitiveRoot zeta m)
    (a : Fin m → Polynomial F) (g : Polynomial F)
    (hrel : ∑ i : Fin m, (XCardMk F) (a i) * ((XCardMk F) g) ^ (i : ℕ) = 0) :
    (firstBlockSymmetric zeta a).eval₂ (XCardMk F) (((XCardMk F) g) ^ m) = 0 := by
  have hA := mapped_firstBlockPolynomial_eval_eq_zero a g hrel
  have hB := map_orbit_eval_zero_of_map_A_eval_zero
    (XCardMk F) (C zeta) (firstBlockPolynomial a) ((XCardMk F) g) hm hA
  change eval ((XCardMk F) g) (map (XCardMk F) (firstBlockOrbitProduct zeta a)) = 0 at hB
  rw [firstBlockOrbit_eq_symmetric_comp hm hzeta, eval_map, eval₂_comp] at hB
  simpa using hB

/-- The cleared expression vanishes modulo `X^q`.-/
theorem firstBlockCleared_quotient_eq_zero
    {m : ℕ} (hm : 0 < m) (hmq : m ∣ Fintype.card F - 1)
    {zeta : F} (hzeta : IsPrimitiveRoot zeta m)
    (a : Fin m → Polynomial F) (f : Polynomial F)
    (hrel : ∑ i : Fin m, (XCardMk F) (a i) *
      ((XCardMk F) (f ^ ((Fintype.card F - 1) / m))) ^ (i : ℕ) = 0) :
    (XCardMk F) (firstBlockCleared zeta a f) = 0 := by
  have hG := firstBlockSymmetric_quotient_eval_eq_zero hm hzeta a
    (f ^ ((Fintype.card F - 1) / m)) hrel
  rw [map_pow, ← pow_mul, Nat.div_mul_cancel hmq] at hG
  have hdeg : (firstBlockSymmetric zeta a).natDegree < m :=
    lt_of_le_of_lt (firstBlockSymmetric_natDegree_le hm hzeta a) (by omega)
  rw [eval₂_eq_sum_range' (XCardMk F) hdeg] at hG
  calc
    (XCardMk F) (firstBlockCleared zeta a f) =
        ((XCardMk F) f) ^ (m - 1) *
          ∑ i ∈ Finset.range m, (XCardMk F) ((firstBlockSymmetric zeta a).coeff i) *
            (((XCardMk F) f) ^ (Fintype.card F - 1)) ^ i := by
      simp only [firstBlockCleared, map_sum, map_mul, map_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ m - 1 := by have := Finset.mem_range.mp hi; omega
      have hp := pow_mul_card_sub_one_pow ((XCardMk F) f)
        (q := Fintype.card F) Fintype.card_pos hi'
      have hf : ((XCardMk F) f) ^ Fintype.card F = (XCardMk F) (C (f.eval 0)) := by
        rw [← map_pow, XCardMk_pow_card]
      rw [hf] at hp
      calc
        _ = (XCardMk F) ((firstBlockSymmetric zeta a).coeff i) *
            (((XCardMk F) (C (f.eval 0))) ^ i * ((XCardMk F) f) ^ (m - 1 - i)) := by ring
        _ = _ := by rw [← hp]; ring
    _ = 0 := by rw [hG, mul_zero]

/-- A polynomial of degree below `q` with zero image modulo `X^q` is zero.-/
theorem eq_zero_of_XCardMk_eq_zero {P : Polynomial F}
    (hdeg : P.natDegree < Fintype.card F) (hzero : (XCardMk F) P = 0) : P = 0 := by
  apply Polynomial.eq_zero_of_dvd_of_natDegree_lt
    (AdjoinRoot.mk_eq_zero.mp hzero)
  simpa using hdeg

/-- The polynomial equality immediately preceding LN97 (6.20).-/
theorem firstBlockCleared_eq_zero
    {m D : ℕ} (hm : 0 < m) (hmq : m ∣ Fintype.card F - 1)
    {zeta : F} (hzeta : IsPrimitiveRoot zeta m)
    (a : Fin m → Polynomial F) (ha : ∀ i, (a i).natDegree ≤ D)
    (f : Polynomial F)
    (hbudget : m * D + (m - 1) * f.natDegree < Fintype.card F)
    (hrel : ∑ i : Fin m, (XCardMk F) (a i) *
      ((XCardMk F) (f ^ ((Fintype.card F - 1) / m))) ^ (i : ℕ) = 0) :
    firstBlockCleared zeta a f = 0 := by
  exact eq_zero_of_XCardMk_eq_zero
    ((firstBlockCleared_natDegree_le hm zeta a ha f).trans_lt hbudget)
    (firstBlockCleared_quotient_eq_zero hm hmq hzeta a f hrel)

/-- **LN97 (6.20)** as an evaluation in `F(X)`.  The coefficients are
the actual contraction coefficients from (6.19), and the argument is
`f(0) / f`.  The nonzero-constant-term hypothesis used later in the book
is not needed until the Kummer-root step; here `f ≠ 0` suffices.-/
theorem ln97_6_20
    {m D : ℕ} (hm : 0 < m) (hmq : m ∣ Fintype.card F - 1)
    {zeta : F} (hzeta : IsPrimitiveRoot zeta m)
    (a : Fin m → Polynomial F) (ha : ∀ i, (a i).natDegree ≤ D)
    (f : Polynomial F) (hf : f ≠ 0)
    (hbudget : m * D + (m - 1) * f.natDegree < Fintype.card F)
    (hrel : ∑ i : Fin m, (XCardMk F) (a i) *
      ((XCardMk F) (f ^ ((Fintype.card F - 1) / m))) ^ (i : ℕ) = 0) :
    (firstBlockSymmetric zeta a).eval₂ (algebraMap (Polynomial F) (RatFunc F))
      ((algebraMap (Polynomial F) (RatFunc F)) (C (f.eval 0)) /
        (algebraMap (Polynomial F) (RatFunc F)) f) = 0 := by
  have hzero := firstBlockCleared_eq_zero hm hmq hzeta a ha f hbudget hrel
  have hf' : (algebraMap (Polynomial F) (RatFunc F)) f ≠ 0 :=
    RatFunc.algebraMap_ne_zero hf
  have hmap := firstBlockCleared_map_eq_mul_eval₂
    (algebraMap (Polynomial F) (RatFunc F)) hm hzeta a f hf'
  rw [hzero, map_zero] at hmap
  exact (mul_eq_zero.mp hmap.symm).resolve_left (pow_ne_zero _ hf')

/-- The displayed finite-sum form of LN97 (6.20).-/
theorem ln97_6_20_sum
    {m D : ℕ} (hm : 0 < m) (hmq : m ∣ Fintype.card F - 1)
    {zeta : F} (hzeta : IsPrimitiveRoot zeta m)
    (a : Fin m → Polynomial F) (ha : ∀ i, (a i).natDegree ≤ D)
    (f : Polynomial F) (hf : f ≠ 0)
    (hbudget : m * D + (m - 1) * f.natDegree < Fintype.card F)
    (hrel : ∑ i : Fin m, (XCardMk F) (a i) *
      ((XCardMk F) (f ^ ((Fintype.card F - 1) / m))) ^ (i : ℕ) = 0) :
    ∑ i ∈ Finset.range m,
      (algebraMap (Polynomial F) (RatFunc F)) ((firstBlockSymmetric zeta a).coeff i) *
        ((algebraMap (Polynomial F) (RatFunc F)) (C (f.eval 0)) /
          (algebraMap (Polynomial F) (RatFunc F)) f) ^ i = 0 := by
  have h := ln97_6_20 hm hmq hzeta a ha f hf hbudget hrel
  have hdeg : (firstBlockSymmetric zeta a).natDegree < m :=
    lt_of_le_of_lt (firstBlockSymmetric_natDegree_le hm hzeta a) (by omega)
  rwa [eval₂_eq_sum_range' _ hdeg] at h

end LN97
end MagicSquares
