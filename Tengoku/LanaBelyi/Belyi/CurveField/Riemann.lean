/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.CurveField.RiemannRochSpace
import Tengoku.Seed.Algebra.Module.Submodule.Union
import Tengoku.Seed.Algebra.Polynomial.Basis
import Tengoku.Seed.Data.Int.ConditionallyCompleteOrder
import Tengoku.Seed.FieldTheory.Minpoly.Field
import Tengoku.Seed.RingTheory.AlgebraTower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Riemann's theorem

For a curve field `K` (with degrees and dimensions taken over `ℚ`), the function
`A ↦ deg A - ℓ(A)` on divisors is bounded above (*Riemann's inequality*); its maximum
`Belyi.CurveField.Divisor.riemannConst K` is attained, and `ℓ(A) = deg A - riemannConst K`
as soon as `deg A` is large (*Riemann's theorem*). (If `k` is the constant field of `K` and
`g` the genus, then `riemannConst K = [k : ℚ] (g - 1)`; we do not need this.)

We follow H. Stichtenoth, *Algebraic Function Fields and Codes*, Ch. 1 §1.4
(Proposition 1.4.14, Lemma 1.4.15, Proposition 1.4.16, Theorem 1.4.17), with the following
simplifications: for `x ∈ K` transcendental with divisor of poles `B = (x)_∞`, a basis
`u_1, …, u_n` of `K / ℚ(x)` and `C = ∑ (u_i)_∞`, the `(l + 1) n` elements `x^k u_i`
(`k ≤ l`) are `ℚ`-linearly independent elements of `L(l B + C)`; this bounds
`deg (l B) - ℓ(l B)` uniformly in `l`. Every divisor `A` is linearly equivalent to a divisor
`≤ l B` for some `l`: add the places one at a time, using `B` at the poles of `x` and the
function `p(x)`, `p` the minimal polynomial over `ℚ` of the residue of `x`, at the others.

Consequences:

* **Realisation of polar divisors** (`Belyi.CurveField.Divisor.exists_polarDivisor_eq`):
  every effective divisor of large degree is the divisor of poles of a function. Indeed for
  `P` in the support of `A` the subspace `L(A - P)` of `L(A)` is proper, and a `ℚ`-vector
  space is not a finite union of proper subspaces.
* every divisor is a difference of two polar divisors
  (`Belyi.CurveField.Divisor.exists_eq_polarDivisor_sub_polarDivisor`);
* a multiple of a divisor of positive degree is linearly equivalent to a polar divisor
  (`Belyi.CurveField.Divisor.exists_polarDivisor_eq_nsmul_add_div`).
-/

open Polynomial IsLocalRing
open scoped IntermediateField

namespace Belyi.CurveField

namespace Divisor

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-! ### Polynomials in a function -/

theorem pow_mem_L (x : K) (k : ℕ) : x ^ k ∈ L (k • polarDivisor x) := by
  refine Or.inr fun P ↦ ?_
  simp only [Finsupp.coe_smul, Pi.smul_apply, polarDivisor_apply, nsmul_eq_mul, Place.ord_pow]
  have h1 := le_max_right 0 (-P.ord x)
  have h2 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  nlinarith

/-- A polynomial of degree `≤ d` in `x` lies in `L(d (x)_∞)`. -/
theorem aeval_mem_L (x : K) (p : ℚ[X]) : aeval x p ∈ L (p.natDegree • polarDivisor x) := by
  rw [aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ (L_mono ?_ (pow_mem_L x i))
  exact nsmul_le_nsmul_left (polarDivisor_nonneg x)
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- At a place `P` where `x` is regular, `p(x)` vanishes for `p` the minimal polynomial of the
residue of `x`. -/
theorem exists_aeval_ord_pos {x : K} (hx : Transcendental ℚ x) (P : Place K) (hxP : x ∈ P.1) :
    ∃ p : ℚ[X], aeval x p ≠ 0 ∧ 0 < P.ord (aeval x p) := by
  set r := P.residue ⟨x, hxP⟩
  have hint : IsIntegral ℚ r := Algebra.IsIntegral.isIntegral r
  set p := minpoly ℚ r
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  have hy0 : aeval x p ≠ 0 := fun h ↦ hx ⟨p, hp0, h⟩
  refine ⟨p, hy0, ?_⟩
  set e : P.1 := p.eval₂ P.ratHom ⟨x, hxP⟩
  have hcomp : P.1.subtype.comp P.ratHom = algebraMap ℚ K := by
    ext q; simp [ValuationSubring.subtype]
  have he : (e : K) = aeval x p := by
    rw [aeval_def, ← hcomp]
    exact Polynomial.hom_eval₂ p P.ratHom P.1.subtype ⟨x, hxP⟩
  have hcomp' : P.residue.comp P.ratHom = algebraMap ℚ P.ResidueField := by
    ext q; simp
  have hres : P.residue e = 0 := by
    rw [Polynomial.hom_eval₂, hcomp', ← aeval_def]
    exact minpoly.aeval ℚ r
  rw [← he]
  refine (P.ord_pos_iff_mem_maximalIdeal (a := e) (by rw [he]; exact hy0)).mpr ?_
  exact P.residue_eq_zero_iff.mp hres

/-! ### Reduction to multiples of a polar divisor -/

section Reduction

variable {x : K} (hx : Transcendental ℚ x)
include hx

omit hx in
theorem single_le_polarDivisor {P : Place K} (hP : P.ord x < 0) :
    Finsupp.single P 1 ≤ polarDivisor x := by
  classical
  intro Q
  by_cases hQ : P = Q
  · subst hQ; simp only [Finsupp.single_eq_same, polarDivisor_apply]; omega
  · rw [Finsupp.single_apply, ite_eq_right hQ]; exact polarDivisor_nonneg x Q

theorem exists_add_single_add_div_le {A : Divisor K} (P : Place K)
    (h : ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + div z ≤ l • polarDivisor x) :
    ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + Finsupp.single P 1 + div z ≤ l • polarDivisor x := by
  classical
  obtain ⟨z, hz, l, hl⟩ := h
  by_cases hP : P.ord x < 0
  · refine ⟨z, hz, l + 1, ?_⟩
    rw [succ_nsmul, show A + Finsupp.single P 1 + div z = (A + div z) + Finsupp.single P 1 by
      abel]
    exact add_le_add hl (single_le_polarDivisor hP)
  obtain ⟨p, hy0, hypos⟩ := exists_aeval_ord_pos hx P (P.mem_of_ord_nonneg (not_lt.mp hP))
  have hyL := (mem_L.mp (aeval_mem_L x p)).resolve_left hy0
  refine ⟨z / aeval x p, div_ne_zero hz hy0, l + p.natDegree, ?_⟩
  rw [div_div hz hy0, add_nsmul, show A + Finsupp.single P 1 + (div z - div (aeval x p)) =
    (A + div z) + (Finsupp.single P 1 - div (aeval x p)) by abel]
  refine add_le_add hl fun Q ↦ ?_
  have h1 := hyL Q
  have h2 := (nsmul_nonneg (polarDivisor_nonneg x) p.natDegree) Q
  simp only [Finsupp.coe_sub, Pi.sub_apply, div_apply, Finsupp.coe_zero,
    Pi.zero_apply] at h1 h2 ⊢
  by_cases hQ : P = Q
  · subst hQ; rw [Finsupp.single_eq_same]; omega
  · rw [Finsupp.single_apply, ite_eq_right hQ]; omega

theorem exists_add_single_nat_add_div_le {A : Divisor K} (P : Place K) (m : ℕ)
    (h : ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + div z ≤ l • polarDivisor x) :
    ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + Finsupp.single P (m : ℤ) + div z ≤ l • polarDivisor x := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    have := exists_add_single_add_div_le hx P ih
    rwa [Nat.cast_succ, Finsupp.single_add, ← add_assoc]

/-- Every divisor is linearly equivalent to a divisor `≤ l (x)_∞` for some `l`
(Stichtenoth, proof of Proposition 1.4.14). -/
theorem exists_add_div_le (A : Divisor K) :
    ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + div z ≤ l • polarDivisor x := by
  classical
  induction A using Finsupp.induction with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | single_add P b f _ _ ih =>
    rcases le_or_gt b 0 with hb | hb
    · obtain ⟨z, hz, l, hl⟩ := ih
      refine ⟨z, hz, l, le_trans ?_ hl⟩
      rw [add_assoc]
      refine add_le_of_nonpos_left fun Q ↦ ?_
      rw [Finsupp.single_apply]
      split_ifs <;> simp [hb]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb.le
      rw [add_comm]
      exact exists_add_single_nat_add_div_le hx P m ih

end Reduction

/-! ### Riemann's theorem -/

variable (K) in
/-- The constant `max_A (deg A - ℓ(A))` of Riemann's theorem (it equals `[k : ℚ](g - 1)`,
for `k` the constant field and `g` the genus). -/
noncomputable def riemannConst : ℤ := sSup (Set.range fun A : Divisor K ↦ A.deg - (ell A : ℤ))

/-! ### Realisation of polar divisors -/

/-- The positive part `∑ max(A(P), 0) P` of a divisor. -/
noncomputable def posPart (A : Divisor K) : Divisor K :=
  Finsupp.mapRange (fun n ↦ max n 0) (by simp) A

omit [CharZero K] [IsCurveField K] in
theorem posPart_apply (A : Divisor K) (P : Place K) : posPart A P = max (A P) 0 :=
  Finsupp.mapRange_apply ..

omit [CharZero K] [IsCurveField K] in
theorem posPart_nonneg (A : Divisor K) : 0 ≤ posPart A := fun P ↦ by
  simp [posPart_apply]

omit [CharZero K] [IsCurveField K] in
theorem posPart_sub_posPart_neg (A : Divisor K) : posPart A - posPart (-A) = A := by
  ext P
  simp only [Finsupp.coe_sub, Pi.sub_apply, posPart_apply, Finsupp.coe_neg, Pi.neg_apply]
  omega

end Divisor

end Belyi.CurveField
