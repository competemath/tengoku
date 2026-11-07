/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Seed.LinearAlgebra.Eigenspace.Semisimple
import Tengoku.Seed.LinearAlgebra.Trace
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Semisimple Endomorphisms with Rank-One Trace Powers

This file isolates the finite-dimensional linear algebra used in the
Jordan--Chevalley step of arXiv:1706.07329v2, Proposition 20, lines 3839--3866.

A semisimple complex endomorphism has one-dimensional range when a nonzero
scalar multiple has trace one at every power above one. The proof applies
QICLean's shifted trace-power characteristic-polynomial theorem to a matrix in
an arbitrary basis. Semisimplicity identifies the generalized zero-eigenspace
with the kernel, and root multiplicity together with rank--nullity then gives
the range dimension.

A commuting nilpotent endomorphism preserves this one-dimensional range. Its
restriction is a scalar endomorphism, whose nilpotence forces that scalar to
vanish. Thus the nilpotent and semisimple parts annihilate one another in both
orders, and sufficiently high powers of their sum are powers of the
semisimple part alone.

No normality, Hermitianity, positivity, or chosen-basis hypothesis is used.

## Reference

* [Molnar--Ge--Schuch--Cirac 2018] arXiv:1706.07329v2, Proposition 20,
  lines 3839--3866
-/

open Polynomial

namespace Module.End

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- A commuting nilpotent summand does not change trace powers.

The commuting binomial expansion has one term without the nilpotent summand.
Every other term is nilpotent and therefore has zero trace. This is the trace
reduction used in arXiv:1706.07329v2, Proposition 20, line 3865.
@isnad1 id=eq.2h4v.s9.e3664366022e from=translated src=- shape=1c2799be vocab=a1adb454
-/
theorem IsNilpotent.trace_add_pow_eq_trace_pow_of_commute
    {N : Module.End ℂ V} (hN : IsNilpotent N) (S : Module.End ℂ V)
    (hcomm : Commute N S) (k : ℕ) :
    LinearMap.trace ℂ V ((N + S) ^ k) = LinearMap.trace ℂ V (S ^ k) := by
  rw [hcomm.add_pow k, map_sum]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro m _ hm
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    apply IsNilpotent.eq_zero
    apply LinearMap.isNilpotent_trace_of_isNilpotent
    rw [pow_succ']
    simp only [mul_assoc]
    apply Commute.isNilpotent_mul_right _ hN
    exact ((Commute.refl N).pow_right n).mul_right
      ((hcomm.pow_right (k - (n + 1))).mul_right (Nat.commute_cast N (k.choose (n + 1))))
  · simp

/-- A nilpotent endomorphism commuting with an endomorphism of one-dimensional
range annihilates it in both orders.

The nilpotent map restricts to the range because of commutation. Every
endomorphism of that one-dimensional range is scalar, and a nilpotent scalar
over `ℂ` is zero.
@isnad1 id=and.3h3v.s8.686c608850e2 from=translated src=- shape=87ddb3c8 vocab=a2984099
-/
theorem IsNilpotent.mul_eq_zero_and_mul_eq_zero_of_commute_of_finrank_range_eq_one
    {N : Module.End ℂ V} (hN : IsNilpotent N) (S : Module.End ℂ V)
    (hcomm : Commute N S) (hrank : Module.finrank ℂ S.range = 1) :
    N * S = 0 ∧ S * N = 0 := by
  have hmaps : Set.MapsTo N S.range S.range := by
    rintro _ ⟨x, rfl⟩
    refine ⟨N x, ?_⟩
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hcomm.eq]
  let R : Module.End ℂ S.range := N.restrict hmaps
  have hRnil : IsNilpotent R := Module.End.isNilpotent.restrict hmaps hN
  obtain ⟨a, ha, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hrank R
  have htr : LinearMap.trace ℂ S.range R = 0 :=
    IsNilpotent.eq_zero (LinearMap.isNilpotent_trace_of_isNilpotent hRnil)
  have ha0 : a = 0 := by
    rw [ha, map_smul, LinearMap.trace_id, hrank, Nat.cast_one] at htr
    simpa using htr
  have hRzero : R = 0 := by rw [ha, ha0, zero_smul]
  have hNS : N * S = 0 := by
    ext x
    have hx :=
      LinearMap.congr_fun hRzero (⟨S x, LinearMap.mem_range_self S x⟩ : S.range)
    dsimp [R] at hx
    exact congrArg Subtype.val hx
  exact ⟨hNS, hcomm.eq ▸ hNS⟩

private lemma add_pow_eq_pow_add_pow_of_mul_eq_zero {R : Type*} [Semiring R]
    (x y : R) (hxy : x * y = 0) (hyx : y * x = 0) {k : ℕ} (hk : 0 < k) :
    (x + y) ^ k = x ^ k + y ^ k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih (by omega)]
      simp [add_mul, mul_add, mul_assoc, hxy, hyx, pow_succ]

omit [FiniteDimensional ℂ V] in
/-- If two endomorphisms annihilate one another and the first is nilpotent,
then sufficiently high powers of their sum are powers of the second alone.
@isnad1 id=ex.3h3v.s8.7b1cdc22d1d4 from=translated src=- shape=6a7f3843 vocab=6c8ce18e
-/
theorem IsNilpotent.exists_add_pow_eq_right_of_mul_eq_zero
    {N : Module.End ℂ V} (hN : IsNilpotent N) (S : Module.End ℂ V)
    (hNS : N * S = 0) (hSN : S * N = 0) :
    ∃ J : ℕ, 0 < J ∧ ∀ k : ℕ, J ≤ k → (N + S) ^ k = S ^ k := by
  obtain ⟨j, hj⟩ := hN
  refine ⟨max 1 j, by omega, ?_⟩
  intro k hk
  rw [add_pow_eq_pow_add_pow_of_mul_eq_zero N S hNS hSN (by omega),
    pow_eq_zero_of_le (le_trans (Nat.le_max_right 1 j) hk) hj, zero_add]

end Module.End
