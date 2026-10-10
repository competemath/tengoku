/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku

/-!
# Coefficient semirings with exact polynomial support

Polynomial support is functorial for semirings in which a sum is zero only
when both summands are zero and nonzero factors have nonzero product.  This
module packages the missing zero-sum condition, proves exact support laws for
addition, multiplication, and substitution, and supplies cross-coefficient
congruence: substitutions over two such semirings have the same support when
their source and variable-image supports agree.

Both `Nat` and the nonnegative rationals satisfy these assumptions.  The
cross-coefficient theorem is the bridge used to transport natural-coefficient
Schnorr combinatorics to nonnegative-rational arithmetic circuits.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace ExactSupport

open scoped Pointwise

noncomputable section

/-- A zero-sum-free additive structure: no two nonzero elements cancel. -/
class ZeroSumFree (R : Type u) [Add R] [Zero R] : Prop where
  add_eq_zero_iff : ∀ left right : R,
    left + right = 0 ↔ left = 0 ∧ right = 0

instance : ZeroSumFree ℕ where
  add_eq_zero_iff := fun _ _ => Nat.add_eq_zero_iff

instance : ZeroSumFree ℚ≥0 where
  add_eq_zero_iff := by
    intro left right
    constructor
    · intro sumZero
      have coercedZero : (left : ℚ) + (right : ℚ) = 0 := by
        rw [← NNRat.coe_add, sumZero, NNRat.coe_zero]
      have parts := (add_eq_zero_iff_of_nonneg
        (NNRat.coe_nonneg left) (NNRat.coe_nonneg right)).mp coercedZero
      exact ⟨NNRat.coe_eq_zero.mp parts.1,
        NNRat.coe_eq_zero.mp parts.2⟩
    · rintro ⟨rfl, rfl⟩
      simp

/-- A finite sum in a zero-sum-free commutative monoid vanishes exactly when
every summand vanishes. -/
theorem finset_sum_eq_zero_iff
    [AddCommMonoid R]
    [ZeroSumFree R]
    (indices : Finset Index)
    (value : Index → R) :
    (∑ index ∈ indices, value index) = 0 ↔
      ∀ index ∈ indices, value index = 0 := by
  classical
  induction indices using Finset.induction with
  | empty => simp
  | @insert index indices absent inductionHypothesis =>
      rw [Finset.sum_insert absent,
        ZeroSumFree.add_eq_zero_iff,
        inductionHypothesis]
      simp

section OneCoefficient

variable [CommSemiring R] [Nontrivial R]
variable [NoZeroDivisors R] [ZeroSumFree R]

omit [Nontrivial R] [NoZeroDivisors R] in
/-- Exact support of addition over a zero-sum-free coefficient semiring. -/
theorem polynomial_support_add
    [DecidableEq Variable]
    (left right : MvPolynomial Variable R) :
    (left + right).support = left.support ∪ right.support := by
  ext exponent
  simp only [MvPolynomial.mem_support_iff,
    AddMonoidAlgebra.coeff_add, Finset.mem_union]
  constructor
  · intro sumNonzero
    by_cases leftNonzero : AddMonoidAlgebra.coeff left exponent ≠ 0
    · exact Or.inl leftNonzero
    · right
      intro rightZero
      apply sumNonzero
      exact (ZeroSumFree.add_eq_zero_iff _ _).mpr
        ⟨not_ne_iff.mp leftNonzero, rightZero⟩
  · intro eitherNonzero sumZero
    have bothZero := (ZeroSumFree.add_eq_zero_iff _ _).mp sumZero
    exact eitherNonzero.elim
      (fun leftNonzero => leftNonzero bothZero.1)
      (fun rightNonzero => rightNonzero bothZero.2)

omit [Nontrivial R] [NoZeroDivisors R] in
/-- Exact support of a finite polynomial sum. -/
theorem support_finset_sum
    [DecidableEq Variable]
    (indices : Finset Index)
    (polynomial : Index → MvPolynomial Variable R) :
    (∑ index ∈ indices, polynomial index).support =
      indices.biUnion fun index => (polynomial index).support := by
  classical
  induction indices using Finset.induction with
  | empty => simp
  | @insert index indices absent inductionHypothesis =>
      rw [Finset.sum_insert absent, polynomial_support_add,
        inductionHypothesis]
      simp

/-- Expansion of one coefficient-one source monomial under substitution. -/
def monomialExpansion
    (substitution : SourceVar → MvPolynomial TargetVar R)
    (exponent : SourceVar →₀ ℕ) : MvPolynomial TargetVar R :=
  MvPolynomial.bind₁ substitution (MvPolynomial.monomial exponent 1)

end OneCoefficient

section CrossCoefficient

variable [CommSemiring R] [Nontrivial R]
variable [NoZeroDivisors R] [ZeroSumFree R]
variable [CommSemiring S] [Nontrivial S]
variable [NoZeroDivisors S] [ZeroSumFree S]

end CrossCoefficient

end
end ExactSupport
end Arithmetic
end Fusion
end Algebraic
