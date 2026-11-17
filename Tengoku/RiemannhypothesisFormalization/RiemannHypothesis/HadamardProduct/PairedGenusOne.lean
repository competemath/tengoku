/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.InfiniteProducts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pairing opposite genus-one factors

For a divisor stable under `ρ ↦ -ρ`, the exponential regularizers in
the two genus-one factors cancel.  The identities here isolate exactly what
the pairing proves; no lower bound for the resulting product is asserted.
-/

namespace OverflowResidueRH

/-- Negating a zero location is the same as negating the argument of its
genus-one factor.
@isnad1 id=eq.0h2v.s4.55ec7e2d995a from=translated src=- shape=04c242a7 vocab=831130ca
-/
theorem hadamardGenus1Factor_neg_location (ρ z : ℂ) :
    hadamardGenus1Factor (-ρ) z = hadamardGenus1Factor ρ (-z) := by
  unfold hadamardGenus1Factor
  rw [div_neg, neg_div]

/-- The paired genus-one factors reduce to a quadratic genus-zero factor.
@isnad1 id=eq.1h2v.s6.cab03f7dd21f from=translated src=- shape=e53ebf5f vocab=2e966eac
-/
theorem hadamardGenus1Factor_mul_neg_location
    {ρ z : ℂ} (hρ : ρ ≠ 0) :
    hadamardGenus1Factor ρ z * hadamardGenus1Factor (-ρ) z =
      1 - (z / ρ) ^ 2 := by
  rw [hadamardGenus1Factor_neg_location]
  unfold hadamardGenus1Factor
  rw [neg_div, Complex.exp_neg]
  have hexp : Complex.exp (z / ρ) ≠ 0 := Complex.exp_ne_zero _
  field_simp [hexp]
  ring

/-- Reindexing an infinite genus-one product by an exact negation
involution makes it even.  This statement is unconditional because
Mathlib's totalized `tprod` is invariant under equivalence reindexing.
@isnad1 id=eq.1h4v.s5.4634cfd44dff from=translated src=- shape=08f0c87f vocab=3c1559ce
-/
theorem infiniteHadamardProduct_even_of_neg_equiv
    {ι : Type*} (zeroLoc : ι → ℂ) (e : ι ≃ ι)
    (he : ∀ i : ι, zeroLoc (e i) = -zeroLoc i) (z : ℂ) :
    infiniteHadamardProduct zeroLoc (-z) =
      infiniteHadamardProduct zeroLoc z := by
  unfold infiniteHadamardProduct
  calc
    ∏' i : ι, hadamardGenus1Factor (zeroLoc i) (-z) =
        ∏' i : ι, hadamardGenus1Factor (zeroLoc (e i)) z := by
      apply tprod_congr
      intro i
      rw [he i]
      exact (hadamardGenus1Factor_neg_location (zeroLoc i) z).symm
    _ = ∏' i : ι, hadamardGenus1Factor (zeroLoc i) z :=
      e.tprod_eq (fun i : ι ↦ hadamardGenus1Factor (zeroLoc i) z)

end OverflowResidueRH
