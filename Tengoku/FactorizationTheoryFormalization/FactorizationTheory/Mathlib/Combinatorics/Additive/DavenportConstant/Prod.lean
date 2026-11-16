/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Tengoku.FactorizationTheoryFormalization.FactorizationTheory.Mathlib.Combinatorics.Additive.DavenportConstant

import Tengoku.FactorizationTheoryFormalization.FactorizationTheory.Mathlib.Combinatorics.Additive.ZeroSum.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Davenport constants of direct products

This file gives the standard lower bound for the Davenport constant of a direct product.

## Main result

* `AddMonoid.add_sub_one_le_davenportConstant_prod`: `D(G) + D(H) - 1 ≤ D(G × H)`.

## References

* [A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic, Combinatorial and
  Analytic Theory*][geroldingerhalterkoch2006]
-/

public section

assert_not_exists Field Ideal

variable {G H : Type*}

namespace AddMonoid

/-- The Davenport constants of two additive commutative monoids satisfy
`D(G) + D(H) - 1 ≤ D(G × H)`.
@isnad1 id=le.0h2v.s5.9f201840fad1 from=translated src=- shape=2062c85c vocab=c90f39b0
-/
theorem add_sub_one_le_davenportConstant_prod [AddCommMonoid G] [AddCommMonoid H] :
    davenportConstant G + davenportConstant H - 1 ≤ davenportConstant (G × H) := by
  have hshifted :
      davenportConstant G + davenportConstant H ≤ davenportConstant (G × H) + 1 := by
    let _ : Nonempty {S : Multiset G // S.IsMinimalZeroSum} :=
      ⟨⟨{0}, Multiset.isMinimalZeroSum_singleton.mpr rfl⟩⟩
    let _ : Nonempty {T : Multiset H // T.IsMinimalZeroSum} :=
      ⟨⟨{0}, Multiset.isMinimalZeroSum_singleton.mpr rfl⟩⟩
    rw [davenportConstant_def, davenportConstant_def]
    apply ENat.iSup_add_iSup_le
    rintro ⟨S, hS⟩ ⟨T, hT⟩
    obtain ⟨g, hg⟩ := Multiset.exists_mem_of_ne_zero hS.ne_zero
    obtain ⟨S', rfl⟩ := Multiset.exists_cons_of_mem hg
    obtain ⟨h, hh⟩ := Multiset.exists_mem_of_ne_zero hT.ne_zero
    obtain ⟨T', rfl⟩ := Multiset.exists_cons_of_mem hh
    have hbound := (hS.prod hT).card_le_davenportConstant
    have hbound' := add_le_add_right hbound 1
    simpa [ENat.natCast_add, add_assoc, add_comm, add_left_comm] using hbound'
  exact (tsub_le_tsub_right hshifted 1).trans_eq
    (ENat.addLECancellable_natCast 1).add_tsub_cancel_right

end AddMonoid
