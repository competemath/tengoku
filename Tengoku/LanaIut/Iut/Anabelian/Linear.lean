/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transitivity of `SL₂(𝔽_ℓ)` on lines with a marked generator of the quotient

The linear algebra behind the existence of the data `V` and `ε` of initial Θ-data
(IUT IV, proof of Corollary 2.2: "the crucial existence of data `V` and `ε` … follows … as
a consequence of the fact that the Galois action on ℓ-torsion points contains the full
special linear group"): for lines `L, M ⊆ 𝔽_ℓ²` and vectors `g ∉ L`, `q ∉ M`, there is
`A ∈ SL₂(𝔽_ℓ)` with `A·L = M` and `A·g ≡ q (mod M)` (`Iut.Anabelian.exists_sl2`).
-/

namespace Iut.Anabelian

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- Multiplication by a matrix, as an additive homomorphism of `𝔽_ℓ²`. -/
def mulVecHom (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) : (Fin 2 → ZMod ℓ) →+ (Fin 2 → ZMod ℓ) :=
  (Matrix.mulVecLin A).toAddMonoidHom

@[simp] lemma mulVecHom_apply (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (v : Fin 2 → ZMod ℓ) :
    mulVecHom A v = A.mulVec v := rfl

lemma nsmul_self_eq_zero (v : Fin 2 → ZMod ℓ) : ℓ • v = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul]

lemma addOrderOf_eq_of_ne_zero {v : Fin 2 → ZMod ℓ} (hv : v ≠ 0) : addOrderOf v = ℓ :=
  addOrderOf_eq_prime (nsmul_self_eq_zero v) hv

lemma card_zmultiples_of_ne_zero {v : Fin 2 → ZMod ℓ} (hv : v ≠ 0) :
    Nat.card (AddSubgroup.zmultiples v) = ℓ := by
  rw [Nat.card_zmultiples, addOrderOf_eq_of_ne_zero hv]

/-- A nonzero element of a subgroup of order `ℓ` generates it. -/
lemma eq_zmultiples_of_card {L : AddSubgroup (Fin 2 → ZMod ℓ)} (hL : Nat.card L = ℓ)
    {v : Fin 2 → ZMod ℓ} (hv : v ∈ L) (hv0 : v ≠ 0) : L = AddSubgroup.zmultiples v := by
  have hle : AddSubgroup.zmultiples v ≤ L := (AddSubgroup.zmultiples_le).mpr hv
  haveI : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; exact hℓ.out.ne_zero)
  exact (AddSubgroup.eq_of_le_of_card_ge hle (by rw [hL, card_zmultiples_of_ne_zero hv0])).symm

/-- A subgroup of order `ℓ` has a nonzero element. -/
lemma exists_ne_zero_of_card {L : AddSubgroup (Fin 2 → ZMod ℓ)} (hL : Nat.card L = ℓ) :
    ∃ v ∈ L, v ≠ 0 := by
  by_contra h
  push_neg at h
  have hbot : L = ⊥ := (AddSubgroup.eq_bot_iff_forall L).mpr h
  rw [hbot, AddSubgroup.card_bot] at hL
  exact hℓ.out.one_lt.ne hL

/-- Scalar multiples lie in the subgroup generated. -/
lemma smul_mem_zmultiples (c : ZMod ℓ) (v : Fin 2 → ZMod ℓ) :
    c • v ∈ AddSubgroup.zmultiples v := by
  rw [← ZMod.intCast_zmod_cast c, Int.cast_smul_eq_zsmul]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨_, rfl⟩

end Iut.Anabelian
