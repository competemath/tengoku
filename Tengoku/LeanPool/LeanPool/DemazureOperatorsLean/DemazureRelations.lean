/-
Copyright (c) 2026 Óscar Álvarez Sánchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Óscar Álvarez Sánchez
-/
module

public import Tengoku.LeanPool.LeanPool.DemazureOperatorsLean.DemazureAuxRelations
public import Tengoku

/-!
# LeanPool.DemazureOperatorsLean.DemazureRelations
-/

@[expose] public section

noncomputable section
open MvPolynomial

namespace Demazure

variable {n : ℕ} (n_pos : n > 0) (n_gt_1 : n > 1)

/- Now we prove the relations for the actual Demazure operator on polynomials.
There isn't a lot of math going on here, we just take the results from DemAux and
translate them to Demazure-/

-- Demazure operator has order two
/--
@isnad1 id=eq.0h3v.s9.389b9a4c7599 from=translated src=- shape=3b8ef8c2 vocab=e03ff9d4
-/
lemma demazure_order_two : ∀ (i : Fin n) (p : MvPolynomial (Fin (n + 1)) ℂ),
  DemazureLinear i (DemazureLinear i p) = 0 := by
  intro i p
  apply eq_zero_of_mk'_zero.mp
  dsimp [DemazureLinear]
  rw[← demazure_definitions_equivalent]
  rw[← demazure_definitions_equivalent]
  exact demaux_order_two i (mk' p)

-- Demazure operators with adjacent indices have a braid relation
/--
@isnad1 id=eq.1h3v.s11.d667ca9cc076 from=translated src=- shape=4f80a336 vocab=8bdd6d74
-/
lemma demazure_commutes_adjacent (i : Fin n) (h : i + 1 < n) : ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
  (DemazureLinear i ∘ DemazureLinear ⟨i+1, h⟩ ∘ DemazureLinear i) p =
    (DemazureLinear ⟨i+1, h⟩ ∘ DemazureLinear i ∘ DemazureLinear ⟨i+1, h⟩) p := by
  intro p
  dsimp [DemazureLinear]
  apply eq_of_eq_mk'.mp
  repeat rw[← demazure_definitions_equivalent]
  apply demaux_commutes_adjacent

-- Demazure operators with non-adjacent indices commute
/--
@isnad1 id=eq.1h4v.s10.55ee021fcac5 from=translated src=- shape=6a197019 vocab=158a4dde
-/
lemma demazure_commutes_non_adjacent (i j : Fin n) (h : NonAdjacent i j) :
    ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
      (DemazureLinear i ∘ DemazureLinear j) p = (DemazureLinear j ∘ DemazureLinear i) p := by
  intro p
  dsimp [DemazureLinear]
  apply eq_of_eq_mk'.mp
  repeat rw[← demazure_definitions_equivalent]
  apply demaux_commutes_non_adjacent
  exact h

-- Relation between demazure operator and multiplication by non-adjacent monomials
/--
@isnad1 id=eq.1h4v.s9.9de15057cd0d from=translated src=- shape=c4fe3dd2 vocab=01339f5b
-/
lemma demazure_mul_monomial_non_adjacent (i j : Fin n) (h : NonAdjacent i j) :
    ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
      DemazureLinear i (p * X (Fin.castSucc j)) =
        (DemazureLinear i p) * (X (Fin.castSucc j)) := by
  intro p
  dsimp [DemazureLinear]
  apply eq_of_eq_mk'.mp
  repeat rw[← demazure_definitions_equivalent]
  rw[← mk'_mul]
  rw[← mk'_mul]
  rw[← demazure_definitions_equivalent]
  rw[mk'_mul]
  apply demaux_mul_monomial_non_adjacent i j h

-- Relation between demazure operator and multiplication by adjacent monomial
/--
@isnad1 id=eq.1h3v.s10.07ba447da211 from=translated src=- shape=bd83a9c8 vocab=6371c536
-/
lemma demazure_mul_monomial_adjacent (i : Fin n) (h : i + 1 < n) :
    ∀ p : MvPolynomial (Fin (n + 1)) ℂ,
      (DemazureLinear i (p * X (Fin.castSucc i))) =
        (DemazureLinear i p) * (X (Fin.succ i)) + p := by
  intro p
  dsimp [DemazureLinear]
  apply eq_of_eq_mk'.mp
  rw[mk'_add]
  rw[← mk'_mul]
  repeat rw[← demazure_definitions_equivalent]
  apply demaux_mul_monomial_adjacent i h

-- Symmetric polynomials act as scalars wrt Demazure operators
/--
@isnad1 id=eq.1h4v.s9.90219d81dd05 from=translated src=- shape=0ef09776 vocab=90f44c47
-/
lemma demazure_mul_symm (i : Fin n) (g f : MvPolynomial (Fin (n + 1)) ℂ)
    (h : MvPolynomial.IsSymmetric g) :
    DemazureLinear i (g*f) = g*(DemazureLinear i f) := by
  dsimp [DemazureLinear]
  rw[← eq_of_eq_mk']
  rw[← demazure_definitions_equivalent]
  rw [← mk'_mul]
  rw [← mk'_mul]
  rw[← demazure_definitions_equivalent]
  have : IsSymmetric (mk' g) := by
    dsimp [IsSymmetric]
    use (toFrac g)
    dsimp [toFrac]
    exact ⟨rfl, h, MvPolynomial.IsSymmetric.one⟩
  exact demaux_mul_symm i (mk' g) (mk' f) this

/- This enables to define the Demazure operator as a linear map over the ring of
symmetric polynomials, the main result of this project -/
/-- The Demazure operator as a linear map over the symmetric-polynomial subalgebra. -/
def Dem (i : Fin n) : LinearMap (RingHom.id (MvPolynomial.symmetricSubalgebra (Fin (n + 1)) ℂ))
 (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (n + 1)) ℂ) where
  toFun := DemazureFun i
  map_add' := demazure_map_add i
  map_smul' := by
    intro r x
    simp only [RingHom.id_apply]
    let p : MvPolynomial (Fin (n + 1)) ℂ := r
    have wah : p = r := by rfl
    have h : MvPolynomial.IsSymmetric p := by
      apply (MvPolynomial.mem_symmetricSubalgebra p).mp
      rw[wah]
      exact SetLike.coe_mem r
    exact demazure_mul_symm i p x h

end Demazure

end
