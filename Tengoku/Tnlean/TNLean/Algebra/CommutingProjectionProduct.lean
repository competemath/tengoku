/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Products of complementary commuting projections

For a finite commuting family of orthogonal projections, the ordered product
of the complementary projections has range equal to the kernel of their sum.
The order of the product is retained in the statement, so the result applies
directly to cyclic chains of local operators.
-/

open scoped BigOperators

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

private theorem apply_list_prod_one_sub_eq_self
    (P : List (E →ₗ[𝕜] E)) (v : E) (hP : ∀ p ∈ P, p v = 0) :
    (P.map fun p ↦ (1 : E →ₗ[𝕜] E) - p).prod v = v := by
  induction P with
  | nil => simp
  | cons p P ih =>
      simp only [List.map_cons, List.prod_cons]
      change (1 - p) ((P.map fun q ↦ (1 : E →ₗ[𝕜] E) - q).prod v) = v
      rw [ih (fun q hq ↦ hP q (List.mem_cons_of_mem p hq))]
      simp [hP p (List.mem_cons_self)]

private theorem mul_list_prod_one_sub_eq_zero
    (P : List (E →ₗ[𝕜] E)) (hcomm : P.Pairwise fun p q ↦ Commute p q)
    (hidem : ∀ p ∈ P, IsIdempotentElem p) {p : E →ₗ[𝕜] E} (hp : p ∈ P) :
    p * (P.map fun q ↦ (1 : E →ₗ[𝕜] E) - q).prod = 0 := by
  induction P with
  | nil => simp at hp
  | cons q P ih =>
      rw [List.pairwise_cons] at hcomm
      simp only [List.map_cons, List.prod_cons]
      rcases List.mem_cons.mp hp with hp | hp
      · subst p
        rw [← mul_assoc, (hidem q (List.mem_cons_self)).mul_one_sub_self, zero_mul]
      · have hpq : Commute p q :=
          (hcomm.1 p hp).symm
        rw [← mul_assoc, ((Commute.one_right p).sub_right hpq).eq, mul_assoc,
          ih hcomm.2 (fun r hr ↦ hidem r (List.mem_cons_of_mem q hr)) hp, mul_zero]

private theorem list_prod_one_sub_isIdempotentElem
    (P : List (E →ₗ[𝕜] E)) (hcomm : P.Pairwise fun p q ↦ Commute p q)
    (hidem : ∀ p ∈ P, IsIdempotentElem p) :
    IsIdempotentElem (P.map fun p ↦ (1 : E →ₗ[𝕜] E) - p).prod := by
  induction P with
  | nil => exact IsIdempotentElem.one
  | cons p P ih =>
      rw [List.pairwise_cons] at hcomm
      simp only [List.map_cons, List.prod_cons]
      have hhead : IsIdempotentElem ((1 : E →ₗ[𝕜] E) - p) :=
        (hidem p List.mem_cons_self).one_sub
      have htail := ih hcomm.2 (fun q hq ↦ hidem q (List.mem_cons_of_mem p hq))
      apply hhead.mul_of_commute _ htail
      apply Commute.list_prod_right
      intro q hq
      rw [List.mem_map] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      exact (Commute.one_left ((1 : E →ₗ[𝕜] E) - r)).sub_left
        ((Commute.one_right p).sub_right (hcomm.1 r hr))

end LinearMap
