/-
# The signed circle product, and the Maurer–Cartan equation

`Operad.Total` builds the *ungraded* circle product `α ⋆ β = ∑ᵢ α ∘ᵢ β`, and `Operad.PreLie`
proves it right pre-Lie. That structure is correct, but it cannot express deformation theory,
for a reason worth stating precisely.

Write `Θ` for a binary operation, so `Θ ∈ P 2`. Then `Θ ⋆ Θ = Θ ∘₀ Θ + Θ ∘₁ Θ`, so `Θ ⋆ Θ = 0`
says `Θ ∘₀ Θ = -(Θ ∘₁ Θ)`: *anti*-associativity, not associativity. The Maurer–Cartan equation
only means what it should once the circle product carries the signs of the operadic suspension.

Those signs are `(-1)^(a * k)`, where `a` is the slot (counting from zero) and `k` is the degree
of the inserted operation — that is, its arity minus one. With them, `Θ ⋆ₛ Θ = Θ ∘₀ Θ - Θ ∘₁ Θ`,
and `Θ ⋆ₛ Θ = 0` is exactly associativity.
-/
import Tengoku.LeanOperads.Operad.Total
import Tengoku.Seed.Algebra.BigOperators.GroupWithZero.Action

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

namespace Operad

open NSOperad Finset

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-- The signed circle product `α ⋆ₛ β = ∑ₐ (-1)^(a * k) • (α ∘ₐ β)`, where `k` is the degree of
`β`. This is the operadic suspension's product; `Operad.star` is the same sum with every sign
replaced by `1`.-/
def sstar {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) : P (j + k + 1) :=
  ∑ a : Fin (j + 1), ((-1 : R) ^ ((a : ℕ) * k)) • compFin (R := R) a α β

@[inherit_doc] scoped infixl:70 " ⋆ₛ " => sstar

lemma sstar_def {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) :
    sstar (R := R) α β = ∑ a : Fin (j + 1), ((-1 : R) ^ ((a : ℕ) * k)) • compFin (R := R) a α β :=
  rfl

/-! ### Bilinearity -/

lemma sstar_add_left {j k : ℕ} (α α' : P (j + 1)) (β : P (k + 1)) :
    sstar (R := R) (α + α') β = sstar (R := R) α β + sstar (R := R) α' β := by
  simp only [sstar_def, compFin_add_left, smul_add]
  rw [Finset.sum_add_distrib]

lemma sstar_add_right {j k : ℕ} (α : P (j + 1)) (β β' : P (k + 1)) :
    sstar (R := R) α (β + β') = sstar (R := R) α β + sstar (R := R) α β' := by
  simp only [sstar_def, compFin_add_right, smul_add]
  rw [Finset.sum_add_distrib]

lemma sstar_smul_left {j k : ℕ} (r : R) (α : P (j + 1)) (β : P (k + 1)) :
    sstar (R := R) (r • α) β = r • sstar (R := R) α β := by
  have hpull : r • sstar (R := R) α β
      = ∑ a : Fin (j + 1), r • (((-1 : R) ^ ((a : ℕ) * k)) • compFin (R := R) a α β) :=
    map_sum (LinearMap.lsmul R (P (j + k + 1)) r) _ _
  rw [sstar_def, hpull]
  exact Finset.sum_congr rfl fun a _ => by rw [compFin_smul_left, smul_comm]

lemma sstar_smul_right {j k : ℕ} (r : R) (α : P (j + 1)) (β : P (k + 1)) :
    sstar (R := R) α (r • β) = r • sstar (R := R) α β := by
  have hpull : r • sstar (R := R) α β
      = ∑ a : Fin (j + 1), r • (((-1 : R) ^ ((a : ℕ) * k)) • compFin (R := R) a α β) :=
    map_sum (LinearMap.lsmul R (P (j + k + 1)) r) _ _
  rw [sstar_def, hpull]
  exact Finset.sum_congr rfl fun a _ => by rw [compFin_smul_right, smul_comm]

@[simp] lemma zero_sstar {j k : ℕ} (β : P (k + 1)) :
    sstar (R := R) (0 : P (j + 1)) β = 0 := by
  simp only [sstar_def, compFin_zero_left, smul_zero, Finset.sum_const_zero]

@[simp] lemma sstar_zero {j k : ℕ} (α : P (j + 1)) :
    sstar (R := R) α (0 : P (k + 1)) = 0 := by
  simp only [sstar_def, compFin_zero_right, smul_zero, Finset.sum_const_zero]

/-! ### Unit laws

The identity has degree zero, so every sign in `α ⋆ₛ 1` is `(-1)^0 = 1` and the signed product
agrees with the unsigned one. Likewise `1 ⋆ₛ β` has a single term, at slot `0`. -/

@[simp] lemma sstar_one {j : ℕ} (α : P (j + 1)) :
    sstar (R := R) α (one (R := R) (P := P)) = (j + 1) • α := by
  rw [sstar_def]
  have h : ∀ a : Fin (j + 1),
      ((-1 : R) ^ ((a : ℕ) * 0)) • compFin (R := R) a α (one (R := R) (P := P)) = α := by
    intro a
    rw [Nat.mul_zero, pow_zero, one_smul, compFin_one]
    exact reindex_self _ _
  rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

@[simp] lemma one_sstar {k : ℕ} (β : P (k + 1)) :
    reindex R P (by omega) (sstar (R := R) (one (R := R) (P := P)) β) = β := by
  rw [sstar_def, Fin.sum_univ_one]
  simp only [Fin.val_zero, Nat.zero_mul, pow_zero, one_smul]
  exact compFin_zero_one β

/-! ### The graded bracket, and Maurer–Cartan -/

/-- The graded commutator `⁅α, β⁆ = α ⋆ₛ β - (-1)^(j k) β ⋆ₛ α`.-/
def gbracket {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) : P (j + k + 1) :=
  sstar (R := R) α β - ((-1 : R) ^ (j * k)) • reindex R P (by omega) (sstar (R := R) β α)

@[inherit_doc] scoped notation "⁅" α ", " β "⁆ₛ" => gbracket α β

/-! ### The associative operad is a Maurer–Cartan element

`Ass R` has a single operation in each arity, so its binary operation is the unit of `R`. That it
solves the Maurer–Cartan equation is the statement that `Ass` is the operad governing
associativity — and it is the concrete case the unsigned product gets wrong, since there the same
element satisfies `Θ ⋆ Θ = 2 • Θ ∘₀ Θ ≠ 0`. -/

end Operad
