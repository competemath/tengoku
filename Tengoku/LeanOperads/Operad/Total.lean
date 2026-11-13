/-
# The total space of an operad, and the `⋆` product

Grade an operad by **arity minus one**: write `α : P (j + 1)` for an element of degree `j`.
The circle product

    α ⋆ β = ∑ i, α ∘ᵢ β

is then additive in the degree: for `α : P (j + 1)` and `β : P (k + 1)` every summand
`compFin i α β` lives in `P ((j + 1) - 1 + (k + 1))`, which Lean reduces definitionally to
`P (j + k + 1)`. So the sum is well-formed with **no reindexing at all** — a direct payoff of
the positional convention, since `compFin` already lands in a uniform arity no matter which slot
is used.

This is the unsigned skeleton of the structure the deformation theory of operads runs on: the
commutator of `⋆` is a Lie bracket. With the suspension signs of `Operad.DG` (in
`Operad.TotalSpaceS`), an operad structure is a Maurer–Cartan element and `d = ⁅Θ, -⁆` is the
differential whose cohomology controls deformations (`Operad.Cohomology`).
-/
import Tengoku.LeanOperads.Operad.Constructions
import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

namespace Operad

open NSOperad Finset

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-- The circle product `α ⋆ β = ∑ᵢ α ∘ᵢ β`, summing over every slot of `α`. Degrees add:
`P (j+1) → P (k+1) → P (j+k+1)`.-/
def star {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) : P (j + k + 1) :=
  ∑ i : Fin (j + 1), compFin (R := R) i α β

@[inherit_doc] scoped infixl:70 " ⋆ " => star

/--
@isnad1 id=eq.0h6v.s8.584904da0971 from=translated src=- shape=ec4f550c vocab=9ceec38b
-/
lemma star_def {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) :
    star (R := R) α β = ∑ i : Fin (j + 1), compFin (R := R) i α β := rfl

/-- Pulling a scalar out of a finite sum, obtained from `map_sum` for `LinearMap.lsmul`.
(`Finset.smul_sum` does exist, in `Mathlib.Algebra.BigOperators.GroupWithZero.Action`, but it is
not imported here; it is also stated for a general `DistribSMul`, which `rw` and `simp` both fail
to match against a `Module`-derived action.)-/
private lemma smul_sum' {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ} (r : R)
    (f : Fin n → M) : r • ∑ i, f i = ∑ i, r • f i :=
  map_sum (LinearMap.lsmul R M r) f Finset.univ

/-! ### Bilinearity -/

/--
@isnad1 id=eq.0h7v.s8.01a235d844a6 from=translated src=- shape=8c8f48b3 vocab=ad830e32
-/
lemma star_add_left {j k : ℕ} (α α' : P (j + 1)) (β : P (k + 1)) :
    star (R := R) (α + α') β = star (R := R) α β + star (R := R) α' β := by
  unfold star
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => compFin_add_left i α α' β

/--
@isnad1 id=eq.0h7v.s8.e610e66a50f4 from=translated src=- shape=0bff8719 vocab=ad830e32
-/
lemma star_add_right {j k : ℕ} (α : P (j + 1)) (β β' : P (k + 1)) :
    star (R := R) α (β + β') = star (R := R) α β + star (R := R) α β' := by
  unfold star
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => compFin_add_right i α β β'

/--
@isnad1 id=eq.0h7v.s10.5d0c38680717 from=translated src=- shape=a540ef6b vocab=e2449621
-/
lemma star_smul_left {j k : ℕ} (r : R) (α : P (j + 1)) (β : P (k + 1)) :
    star (R := R) (r • α) β = r • star (R := R) α β := by
  unfold star
  rw [smul_sum']
  exact Finset.sum_congr rfl fun i _ => compFin_smul_left i r α β

/--
@isnad1 id=eq.0h7v.s10.a229fdf5dfe4 from=translated src=- shape=0a89a3f3 vocab=e2449621
-/
lemma star_smul_right {j k : ℕ} (r : R) (α : P (j + 1)) (β : P (k + 1)) :
    star (R := R) α (r • β) = r • star (R := R) α β := by
  unfold star
  rw [smul_sum']
  exact Finset.sum_congr rfl fun i _ => compFin_smul_right i r α β

/--
@isnad1 id=eq.0h5v.s8.819e3f61cd8e from=translated src=- shape=4a7e5153 vocab=ad830e32
-/
@[simp] lemma zero_star {j k : ℕ} (β : P (k + 1)) :
    star (R := R) (0 : P (j + 1)) β = 0 := by
  unfold star
  exact Finset.sum_eq_zero fun i _ => compFin_zero_left i β

/--
@isnad1 id=eq.0h5v.s8.057b4f8643ac from=translated src=- shape=0b88396d vocab=ad830e32
-/
@[simp] lemma star_zero {j k : ℕ} (α : P (j + 1)) :
    star (R := R) α (0 : P (k + 1)) = 0 := by
  unfold star
  exact Finset.sum_eq_zero fun i _ => compFin_zero_right i α

/-! ### The unit -/

/-- Plugging the identity into any slot gives back the operation.
@isnad1 id=eq.0h5v.s9.ba18749f8767 from=translated src=- shape=4eb19eb4 vocab=70062a34
-/
lemma compFin_one {m : ℕ} (i : Fin m) (α : P m) :
    compFin (R := R) i α (one (R := R) (P := P))
      = reindex R P (by have := i.isLt; omega) α := by
  unfold compFin
  rw [comp_one_right]
  simp

/-- Filling the single slot of the identity operation does nothing. The reindexing is genuinely
needed: `0 + (k + 1)` is *not* definitionally `k + 1` in Lean, since `Nat.add` recurses on its
second argument.
@isnad1 id=eq.0h4v.s10.b00f339da8f0 from=translated src=- shape=00011457 vocab=42c5184c
-/
lemma compFin_zero_one {k : ℕ} (β : P (k + 1)) :
    reindex R P (by omega)
        (compFin (R := R) (0 : Fin (0 + 1)) (one (R := R) (P := P)) β) = β := by
  have h0 : (0 : Fin (0 + 1)) = ⟨0, by omega⟩ := by apply Fin.ext; simp
  rw [h0, compFin_eq_comp 0 0, reindex_reindex]
  exact comp_one_left β

/-- `1 ⋆ β = β`: the identity operation has a single slot, and filling it does nothing.
@isnad1 id=eq.0h4v.s9.2ede5f049960 from=translated src=- shape=c37efe6c vocab=2c2512b1
-/
@[simp] lemma one_star {k : ℕ} (β : P (k + 1)) :
    reindex R P (by omega) (star (R := R) (one (R := R) (P := P)) β) = β := by
  rw [star_def, Fin.sum_univ_one]
  exact compFin_zero_one β

/-- `α ⋆ 1 = (arity) • α`: every one of the `j + 1` slots contributes a copy of `α`.
Here no reindexing is needed, because `j + 0` *is* definitionally `j`.
@isnad1 id=eq.0h4v.s8.0f5a8e144758 from=translated src=- shape=076e6ffd vocab=1639826e
-/
@[simp] lemma star_one {j : ℕ} (α : P (j + 1)) :
    star (R := R) α (one (R := R) (P := P)) = (j + 1) • α := by
  rw [star_def]
  have h : ∀ i : Fin (j + 1), compFin (R := R) i α (one (R := R) (P := P)) = α := fun i => by
    rw [compFin_one]; exact reindex_self _ _
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]

/-! ### The Lie bracket

The commutator of `⋆`. Once the pre-Lie identity is available this is a genuine Lie bracket;
antisymmetry below holds unconditionally. -/

/-- The graded commutator `[α, β] = α ⋆ β - β ⋆ α`.-/
def bracket {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) : P (j + k + 1) :=
  star (R := R) α β - reindex R P (by omega) (star (R := R) β α)

@[inherit_doc] scoped notation "⁅" α ", " β "⁆" => bracket α β

/--
@isnad1 id=eq.0h6v.s10.c92457052261 from=translated src=- shape=6ed7d19f vocab=0b106dbf
-/
lemma bracket_def {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) :
    bracket (R := R) α β
      = star (R := R) α β - reindex R P (by omega) (star (R := R) β α) := rfl

/-- The bracket is antisymmetric.
@isnad1 id=eq.0h6v.s10.87d089159f4c from=translated src=- shape=efcf107e vocab=ba4e46bc
-/
lemma bracket_antisymm {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) :
    bracket (R := R) α β = - reindex R P (by omega) (bracket (R := R) β α) := by
  rw [bracket_def, bracket_def, map_sub, neg_sub, reindex_reindex, reindex_self]

/--
@isnad1 id=eq.0h4v.s8.07670f6bded9 from=translated src=- shape=068f1349 vocab=684c2c31
-/
@[simp] lemma bracket_self {j : ℕ} (α : P (j + 1)) :
    bracket (R := R) α α = 0 := by
  rw [bracket_def, reindex_self, sub_self]

/--
@isnad1 id=eq.0h7v.s8.a0d592e64450 from=translated src=- shape=8c8f48b3 vocab=684c2c31
-/
lemma bracket_add_left {j k : ℕ} (α α' : P (j + 1)) (β : P (k + 1)) :
    bracket (R := R) (α + α') β = bracket (R := R) α β + bracket (R := R) α' β := by
  rw [bracket_def, bracket_def, bracket_def, star_add_left, star_add_right, map_add]
  abel

/--
@isnad1 id=eq.0h7v.s8.e98c3264ef4c from=translated src=- shape=0bff8719 vocab=684c2c31
-/
lemma bracket_add_right {j k : ℕ} (α : P (j + 1)) (β β' : P (k + 1)) :
    bracket (R := R) α (β + β') = bracket (R := R) α β + bracket (R := R) α β' := by
  rw [bracket_def, bracket_def, bracket_def, star_add_right, star_add_left, map_add]
  abel

end Operad
