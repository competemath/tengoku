import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.Basic
import Tengoku.Seed.Algebra.Order.Field.Basic
import Tengoku.Seed.Algebra.Field.Rat
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Algebra.Order.Ring.Rat
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Data.Nat.Cast.Order.Ring
import Tengoku.Seed.Data.Fintype.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite branching trees

This file isolates the only tree-counting argument used in the escape
method.  A path of length `r` is a sequence of choices in which the type of
the next choice may depend on the current state.  The theorem
`leaf_product_bound` says that the number of paths is at least any common
lower bound for the product of the branching degrees along a path.
-/

namespace SharpIntermediateSubgroupBounds

open scoped BigOperators

namespace BranchingTree

universe u

variable {State : Type*}
variable (Choice : State → Type*) [∀ s, Fintype (Choice s)]
variable (next : ∀ s, Choice s → State)

/-- Paths of a prescribed length in a state-dependent finite branching
system.-/
def Path : ℕ → State → Type _
  | 0, _ => PUnit
  | r + 1, s => Σ x : Choice s, Path r (next s x)

noncomputable instance pathFintype (r : ℕ) (s : State) :
    Fintype (Path Choice next r s) := by
  induction r generalizing s with
  | zero =>
      simp only [Path]
      infer_instance
  | succ r ih =>
      simp only [Path]
      letI (x : Choice s) : Fintype (Path Choice next r (next s x)) := ih (next s x)
      infer_instance

/-- Product of the branching degrees encountered along a path.-/
def branchProduct : ∀ {r s}, Path Choice next r s → ℕ
  | 0, _, _ => 1
  | _ + 1, s, ⟨x, z⟩ => Fintype.card (Choice s) * branchProduct z

/--
@isnad1 id=eq.0h5v.s5.d695c8c5931e from=translated src=- shape=4c590674 vocab=94ac878c
-/
@[simp]
theorem branchProduct_zero (s : State) (z : Path Choice next 0 s) :
    branchProduct Choice next z = 1 := by
  cases z
  rfl

/-- The leaf-product bound.  Positivity of every branching type is the
type-theoretic form of saying that no leaf occurs before the prescribed
depth.
@isnad1 id=le.1h6v.s6.77a5446a238e from=translated src=- shape=b43b2a04 vocab=09afe6ba
-/
theorem leaf_product_bound [∀ s, Nonempty (Choice s)]
    (r : ℕ) (s : State) (q : ℚ)
    (hq : ∀ z : Path Choice next r s,
      q ≤ (branchProduct Choice next z : ℚ)) :
    q ≤ (Fintype.card (Path Choice next r s) : ℚ) := by
  induction r generalizing s q with
  | zero =>
      have h := hq PUnit.unit
      simpa [Path, branchProduct] using h
  | succ r ih =>
      let b : ℕ := Fintype.card (Choice s)
      have hbNat : 0 < b := Fintype.card_pos
      have hb : (0 : ℚ) < (b : ℚ) := (Nat.cast_pos (α := ℚ)).2 hbNat
      have hchild : ∀ x : Choice s,
          q / (b : ℚ) ≤
            (Fintype.card (Path Choice next r (next s x)) : ℚ) := by
        intro x
        apply ih (s := next s x) (q := q / (b : ℚ))
        intro z
        apply (div_le_iff₀ hb).2
        let zx : Path Choice next (r + 1) s := by
          change Σ x : Choice s, Path Choice next r (next s x)
          exact ⟨x, z⟩
        have hz := hq zx
        change q ≤ ((Fintype.card (Choice s) *
          branchProduct Choice next z : ℕ) : ℚ) at hz
        simpa only [Nat.cast_mul, b, mul_comm] using hz
      calc
        q = ∑ _x : Choice s, q / (b : ℚ) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [show Fintype.card (Choice s) = b by rfl]
          exact (mul_div_cancel₀ q hb.ne').symm
        _ ≤ ∑ x : Choice s,
            (Fintype.card (Path Choice next r (next s x)) : ℚ) :=
          Finset.sum_le_sum fun x _hx => hchild x
        _ = (Fintype.card (Path Choice next (r + 1) s) : ℚ) := by
          simp only [Path, Fintype.card_sigma, Nat.cast_sum]

/-- Same-universe wrapper for applications in which states and choices are
subtypes of one fixed ambient type.  Making this universe equality explicit
avoids leaving a metavariable in downstream declarations.
@isnad1 id=le.1h6v.s6.8c33c86ab0b2 from=translated src=- shape=b43b2a04 vocab=09afe6ba
-/
theorem leaf_product_bound_sameUniverse {State : Type u}
    (Choice : State → Type u) [∀ s, Fintype (Choice s)]
    (next : ∀ s, Choice s → State) [∀ s, Nonempty (Choice s)]
    (r : ℕ) (s : State) (q : ℚ)
    (hq : ∀ z : Path Choice next r s,
      q ≤ (branchProduct Choice next z : ℚ)) :
    q ≤ (Fintype.card (Path Choice next r s) : ℚ) :=
  leaf_product_bound Choice next r s q hq

end BranchingTree

end SharpIntermediateSubgroupBounds
