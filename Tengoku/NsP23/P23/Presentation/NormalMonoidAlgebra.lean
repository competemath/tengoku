import Tengoku.NsP23.P23.Artin.MaximalIdealTrace
import Tengoku.Seed.Algebra.MonoidAlgebra.Basic
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The normalized one-tie monoid algebra and its truncation map

This is the first presentation layer above the frozen direct finite model.
It uses the existing `Normal` commutative monoid and introduces no second
exponent object.
-/

namespace P23.Presentation

noncomputable section

open P23.OneTie P23.Artin

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

/-- The monoid algebra of frozen normalized one-tie exponent triples.-/
abbrev NormalMonoidAlgebra (k : Type*) [Field k] (a b c : ℕ) [NeZero a] :=
  MonoidAlgebra k (Normal a b c)

/-- The canonical monomial belonging to a normalized exponent.-/
def monomial (p : Normal a b c) : NormalMonoidAlgebra k a b c :=
  MonoidAlgebra.single p 1

@[simp]
theorem monomial_coeff (p q : Normal a b c) :
    (monomial (k := k) p).coeff q = if p = q then 1 else 0 := by
  classical
  simp [monomial, Finsupp.single_apply]

@[simp]
theorem monomial_one : monomial (k := k) (1 : Normal a b c) = 1 := by
  rw [MonoidAlgebra.one_def]
  rfl

@[simp]
theorem monomial_mul (p q : Normal a b c) :
    monomial (k := k) p * monomial (k := k) q = monomial (k := k) (p * q) := by
  simp [monomial, MonoidAlgebra.single_mul_single]

/-- A normalized monomial interpreted in the finite direct model.-/
def truncatedMonomial (S : Finset (Normal a b c)) (p : Normal a b c) :
    MonomialArtin k S :=
  if hp : p ∈ standardFinset S then X (k := k) S p hp else 0

@[simp]
theorem truncatedMonomial_of_mem (S : Finset (Normal a b c))
    (p : Normal a b c) (hp : p ∈ standardFinset S) :
    truncatedMonomial (k := k) S p = X (k := k) S p hp := by
  simp [truncatedMonomial, hp]

@[simp]
theorem truncatedMonomial_of_not_mem (S : Finset (Normal a b c))
    (p : Normal a b c) (hp : p ∉ standardFinset S) :
    truncatedMonomial (k := k) S p = 0 := by
  simp [truncatedMonomial, hp]

@[simp]
theorem truncatedMonomial_one (S : Finset (Normal a b c)) :
    truncatedMonomial (k := k) S 1 = 1 := by
  classical
  by_cases hS : S.Nonempty
  · have h1 := one_mem_standardFinset S hS
    rw [truncatedMonomial_of_mem S 1 h1]
    exact X_one (k := k) S hS
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    subst S
    simp [truncatedMonomial, MonomialArtin.one_def]

@[simp]
theorem truncatedMonomial_mul (S : Finset (Normal a b c))
    (p q : Normal a b c) :
    truncatedMonomial (k := k) S (p * q) =
      truncatedMonomial (k := k) S p * truncatedMonomial (k := k) S q := by
  classical
  by_cases hpq : p * q ∈ standardFinset S
  · have hp := MonomialArtin.mem_standardFinset_of_mul_mem_left S hpq
    have hq := MonomialArtin.mem_standardFinset_of_mul_mem_right S hpq
    simp [truncatedMonomial, hpq, hp, hq, X_mul_X]
  · by_cases hp : p ∈ standardFinset S <;>
      by_cases hq : q ∈ standardFinset S <;>
      simp [truncatedMonomial, hpq, hp, hq, X_mul_X]

/-- The multiplicative normalized-monomial truncation.-/
def truncatedMonomialHom (S : Finset (Normal a b c)) :
    Normal a b c →* MonomialArtin k S where
  toFun := truncatedMonomial (k := k) S
  map_one' := truncatedMonomial_one (k := k) S
  map_mul' p q := truncatedMonomial_mul (k := k) S p q

/-- The algebra homomorphism killing precisely the nonstandard monomials.-/
def truncateAlgHom (S : Finset (Normal a b c)) :
    NormalMonoidAlgebra k a b c →ₐ[k] MonomialArtin k S :=
  MonoidAlgebra.lift k (MonomialArtin k S) (Normal a b c)
    (truncatedMonomialHom (k := k) S)

@[simp]
theorem truncateAlgHom_single (S : Finset (Normal a b c))
    (p : Normal a b c) (r : k) :
    truncateAlgHom (k := k) S (MonoidAlgebra.single p r) =
      r • truncatedMonomial (k := k) S p := by
  exact MonoidAlgebra.lift_single _ _ _

@[simp]
theorem truncateAlgHom_monomial (S : Finset (Normal a b c))
    (p : Normal a b c) :
    truncateAlgHom (k := k) S (monomial (k := k) p) =
      truncatedMonomial (k := k) S p := by
  simp [monomial]

theorem truncateAlgHom_monomial_of_mem (S : Finset (Normal a b c))
    (p : Normal a b c) (hp : p ∈ standardFinset S) :
    truncateAlgHom (k := k) S (monomial (k := k) p) =
      X (k := k) S p hp := by
  simp [hp]

theorem truncateAlgHom_monomial_of_not_mem (S : Finset (Normal a b c))
    (p : Normal a b c) (hp : p ∉ standardFinset S) :
    truncateAlgHom (k := k) S (monomial (k := k) p) = 0 := by
  simp [hp]

/-- A surviving output coordinate is exactly the corresponding input
monoid-algebra coefficient.-/
theorem coeff_truncateAlgHom (S : Finset (Normal a b c))
    (f : NormalMonoidAlgebra k a b c) (p : MonomialIndex S) :
    (truncateAlgHom (k := k) S f).coeff p = f.coeff p.1 := by
  classical
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single q r =>
      by_cases hq : q ∈ standardFinset S
      · by_cases hqp : q = p.1
        · subst q
          simp [truncatedMonomial, hq]
        · have hpne : p ≠ (⟨q, hq⟩ : MonomialIndex S) := by
            intro h
            apply hqp
            exact (congrArg Subtype.val h).symm
          simp [truncatedMonomial, hq, hqp, hpne]
      · have hne : q ≠ p.1 := by
          intro h
          apply hq
          simpa [h] using p.2
        simp [truncatedMonomial, hq, Finsupp.single_apply, hne]

theorem truncateAlgHom_surjective (S : Finset (Normal a b c)) :
    Function.Surjective (truncateAlgHom (k := k) S) := by
  intro v
  induction v using MonomialArtin.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
      rcases hx with ⟨fx, hfx⟩
      rcases hy with ⟨fy, hfy⟩
      exact ⟨fx + fy, by simp [hfx, hfy]⟩
  | single p r =>
      refine ⟨MonoidAlgebra.single p.1 r, ?_⟩
      simp [truncatedMonomial, p.2, MonomialArtin.smul_X]

end

end P23.Presentation
