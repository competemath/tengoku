import Tengoku.Seed.Algebra.Polynomial.Laurent
import Tengoku.Seed.RingTheory.FilteredAlgebra.Basic
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

/-!
# The associated graded algebra via the extended Rees algebra

For an increasing integer filtration `F`, the Rees algebra consists of Laurent
polynomials whose coefficient at `d` belongs to `F d`.  Its quotient by `T`
is the associated graded algebra.  This construction supplies an actual ring,
including negative filtration indices, without treating the associated-graded
algebra or its multiplicative structure as an assumed interface.
-/

namespace StableCoordinate.FilteredRees

open AddMonoidAlgebra

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable (F : ℤ → Submodule k A) [SetLike.GradedMonoid F]

/-- The extended Rees algebra with integer-indexed, increasing convention. -/
noncomputable def rees : Subalgebra k (LaurentPolynomial A) where
  carrier := {p | ∀ d, p.coeff d ∈ F d}
  zero_mem' := by intro d; exact (F d).zero_mem
  one_mem' := by
    intro d
    by_cases hd : d = 0
    · subst d
      simpa only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_same] using SetLike.one_mem_graded F
    · simpa only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply, ite_eq_right (Ne.symm hd)] using (F d).zero_mem
  add_mem' hp hq := by
    intro d
    exact (F d).add_mem (hp d) (hq d)
  mul_mem' {p q} hp hq := by
    intro d
    rw [AddMonoidAlgebra.coeff_mul]
    simp only [Finsupp.sum]
    apply (F d).sum_mem
    intro i hi
    apply (F d).sum_mem
    intro j hj
    split_ifs with hij
    · simpa only [← hij] using SetLike.mul_mem_graded (hp i) (hq j)
    · exact (F d).zero_mem
  algebraMap_mem' r := by
    intro d
    rw [Algebra.algebraMap_eq_smul_one, AddMonoidAlgebra.coeff_smul_apply]
    by_cases hd : d = 0
    · subst d
      simpa only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_same] using (F 0).smul_mem r (SetLike.one_mem_graded F)
    · simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply, ite_eq_right (Ne.symm hd), smul_zero, Submodule.zero_mem]

@[simp] theorem mem_rees (p : LaurentPolynomial A) :
    p ∈ rees F ↔ ∀ d, p.coeff d ∈ F d := Iff.rfl

/-- A homogeneous element of the Rees algebra. -/
noncomputable def homogeneous (d : ℤ) (a : F d) : rees F :=
  ⟨AddMonoidAlgebra.single d (a : A), by
    intro i
    by_cases hi : d = i
    · subst i
      simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using a.property
    · simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right hi] using (F i).zero_mem⟩

@[simp] theorem homogeneous_coe (d : ℤ) (a : F d) :
    (homogeneous F d a : LaurentPolynomial A) = AddMonoidAlgebra.single d (a : A) := rfl

/-- The positive Laurent parameter lies in the Rees algebra by monotonicity. -/
noncomputable def parameter (hmono : Monotone F) : rees F :=
  homogeneous F 1 ⟨1, hmono (by decide : (0 : ℤ) ≤ 1) (SetLike.one_mem_graded F)⟩

@[simp] theorem parameter_coe (hmono : Monotone F) :
    (parameter F hmono : LaurentPolynomial A) = AddMonoidAlgebra.single 1 1 := rfl

noncomputable def parameterIdeal (hmono : Monotone F) : Ideal (rees F) :=
  Ideal.span {parameter F hmono}

/-- The genuine associated graded algebra, modeled as the Rees special fiber. -/
abbrev Gr (hmono : Monotone F) := rees F ⧸ parameterIdeal F hmono

/-- The class of `a` in degree `d`. -/
noncomputable def initial (hmono : Monotone F) (d : ℤ) (a : F d) : Gr F hmono :=
  Ideal.Quotient.mk (parameterIdeal F hmono) (homogeneous F d a)

/-- Every Rees element is the finite sum of its homogeneous coefficients. -/
theorem rees_eq_sum (p : rees F) :
    p = ∑ d ∈ (p : LaurentPolynomial A).coeff.support,
      homogeneous F d ⟨(p : LaurentPolynomial A).coeff d, p.property d⟩ := by
  apply Subtype.ext
  change (p : LaurentPolynomial A) = (rees F).val
    (∑ d ∈ (p : LaurentPolynomial A).coeff.support,
      homogeneous F d ⟨(p : LaurentPolynomial A).coeff d, p.property d⟩)
  rw [map_sum]
  exact (AddMonoidAlgebra.sum_coeff_single (p : LaurentPolynomial A)).symm

/-- Addition of initial forms within one degree. -/
theorem initial_add (hmono : Monotone F) (d : ℤ) (a b : F d) :
    initial F hmono d (a + b) = initial F hmono d a + initial F hmono d b := by
  rw [initial, initial, initial, ← map_add]
  congr 1
  apply Subtype.ext
  exact AddMonoidAlgebra.single_add d (a : A) (b : A)

end StableCoordinate.FilteredRees

end OAI
