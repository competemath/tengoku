import Tengoku.KuroshProblemAtGkDimensionTwo.CriticalGK2.LocalContainment

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Physical common-prefix polynomials and reset stems

This file identifies the explicit block substitution with the common-prefix
formula `t * x`, `t * y` in the actual two-letter free algebra.  The new reset
stem `g * t` is nonzero and homogeneous.  All statements are in the ambient free
algebra, before any quotient is constructed.
-/

namespace CriticalGK2

open scoped BigOperators

/-- The actual homogeneous polynomial represented by a stem coefficient vector.-/
noncomputable def stemPolynomial (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) : BinaryFreeAlgebra F :=
  ∑ a : StemWord n, t a • MonoidAlgebra.single (FreeMonoid.ofList (List.ofFn a)) 1

/-- Every actual word of degree `n` is represented by one fixed-length tuple.
@isnad1 id=ex.1h2v.s5.31841378d22b from=translated src=- shape=2ad6f03b vocab=0a7dfc2b
-/
theorem exists_stemWord_of_length (n : ℕ) (w : FreeMonoid Bool) (hw : w.length = n) :
    ∃ a : StemWord n, FreeMonoid.ofList (List.ofFn a) = w := by
  subst n
  refine ⟨w.toList.get, ?_⟩
  exact (congrArg FreeMonoid.ofList (List.ofFn_get w.toList)).trans
    (FreeMonoid.ofList_toList w)

/-- The next common prefix produced by the local operation, in the ambient algebra.-/
noncomputable def localResetStem (F : Type*) [Field F] (n : ℕ)
    (t : StemWord n → F) (k : ℕ) (u : FreeMonoid Bool) : BinaryFreeAlgebra F :=
  localPIBlock F n t k u * stemPolynomial F n t

/-- The physical degree of the reset common prefix.-/
def localResetDegree (n k : ℕ) (u : FreeMonoid Bool) : ℕ :=
  (((k * k + 1) * (k * k + 1) + u.length) * (n + 1)) + n

end CriticalGK2
