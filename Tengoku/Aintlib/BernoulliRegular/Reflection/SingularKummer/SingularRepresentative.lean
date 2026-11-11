module

public import Tengoku.Aintlib.BernoulliRegular.Reflection.SingularKummer.SingularClassChoice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Singular Kummer: representatives of singular quotient classes

This file unwraps a class in the singular quotient into an explicit singular
pair `(I, alpha)`.  The representative automatically satisfies
`(alpha) = I^p`, and nontriviality of the quotient class image in `A[p]`
transfers to the represented singular pair.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
/-- Every singular quotient class has a singular-pair representative.
@isnad1 id=ex.0h4v.s9.93179fac836c from=translated src=- shape=b0ba1890 vocab=5c9e4ccb
-/
theorem exists_representative (p : ℕ)
    (x : SingularGroup (R := R) (K := K) p) :
    ∃ s : SingularPair R K p,
      (QuotientGroup.mk s : SingularGroup (R := R) (K := K) p) = x := by
  refine QuotientGroup.induction_on x ?_
  intro s
  exact ⟨s, rfl⟩

/-- A singular quotient class with nontrivial image in `A[p]` has a
singular-pair representative with nontrivial image in `A[p]`.
@isnad1 id=ex.1h4v.s12.a20c2713111f from=translated src=- shape=e5ffff05 vocab=a1fc5133
-/
theorem exists_representative_of_nontrivial_class_image (p : ℕ)
    {x : SingularGroup (R := R) (K := K) p}
    (hx : singularGroupClassMapToPTorsion (R := R) (K := K) p x ≠ 1) :
    ∃ s : SingularPair R K p,
      (QuotientGroup.mk s : SingularGroup (R := R) (K := K) p) = x ∧
        classMapToPTorsion (R := R) (K := K) p s ≠ 1 ∧
          toPrincipalIdeal R K (generator s) = ideal s ^ p := by
  obtain ⟨s, hs⟩ := exists_representative (R := R) (K := K) p x
  refine ⟨s, hs, ?_, principal_eq_ideal_pow (R := R) (K := K) s⟩
  intro hs_trivial
  apply hx
  rw [← hs]
  exact hs_trivial

end SingularPair

namespace SingularLinearAction
namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

end SingularPair
end SingularLinearAction

end SingularKummer
end Reflection
end BernoulliRegular

end

end
