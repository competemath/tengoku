import Tengoku.MiyaokaMoriCharzero.MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierFiniteSupport
import Tengoku.MiyaokaMoriCharzero.MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeAdditivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Principal Cartier divisors on the same integral scheme

A unit of the actual function field defines Cartier data on the single open chart `X`.
The overlap unit is the structure-sheaf section `1`, and the resulting coefficients are
the existing length-based `Scheme.ord`. On a Noetherian scheme of dimension at most one,
`CartierLocalData.zeroCycle` supplies the same principal divisor as an actual zero cycle.

The theorem that its existing residue-field-weighted degree is zero over any field when the
structure morphism is proper, `rawZeroCycleDegree_principal_eq_zero` (Stacks 02RU), lives in
`MiyaokaMori.AlgebraicGeometry.Chow.Degree.PrincipalDivisorDegreeZero`: its one-dimensional case is derived there
from `principalDivisor_degree_eq_zero`, which this file cannot import. This file provides the bookkeeping
it uses (`rawZeroCycleDegree_principal_eq_sum`, `principalCartierData_zeroCycle_eq_zero_of_dim_lt_one`).
No smoothness, normality, or field-characteristic assumption is used.

Sources: Stacks Project, `chow.tex`, `lemma-curve-principal-divisor` (Tag 02RU), and
`algebra.tex`, `definition-ord`; Theorem 1.1 of the paper and the coordinate-divisor
calculation in the proof of Proposition 2.4. The interface chooses neither a rational
section nor a degree from an existence theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped Classical BigOperators

namespace AlgebraicGeometry.Intersection

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The principal Cartier datum has one full-space chart and the given nonzero rational equation.-/
def principalCartierData (a : X.functionFieldˣ) : CartierLocalData X where
  index := ULift.{u} (Fin 1)
  opens := fun _ ↦ ⊤
  cover := by ext x; simp
  locallyFinite := locallyFinite_of_finite _
  equation := fun _ ↦ (a : X.functionField)
  equation_ne_zero := fun _ ↦ a.ne_zero
  ratio_unit := by
    intro i j hU
    letI : Nonempty ↑((⊤ : X.Opens) ⊓ ⊤) := hU
    refine ⟨1, isUnit_one, ?_⟩
    simp [a.ne_zero]

/-- The principal coefficient is the actual local length order at every scheme point.
@isnad1 id=eq.0h3v.s6.110654996854 from=translated src=- shape=b6b4e6b4 vocab=229517ab
-/
@[simp]
theorem principalCartierData_coefficient (a : X.functionFieldˣ) (x : X) :
    (principalCartierData a).coefficient x = X.ord (a : X.functionField) x := by
  by_cases hx : coheight x = 1
  · rw [CartierLocalData.coefficient_eq_ord _ x hx]
    rfl
  · rw [CartierLocalData.coefficient_eq_zero_of_coheight_ne_one _ x hx,
      Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- The unit rational function has zero principal coefficient.
@isnad1 id=eq.0h2v.s6.93dd2711e3ab from=translated src=- shape=1b67fea4 vocab=3eb0f746
-/
@[simp]
theorem principalCartierData_coefficient_one (x : X) :
    (principalCartierData (1 : X.functionFieldˣ)).coefficient x = 0 := by
  rw [principalCartierData_coefficient]
  have : Nonempty ↑(⊤ : X.Opens) := ⟨⟨x, Set.mem_univ x⟩⟩
  have h := Scheme.ord_of_isUnit (X := X) (U := ⊤) (f := (1 : Γ(X, ⊤)))
    isUnit_one (x := x) (by trivial)
  simpa only [map_one, Units.val_one] using h

/-- Multiplication of the same rational equations adds their principal coefficients.
@isnad1 id=eq.0h4v.s8.c79c5b47d540 from=translated src=- shape=f9b40f99 vocab=afe1cee5
-/
theorem principalCartierData_coefficient_mul (a b : X.functionFieldˣ) (x : X) :
    (principalCartierData (a * b)).coefficient x =
      (principalCartierData a).coefficient x + (principalCartierData b).coefficient x := by
  simpa only [principalCartierData_coefficient, Units.val_mul] using
    (Scheme.ord_mul (x := x) a.ne_zero b.ne_zero)

/-- The existing zero-cycle construction retains exactly the principal local orders.
@isnad1 id=eq.1h3v.s8.a4681b281ef5 from=translated src=- shape=2224550b vocab=fbd414e4
-/
@[simp]
theorem principalCartierData_zeroCycle_apply [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (a : X.functionFieldˣ) (x : X) :
    ((principalCartierData a).zeroCycle hdim).1 x = X.ord (a : X.functionField) x :=
  principalCartierData_coefficient a x

/-- The principal divisor of the unit function is the existing zero cycle.
@isnad1 id=eq.1h1v.s7.a3e8be709aa6 from=translated src=- shape=fc622ad5 vocab=a0199918
-/
@[simp]
theorem principalCartierData_zeroCycle_one [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) :
    (principalCartierData (1 : X.functionFieldˣ)).zeroCycle hdim =
      DimensionCycle.zero X 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  exact principalCartierData_coefficient_one x

/-- Principal divisors turn multiplication into the existing addition of actual zero cycles.
@isnad1 id=eq.1h3v.s8.d0a73ee322b1 from=translated src=- shape=ab0e164e vocab=8b958e7a
-/
theorem principalCartierData_zeroCycle_mul [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (a b : X.functionFieldˣ) :
    (principalCartierData (a * b)).zeroCycle hdim =
      DimensionCycle.add ((principalCartierData a).zeroCycle hdim)
        ((principalCartierData b).zeroCycle hdim) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  exact principalCartierData_coefficient_mul a b x

/-- Below dimension one every principal coefficient vanishes, since no point has codimension one.
@isnad1 id=eq.1h2v.s6.eaca28c4480e from=translated src=- shape=aa4e9e1c vocab=fa973928
-/
theorem principalCartierData_zeroCycle_eq_zero_of_dim_lt_one [IsNoetherian X]
    (hdim : topologicalKrullDim X < 1) (a : X.functionFieldˣ) :
    (principalCartierData a).zeroCycle hdim.le = DimensionCycle.zero X 0 := by
  have hdim' : Order.krullDim X < 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  apply (principalCartierData a).coefficient_eq_zero_of_coheight_ne_one x
  intro hx
  have hle := Order.coheight_le_krullDim x
  rw [hx] at hle
  exact (not_le_of_gt hdim') hle

/-- Principal degree is the finite sum of the actual local orders with their
residue-field weights.
@isnad1 id=eq.1h4v.s8.e24c89ce5d9f from=translated src=- shape=fdf5f8cc vocab=3f65232e
-/
theorem rawZeroCycleDegree_principal_eq_sum {k : Type u} [Field k] [IsNoetherian X]
    (c : X ⟶ Spec (CommRingCat.of k)) [IsProper c]
    (hdim : topologicalKrullDim X ≤ 1) (a : X.functionFieldˣ) :
    rawZeroCycleDegree c ((principalCartierData a).zeroCycle hdim) =
      ∑ x ∈ (AlgebraicGeometry.Divisors.finite_support_ord X (a : X.functionField) a.ne_zero).toFinset,
        X.ord (a : X.functionField) x * (residueFieldDegree c x : ℤ) := by
  rw [rawZeroCycleDegree_eq_sum_on c _
    (AlgebraicGeometry.Divisors.finite_support_ord X (a : X.functionField) a.ne_zero).toFinset (by
      intro x hx
      rw [principalCartierData_zeroCycle_apply]
      by_contra hn
      exact hx ((AlgebraicGeometry.Divisors.finite_support_ord X (a : X.functionField) a.ne_zero).mem_toFinset.mpr hn))]
  simp only [principalCartierData_zeroCycle_apply]

end AlgebraicGeometry.Intersection
