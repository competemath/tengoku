import Tengoku.MiyaokaMoriCharzero.MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PrincipalCartierDivisor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebraic cycles of the existing Cartier data

The raw cycle has exactly the existing Cartier order coefficients, in any dimension.
A `FiniteCartierDivisor` already supplies finite support; on a Noetherian scheme the
existing finite-support theorem supplies it for `CartierLocalData`. No dimension function
is changed, and the comparison with the existing zero cycle is made only when its actual
support condition holds.

The principal cycle `div(r)` is `AlgebraicGeometry.Scheme.principalCycle`
(`MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor`); on a Noetherian scheme it is the cycle of the
principal Cartier datum `principalCartierData r` defined here (see that module). The inherited
integral-scheme hypothesis allows singular and nonnormal schemes; cycles of nonreduced intermediate
zero schemes and their Cartier action require separate constructions.

Sources: Stacks Project, Tags 02RO, 02RW, 02SJ and 02SO; the proof of Proposition 2.4 of the paper (the relation (2.10)). Dimension drop, rational equivalence and the global cap action are subsequent
obligations; this file supplies their raw Cartier and principal cycles.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace
open scoped Classical

namespace AlgebraicGeometry.Intersection

universe u

variable {X : Scheme.{u}} [IsIntegral X]

namespace FiniteCartierDivisor

variable [IsLocallyNoetherian X]

/-- The actual algebraic cycle whose coefficients are the given Cartier orders.-/
def algebraicCycle (D : FiniteCartierDivisor X) : AlgebraicCycle X ℤ where
  toFun := D.toCartierLocalData.coefficient
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ :=
    ⟨Set.univ, Filter.univ_mem, by simpa using D.finite_support⟩

/-- The raw cycle keeps every existing Cartier order coefficient.
@isnad1 id=eq.0h3v.s6.d4c19b36b1af from=translated src=- shape=1bf0da43 vocab=6e07bb4b
-/
@[simp]
theorem algebraicCycle_apply (D : FiniteCartierDivisor X) (x : X) :
    D.algebraicCycle x = D.toCartierLocalData.coefficient x := rfl

/-- The raw cycle retains the finite support supplied by the divisor.
@isnad1 id=finite.0h2v.s6.f5ace2cdc3c4 from=translated src=- shape=784831b8 vocab=472399fc
-/
theorem algebraicCycle_support_finite (D : FiniteCartierDivisor X) :
    (Function.support D.algebraicCycle).Finite := D.finite_support

/-- When the same support is zero-dimensional, the old zero cycle has this underlying cycle.
@isnad1 id=eq.1h2v.s7.8c0c2f34b81a from=translated src=- shape=55d1b5d0 vocab=da3e97e2
-/
theorem algebraicCycle_eq_zeroCycle (D : FiniteCartierDivisor X)
    (hD : D.ZeroDimensionalSupport) : D.algebraicCycle = (D.zeroCycle hD).1 := rfl

end FiniteCartierDivisor

namespace CartierLocalData

variable [IsNoetherian X]

/-- The raw Cartier cycle with finite support proved from the same local equations.-/
def algebraicCycle (D : CartierLocalData X) : AlgebraicCycle X ℤ :=
  D.toFiniteCartierDivisor.algebraicCycle

/-- The raw Cartier cycle retains its original order coefficient at every point.
@isnad1 id=eq.0h3v.s6.8ded0686b151 from=translated src=- shape=63bc9b32 vocab=1d433d72
-/
@[simp]
theorem algebraicCycle_apply (D : CartierLocalData X) (x : X) :
    D.algebraicCycle x = D.coefficient x := rfl

/-- Any chart containing the point computes its raw cycle coefficient.
@isnad1 id=eq.1h4v.s7.a6d5471c2c87 from=translated src=- shape=717f74f4 vocab=4806bb23
-/
theorem algebraicCycle_apply_eq_ord_of_mem (D : CartierLocalData X) (x : X)
    (i : D.index) (hxi : x ∈ D.opens i) :
    D.algebraicCycle x = X.ord (D.equation i) x :=
  D.coefficient_eq_ord_of_mem x i hxi

/-- The actual Cartier cycle has finite support on a Noetherian scheme.
@isnad1 id=finite.0h2v.s6.1e570d05b9b0 from=translated src=- shape=784831b8 vocab=f9b5e55c
-/
theorem algebraicCycle_support_finite (D : CartierLocalData X) :
    (Function.support D.algebraicCycle).Finite := D.coefficient_finite_support

/-- In dimension at most one, the existing zero cycle is this same raw cycle.
@isnad1 id=eq.1h2v.s7.6fc88da2bcdf from=translated src=- shape=adb40a8a vocab=bdc4b288
-/
theorem algebraicCycle_eq_zeroCycle (D : CartierLocalData X)
    (hdim : topologicalKrullDim X ≤ 1) : D.algebraicCycle = (D.zeroCycle hdim).1 := rfl

end CartierLocalData

end AlgebraicGeometry.Intersection
