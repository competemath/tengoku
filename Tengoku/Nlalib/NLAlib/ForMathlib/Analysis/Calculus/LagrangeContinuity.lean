import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Calculus.PolynomialCoefficients
import Tengoku.Seed.LinearAlgebra.Lagrange
import Tengoku.Seed.Topology.Algebra.Field

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Continuous coefficients of Lagrange cardinal polynomials

The cardinal coefficients are finite products of node differences and their
reciprocals. Distinctness at the limiting node vector suffices for continuity.
-/

noncomputable section
open Polynomial
namespace Lagrange

/-- A cardinal polynomial's degree budget holds even for coincident nodes.
@isnad1 id=le.1h5v.s6.148d05b16365 from=translated src=- shape=b67e2944 vocab=38a9eb65
-/
theorem degree_basis_le_of_mem {F ι : Type*} [Field F] [DecidableEq ι]
    {s : Finset ι} (v : ι → F) {i : ι} (hi : i ∈ s) :
    (Lagrange.basis s v i).degree ≤ ((s.card - 1 : ℕ) : WithBot ℕ) := by
  apply degree_le_natDegree.trans
  apply WithBot.coe_mono
  unfold Lagrange.basis
  apply (natDegree_prod_le _ _).trans
  calc (∑ j ∈ s.erase i, (basisDivisor (v i) (v j)).natDegree) ≤
      ∑ _j ∈ s.erase i, 1 := by
        apply Finset.sum_le_sum
        intro j _
        unfold basisDivisor
        exact (natDegree_C_mul_le _ _).trans (by simp)
    _ = s.card - 1 := by simp [Finset.card_erase_of_mem hi]

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace E]
  [DecidableEq ι] {a : E}

/-- A linear cardinal factor has continuous coefficients at unequal limiting nodes.
@isnad1 id=continuo.3h6v.s6.f37f056c18e6 from=translated src=- shape=bc5f6c05 vocab=d23efd26
-/
theorem continuousAt_coeff_basisDivisor {u v : E → 𝕜}
    (hu : ContinuousAt u a) (hv : ContinuousAt v a) (hne : u a ≠ v a) (k : ℕ) :
    ContinuousAt (fun y => (basisDivisor (u y) (v y)).coeff k) a := by
  simp only [basisDivisor, coeff_C_mul, coeff_sub, coeff_C]
  apply ContinuousAt.mul ((hu.sub hv).inv₀ (sub_ne_zero.mpr hne))
  apply ContinuousAt.sub continuousAt_const
  split_ifs
  · exact hv
  · exact continuousAt_const

/-- Every Lagrange cardinal coefficient is continuous in its node vector at
distinct limiting nodes.
@isnad1 id=continuo.3h8v.s7.9d72b150be5d from=translated src=- shape=66ca4c64 vocab=9886255b
-/
theorem continuousAt_coeff_basis {s : Finset ι} {v : E → ι → 𝕜} {i : ι}
    (hv : ∀ j, ContinuousAt (fun y => v y j) a)
    (hi : i ∈ s) (hinj : Set.InjOn (v a) s) (k : ℕ) :
    ContinuousAt (fun y => (Lagrange.basis s (v y) i).coeff k) a := by
  simp only [Lagrange.basis]
  apply Polynomial.continuousAt_coeff_prod
  intro j hj l
  exact continuousAt_coeff_basisDivisor (hv i) (hv j)
    (fun h => (Finset.mem_erase.mp hj).1 (hinj (Finset.mem_erase.mp hj).2 hi h.symm)) l

end Lagrange
