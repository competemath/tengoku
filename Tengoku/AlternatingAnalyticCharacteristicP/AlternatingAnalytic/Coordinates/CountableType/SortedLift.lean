import Tengoku.Seed.Analysis.Normed.Module.Alternating.Basic
import Tengoku.Seed.Analysis.Normed.Group.Ultra
import Tengoku.Seed.Data.Fin.Tuple.Sort
import Tengoku.Seed.LinearAlgebra.Multilinear.Basis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The sorted lift on a basis with bounded coordinates

Let `b` be a Hamel basis of a normed space `M` over a nonarchimedean field `K`, indexed by a
linear order, whose coordinates satisfy `‖b.coord i y‖ * ‖b i‖ ≤ C * ‖y‖`. For a scalar
`k`-linear form `g` on `M`, the sorted lift
`S g (y₁, …, y_k) = ∑_{i₁ < ⋯ < i_k} g (b_{i₁}, …, b_{i_k}) ∏ₐ b.coord iₐ yₐ`
is a finitely supported sum. It defines a bounded linear operator `sortedLift` of norm at most
`C ^ k`, and unnormalized alternatization is a left inverse of `S` on alternating forms
(`alternatization_sortedLift`), in every characteristic. This is the sorted-lift step in the
proof of Proposition I.1.
-/

noncomputable section

open scoped BigOperators

namespace AlternatingAnalytic.CountableType

variable {K M ι : Type*} [NontriviallyNormedField K] [NormedAddCommGroup M] [NormedSpace K M]
  [LinearOrder ι]

/-- The coordinate monomial `y ↦ ∏ₐ b.coord (e a) (y a)` of an increasing index tuple.-/
def coordMonomial (b : Module.Basis ι K M) (k : ℕ) (e : Fin k ↪o ι) :
    MultilinearMap K (fun _ : Fin k => M) K :=
  (MultilinearMap.mkPiAlgebra K (Fin k) K).compLinearMap fun a => b.coord (e a)

theorem coordMonomial_apply (b : Module.Basis ι K M) (k : ℕ) (e : Fin k ↪o ι)
    (y : Fin k → M) : coordMonomial b k e y = ∏ a, b.coord (e a) (y a) := by
  simp [coordMonomial, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-- Only finitely many coordinate monomials are nonzero at a given tuple.-/
theorem coordMonomial_hasFiniteSupport (b : Module.Basis ι K M) (k : ℕ)
    (c : (Fin k ↪o ι) → K) (y : Fin k → M) :
    Function.HasFiniteSupport fun e : Fin k ↪o ι => c e * coordMonomial b k e y := by
  classical
  have hfin : ((fun e : Fin k ↪o ι => (e : Fin k → ι)) ⁻¹'
      Set.pi Set.univ fun a => ((b.repr (y a)).support : Set ι)).Finite :=
    (Set.Finite.pi fun a => (b.repr (y a)).support.finite_toSet).preimage
      (DFunLike.coe_injective.injOn)
  refine hfin.subset fun e he => ?_
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Finset.mem_coe,
    Finsupp.mem_support_iff, forall_true_left]
  intro a ha
  apply he
  simp only [coordMonomial_apply, Module.Basis.coord_apply]
  rw [Finset.prod_eq_zero (Finset.mem_univ a) ha, mul_zero]

theorem coordMonomial_summable (b : Module.Basis ι K M) (k : ℕ)
    (c : (Fin k ↪o ι) → K) (y : Fin k → M) :
    Summable fun e : Fin k ↪o ι => c e * coordMonomial b k e y :=
  summable_of_hasFiniteSupport (coordMonomial_hasFiniteSupport b k c y)

/-- The sorted lift of a scalar multilinear form, as an algebraic multilinear map.-/
def sortedLiftMultilinear (b : Module.Basis ι K M) (k : ℕ)
    (g : ContinuousMultilinearMap K (fun _ : Fin k => M) K) :
    MultilinearMap K (fun _ : Fin k => M) K where
  toFun y := ∑' e : Fin k ↪o ι, g (fun a => b (e a)) * coordMonomial b k e y
  map_update_add' y a u v := by
    simp only [MultilinearMap.map_update_add, mul_add]
    exact (coordMonomial_summable b k _ _).tsum_add (coordMonomial_summable b k _ _)
  map_update_smul' y a r u := by
    simp only [MultilinearMap.map_update_smul, smul_eq_mul]
    rw [← tsum_mul_left]
    exact tsum_congr fun e => by ring

theorem sortedLiftMultilinear_apply (b : Module.Basis ι K M) (k : ℕ)
    (g : ContinuousMultilinearMap K (fun _ : Fin k => M) K) (y : Fin k → M) :
    sortedLiftMultilinear b k g y =
      ∑' e : Fin k ↪o ι, g (fun a => b (e a)) * ∏ a, b.coord (e a) (y a) := by
  simp only [sortedLiftMultilinear, MultilinearMap.coe_mk, coordMonomial_apply]

variable [IsUltrametricDist K]

end AlternatingAnalytic.CountableType
