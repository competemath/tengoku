import Tengoku.TdaLib.TDA.Persistence.FinitePMatchingCost
import Tengoku.TdaLib.TDA.Persistence.FiniteBoundaryTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite boundary transport with real matching exponents

Costs raise geometric distances to `p`, while real mass coefficients and boundary
residuals remain linear. The existing assignment/Birkhoff bridge proves equality
with the powered partial-matching minimum. At `1 ≤ p`, the rooted optimum also
minimizes rooted candidate costs. A minimizing incidence plan is constructed from
a powered-cost minimizing matching; first-order optimizers are not reused.

These are finite unit-occurrence reservoir matrices. The maximum ground norm is
independent of the real matching exponent. The finite cost-matrix adaptation of
Divol–Lacombe and Lacombe–Cuturi–Oudot does not identify all Radon couplings.
`FinitePBoundaryTransportLaws` supplies the rooted distance laws for `1 ≤ p`.
-/

noncomputable section
namespace TDA.Persistence
open scoped Classical

namespace FiniteBoundaryPlan
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Power only the distance coefficients; transported and residual masses stay linear.-/
def powerCost (a : FiniteBoundaryPlan I J) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  a.linearCost (fun i j => (finitePairCost (x i) (y j)).toReal ^ p)
    (fun i => (diagonalCost (x i)).toReal ^ p) (fun j => (diagonalCost (y j)).toReal ^ p)

/--
@isnad1 id=le.0h6v.s5.04c8cbee2a93 from=translated src=- shape=0754fa8d vocab=50f0f9e8
-/
theorem powerCost_nonneg (a : FiniteBoundaryPlan I J) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : 0 ≤ a.powerCost p x y :=
  a.linearCost_nonneg _ _ _
    (fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)

/--
@isnad1 id=eq.0h5v.s5.071e768a0cd6 from=translated src=- shape=e7e389fb vocab=e254854c
-/
@[simp] theorem powerCost_one (a : FiniteBoundaryPlan I J)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : a.powerCost 1 x y = a.cost x y := by
  simp only [powerCost, linearCost, Real.rpow_one, cost]

/--
@isnad1 id=eq.0h6v.s5.0ee8fa6be826 from=translated src=- shape=f7305982 vocab=62bef440
-/
theorem powerCost_ofMatching (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    (ofMatching M).powerCost p x y = M.totalFinitePowerCost p x y :=
  linearCost_ofMatching M _ _ _

/-- A genuine partial matching is no more expensive than any fractional real plan.
@isnad1 id=ex.0h6v.s5.229bd7a77085 from=translated src=- shape=df73a86e vocab=afa0f6cb
-/
theorem exists_powerMatching_cost_le (a : FiniteBoundaryPlan I J) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      M.totalFinitePowerCost p x y ≤ a.powerCost p x y :=
  a.exists_matching_linearCost_le _ _ _

/--
@isnad1 id=le.0h6v.s5.4ffc392bb258 from=translated src=- shape=2b4d8af1 vocab=3cac4673
-/
theorem matchingPowerCost_le_powerCost (a : FiniteBoundaryPlan I J) (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerMatchingCost p x y ≤ a.powerCost p x y := by
  obtain ⟨M, hM⟩ := a.exists_powerMatching_cost_le p x y
  exact (finitePowerMatchingCost_le_matching p x y M).trans hM

end FiniteBoundaryPlan

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Real infimum of powered costs over every feasible finite reservoir matrix.-/
def finitePowerBoundaryTransportCost (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  ⨅ a : FiniteBoundaryPlan I J, a.powerCost p x y

/-- Reciprocal-power root after optimization. Its PD exponent domain is `1 ≤ p`.-/
def finitePBoundaryTransportCost (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  finitePowerBoundaryTransportCost p x y ^ p⁻¹

/--
@isnad1 id=le.0h6v.s5.52aa6f27322d from=translated src=- shape=cd3565dc vocab=10c99f5e
-/
theorem finitePowerBoundaryTransportCost_le_plan (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (a : FiniteBoundaryPlan I J) :
    finitePowerBoundaryTransportCost p x y ≤ a.powerCost p x y :=
  ciInf_le ⟨0, by rintro _ ⟨b, rfl⟩; exact b.powerCost_nonneg p x y⟩ a

/-- Finite assignment equality, with the matching exponent independent of ground norm.
@isnad1 id=eq.0h5v.s5.757af3e9f863 from=translated src=- shape=e24fe687 vocab=72e73700
-/
theorem finitePowerBoundaryTransportCost_eq_matchingCost (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerBoundaryTransportCost p x y = finitePowerMatchingCost p x y := by
  apply le_antisymm
  · obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
    calc
      _ ≤ (FiniteBoundaryPlan.ofMatching M).powerCost p x y :=
        finitePowerBoundaryTransportCost_le_plan _ _ _ _
      _ = _ := by rw [FiniteBoundaryPlan.powerCost_ofMatching, hM]
  · exact le_ciInf fun a => a.matchingPowerCost_le_powerCost p x y

/--
@isnad1 id=le.0h5v.s5.2a7a17460294 from=translated src=- shape=96f5c5ea vocab=48bf8fbe
-/
theorem finitePowerBoundaryTransportCost_nonneg (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : 0 ≤ finitePowerBoundaryTransportCost p x y := by
  rw [finitePowerBoundaryTransportCost_eq_matchingCost]
  exact finitePowerMatchingCost_nonneg p x y

/-- Some integral incidence plan attains the optimum; fractional optima can coexist.
@isnad1 id=ex.0h5v.s5.d4c126d6c6ca from=translated src=- shape=c23a0875 vocab=177ceab7
-/
theorem exists_minimizing_powerBoundaryPlan (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      (FiniteBoundaryPlan.ofMatching M).powerCost p x y = finitePowerBoundaryTransportCost p x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
  exact ⟨M, by rw [FiniteBoundaryPlan.powerCost_ofMatching,
    finitePowerBoundaryTransportCost_eq_matchingCost, hM]⟩

/--
@isnad1 id=eq.0h5v.s5.326530262a2f from=translated src=- shape=e24fe687 vocab=d9544c75
-/
theorem finitePBoundaryTransportCost_eq_matchingCost (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p x y = finitePMatchingCost p x y := by
  simp only [finitePBoundaryTransportCost, finitePMatchingCost,
    finitePowerBoundaryTransportCost_eq_matchingCost]

/--
@isnad1 id=le.0h5v.s5.ff1027f4a4fd from=translated src=- shape=96f5c5ea vocab=4273cd30
-/
theorem finitePBoundaryTransportCost_nonneg (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : 0 ≤ finitePBoundaryTransportCost p x y :=
  Real.rpow_nonneg (finitePowerBoundaryTransportCost_nonneg p x y) _

/--
@isnad1 id=le.1h6v.s6.fdf0a7b200f6 from=translated src=- shape=0dfaf19d vocab=fc64d9ed
-/
theorem finitePBoundaryTransportCost_le_plan {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (a : FiniteBoundaryPlan I J) :
    finitePBoundaryTransportCost p x y ≤ a.powerCost p x y ^ p⁻¹ :=
  Real.rpow_le_rpow (finitePowerBoundaryTransportCost_nonneg p x y)
    (finitePowerBoundaryTransportCost_le_plan p x y a)
    (inv_nonneg.mpr (le_trans zero_le_one hp))

/-- The same incidence plan attains the rooted optimum.
@isnad1 id=ex.0h5v.s6.26985b163499 from=translated src=- shape=1e7571f7 vocab=a6f00c90
-/
theorem exists_minimizing_pBoundaryPlan (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      (FiniteBoundaryPlan.ofMatching M).powerCost p x y ^ p⁻¹ = finitePBoundaryTransportCost p x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_powerBoundaryPlan p x y
  exact ⟨M, by rw [hM]; rfl⟩

/-- Attainment and root monotonicity identify the infimum of rooted plan costs.
@isnad1 id=eq.1h5v.s6.b40c5fe3b775 from=translated src=- shape=9c6a02eb vocab=613a213a
-/
theorem finitePBoundaryTransportCost_eq_iInf {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p x y = ⨅ a : FiniteBoundaryPlan I J, a.powerCost p x y ^ p⁻¹ := by
  have hbd : BddBelow (Set.range fun a : FiniteBoundaryPlan I J => a.powerCost p x y ^ p⁻¹) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact Real.rpow_nonneg (a.powerCost_nonneg p x y) _
  apply le_antisymm
  · exact le_ciInf fun a => finitePBoundaryTransportCost_le_plan hp x y a
  · obtain ⟨M, hM⟩ := exists_minimizing_pBoundaryPlan p x y
    exact (ciInf_le hbd (FiniteBoundaryPlan.ofMatching M)).trans_eq hM

/--
@isnad1 id=eq.0h4v.s5.c3628f81c6b7 from=translated src=- shape=aab87b45 vocab=28876364
-/
@[simp] theorem finitePowerBoundaryTransportCost_one
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerBoundaryTransportCost 1 x y = finiteFirstOrderBoundaryTransportCost x y := by
  rw [finitePowerBoundaryTransportCost_eq_matchingCost, finitePowerMatchingCost_one,
    finiteFirstOrderBoundaryTransportCost_eq_matchingCost]

/--
@isnad1 id=eq.0h4v.s5.cfad16a2f7ec from=translated src=- shape=aab87b45 vocab=10ce0db5
-/
@[simp] theorem finitePBoundaryTransportCost_one
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost 1 x y = finiteFirstOrderBoundaryTransportCost x y := by
  simp [finitePBoundaryTransportCost]

/--
@isnad1 id=eq.0h5v.s5.b9bba7604bed from=translated src=- shape=b96489cd vocab=5df59955
-/
theorem finitePowerBoundaryTransportCost_of_isEmpty_right [IsEmpty J]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerBoundaryTransportCost p x y = ∑ i, (diagonalCost (x i)).toReal ^ p := by
  rw [finitePowerBoundaryTransportCost_eq_matchingCost, finitePowerMatchingCost_of_isEmpty_right]

/--
@isnad1 id=eq.0h5v.s5.7b0560ac9044 from=translated src=- shape=1514b76f vocab=5df59955
-/
theorem finitePowerBoundaryTransportCost_of_isEmpty_left [IsEmpty I]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerBoundaryTransportCost p x y = ∑ j, (diagonalCost (y j)).toReal ^ p := by
  rw [finitePowerBoundaryTransportCost_eq_matchingCost, finitePowerMatchingCost_of_isEmpty_left]

/--
@isnad1 id=eq.0h5v.s5.2723bd5703b0 from=translated src=- shape=224fad33 vocab=e8280ec1
-/
@[simp] theorem finitePowerBoundaryTransportCost_empty [IsEmpty I] [IsEmpty J]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : finitePowerBoundaryTransportCost p x y = 0 := by
  rw [finitePowerBoundaryTransportCost_of_isEmpty_right]; exact Fintype.sum_empty _

/--
@isnad1 id=eq.0h5v.s6.a48086612c9b from=translated src=- shape=5568a38f vocab=87aada5d
-/
theorem finitePBoundaryTransportCost_of_isEmpty_right [IsEmpty J]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p x y = (∑ i, (diagonalCost (x i)).toReal ^ p) ^ p⁻¹ := by
  rw [finitePBoundaryTransportCost, finitePowerBoundaryTransportCost_of_isEmpty_right]

/--
@isnad1 id=eq.0h5v.s6.42418f5eb291 from=translated src=- shape=9269f699 vocab=87aada5d
-/
theorem finitePBoundaryTransportCost_of_isEmpty_left [IsEmpty I]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p x y = (∑ j, (diagonalCost (y j)).toReal ^ p) ^ p⁻¹ := by
  rw [finitePBoundaryTransportCost, finitePowerBoundaryTransportCost_of_isEmpty_left]

/--
@isnad1 id=eq.1h5v.s5.9e5df537fbbc from=translated src=- shape=24831e73 vocab=fd30c541
-/
@[simp] theorem finitePBoundaryTransportCost_empty [IsEmpty I] [IsEmpty J]
    {p : ℝ} (hp : 1 ≤ p) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p x y = 0 := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_empty hp x y

/--
@isnad1 id=eq.0h9v.s6.5548109c8cf5 from=translated src=- shape=2fbafb3a vocab=aeb719eb
-/
theorem finitePowerBoundaryTransportCost_reindex {I' J' : Type*} [Fintype I'] [Fintype J']
    (u : I' ≃ I) (v : J' ≃ J) (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerBoundaryTransportCost p (x ∘ u) (y ∘ v) = finitePowerBoundaryTransportCost p x y := by
  simp only [finitePowerBoundaryTransportCost_eq_matchingCost, finitePowerMatchingCost_reindex]

/--
@isnad1 id=eq.0h9v.s6.f57901515827 from=translated src=- shape=2fbafb3a vocab=07088818
-/
theorem finitePBoundaryTransportCost_reindex {I' J' : Type*} [Fintype I'] [Fintype J']
    (u : I' ≃ I) (v : J' ≃ J) (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p (x ∘ u) (y ∘ v) = finitePBoundaryTransportCost p x y := by
  simp only [finitePBoundaryTransportCost, finitePowerBoundaryTransportCost_reindex]

end TDA.Persistence
