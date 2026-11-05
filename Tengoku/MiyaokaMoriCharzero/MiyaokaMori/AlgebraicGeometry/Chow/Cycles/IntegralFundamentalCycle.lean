import Tengoku.MiyaokaMoriCharzero.MiyaokaMori.AlgebraicGeometry.Chow.Cycles.AlgebraicCycles
import Tengoku.Seed.RingTheory.HopkinsLevitzki

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integral fundamental cycles with the actual generic multiplicities

The local ring at a component generic point of a Noetherian scheme has dimension zero,
hence is Artinian and has finite module length. Only after proving this finiteness do we
lift the existing extended multiplicities to integers. The dimension-indexed cycle keeps
exactly the components of the specified dimension, including their nonreduced lengths.

Sources: Stacks Tags 02QT and 02QU. The resulting cycles are inputs to the geometric
Cartier comparisons in Tags 0EPI and 02SQ; those comparisons are not proved here.
The intended consumers in the paper are the polarized degenerations of §2 and the
scheme-theoretic fiber multiplicities of Lemma 5.1.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace
open scoped Classical

namespace AlgebraicGeometry.Intersection

universe u

/-- A component generic point is maximal in the scheme's specialization order.
@isnad1 id=ismax.1h2v.s6.b06ca88ca8ec from=translated src=- shape=b0d31b70 vocab=bf7de4af
-/
theorem isMax_of_mem_genericPoints (X : Scheme.{u}) (x : X) (hx : x ∈ genericPoints X) :
    IsMax x := by
  intro y hxy
  apply Scheme.le_iff_specializes.mpr
  apply specializes_iff_closure_subset.mpr
  exact hx.2 isIrreducible_singleton.closure
    (Scheme.le_iff_specializes.mp hxy).closure_subset

/-- A generic local ring of a locally Noetherian scheme has finite module length.
@isnad1 id=lt.1h2v.s6.0bffd6ac5bd6 from=translated src=- shape=7b5f311e vocab=2ec36fbc
-/
theorem stalkLength_lt_top_of_generic (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) (hx : x ∈ genericPoints X) : stalkLength X x < ⊤ := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) :=
    krullDimLE_of_coheight_le
      (le_of_eq (Order.coheight_eq_zero.mpr (isMax_of_mem_genericPoints X x hx)))
  have : IsArtinianRing (X.presheaf.stalk x) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  exact (Module.length_ne_top (R := X.presheaf.stalk x)
    (M := X.presheaf.stalk x)).lt_top

/-- Every extended fundamental multiplicity of a locally Noetherian scheme is finite.
@isnad1 id=lt.0h2v.s4.11f502f381d7 from=translated src=- shape=05a45834 vocab=38abc561
-/
theorem fundamentalMultiplicity_lt_top (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    fundamentalMultiplicity X x < ⊤ := by
  by_cases hx : x ∈ genericPoints X
  · simpa only [fundamentalMultiplicity_of_generic X x hx] using
      stalkLength_lt_top_of_generic X x hx
  · simp [fundamentalMultiplicity_of_not_generic X x hx]

/-- The integer generic multiplicity, lifted using the proved finiteness of the actual length.-/
def integralFundamentalMultiplicity (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) : ℤ :=
  ENat.lift (fundamentalMultiplicity X x) (fundamentalMultiplicity_lt_top X x)

/-- Fundamental integer multiplicities are nonnegative.
@isnad1 id=le.0h2v.s4.bfe92f0bb506 from=translated src=- shape=c61b87e0 vocab=0976f844
-/
theorem integralFundamentalMultiplicity_nonneg
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    0 ≤ integralFundamentalMultiplicity X x := Int.natCast_nonneg _

/-- Lifting the finite extended multiplicity loses no coefficient.
@isnad1 id=eq.0h2v.s4.b4720865c11a from=translated src=- shape=b52b21ec vocab=252b1aa7
-/
@[simp]
theorem integralFundamentalMultiplicity_toNat
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    ((integralFundamentalMultiplicity X x).toNat : ℕ∞) = fundamentalMultiplicity X x := by
  simp [integralFundamentalMultiplicity]

/-- Away from component generic points, the integer multiplicity is zero.
@isnad1 id=eq.1h2v.s6.e21928d59fe6 from=translated src=- shape=87a9903b vocab=0a8f3fe4
-/
@[simp]
theorem integralFundamentalMultiplicity_of_not_generic
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) (hx : x ∉ genericPoints X) :
    integralFundamentalMultiplicity X x = 0 := by
  simp [integralFundamentalMultiplicity, fundamentalMultiplicity, hx]

/-- A Noetherian scheme has finitely many nonzero integer generic multiplicities.
@isnad1 id=finite.0h1v.s5.533e480c1345 from=translated src=- shape=519ba889 vocab=0ae9e6e2
-/
theorem integralFundamentalMultiplicity_finiteSupport (X : Scheme.{u}) [IsNoetherian X] :
    (Function.support (integralFundamentalMultiplicity X)).Finite := by
  apply (genericPoints.finite
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X))).subset
  intro x hx
  by_contra hn
  exact hx (integralFundamentalMultiplicity_of_not_generic X x hn)

/-- The canonical integer lift of the original extended fundamental cycle.-/
def integralFundamentalCycle (X : Scheme.{u}) [IsNoetherian X] : AlgebraicCycle X ℤ where
  toFun := integralFundamentalMultiplicity X
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ :=
    ⟨Set.univ, Filter.univ_mem, by simpa using integralFundamentalMultiplicity_finiteSupport X⟩

/-- The canonical cycle has the actual integer generic multiplicities.
@isnad1 id=eq.0h2v.s6.a1d0c0ac39fc from=translated src=- shape=2c7f292f vocab=3e9a927b
-/
@[simp]
theorem integralFundamentalCycle_apply (X : Scheme.{u}) [IsNoetherian X] (x : X) :
    integralFundamentalCycle X x = integralFundamentalMultiplicity X x := rfl

/-- The canonical integer cycle faithfully lifts every coefficient of the original cycle.
@isnad1 id=isintegr.0h1v.s3.e7c240abbbcf from=translated src=- shape=9b092fdc vocab=a6504700
-/
theorem integralFundamentalCycle_isIntegralCycleLift (X : Scheme.{u}) [IsNoetherian X] :
    IsIntegralCycleLift (extendedFundamentalCycle X) (integralFundamentalCycle X) := by
  intro x
  exact ⟨integralFundamentalMultiplicity_nonneg X x, integralFundamentalMultiplicity_toNat X x⟩

/-- The canonical cycle is the unique nonnegative integer lift of the extended cycle.-/
theorem eq_integralFundamentalCycle (X : Scheme.{u}) [IsNoetherian X]
    {α : AlgebraicCycle X ℤ} (hα : IsIntegralCycleLift (extendedFundamentalCycle X) α) :
    α = integralFundamentalCycle X :=
  hα.unique (integralFundamentalCycle_isIntegralCycleLift X)

/-- The actual dimension-`d` part of the integer fundamental cycle.-/
def dimensionFundamentalCycle (X : Scheme.{u}) [IsNoetherian X] (d : ℕ) :
    DimensionCycle X d := by
  let c : AlgebraicCycle X ℤ :=
    { toFun := fun x ↦ if pointClosureDimension X x = d then integralFundamentalCycle X x else 0
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := by
        intro x _
        refine ⟨Set.univ, Filter.univ_mem, ?_⟩
        apply (integralFundamentalMultiplicity_finiteSupport X).subset
        intro y hy
        by_cases hdim : pointClosureDimension X y = d
        · simpa [hdim, integralFundamentalCycle_apply] using hy
        · simp [hdim] at hy }
  refine ⟨c, isDimensionCycle_of_pointClosureDimension ?_⟩
  intro x hx
  by_contra hdim
  exact hx (by simp [c, hdim])

/-- Dimension filtering acts on the coefficients of the same fundamental cycle.
@isnad1 id=eq.0h3v.s8.05a2b167faff from=translated src=- shape=fa2ce9f1 vocab=9faa4376
-/
@[simp]
theorem dimensionFundamentalCycle_apply (X : Scheme.{u}) [IsNoetherian X] (d : ℕ) (x : X) :
    (dimensionFundamentalCycle X d).1 x =
      if pointClosureDimension X x = d then integralFundamentalMultiplicity X x else 0 := rfl

/-- Dimension filtering preserves effectivity of the actual fundamental cycle.
@isnad1 id=le.0h3v.s7.3cd2bacb7307 from=translated src=- shape=0cdd4114 vocab=e99b7384
-/
theorem dimensionFundamentalCycle_nonneg (X : Scheme.{u}) [IsNoetherian X] (d : ℕ) (x : X) :
    0 ≤ (dimensionFundamentalCycle X d).1 x := by
  rw [dimensionFundamentalCycle_apply]
  split_ifs
  · exact integralFundamentalMultiplicity_nonneg X x
  · exact le_rfl

/-- The dimension-`d` coefficient is precisely the corresponding finite generic length.
@isnad1 id=eq.0h3v.s8.10fced969a14 from=translated src=- shape=f2d53ef0 vocab=61e53b8f
-/
theorem dimensionFundamentalCycle_toNat (X : Scheme.{u}) [IsNoetherian X] (d : ℕ) (x : X) :
    (((dimensionFundamentalCycle X d).1 x).toNat : ℕ∞) =
      if pointClosureDimension X x = d then fundamentalMultiplicity X x else 0 := by
  rw [dimensionFundamentalCycle_apply]
  split_ifs <;> simp

/-- On a pure-dimensional scheme, the dimension filter retains the entire fundamental cycle.
@isnad1 id=eq.1h2v.s7.3c8c9b0f1b08 from=translated src=- shape=47aef6d6 vocab=1ff56e82
-/
theorem dimensionFundamentalCycle_eq_of_isPureDimension
    (X : Scheme.{u}) [IsNoetherian X] (d : ℕ) (hdim : IsPureDimension X d) :
    (dimensionFundamentalCycle X d).1 = integralFundamentalCycle X := by
  apply DFunLike.ext
  intro x
  by_cases hx : x ∈ genericPoints X
  · simp [hdim x hx]
  · simp [integralFundamentalMultiplicity_of_not_generic X x hx]

/-- The actual integer fundamental cycle of the empty scheme is zero.
@isnad1 id=eq.0h1v.s6.824d1ef1ecf5 from=translated src=- shape=b7e4b5b5 vocab=1cf90508
-/
@[simp]
theorem integralFundamentalCycle_eq_zero_of_isEmpty
    (X : Scheme.{u}) [IsNoetherian X] [IsEmpty X] : integralFundamentalCycle X = 0 := by
  apply DFunLike.ext
  intro x
  exact isEmptyElim x

/-- Every dimension part of the empty scheme's fundamental cycle is zero.
@isnad1 id=eq.0h2v.s7.335e8f55fc6a from=translated src=- shape=56e2daec vocab=550c8136
-/
@[simp]
theorem dimensionFundamentalCycle_eq_zero_of_isEmpty
    (X : Scheme.{u}) [IsNoetherian X] [IsEmpty X] (d : ℕ) :
    (dimensionFundamentalCycle X d).1 = 0 := by
  apply DFunLike.ext
  intro x
  exact isEmptyElim x

end AlgebraicGeometry.Intersection
