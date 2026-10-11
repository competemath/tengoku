module
public import Tengoku.Causalean.Causalean.Mathlib.MeasureTheory.FinsetValues
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Independence.Conditional.CondExp
public import Tengoku

/-!
# Product coordinates and density factorizations

This module fixes the product ordering and the measurable coordinate maps used by the
positive-density intersection theorem.  It also records the three density-factorization
predicates which express the two premises and the desired conclusion.  The definitions are
measure-theoretic and contain no graph- or paper-specific assumptions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection

universe uX uY uV uZ uM uΩ

/-- The canonical sample space for four random blocks, ordered as `X`, `Y`, `V`, and `Z`. -/
abbrev FourBlock (X : Type uX) (Y : Type uY) (V : Type uV) (Z : Type uZ) :=
  X × (Y × (V × Z))

/-- The first coordinate of a four-block sample is its `X` block. -/
def xCoord {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ} :
    FourBlock X Y V Z → X := fun q => q.1

/-- The second coordinate of a four-block sample is its `Y` block. -/
def yCoord {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ} :
    FourBlock X Y V Z → Y := fun q => q.2.1

/-- The third coordinate of a four-block sample is its `V` block. -/
def vCoord {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ} :
    FourBlock X Y V Z → V := fun q => q.2.2.1

/-- The fourth coordinate of a four-block sample is its `Z` block. -/
def zCoord {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ} :
    FourBlock X Y V Z → Z := fun q => q.2.2.2

/-- A four-block sample determines the conditioning pair `(Z,V)`. -/
def zvCoord {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ} :
    FourBlock X Y V Z → Z × V := fun q => (q.2.2.2, q.2.2.1)

/-- A four-block sample determines the conditioning pair `(Z,Y)`. -/
def zyCoord {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ} :
    FourBlock X Y V Z → Z × Y := fun q => (q.2.2.2, q.2.1)

/-- A four-block sample determines the combined block `(Y,V)`. -/
def yvCoord {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ} :
    FourBlock X Y V Z → Y × V := fun q => (q.2.1, q.2.2.1)

section MeasurableCoordinates

variable {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]

/-- [The first-coordinate map of a four-block observation is measurable](goal).
@isnad1 id=measurab.0h4v.s5.3515003ac0cd from=translated src=- shape=98c3035e vocab=95c19fee
-/
@[fun_prop] theorem measurable_xCoord : Measurable (@xCoord X Y V Z) := by
  exact measurable_fst

/-- The `Y` coordinate map on the four-block product is measurable.
@isnad1 id=measurab.0h4v.s5.f62cb186e750 from=translated src=- shape=6bf355dc vocab=61a0f734
-/
@[fun_prop] theorem measurable_yCoord : Measurable (@yCoord X Y V Z) := by
  exact measurable_fst.comp measurable_snd

/-- The `V` coordinate map on the four-block product is measurable.
@isnad1 id=measurab.0h4v.s5.8e73b0c53b81 from=translated src=- shape=ce52ef86 vocab=9e32fc75
-/
@[fun_prop] theorem measurable_vCoord : Measurable (@vCoord X Y V Z) := by
  exact measurable_fst.comp (measurable_snd.comp measurable_snd)

/-- The `Z` coordinate map on the four-block product is measurable.
@isnad1 id=measurab.0h4v.s5.22a253247a5e from=translated src=- shape=2f251bff vocab=666be701
-/
@[fun_prop] theorem measurable_zCoord : Measurable (@zCoord X Y V Z) := by
  exact measurable_snd.comp (measurable_snd.comp measurable_snd)

/-- The conditioning-pair map `(Z,V)` is measurable.
@isnad1 id=measurab.0h4v.s5.a66f1553b62e from=translated src=- shape=02a2330f vocab=f1680b00
-/
@[fun_prop] theorem measurable_zvCoord : Measurable (@zvCoord X Y V Z) := by
  change Measurable (fun q : X × (Y × (V × Z)) => (q.2.2.2, q.2.2.1))
  fun_prop

/-- The conditioning-pair map `(Z,Y)` is measurable.
@isnad1 id=measurab.0h4v.s5.309fd37ca0cf from=translated src=- shape=5f2dacba vocab=febba48a
-/
@[fun_prop] theorem measurable_zyCoord : Measurable (@zyCoord X Y V Z) := by
  change Measurable (fun q : X × (Y × (V × Z)) => (q.2.2.2, q.2.1))
  fun_prop

/-- The combined-block map `(Y,V)` is measurable.
@isnad1 id=measurab.0h4v.s5.a0094e51586d from=translated src=- shape=c4b3b03e vocab=c9b3de6d
-/
@[fun_prop] theorem measurable_yvCoord : Measurable (@yvCoord X Y V Z) := by
  change Measurable (fun q : X × (Y × (V × Z)) => (q.2.1, q.2.2.1))
  fun_prop

end MeasurableCoordinates

/-- Four coordinate reference measures determine their right-associated product reference
measure on the canonical four-block sample space. -/
def fourBlockReference {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]
    (μX : Measure X) (μY : Measure Y) (μV : Measure V) (μZ : Measure Z) :
    Measure (FourBlock X Y V Z) := μX.prod (μY.prod (μV.prod μZ))

section Factorizations

variable {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]

/-- A density factors according to `X ⟂ Y | (Z,V)` when it is almost everywhere a product of
one measurable factor depending on `(X,V,Z)` and another depending on `(Y,V,Z)`. -/
def FactorsXYGivenZV (μX : Measure X) (μY : Measure Y) (μV : Measure V) (μZ : Measure Z)
    (d : FourBlock X Y V Z → ℝ≥0∞) : Prop :=
  ∃ a : X × (V × Z) → ℝ≥0∞, ∃ b : Y × (V × Z) → ℝ≥0∞,
    Measurable a ∧ Measurable b ∧
      d =ᵐ[fourBlockReference μX μY μV μZ]
        (fun q => a (xCoord q, (vCoord q, zCoord q)) *
          b (yCoord q, (vCoord q, zCoord q)))

/-- A density factors according to `X ⟂ V | (Z,Y)` when it is almost everywhere a product of
one measurable factor depending on `(X,Y,Z)` and another depending on `(V,Y,Z)`. -/
def FactorsXVGivenZY (μX : Measure X) (μY : Measure Y) (μV : Measure V) (μZ : Measure Z)
    (d : FourBlock X Y V Z → ℝ≥0∞) : Prop :=
  ∃ a : X × (Y × Z) → ℝ≥0∞, ∃ b : V × (Y × Z) → ℝ≥0∞,
    Measurable a ∧ Measurable b ∧
      d =ᵐ[fourBlockReference μX μY μV μZ]
        (fun q => a (xCoord q, (yCoord q, zCoord q)) *
          b (vCoord q, (yCoord q, zCoord q)))

/-- A density factors according to `X ⟂ (Y,V) | Z` when it is almost everywhere a product of
one measurable factor depending on `(X,Z)` and another depending on `(Y,V,Z)`. -/
def FactorsXYVGivenZ (μX : Measure X) (μY : Measure Y) (μV : Measure V) (μZ : Measure Z)
    (d : FourBlock X Y V Z → ℝ≥0∞) : Prop :=
  ∃ a : X × Z → ℝ≥0∞, ∃ b : (Y × V) × Z → ℝ≥0∞,
    Measurable a ∧ Measurable b ∧
      d =ᵐ[fourBlockReference μX μY μV μZ]
        (fun q => a (xCoord q, zCoord q) * b ((yCoord q, vCoord q), zCoord q))

end Factorizations

/-- Four finite index blocks determine the ambient index set on which the finite-coordinate
specialization is stated. -/
def fourBlockIndices {M : Type uM} [DecidableEq M]
    (I J K L : Finset M) : Finset M := I ∪ J ∪ K ∪ L

section FourBlockSubsets

variable {M : Type uM} [DecidableEq M]
variable (I J K L : Finset M)

/-- The first block is contained in the union of all four blocks.
@isnad1 id=le.0h5v.s5.de460fe4fdd3 from=translated src=- shape=3ea99601 vocab=5d33de52
-/
theorem first_subset_fourBlock : I ⊆ fourBlockIndices I J K L := by
  simp [fourBlockIndices]

/-- The second block is contained in the union of all four blocks.
@isnad1 id=le.0h5v.s5.39bbbd5e4fb8 from=translated src=- shape=ffa6bf14 vocab=5d33de52
-/
theorem second_subset_fourBlock : J ⊆ fourBlockIndices I J K L := by
  intro i hi
  simp [fourBlockIndices, hi]

/-- The third block is contained in the union of all four blocks.
@isnad1 id=le.0h5v.s5.1c82f4558810 from=translated src=- shape=b71f49dd vocab=5d33de52
-/
theorem third_subset_fourBlock : K ⊆ fourBlockIndices I J K L := by
  intro i hi
  simp [fourBlockIndices, hi]

/-- The fourth block is contained in the union of all four blocks.
@isnad1 id=le.0h5v.s5.19c67de917f2 from=translated src=- shape=27d118b8 vocab=5d33de52
-/
theorem fourth_subset_fourBlock : L ⊆ fourBlockIndices I J K L := by
  intro i hi
  simp [fourBlockIndices, hi]

/-- [Four finite coordinate blocks](hyp:I,J,K,L) determine [a union of the second and third
blocks contained in their full union](goal).
@isnad1 id=le.0h5v.s5.851db8328145 from=translated src=- shape=16bb0d3e vocab=62ad50dd
-/
theorem secondThird_subset_fourBlock : J ∪ K ⊆ fourBlockIndices I J K L := by
  intro i hi
  simp only [fourBlockIndices, Finset.mem_union] at hi ⊢
  aesop

/-- The union of the fourth and third blocks is contained in the union of all four blocks.
@isnad1 id=le.0h5v.s5.0914ecea53ea from=translated src=- shape=a57e2199 vocab=62ad50dd
-/
theorem fourthThird_subset_fourBlock : L ∪ K ⊆ fourBlockIndices I J K L := by
  intro i hi
  simp only [fourBlockIndices, Finset.mem_union] at hi ⊢
  aesop

/-- The union of the fourth and second blocks is contained in the union of all four blocks.
@isnad1 id=le.0h5v.s5.88db52d0a2a7 from=translated src=- shape=dafc0392 vocab=62ad50dd
-/
theorem fourthSecond_subset_fourBlock : L ∪ J ⊆ fourBlockIndices I J K L := by
  intro i hi
  simp only [fourBlockIndices, Finset.mem_union] at hi ⊢
  aesop

end FourBlockSubsets

/-- Coordinate reference measures determine the product reference measure on assignments to the
union of four finite coordinate blocks. -/
def finiteBlockReference {M : Type uM} [DecidableEq M]
    {Ω : M → Type uΩ} [∀ i, MeasurableSpace (Ω i)]
    (I J K L : Finset M) (μ : ∀ i, Measure (Ω i)) :
    Measure (Causalean.Mathlib.MeasureTheory.ValuesOn (fourBlockIndices I J K L) Ω) :=
  Measure.pi fun i => μ i

end Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection
