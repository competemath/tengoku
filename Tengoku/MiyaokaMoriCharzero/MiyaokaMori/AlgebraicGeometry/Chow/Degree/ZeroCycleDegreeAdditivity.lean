import Tengoku.MiyaokaMoriCharzero.MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite sums of dimension cycles and additivity of their actual zero-cycle degree

All constructions use `DimensionCycle X d = ↥(AlgebraicGeometry.cycleSubgroup X d)`, the subgroup of Mathlib algebraic cycles. Their
coefficients are the actual pointwise sum or integer multiple. In dimension zero, degree is the
existing `rawZeroCycleDegree`, with the residue-field weights and finiteness supplied by properness.

The finite weighted sum is used by the one-cycle Cartier action in the main theorem: each integral
curve's divisor is pushed to the target, then summed with the original one-cycle's integer
multiplicity. No degree evaluator or numerical equality is supplied as an extra input.

Sources: Stacks Project, Tags 0AZ1 and 0AZ2; Theorem 1.1 of the paper.
This file concerns actual cycles before descent through rational equivalence.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators

namespace AlgebraicGeometry.Intersection

universe u v

namespace IsDimensionCycle

/-! `IsDimensionCycle X d α` is `α ∈ AlgebraicGeometry.cycleSubgroup X d`;
the closure properties below are the subgroup axioms, kept under their old names for the callers. -/

/-- The zero algebraic cycle is concentrated in any specified dimension.
@isnad1 id=isdimens.0h2v.s6.b85113207381 from=translated src=- shape=51a0fed0 vocab=a50542f0
-/
theorem zero (X : Scheme.{u}) (d : ℕ) : IsDimensionCycle X d 0 :=
  (AlgebraicGeometry.cycleSubgroup X d).zero_mem

/-- Adding cycles of the same dimension preserves the dimension of every nonzero coefficient.
@isnad1 id=isdimens.2h4v.s6.8c9807ef0df8 from=translated src=- shape=570dd09e vocab=2667d2b8
-/
theorem add {X : Scheme.{u}} {d : ℕ} {α β : AlgebraicCycle X ℤ}
    (hα : IsDimensionCycle X d α) (hβ : IsDimensionCycle X d β) :
    IsDimensionCycle X d (α + β) :=
  (AlgebraicGeometry.cycleSubgroup X d).add_mem hα hβ

/-- Negation preserves the dimension of a cycle.
@isnad1 id=isdimens.1h3v.s5.1ef71590b023 from=translated src=- shape=bd4d3f81 vocab=88a400f0
-/
theorem neg {X : Scheme.{u}} {d : ℕ} {α : AlgebraicCycle X ℤ}
    (hα : IsDimensionCycle X d α) : IsDimensionCycle X d (-α) :=
  (AlgebraicGeometry.cycleSubgroup X d).neg_mem hα

/-- Integer multiplication preserves the dimension, including zero and negative multiplicities.
@isnad1 id=isdimens.1h4v.s6.077433eb71be from=translated src=- shape=17a64dce vocab=f8bc13d2
-/
theorem zsmul {X : Scheme.{u}} {d : ℕ} {α : AlgebraicCycle X ℤ}
    (hα : IsDimensionCycle X d α) (n : ℤ) : IsDimensionCycle X d (n • α) :=
  (AlgebraicGeometry.cycleSubgroup X d).zsmul_mem hα n

/-- A finite sum of cycles of the same dimension remains concentrated in that dimension.
@isnad1 id=isdimens.1h5v.s6.04a713f7e204 from=translated src=- shape=e22e9a07 vocab=6f46ad17
-/
theorem finsetSum {X : Scheme.{u}} {d : ℕ} {ι : Type v} (s : Finset ι)
    (α : ι → AlgebraicCycle X ℤ) (hα : ∀ i ∈ s, IsDimensionCycle X d (α i)) :
    IsDimensionCycle X d (∑ i ∈ s, α i) :=
  sum_mem hα

end IsDimensionCycle

namespace DimensionCycle

/-! `DimensionCycle X d = ↥(AlgebraicGeometry.cycleSubgroup X d)` carries the `AddCommGroup`
structure of a subgroup; the names below are aliases for `0`, `+`, `-`, `•`, `∑` kept for the
callers. -/

/-- The zero `d`-cycle (alias for `0`).-/
abbrev zero (X : Scheme.{u}) (d : ℕ) : DimensionCycle X d := 0

/-- Addition of `d`-cycles (alias for `+`).-/
abbrev add {X : Scheme.{u}} {d : ℕ} (α β : DimensionCycle X d) : DimensionCycle X d := α + β

/-- Negation of a `d`-cycle (alias for `-`).-/
abbrev neg {X : Scheme.{u}} {d : ℕ} (α : DimensionCycle X d) : DimensionCycle X d := -α

/-- Integer multiple of a `d`-cycle (alias for `n • α`).-/
abbrev zsmul {X : Scheme.{u}} {d : ℕ} (n : ℤ) (α : DimensionCycle X d) :
    DimensionCycle X d := n • α

/-- A finite sum of `d`-cycles (alias for `∑`).-/
abbrev finsetSum {X : Scheme.{u}} {d : ℕ} {ι : Type v} (s : Finset ι)
    (α : ι → DimensionCycle X d) : DimensionCycle X d := ∑ i ∈ s, α i

/-- A finite integer-weighted sum of `d`-cycles, allowing cancellation and an empty index set.-/
abbrev weightedSum {X : Scheme.{u}} {d : ℕ} {ι : Type v} (s : Finset ι)
    (n : ι → ℤ) (α : ι → DimensionCycle X d) : DimensionCycle X d :=
  finsetSum s (fun i ↦ zsmul (n i) (α i))

/--
@isnad1 id=eq.0h2v.s7.b65102a60955 from=translated src=- shape=d23f8dd4 vocab=2f6b6bde
-/
@[simp]
theorem zero_val (X : Scheme.{u}) (d : ℕ) : (zero X d).1 = 0 := rfl

/--
@isnad1 id=eq.0h4v.s9.0c45f73cce48 from=translated src=- shape=e2ddcff3 vocab=41f8e726
-/
@[simp]
theorem add_val {X : Scheme.{u}} {d : ℕ} (α β : DimensionCycle X d) :
    (add α β).1 = α.1 + β.1 := rfl

/--
@isnad1 id=eq.0h3v.s8.6dc897fcf7de from=translated src=- shape=b107fe2f vocab=16014203
-/
@[simp]
theorem neg_val {X : Scheme.{u}} {d : ℕ} (α : DimensionCycle X d) :
    (neg α).1 = -α.1 := rfl

/--
@isnad1 id=eq.0h4v.s8.731cf72ab9ba from=translated src=- shape=3d8e8d55 vocab=5dcc7132
-/
@[simp]
theorem zsmul_val {X : Scheme.{u}} {d : ℕ} (n : ℤ) (α : DimensionCycle X d) :
    (zsmul n α).1 = n • α.1 := rfl

/--
@isnad1 id=eq.0h5v.s8.a400fa804bc3 from=translated src=- shape=f6f3c16a vocab=2554bde7
-/
@[simp]
theorem finsetSum_val {X : Scheme.{u}} {d : ℕ} {ι : Type v} (s : Finset ι)
    (α : ι → DimensionCycle X d) : (finsetSum s α).1 = ∑ i ∈ s, (α i).1 :=
  AddSubmonoidClass.coe_finsetSum _ _

/--
@isnad1 id=eq.0h6v.s8.ef50dd85c533 from=translated src=- shape=c69aedc6 vocab=7f1f9de4
-/
@[simp]
theorem weightedSum_val {X : Scheme.{u}} {d : ℕ} {ι : Type v} (s : Finset ι)
    (n : ι → ℤ) (α : ι → DimensionCycle X d) :
    (weightedSum s n α).1 = ∑ i ∈ s, n i • (α i).1 := by
  rw [weightedSum, finsetSum_val]
  rfl

/-- The weighted sum has precisely the expected coefficient at every scheme point.
@isnad1 id=eq.0h7v.s8.63730ae4e62a from=translated src=- shape=3472235d vocab=4c54590b
-/
theorem weightedSum_apply {X : Scheme.{u}} {d : ℕ} {ι : Type v} (s : Finset ι)
    (n : ι → ℤ) (α : ι → DimensionCycle X d) (x : X) :
    (weightedSum s n α).1 x = ∑ i ∈ s, n i * (α i).1 x := by
  simp [Function.locallyFinsuppWithin.coe_sum, Function.locallyFinsuppWithin.coe_zsmul,
    Finset.sum_apply, zsmul_eq_mul]

/--
@isnad1 id=eq.0h4v.s4.ac31d75e939a from=translated src=- shape=65e38a03 vocab=7cc48572
-/
@[simp]
theorem finsetSum_empty {X : Scheme.{u}} {d : ℕ} {ι : Type v}
    (α : ι → DimensionCycle X d) : finsetSum ∅ α = zero X d := by
  apply Subtype.ext
  simp

/--
@isnad1 id=eq.1h6v.s6.228b51104c41 from=translated src=- shape=937bfde5 vocab=8e214d92
-/
theorem finsetSum_insert {X : Scheme.{u}} {d : ℕ} {ι : Type v} (s : Finset ι)
    (α : ι → DimensionCycle X d) (i : ι) (hi : i ∉ s) :
    finsetSum (insert i s) α = add (α i) (finsetSum s α) := by
  apply Subtype.ext
  simp [hi]

end DimensionCycle

/-- The degree of the actual zero cycle is zero.
@isnad1 id=eq.0h3v.s5.dac9ac9e7034 from=translated src=- shape=c431dbf0 vocab=d522ac09
-/
@[simp]
theorem rawZeroCycleDegree_zero {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] :
    rawZeroCycleDegree f (DimensionCycle.zero X 0) = 0 := by
  rw [rawZeroCycleDegree_eq_sum_on f (DimensionCycle.zero X 0) ∅ (by
    intro x _
    rfl)]
  simp

/-- The residue-field-weighted degree is additive on actual zero cycles.
@isnad1 id=eq.0h5v.s6.7d5428d0b099 from=translated src=- shape=c9d2873e vocab=cc47a543
-/
theorem rawZeroCycleDegree_add {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] (α β : DimensionCycle X 0) :
    rawZeroCycleDegree f (DimensionCycle.add α β) =
      rawZeroCycleDegree f α + rawZeroCycleDegree f β := by
  let s := (properCycle_finiteSupport f α.1).toFinset ∪
    (properCycle_finiteSupport f β.1).toFinset
  have hα : ∀ x, x ∉ s → α.1 x = 0 := by
    intro x hx
    by_contra hn
    apply hx
    exact Finset.mem_union.mpr (Or.inl ((properCycle_finiteSupport f α.1).mem_toFinset.mpr hn))
  have hβ : ∀ x, x ∉ s → β.1 x = 0 := by
    intro x hx
    by_contra hn
    apply hx
    exact Finset.mem_union.mpr (Or.inr ((properCycle_finiteSupport f β.1).mem_toFinset.mpr hn))
  rw [rawZeroCycleDegree_eq_sum_on f (DimensionCycle.add α β) s (by
    intro x hx
    change α.1 x + β.1 x = 0
    simp [hα x hx, hβ x hx]),
    rawZeroCycleDegree_eq_sum_on f α s hα, rawZeroCycleDegree_eq_sum_on f β s hβ]
  simp [Function.locallyFinsuppWithin.coe_add, add_mul, Finset.sum_add_distrib]

/-- Actual zero-cycle degree commutes with every integer multiplicity.
@isnad1 id=eq.0h5v.s6.ae0bf24aa303 from=translated src=- shape=ef13c1f9 vocab=78572807
-/
theorem rawZeroCycleDegree_zsmul {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] (n : ℤ) (α : DimensionCycle X 0) :
    rawZeroCycleDegree f (DimensionCycle.zsmul n α) = n * rawZeroCycleDegree f α := by
  let s := (properCycle_finiteSupport f α.1).toFinset
  have hα : ∀ x, x ∉ s → α.1 x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((properCycle_finiteSupport f α.1).mem_toFinset.mpr hn)
  rw [rawZeroCycleDegree_eq_sum_on f (DimensionCycle.zsmul n α) s (by
    intro x hx
    change n • α.1 x = 0
    simp [hα x hx]), rawZeroCycleDegree_eq_sum_on f α s hα]
  simp [Function.locallyFinsuppWithin.coe_zsmul, zsmul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Negating the actual zero cycle negates its residue-field-weighted degree.
@isnad1 id=eq.0h4v.s6.f919b8c3e5e4 from=translated src=- shape=379b6663 vocab=950b660a
-/
theorem rawZeroCycleDegree_neg {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] (α : DimensionCycle X 0) :
    rawZeroCycleDegree f (DimensionCycle.neg α) = -rawZeroCycleDegree f α := by
  have heq : DimensionCycle.neg α = DimensionCycle.zsmul (-1) α := by
    apply Subtype.ext
    simp
  rw [heq, rawZeroCycleDegree_zsmul]
  simp

/-- The degree of a finite sum of actual zero cycles is the sum of their degrees.
@isnad1 id=eq.0h6v.s6.64c6eccc28b8 from=translated src=- shape=fb7662aa vocab=88d1c6de
-/
theorem rawZeroCycleDegree_finsetSum {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] {ι : Type v}
    (s : Finset ι) (α : ι → DimensionCycle X 0) :
    rawZeroCycleDegree f (DimensionCycle.finsetSum s α) =
      ∑ i ∈ s, rawZeroCycleDegree f (α i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    rw [DimensionCycle.finsetSum_insert s α i hi, rawZeroCycleDegree_add,
      ih, Finset.sum_insert hi]

/-- Finite weighted sums retain the one-cycle multiplicities in their actual zero-cycle degree.
@isnad1 id=eq.0h7v.s6.551fcf9ee910 from=translated src=- shape=cae6fde9 vocab=61a304cd
-/
theorem rawZeroCycleDegree_weightedSum {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] {ι : Type v}
    (s : Finset ι) (n : ι → ℤ) (α : ι → DimensionCycle X 0) :
    rawZeroCycleDegree f (DimensionCycle.weightedSum s n α) =
      ∑ i ∈ s, n i * rawZeroCycleDegree f (α i) := by
  rw [DimensionCycle.weightedSum, rawZeroCycleDegree_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  exact rawZeroCycleDegree_zsmul f (n i) (α i)

end AlgebraicGeometry.Intersection
