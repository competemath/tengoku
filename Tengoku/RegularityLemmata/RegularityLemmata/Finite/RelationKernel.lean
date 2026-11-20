/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.RectKernel
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.PairDensity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relation indicators as rectangular kernels

The bridge between the two independent cores. `RegularityLemmata/Finite/RectKernel.lean` knows
nothing about relations and `RegularityLemmata/Finite/PairDensity.lean` knows nothing about kernels;
this file imports both and identifies the indicator kernel's uniform-counting sum and average with
`pairCount` and `pairDensity`.

```
PairDensity ────┐
                ├─→ RelationKernel
RectKernel ─────┘
```

Keeping the two cores mutually independent is deliberate: the box layer wants masses without
kernels, and the kernel layer wants to develop its algebra and estimates without a relation
in sight.

Indicators are the `[0,1]`-valued case, so they satisfy `IsUnitIntervalOnRectangle`
unconditionally — this is the predicate that exists separately from `IsAbsBoundedOnRectangle`
precisely so that indicators and signed residuals are not conflated.
-/

namespace RegularityLemmata

variable {α β : Type*}

/-- The `0/1` indicator kernel of a relation.-/
def relationKernel (R : α → β → Prop) [DecidableRel R] : RectKernel α β :=
  fun a b => if R a b then 1 else 0

variable {R : α → β → Prop} [DecidableRel R] {A : Finset α} {B : Finset β}

/--
@isnad1 id=eq.0h5v.s5.4380def120b7 from=translated src=- shape=c46d79ed vocab=45bf6d63
-/
@[simp] theorem relationKernel_apply (a : α) (b : β) :
    relationKernel R a b = if R a b then 1 else 0 := rfl

/-- Indicators take values in `[0,1]`, on every rectangle.
@isnad1 id=isunitin.0h5v.s4.a40ed72ba161 from=translated src=- shape=d6820874 vocab=52d1152b
-/
theorem isUnitIntervalOnRectangle_relationKernel (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) : IsUnitIntervalOnRectangle (relationKernel R) A B := by
  intro a _ b _
  rw [Set.mem_Icc, relationKernel]
  split <;> norm_num

/-- The indicator's absolute bound is `1` — the weaker signed statement, recorded so a
consumer working with residuals can use it without reproving.
@isnad1 id=isabsuni.0h5v.s4.d7aa9f112f89 from=translated src=- shape=d6820874 vocab=6cd02dce
-/
theorem isAbsUnitBoundedOnRectangle_relationKernel (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) : IsAbsUnitBoundedOnRectangle (relationKernel R) A B :=
  (isUnitIntervalOnRectangle_relationKernel R A B).absBounded (by norm_num) le_rfl

/-! ### The pair bridges -/

/-- **The counting bridge**: at uniform weights, the indicator kernel's rectangle sum is the
pair count.
@isnad1 id=eq.0h5v.s5.a9acf4b96c37 from=translated src=- shape=633ff0d1 vocab=c3512de3
-/
theorem rectSum_relationKernel (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) :
    rectSum (relationKernel R) (fun _ => 1) (fun _ => 1) A B = (pairCount R A B : ℝ) := by
  classical
  rw [rectSum, pairCount, Finset.card_filter, Finset.sum_product]
  push_cast
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    rw [relationKernel]
    split <;> norm_num

/-- The same statement through the counting wrapper.
@isnad1 id=eq.0h5v.s5.7e9cf25f9bda from=translated src=- shape=c1dab9a9 vocab=639df08a
-/
theorem rectSumCount_relationKernel (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) :
    rectSumCount (relationKernel R) A B = (pairCount R A B : ℝ) :=
  rectSum_relationKernel R A B

/-- **The density bridge**: at uniform weights, the indicator kernel's rectangle average is
the pair density. Guard-free on both sides — an empty side gives `0` either way.
@isnad1 id=eq.0h5v.s5.300dbfa7f772 from=translated src=- shape=8a665ff7 vocab=a9dbdbbd
-/
theorem rectAverage_relationKernel (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) :
    rectAverage (relationKernel R) (fun _ => 1) (fun _ => 1) A B = pairDensity R A B := by
  rw [rectAverage, rectSum_relationKernel, finsetMass_one, finsetMass_one,
    pairDensity_eq_count_div]

/--
@isnad1 id=eq.0h5v.s5.b6b6e1528b46 from=translated src=- shape=0e6d7c7e vocab=d15416ab
-/
theorem rectAverageCount_relationKernel (R : α → β → Prop) [DecidableRel R]
    (A : Finset α) (B : Finset β) :
    rectAverageCount (relationKernel R) A B = pairDensity R A B :=
  rectAverage_relationKernel R A B

/-! ### Transpose and complement -/

/-- Transposing the kernel is transposing the relation.
@isnad1 id=eq.0h3v.s5.32cc99d2d00f from=translated src=- shape=ac3d49be vocab=09cc95e3
-/
@[simp] theorem relationKernel_op (R : α → β → Prop) [DecidableRel R] :
    (relationKernel R).op = relationKernel (swapRel R) := rfl

/-- The complement's indicator is `1` minus the indicator, pointwise.
@isnad1 id=eq.0h5v.s6.0f17861e3d55 from=translated src=- shape=395bb1b0 vocab=3415cc19
-/
theorem relationKernel_not (R : α → β → Prop) [DecidableRel R] (a : α) (b : β) :
    relationKernel (fun a b => ¬ R a b) a b = 1 - relationKernel R a b := by
  by_cases h : R a b <;> simp [relationKernel, h]

/-! ### Rectangle indicators and their finite combinations

The building blocks of the cut-matrix decomposition (design freeze
`docs/design/cut-matrix-decomposition.md`): the `0/1` indicator of a rectangle `S ×ˢ T`, as the
relation indicator of `x ∈ S ∧ y ∈ T`, and finite weighted combinations
`∑ k, c k • 𝟙_{S k} ⊗ 𝟙_{T k}`, indexed by `Fin n` so that the term count is a first-class
natural number. Rectangles may overlap freely; no partition is involved. -/

/-- The indicator kernel of the rectangle `S ×ˢ T`.-/
def rectIndicator [DecidableEq α] [DecidableEq β] (S : Finset α) (T : Finset β) :
    RectKernel α β :=
  relationKernel fun a b => a ∈ S ∧ b ∈ T

section RectIndicator

variable [DecidableEq α] [DecidableEq β] {S : Finset α} {T : Finset β}

/--
@isnad1 id=eq.0h6v.s6.f268da2db2ae from=translated src=- shape=477bff92 vocab=a7bb8851
-/
@[simp] theorem rectIndicator_apply (S : Finset α) (T : Finset β) (a : α) (b : β) :
    rectIndicator S T a b = if a ∈ S ∧ b ∈ T then 1 else 0 := rfl

/--
@isnad1 id=isunitin.0h6v.s5.96c669f3e472 from=translated src=- shape=4f4e5f39 vocab=b1b8a15f
-/
theorem isUnitIntervalOnRectangle_rectIndicator (S : Finset α) (T : Finset β) (A : Finset α)
    (B : Finset β) : IsUnitIntervalOnRectangle (rectIndicator S T) A B :=
  isUnitIntervalOnRectangle_relationKernel _ A B

/-- **The rectangle sum of an indicator is the mass of the overlap**: on `S' ×ˢ T'` it is
`mass (S' ∩ S) · mass (T' ∩ T)`, for arbitrary (signed) weights.
@isnad1 id=eq.0h8v.s6.7672add38ab5 from=translated src=- shape=9ee62471 vocab=eef58f1d
-/
theorem rectSum_rectIndicator (S : Finset α) (T : Finset β) (wX : α → ℝ) (wY : β → ℝ)
    (S' : Finset α) (T' : Finset β) :
    rectSum (rectIndicator S T) wX wY S' T' = finsetMass wX (S' ∩ S) * finsetMass wY (T' ∩ T) := by
  rw [rectSum, finsetMass, finsetMass, Finset.sum_mul_sum, ← Finset.filter_mem_eq_inter,
    ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [rectIndicator_apply]
    split_ifs with hy <;> simp_all
  · refine Finset.sum_eq_zero fun y _ => ?_
    rw [rectIndicator_apply]
    split_ifs with hy <;> simp_all

/-- Transposing a rectangle indicator swaps its sides.
@isnad1 id=eq.0h4v.s5.42d1fcb6a4f8 from=translated src=- shape=e8e85ef6 vocab=88344d9d
-/
theorem rectIndicator_op (S : Finset α) (T : Finset β) :
    (rectIndicator S T).op = rectIndicator T S := by
  funext b a
  simp [RectKernel.op, rectIndicator, relationKernel, and_comm]

end RectIndicator

/-- The kernel `∑ k, c k • 𝟙_{S k} ⊗ 𝟙_{T k}`: a finite weighted combination of rectangle
indicators, indexed by `Fin n`.-/
def rectCombination [DecidableEq α] [DecidableEq β] {n : ℕ} (c : Fin n → ℝ)
    (S : Fin n → Finset α) (T : Fin n → Finset β) : RectKernel α β :=
  fun a b => ∑ k, c k * rectIndicator (S k) (T k) a b

section RectCombination

variable [DecidableEq α] [DecidableEq β] {n : ℕ}

/--
@isnad1 id=eq.0h8v.s6.4fe3a3d383d2 from=translated src=- shape=4be6dcf3 vocab=670d56ef
-/
@[simp] theorem rectCombination_apply (c : Fin n → ℝ) (S : Fin n → Finset α)
    (T : Fin n → Finset β) (a : α) (b : β) :
    rectCombination c S T a b = ∑ k, c k * rectIndicator (S k) (T k) a b := rfl

/-- The empty combination is the zero kernel.
@isnad1 id=eq.0h5v.s6.017f5a6e05db from=translated src=- shape=1440967a vocab=8e0f097b
-/
@[simp] theorem rectCombination_zero (c : Fin 0 → ℝ) (S : Fin 0 → Finset α)
    (T : Fin 0 → Finset β) : rectCombination c S T = fun _ _ => 0 := by
  funext a b; simp [rectCombination]

/-- **Linearity**: the rectangle sum of a combination is the combination of the overlap
masses, for arbitrary (signed) weights.
@isnad1 id=eq.0h10v.s6.88b2bf16d5cd from=translated src=- shape=f9acd876 vocab=15322a7e
-/
theorem rectSum_rectCombination (c : Fin n → ℝ) (S : Fin n → Finset α) (T : Fin n → Finset β)
    (wX : α → ℝ) (wY : β → ℝ) (S' : Finset α) (T' : Finset β) :
    rectSum (rectCombination c S T) wX wY S' T'
      = ∑ k, c k * (finsetMass wX (S' ∩ S k) * finsetMass wY (T' ∩ T k)) := by
  unfold rectCombination
  rw [rectSum_finset_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [rectSum_smul, rectSum_rectIndicator]

/-- Appending one weighted rectangle to a combination adds its term pointwise.
@isnad1 id=eq.0h9v.s7.4ba0a7ba7745 from=translated src=- shape=a72c5bac vocab=e22b6658
-/
theorem rectCombination_snoc (c : Fin n → ℝ) (S : Fin n → Finset α) (T : Fin n → Finset β)
    (a : ℝ) (S₀ : Finset α) (T₀ : Finset β) :
    rectCombination (Fin.snoc c a) (Fin.snoc S S₀) (Fin.snoc T T₀)
      = fun x y => rectCombination c S T x y + a * rectIndicator S₀ T₀ x y := by
  funext x y
  simp only [rectCombination_apply, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- The combination transposes with its rectangles swapped.
@isnad1 id=eq.0h6v.s5.8445a278b452 from=translated src=- shape=e62b1af7 vocab=83ee8d32
-/
theorem rectCombination_op (c : Fin n → ℝ) (S : Fin n → Finset α) (T : Fin n → Finset β) :
    (rectCombination c S T).op = rectCombination c T S := by
  funext y x
  simp only [RectKernel.op, rectCombination_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← rectIndicator_op]
  rfl

end RectCombination

/-! ### The decrement identities

The algebra of one round of the cut-matrix decomposition: subtracting a multiple of a
rectangle indicator from a kernel changes the pointwise square by a quadratic in the
coefficient, and at the rectangle's own average the change is exactly minus the block energy.
Both identities are **hypothesis-free apart from rectangle containment** and hold for arbitrary
signed weights; positivity enters only the estimates (`RegularityLemmata/Finite/RectKernel.lean`).
-/

section Decrement

variable [DecidableEq α] [DecidableEq β] {wX : α → ℝ} {wY : β → ℝ} {A : Finset α}
  {B : Finset β} {S : Finset α} {T : Finset β}

/-- Multiplying by a rectangle indicator restricts the rectangle sum to the rectangle, when the
rectangle lies inside the carriers.
@isnad1 id=eq.2h9v.s6.ac2102eb6728 from=translated src=- shape=1b9b05f0 vocab=8178c15a
-/
theorem rectSum_mul_rectIndicator (f : RectKernel α β) (hS : S ⊆ A) (hT : T ⊆ B) :
    rectSum (fun x y => f x y * rectIndicator S T x y) wX wY A B = rectSum f wX wY S T := by
  rw [rectSum, rectSum, ← Finset.inter_eq_right.mpr hS, ← Finset.inter_eq_right.mpr hT,
    ← Finset.filter_mem_eq_inter, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with hx
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [rectIndicator_apply]
    split_ifs with hy <;> simp_all
  · refine Finset.sum_eq_zero fun y _ => ?_
    rw [rectIndicator_apply]
    split_ifs with hy <;> simp_all

/-- **The quadratic expansion**, arbitrary coefficient `a`:
`Φ(f − a·𝟙_{S×T}) = Φ(f) − 2a · rectSum f S T + a² · mass S · mass T`.
@isnad1 id=eq.2h10v.s7.b0be4cf90799 from=translated src=- shape=6fb7a7eb vocab=8e57bae5
-/
theorem rectSqMass_sub_smul_rectIndicator (f : RectKernel α β) (hS : S ⊆ A) (hT : T ⊆ B)
    (a : ℝ) :
    rectSqMass (fun x y => f x y - a * rectIndicator S T x y) wX wY A B
      = rectSqMass f wX wY A B - 2 * a * rectSum f wX wY S T
        + a ^ 2 * (finsetMass wX S * finsetMass wY T) := by
  have hpt : ∀ x y, (f x y - a * rectIndicator S T x y) ^ 2
      = f x y ^ 2 - 2 * a * (f x y * rectIndicator S T x y) + a ^ 2 * rectIndicator S T x y := by
    intro x y
    rw [rectIndicator_apply]
    split_ifs <;> ring
  rw [rectSqMass, rectSqMass]
  simp_rw [hpt]
  rw [rectSum_add, rectSum_sub, rectSum_smul, rectSum_smul, rectSum_mul_rectIndicator f hS hT,
    rectSum_rectIndicator, Finset.inter_eq_right.mpr hS, Finset.inter_eq_right.mpr hT]

/-- **The decrement at the average**: subtracting the rectangle's own average drops the
pointwise square by exactly the block energy, `Φ(f − c·𝟙_{S×T}) = Φ(f) − c²·d` with
`c = rectAverage f S T`. Signed weights are admitted: when the rectangle mass `d` vanishes the
totalized average is `0` and nothing changes; when `d ≠ 0`, `c · d = rectSum f S T` by
cancellation.
@isnad1 id=eq.2h9v.s7.150afd80a741 from=translated src=- shape=08435c2e vocab=6ea1a983
-/
theorem rectSqMass_sub_rectAverage_smul_rectIndicator (f : RectKernel α β) (hS : S ⊆ A)
    (hT : T ⊆ B) :
    rectSqMass (fun x y => f x y - rectAverage f wX wY S T * rectIndicator S T x y) wX wY A B
      = rectSqMass f wX wY A B - rectBlockEnergy f wX wY S T := by
  rw [rectSqMass_sub_smul_rectIndicator f hS hT, rectBlockEnergy]
  rcases eq_or_ne (finsetMass wX S * finsetMass wY T) 0 with h0 | h0
  · rw [rectAverage, h0, div_zero]
    ring
  · have hc : rectAverage f wX wY S T * (finsetMass wX S * finsetMass wY T)
        = rectSum f wX wY S T := by
      rw [rectAverage]
      exact div_mul_cancel₀ _ h0
    rw [← hc]
    ring

end Decrement

/-! ### Tests and adversarial examples -/

section Tests

-- The rectangular running example: `a ≤ b` on `Fin 2 → Fin 3` has `5` related pairs and
-- density `5/6`, recovered through the kernel layer.

/-! #### The decrement identities -/

/-- The `±1` chequerboard on `Fin 2 × Fin 2`.-/
private def cheqR : RectKernel (Fin 2) (Fin 2) := fun x y => if x = y then 1 else -1

-- **One round on the chequerboard**: subtracting the cell `{0} × {0}` at its average `1` drops
-- the pointwise square from `4` by the block energy `1`, statement-level from the identity.

end Tests

end RegularityLemmata
