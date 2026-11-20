/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.Weight
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.Inequalities
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Order.Interval.Set.Basic
import Tengoku.Seed.Data.Fin.VecNotation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rectangular weighted kernels

A kernel between two possibly different finite carriers, together with **raw carrier weights
on both sides**. The design freeze is `docs/design/rectangular-kernels.md`.

`RectKernel` is an unbundled function alias, not a structure: bundling a boundedness proof
into the kernel would make addition, subtraction, indicators, and restriction awkward, so
bounds are predicates and hypotheses instead.

The weighted `rectSum` is the **primitive**; `rectAverage` divides by the product of the two
carrier masses, and the unweighted counting forms are wrappers at `wX = wY = 1`. Building the
unweighted version as primitive would force a second weighted API later, and would make cell
masses in partition formulas come out as cardinalities.

## Traps this file pins

* A **nonempty** rectangle can have **zero mass**, since every weight may vanish. So
  `rectAverage_const` requires `0 < finsetMass`, not nonemptiness — and a test witnesses the
  gap.
* General interval preservation on a zero-mass rectangle needs `0 ∈ [a,b]`, because the
  guard-free average is then `0`. Only `[0,1]` and `[-C,C]` get unconditional forms.
* Absolute estimates need **nonnegative** carrier weights; with signed weights the triangle
  inequality goes the wrong way.
* `pullback` evaluation and composition are unconditional, but transporting a *sum* along an
  arbitrary map needs injectivity or explicit fiber multiplicities. No such transport is
  claimed here.
* `restrict` restricts the kernel **and the weights** by subtype inclusion, with **no
  renormalization**.

**The boundary.** This module holds the **partition-free** quantities of a kernel on a
rectangle: sums, averages, bounds, the pointwise mass-weighted square (`rectSqMass`), the block
energy of one rectangle (`rectBlockEnergy`), and the witness lemma
(`finsetMass_mul_pos_of_lt_abs_rectSum`). Everything indexed by a partition — stepification,
the partition energy and its variance identities, cut discrepancy, and the Frieze–Kannan
iteration — lives in the `Partition/RectKernel*` modules.
-/

namespace RegularityLemmata

/-- A rectangular kernel between two carriers. Unbundled on purpose — boundedness is a
hypothesis, not a field.-/
abbrev RectKernel (X Y : Type*) := X → Y → ℝ

variable {X Y X' Y' : Type*}

/-! ### Weighted rectangle sums and averages -/

/-- The **primitive**: the weighted sum of a kernel over a rectangle.-/
def rectSum (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ B, wX x * wY y * f x y

/-- The weighted average, guard-free: zero when either carrier mass vanishes.-/
noncomputable def rectAverage (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) : ℝ :=
  rectSum f wX wY A B / (finsetMass wX A * finsetMass wY B)

/-- The uniform-counting specialization of `rectSum`.-/
noncomputable abbrev rectSumCount (f : RectKernel X Y) (A : Finset X) (B : Finset Y) : ℝ :=
  rectSum f (fun _ => 1) (fun _ => 1) A B

/-- The uniform-counting specialization of `rectAverage`.-/
noncomputable abbrev rectAverageCount (f : RectKernel X Y) (A : Finset X)
    (B : Finset Y) : ℝ :=
  rectAverage f (fun _ => 1) (fun _ => 1) A B

variable {f g : RectKernel X Y} {wX : X → ℝ} {wY : Y → ℝ} {A : Finset X} {B : Finset Y}

/--
@isnad1 id=eq.0h6v.s5.f976cfe1afe7 from=translated src=- shape=6001d152 vocab=7f4ccb33
-/
@[simp] theorem rectSum_empty_left (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (B : Finset Y) : rectSum f wX wY ∅ B = 0 := by
  rw [rectSum, Finset.sum_empty]

/--
@isnad1 id=eq.0h6v.s5.514bcc336e85 from=translated src=- shape=7d3e0bbe vocab=7f4ccb33
-/
@[simp] theorem rectSum_empty_right (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) : rectSum f wX wY A ∅ = 0 := by
  rw [rectSum]
  exact Finset.sum_eq_zero fun x _ => Finset.sum_empty

/-! ### Algebra -/

/--
@isnad1 id=eq.0h6v.s5.c84bf8898c30 from=translated src=- shape=a743a4a8 vocab=7cff5719
-/
@[simp] theorem rectSum_zero (wX : X → ℝ) (wY : Y → ℝ) (A : Finset X) (B : Finset Y) :
    rectSum (fun _ _ => (0 : ℝ)) wX wY A B = 0 := by
  rw [rectSum]
  exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => mul_zero _

/-- A constant kernel's weighted sum is the constant times the rectangle mass.
@isnad1 id=eq.0h7v.s5.57e0a404024d from=translated src=- shape=6b6af3a6 vocab=e6fc28c2
-/
theorem rectSum_const (c : ℝ) (wX : X → ℝ) (wY : Y → ℝ) (A : Finset X) (B : Finset Y) :
    rectSum (fun _ _ => c) wX wY A B = c * (finsetMass wX A * finsetMass wY B) := by
  rw [rectSum, finsetMass, finsetMass, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/--
@isnad1 id=eq.0h8v.s6.d3d7c24b4e24 from=translated src=- shape=7dac5cc7 vocab=47ee840d
-/
theorem rectSum_add (f g : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectSum (fun x y => f x y + g x y) wX wY A B
      = rectSum f wX wY A B + rectSum g wX wY A B := by
  rw [rectSum, rectSum, rectSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/--
@isnad1 id=eq.0h7v.s5.123f4dc8b872 from=translated src=- shape=ae4bacfd vocab=d7fbcaef
-/
theorem rectSum_neg (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectSum (fun x y => -f x y) wX wY A B = -rectSum f wX wY A B := by
  rw [rectSum, rectSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/--
@isnad1 id=eq.0h8v.s6.69e61e71ef3e from=translated src=- shape=7dac5cc7 vocab=2e5e23b8
-/
theorem rectSum_sub (f g : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectSum (fun x y => f x y - g x y) wX wY A B
      = rectSum f wX wY A B - rectSum g wX wY A B := by
  rw [rectSum, rectSum, rectSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/--
@isnad1 id=eq.0h8v.s6.0082dfa282ac from=translated src=- shape=1713a2a8 vocab=af1a3d81
-/
theorem rectSum_smul (c : ℝ) (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectSum (fun x y => c * f x y) wX wY A B = c * rectSum f wX wY A B := by
  rw [rectSum, rectSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Rescaling one carrier weight rescales the sum.** Rescaling the other side is the same
statement through `op`.
@isnad1 id=eq.0h8v.s5.799a789e4249 from=translated src=- shape=28e87577 vocab=af1a3d81
-/
theorem rectSum_smul_weight_left (c : ℝ) (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectSum f (fun x => c * wX x) wY A B = c * rectSum f wX wY A B := by
  rw [rectSum, rectSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- Rescaling **one** carrier weight leaves the average unchanged, for `c ≠ 0`: the sum and
the mass scale together.
@isnad1 id=eq.1h8v.s6.2c6b831e5931 from=translated src=- shape=1cc2ae9f vocab=442f00bb
-/
theorem rectAverage_smul_weight_left {c : ℝ} (hc : c ≠ 0) (f : RectKernel X Y)
    (wX : X → ℝ) (wY : Y → ℝ) (A : Finset X) (B : Finset Y) :
    rectAverage f (fun x => c * wX x) wY A B = rectAverage f wX wY A B := by
  rw [rectAverage, rectAverage, rectSum_smul_weight_left, finsetMass_smul,
    show c * finsetMass wX A * finsetMass wY B
      = c * (finsetMass wX A * finsetMass wY B) from by ring]
  rcases eq_or_ne (finsetMass wX A * finsetMass wY B) 0 with h | h
  · rw [h, mul_zero, div_zero, div_zero]
  · rw [mul_div_mul_left _ _ hc]

/-- **Linearity over a finite family of kernels.** The rectangle sum of a pointwise finite sum
is the finite sum of the rectangle sums, for arbitrary weights.
@isnad1 id=eq.0h9v.s6.c777c518866c from=translated src=- shape=0280fd23 vocab=9801d46e
-/
theorem rectSum_finset_sum {ι : Type*} (s : Finset ι) (h : ι → RectKernel X Y) (wX : X → ℝ)
    (wY : Y → ℝ) (A : Finset X) (B : Finset Y) :
    rectSum (fun x y => ∑ k ∈ s, h k x y) wX wY A B = ∑ k ∈ s, rectSum (h k) wX wY A B := by
  simp only [rectSum, Finset.mul_sum]
  have hinner : ∀ x, (∑ y ∈ B, ∑ k ∈ s, wX x * wY y * h k x y)
      = ∑ k ∈ s, ∑ y ∈ B, wX x * wY y * h k x y := fun x => Finset.sum_comm
  simp only [hinner]
  exact Finset.sum_comm

/-! ### Transpose, pullback, restriction -/

/-- The transposed kernel.-/
def RectKernel.op (f : RectKernel X Y) : RectKernel Y X := fun y x => f x y

/--
@isnad1 id=eq.0h5v.s4.1125be5e209f from=translated src=- shape=a8498672 vocab=46792e85
-/
@[simp] theorem RectKernel.op_apply (f : RectKernel X Y) (y : Y) (x : X) :
    f.op y x = f x y := rfl

/--
@isnad1 id=eq.0h3v.s4.2610d4156587 from=translated src=- shape=143197b8 vocab=171c5b3d
-/
@[simp] theorem RectKernel.op_op (f : RectKernel X Y) : f.op.op = f := rfl

/-- `op` exchanges the two sides of a weighted sum.
@isnad1 id=eq.0h7v.s5.1afc2257ad6a from=translated src=- shape=6037f121 vocab=ec1a8746
-/
theorem rectSum_op (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectSum f.op wY wX B A = rectSum f wX wY A B := by
  rw [rectSum, rectSum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [RectKernel.op_apply]; ring

/--
@isnad1 id=eq.0h7v.s5.0053c7e46abe from=translated src=- shape=6037f121 vocab=26da7a5a
-/
theorem rectAverage_op (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectAverage f.op wY wX B A = rectAverage f wX wY A B := by
  rw [rectAverage, rectAverage, rectSum_op, mul_comm (finsetMass wY B)]

/-- Pullback along maps of both carriers. Evaluation and composition are unconditional;
transporting a **sum** along `u`, `v` is not, and is deliberately not stated — it would need
injectivity or explicit fiber multiplicities.-/
def RectKernel.pullback (f : RectKernel X Y) (u : X' → X) (v : Y' → Y) : RectKernel X' Y' :=
  fun x y => f (u x) (v y)

/--
@isnad1 id=eq.0h9v.s5.374e5eae1276 from=translated src=- shape=fd88e09e vocab=ad14dc1e
-/
@[simp] theorem RectKernel.pullback_apply (f : RectKernel X Y) (u : X' → X) (v : Y' → Y)
    (x : X') (y : Y') : f.pullback u v x y = f (u x) (v y) := rfl

/--
@isnad1 id=eq.0h11v.s6.efd1f6a37546 from=translated src=- shape=c65b139f vocab=f77d074d
-/
theorem RectKernel.pullback_pullback {X'' Y'' : Type*} (f : RectKernel X Y)
    (u : X' → X) (v : Y' → Y) (u' : X'' → X') (v' : Y'' → Y') :
    (f.pullback u v).pullback u' v' = f.pullback (u ∘ u') (v ∘ v') := rfl

/--
@isnad1 id=eq.0h3v.s4.32b8978619f8 from=translated src=- shape=c2cebbe4 vocab=355197e9
-/
@[simp] theorem RectKernel.pullback_id (f : RectKernel X Y) : f.pullback id id = f := rfl

/-- Restriction to subcarriers, by subtype inclusion. The **weights are carried across
unchanged** — no renormalization, per the design freeze.-/
def RectKernel.restrict (f : RectKernel X Y) (A : Finset X) (B : Finset Y) :
    RectKernel {x // x ∈ A} {y // y ∈ B} :=
  f.pullback Subtype.val Subtype.val

/--
@isnad1 id=eq.0h7v.s6.96296c173f91 from=translated src=- shape=cea7b9e1 vocab=43b68519
-/
@[simp] theorem RectKernel.restrict_apply (f : RectKernel X Y) (A : Finset X) (B : Finset Y)
    (x : {x // x ∈ A}) (y : {y // y ∈ B}) : f.restrict A B x y = f x.val y.val := rfl

/-- The restricted weight on a subcarrier: the same raw weight, not renormalized.-/
def restrictWeight (w : X → ℝ) (A : Finset X) : {x // x ∈ A} → ℝ := fun x => w x.val

/--
@isnad1 id=eq.0h4v.s5.61caab797ce4 from=translated src=- shape=08efe1c3 vocab=18fb4895
-/
@[simp] theorem restrictWeight_apply (w : X → ℝ) (A : Finset X) (x : {x // x ∈ A}) :
    restrictWeight w A x = w x.val := rfl

/-! ### Boundedness

Signed and interval bounds are **different predicates**, because the Frieze–Kannan theory
handles signed residuals while relation indicators live in `[0,1]`. -/

/-- The kernel takes values in `[a, b]` on the rectangle.-/
def IsIccBoundedOnRectangle (f : RectKernel X Y) (a b : ℝ) (A : Finset X)
    (B : Finset Y) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, f x y ∈ Set.Icc a b

/-- The kernel is bounded in absolute value by `C` on the rectangle.-/
def IsAbsBoundedOnRectangle (f : RectKernel X Y) (C : ℝ) (A : Finset X)
    (B : Finset Y) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, |f x y| ≤ C

/-- Values in `[0,1]` — the relation-indicator case.-/
abbrev IsUnitIntervalOnRectangle (f : RectKernel X Y) (A : Finset X) (B : Finset Y) : Prop :=
  IsIccBoundedOnRectangle f 0 1 A B

/-- Absolute value at most `1` — the signed-residual case.-/
abbrev IsAbsUnitBoundedOnRectangle (f : RectKernel X Y) (A : Finset X)
    (B : Finset Y) : Prop :=
  IsAbsBoundedOnRectangle f 1 A B

/--
@isnad1 id=isabsbou.3h8v.s5.1c82d21ae48d from=translated src=- shape=93fb163b vocab=7038123d
-/
theorem IsIccBoundedOnRectangle.absBounded {a b C : ℝ}
    (h : IsIccBoundedOnRectangle f a b A B) (ha : -C ≤ a) (hb : b ≤ C) :
    IsAbsBoundedOnRectangle f C A B := fun x hx y hy => by
  have := h x hx y hy
  rw [Set.mem_Icc] at this
  rw [abs_le]
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-! ### Estimates

All of these need **nonnegative carrier weights**: with signed weights the triangle
inequality points the wrong way. -/

/--
@isnad1 id=le.3h7v.s7.532ed67cbfc7 from=translated src=- shape=afba7969 vocab=9a639382
-/
theorem rectSum_nonneg (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : ∀ x ∈ A, ∀ y ∈ B, 0 ≤ f x y) : 0 ≤ rectSum f wX wY A B :=
  Finset.sum_nonneg fun x hx => Finset.sum_nonneg fun y hy =>
    mul_nonneg (mul_nonneg (hwX x hx) (hwY y hy)) (hf x hx y hy)

/--
@isnad1 id=le.3h7v.s7.f839548e076b from=translated src=- shape=afba7969 vocab=c5814889
-/
theorem rectAverage_nonneg (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : ∀ x ∈ A, ∀ y ∈ B, 0 ≤ f x y) : 0 ≤ rectAverage f wX wY A B :=
  div_nonneg (rectSum_nonneg hwX hwY hf)
    (mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY))

/-- The absolute rectangle-sum estimate, in **multiplication form**: no denominator, so no
positivity hypothesis on the masses.
@isnad1 id=le.3h8v.s6.fba5dd5b4215 from=translated src=- shape=9bd6b8ad vocab=2e284559
-/
theorem abs_rectSum_le {C : ℝ} (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsBoundedOnRectangle f C A B) :
    |rectSum f wX wY A B| ≤ C * (finsetMass wX A * finsetMass wY B) := by
  rw [← rectSum_const C wX wY A B]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [rectSum]
  refine Finset.sum_le_sum fun x hx => ?_
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun y hy => ?_
  rw [abs_mul, abs_of_nonneg (mul_nonneg (hwX x hx) (hwY y hy))]
  exact mul_le_mul_of_nonneg_left (hf x hx y hy) (mul_nonneg (hwX x hx) (hwY y hy))

/-- The absolute average estimate. **Guard-free**: on a zero-mass rectangle the average is
`0`, which is why `0 ≤ C` is the only extra hypothesis needed.
@isnad1 id=le.4h8v.s6.bc21dcef2bb7 from=translated src=- shape=6e35a833 vocab=fffe5a41
-/
theorem abs_rectAverage_le {C : ℝ} (hC : 0 ≤ C) (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (hwY : ∀ y ∈ B, 0 ≤ wY y) (hf : IsAbsBoundedOnRectangle f C A B) :
    |rectAverage f wX wY A B| ≤ C := by
  have hm : 0 ≤ finsetMass wX A * finsetMass wY B :=
    mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY)
  rcases eq_or_lt_of_le hm with h | h
  · rw [rectAverage, ← h, div_zero, abs_zero]
    exact hC
  · rw [rectAverage, abs_div, abs_of_pos h, div_le_iff₀ h]
    exact abs_rectSum_le hwX hwY hf

/-- **Guard-free `[0,1]` bounds** for a unit-interval kernel: on a zero-mass rectangle the
average is `0`, which lies in `[0,1]`. This is the case where the interval contains `0`; see
`rectAverage_mem_Icc` for the general interval, which needs positive mass.
@isnad1 id=mem.3h7v.s6.814bf08b6957 from=translated src=- shape=58c944ff vocab=fb46add3
-/
theorem rectAverage_mem_unitInterval (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsUnitIntervalOnRectangle f A B) :
    rectAverage f wX wY A B ∈ Set.Icc (0 : ℝ) 1 := by
  have habs : IsAbsBoundedOnRectangle f 1 A B :=
    hf.absBounded (by norm_num) le_rfl
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · exact rectAverage_nonneg hwX hwY fun x hx y hy => (Set.mem_Icc.mp (hf x hx y hy)).1
  · have := abs_rectAverage_le (by norm_num : (0:ℝ) ≤ 1) hwX hwY habs
    exact (abs_le.mp this).2

/-! ### Positive mass, not nonemptiness

A nonempty rectangle can have zero mass, so these statements assume positive mass. -/

/-- The average of a constant is the constant — **only under positive mass on both sides**.
Nonemptiness is not enough: every weight may vanish, and then the guard-free average is `0`
rather than `c`.
@isnad1 id=eq.2h7v.s5.ad0b1e7b2197 from=translated src=- shape=e7b680d0 vocab=657c6bf7
-/
theorem rectAverage_const (c : ℝ) (hA : 0 < finsetMass wX A) (hB : 0 < finsetMass wY B) :
    rectAverage (fun _ _ => c) wX wY A B = c := by
  rw [rectAverage, rectSum_const, mul_div_assoc, div_self (by positivity), mul_one]

/-- General interval preservation. Positive mass is required, and unlike the `[0,1]` case it
cannot be dropped: on a zero-mass rectangle the average is `0`, which need not lie in
`[a,b]`.
@isnad1 id=mem.5h9v.s7.d84a0aabfff4 from=translated src=- shape=6da3610a vocab=3eff0193
-/
theorem rectAverage_mem_Icc {a b : ℝ} (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hA : 0 < finsetMass wX A) (hB : 0 < finsetMass wY B)
    (hf : IsIccBoundedOnRectangle f a b A B) :
    rectAverage f wX wY A B ∈ Set.Icc a b := by
  have hm : 0 < finsetMass wX A * finsetMass wY B := mul_pos hA hB
  have hlow : a * (finsetMass wX A * finsetMass wY B) ≤ rectSum f wX wY A B := by
    rw [← rectSum_const a wX wY A B, rectSum, rectSum]
    refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
    exact mul_le_mul_of_nonneg_left (Set.mem_Icc.mp (hf x hx y hy)).1
      (mul_nonneg (hwX x hx) (hwY y hy))
  have hhigh : rectSum f wX wY A B ≤ b * (finsetMass wX A * finsetMass wY B) := by
    rw [← rectSum_const b wX wY A B, rectSum, rectSum]
    refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
    exact mul_le_mul_of_nonneg_left (Set.mem_Icc.mp (hf x hx y hy)).2
      (mul_nonneg (hwX x hx) (hwY y hy))
  rw [rectAverage, Set.mem_Icc, le_div_iff₀ hm, div_le_iff₀ hm]
  exact ⟨by linarith, by linarith⟩

/-! ### Positive mass from a rectangle-sum witness

Partition-free form of the Frieze–Kannan witness lemma: a rectangle whose sum exceeds
`ε · (mass A · mass B)` in absolute value forces the total mass to be positive, because under
nonnegative weights zero total mass makes every rectangle sum inside the carriers vanish. No
`0 < ε` is needed. -/

/-- Zero total mass with nonnegative weights annihilates every rectangle sum inside the
carriers.
@isnad1 id=eq.5h9v.s7.8f6fb8256a15 from=translated src=- shape=d9d17f7c vocab=3169a03b
-/
theorem rectSum_eq_zero_of_finsetMass_mul_eq_zero (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (hwY : ∀ y ∈ B, 0 ≤ wY y) {S : Finset X} {T : Finset Y} (hS : S ⊆ A) (hT : T ⊆ B)
    (h : finsetMass wX A * finsetMass wY B = 0) : rectSum f wX wY S T = 0 := by
  rcases mul_eq_zero.mp h with hA | hB
  · have hz : ∀ x ∈ A, wX x = 0 := fun x hx =>
      (Finset.sum_eq_zero_iff_of_nonneg hwX).mp hA x hx
    exact Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y _ => by
      rw [hz x (hS hx), zero_mul, zero_mul]
  · have hz : ∀ y ∈ B, wY y = 0 := fun y hy =>
      (Finset.sum_eq_zero_iff_of_nonneg hwY).mp hB y hy
    exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y hy => by
      rw [hz y (hT hy), mul_zero, zero_mul]

/-- **A witness forces positive mass.**
@isnad1 id=lt.5h10v.s7.728dcac7ae22 from=translated src=- shape=51bc35c8 vocab=f8a0b479
-/
theorem finsetMass_mul_pos_of_lt_abs_rectSum (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (hwY : ∀ y ∈ B, 0 ≤ wY y) {S : Finset X} {T : Finset Y} (hS : S ⊆ A) (hT : T ⊆ B) {ε : ℝ}
    (hwit : ε * (finsetMass wX A * finsetMass wY B) < |rectSum f wX wY S T|) :
    0 < finsetMass wX A * finsetMass wY B := by
  rcases eq_or_lt_of_le (mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY)) with h | h
  · exfalso
    rw [← h, mul_zero, rectSum_eq_zero_of_finsetMass_mul_eq_zero hwX hwY hS hT h.symm,
      abs_zero] at hwit
    exact lt_irrefl _ hwit
  · exact h

/-! ### The pointwise square and the block energy

Two partition-free quantities: the **pointwise mass-weighted square** `rectSqMass`, defined
through `rectSum` applied to the pointwise square so that its algebra is `rectSum`'s, and the
**block energy** `rectBlockEnergy`, the mass-weighted square of a rectangle's average.
`RegularityLemmata/Partition/RectKernelEnergy.lean` sums the block energy over a partition pair; the
cut-matrix decomposition (`docs/design/cut-matrix-decomposition.md`) uses the square as its
potential and
the block energy as its per-round gain. -/

/-- The raw rectangle sum of the pointwise square, `∑ x ∈ A, ∑ y ∈ B, wX x * wY y * f x y ^ 2`.-/
noncomputable def rectSqMass (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) : ℝ :=
  rectSum (fun x y => f x y ^ 2) wX wY A B

/--
@isnad1 id=eq.0h7v.s6.1d4a35eec4c3 from=translated src=- shape=f9d041ef vocab=fd77dc09
-/
theorem rectSqMass_def :
    rectSqMass f wX wY A B = ∑ x ∈ A, ∑ y ∈ B, wX x * wY y * f x y ^ 2 := rfl

/--
@isnad1 id=le.2h7v.s6.6a1da0c7d4c0 from=translated src=- shape=c8001003 vocab=cc9288e4
-/
theorem rectSqMass_nonneg (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    0 ≤ rectSqMass f wX wY A B :=
  rectSum_nonneg hwX hwY fun _ _ _ _ => sq_nonneg _

/-- The pointwise square of an absolutely `C`-bounded kernel has mass at most `C²` times the
rectangle mass. Guard-free.
@isnad1 id=le.3h8v.s7.50c37bf40157 from=translated src=- shape=6d7a5555 vocab=d8486e77
-/
theorem rectSqMass_le (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) {C : ℝ}
    (hf : IsAbsBoundedOnRectangle f C A B) :
    rectSqMass f wX wY A B ≤ C ^ 2 * (finsetMass wX A * finsetMass wY B) := by
  rw [rectSqMass, ← rectSum_const (C ^ 2) wX wY A B, rectSum, rectSum]
  refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hwX x hx) (hwY y hy))
  have := hf x hx y hy
  nlinarith [abs_nonneg (f x y), sq_abs (f x y), abs_le.mp this]

/--
@isnad1 id=eq.0h7v.s5.557fcea6820a from=translated src=- shape=6037f121 vocab=131dc17c
-/
theorem rectSqMass_op : rectSqMass f.op wY wX B A = rectSqMass f wX wY A B :=
  rectSum_op _ wX wY A B

/-- The energy of one rectangle: its average squared, weighted by its mass.-/
noncomputable def rectBlockEnergy (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) : ℝ :=
  rectAverage f wX wY A B ^ 2 * (finsetMass wX A * finsetMass wY B)

/--
@isnad1 id=le.2h7v.s6.b7fea71d255e from=translated src=- shape=c8001003 vocab=45411373
-/
theorem rectBlockEnergy_nonneg (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    0 ≤ rectBlockEnergy f wX wY A B :=
  mul_nonneg (sq_nonneg _)
    (mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY))

/-- **The mass upper bound.** For an absolutely unit-bounded kernel the block energy is at
most the block's mass. Guard-free: at zero mass both sides are `0`.
@isnad1 id=le.3h7v.s6.c7fd3550140a from=translated src=- shape=a3832e1d vocab=77e857a2
-/
theorem rectBlockEnergy_le_mass (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y)
    (hf : IsAbsUnitBoundedOnRectangle f A B) :
    rectBlockEnergy f wX wY A B ≤ finsetMass wX A * finsetMass wY B := by
  have habs := abs_rectAverage_le (by norm_num : (0:ℝ) ≤ 1) hwX hwY hf
  have hsq : rectAverage f wX wY A B ^ 2 ≤ 1 := by
    have := abs_le.mp habs
    nlinarith [this.1, this.2]
  calc rectBlockEnergy f wX wY A B
      ≤ 1 * (finsetMass wX A * finsetMass wY B) :=
        mul_le_mul_of_nonneg_right hsq
          (mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY))
    _ = finsetMass wX A * finsetMass wY B := one_mul _

/-- `op` exchanges the two sides of the block energy.
@isnad1 id=eq.0h7v.s5.621eb2355211 from=translated src=- shape=6037f121 vocab=4561a0e7
-/
theorem rectBlockEnergy_op (f : RectKernel X Y) (wX : X → ℝ) (wY : Y → ℝ)
    (A : Finset X) (B : Finset Y) :
    rectBlockEnergy f.op wY wX B A = rectBlockEnergy f wX wY A B := by
  rw [rectBlockEnergy, rectBlockEnergy, rectAverage_op, mul_comm (finsetMass wY B)]

/-! ### Cauchy–Schwarz on a rectangle, and the coefficient estimate

The two estimates of the cut-matrix decomposition's round (design freeze
`docs/design/cut-matrix-decomposition.md`, §4): the block energy of a rectangle is at most its
pointwise square (mass-weighted Cauchy–Schwarz, `sq_sum_mul_le_sum_mul_sum_sq_mul`), and a
witness rectangle whose sum exceeds `ε` times the total mass, on a kernel whose pointwise square
is at most the total mass, has average bounded by `1/ε`. Nonnegative weights and the positive
threshold `0 < ε` enter here — the witness lemma `finsetMass_mul_pos_of_lt_abs_rectSum` itself
stays unconstrained in `ε`. -/

/-- The pointwise square is monotone in the rectangle under nonnegative weights.
@isnad1 id=le.4h9v.s7.dcd1659391f6 from=translated src=- shape=eadbb3ab vocab=cc9288e4
-/
theorem rectSqMass_mono (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) {S : Finset X}
    {T : Finset Y} (hS : S ⊆ A) (hT : T ⊆ B) :
    rectSqMass f wX wY S T ≤ rectSqMass f wX wY A B := by
  rw [rectSqMass, rectSqMass, rectSum, rectSum]
  calc ∑ x ∈ S, ∑ y ∈ T, wX x * wY y * f x y ^ 2
      ≤ ∑ x ∈ S, ∑ y ∈ B, wX x * wY y * f x y ^ 2 :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum_of_subset_of_nonneg hT fun y hy _ =>
          mul_nonneg (mul_nonneg (hwX x (hS hx)) (hwY y hy)) (sq_nonneg _)
    _ ≤ ∑ x ∈ A, ∑ y ∈ B, wX x * wY y * f x y ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun x hx _ => Finset.sum_nonneg fun y hy =>
          mul_nonneg (mul_nonneg (hwX x hx) (hwY y hy)) (sq_nonneg _)

/-- **Cauchy–Schwarz on a rectangle**: `(rectSum f)² ≤ mass · rectSqMass f`, nonnegative
weights.
@isnad1 id=le.2h7v.s7.b0296ef7eea2 from=translated src=- shape=06e1df9f vocab=ad44c57c
-/
theorem sq_rectSum_le_mul_rectSqMass (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectSum f wX wY A B ^ 2 ≤ (finsetMass wX A * finsetMass wY B) * rectSqMass f wX wY A B := by
  classical
  have h := sq_sum_mul_le_sum_mul_sum_sq_mul (fun p : X × Y => f p.1 p.2)
    (fun p => wX p.1 * wY p.2) (A ×ˢ B) fun p hp =>
      mul_nonneg (hwX p.1 (Finset.mem_product.mp hp).1) (hwY p.2 (Finset.mem_product.mp hp).2)
  have e1 : ∑ p ∈ A ×ˢ B, f p.1 p.2 * (wX p.1 * wY p.2) = rectSum f wX wY A B := by
    rw [rectSum, Finset.sum_product]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have e2 : ∑ p ∈ A ×ˢ B, wX p.1 * wY p.2 = finsetMass wX A * finsetMass wY B := by
    rw [finsetMass, finsetMass, Finset.sum_mul_sum, Finset.sum_product]
  have e3 : ∑ p ∈ A ×ˢ B, f p.1 p.2 ^ 2 * (wX p.1 * wY p.2) = rectSqMass f wX wY A B := by
    rw [rectSqMass, rectSum, Finset.sum_product]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rwa [e1, e2, e3] at h

/-- **The block energy is at most the pointwise square.** Guard-free at zero mass, where the
block energy is `0`.
@isnad1 id=le.2h7v.s6.519ea74ebff7 from=translated src=- shape=3a9e2ea4 vocab=105a4ca2
-/
theorem rectBlockEnergy_le_rectSqMass (hwX : ∀ x ∈ A, 0 ≤ wX x) (hwY : ∀ y ∈ B, 0 ≤ wY y) :
    rectBlockEnergy f wX wY A B ≤ rectSqMass f wX wY A B := by
  have hd0 : 0 ≤ finsetMass wX A * finsetMass wY B :=
    mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY)
  rcases eq_or_lt_of_le hd0 with h0 | hpos
  · rw [rectBlockEnergy, ← h0, mul_zero]
    exact rectSqMass_nonneg hwX hwY
  · have hcs := sq_rectSum_le_mul_rectSqMass (f := f) hwX hwY
    rw [rectBlockEnergy, rectAverage, div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hcs, hpos]

/-- **The coefficient estimate.** A witness rectangle `S ×ˢ T` inside the carriers with
`ε · M < |rectSum f S T|`, on a kernel whose pointwise square is at most the total mass `M`, has
absolute average at most `1/ε`. From `|c|·d > ε·M` and `c²·d ≤ M`, where `d` is the witness
rectangle's mass; the positive threshold `0 < ε` is used here and only here.
@isnad1 id=le.7h10v.s7.4bba09b3d014 from=translated src=- shape=f17051b3 vocab=92314532
-/
theorem abs_rectAverage_le_inv_of_lt_abs_rectSum (hwX : ∀ x ∈ A, 0 ≤ wX x)
    (hwY : ∀ y ∈ B, 0 ≤ wY y) {S : Finset X} {T : Finset Y} (hS : S ⊆ A) (hT : T ⊆ B) {ε : ℝ}
    (hε : 0 < ε) (hwit : ε * (finsetMass wX A * finsetMass wY B) < |rectSum f wX wY S T|)
    (hsq : rectSqMass f wX wY A B ≤ finsetMass wX A * finsetMass wY B) :
    |rectAverage f wX wY S T| ≤ 1 / ε := by
  have hwS : ∀ x ∈ S, 0 ≤ wX x := fun x hx => hwX x (hS hx)
  have hwT : ∀ y ∈ T, 0 ≤ wY y := fun y hy => hwY y (hT hy)
  set M := finsetMass wX A * finsetMass wY B with hM
  set d := finsetMass wX S * finsetMass wY T with hd
  set c := rectAverage f wX wY S T with hc
  have hM0 : 0 ≤ M := mul_nonneg (finsetMass_nonneg hwX) (finsetMass_nonneg hwY)
  have hdpos : 0 < d := by
    rcases eq_or_lt_of_le (mul_nonneg (finsetMass_nonneg hwS) (finsetMass_nonneg hwT)) with
      h0 | h
    · exfalso
      rw [rectSum_eq_zero_of_finsetMass_mul_eq_zero hwS hwT (Finset.Subset.refl S)
        (Finset.Subset.refl T) h0.symm, abs_zero] at hwit
      nlinarith [mul_nonneg hε.le hM0]
    · exact h
  have hcd : |c| * d = |rectSum f wX wY S T| := by
    rw [hc, rectAverage, ← hd, abs_div, abs_of_pos hdpos, div_mul_cancel₀ _ hdpos.ne']
  -- `c²·d` is the block energy of the witness rectangle, at most its pointwise square, at most
  -- the carriers' pointwise square, at most `M`.
  have hcM : |c| ^ 2 * d ≤ M := by
    rw [sq_abs]
    exact (rectBlockEnergy_le_rectSqMass (f := f) hwS hwT).trans
      ((rectSqMass_mono hwX hwY hS hT).trans hsq)
  have h1 : ε * M < |c| * d := by rw [hcd]; exact hwit
  rw [le_div_iff₀ hε]
  rcases eq_or_lt_of_le (abs_nonneg c) with hc0 | hcpos
  · rw [← hc0, zero_mul]; exact zero_le_one
  · have h3 : ε * |c| * (|c| * d) < 1 * (|c| * d) := by
      calc ε * |c| * (|c| * d) = ε * (|c| ^ 2 * d) := by ring
        _ ≤ ε * M := mul_le_mul_of_nonneg_left hcM hε.le
        _ < |c| * d := h1
        _ = 1 * (|c| * d) := (one_mul _).symm
    have := lt_of_mul_lt_mul_right h3 (mul_pos hcpos hdpos).le
    linarith

/-! ### Tests and adversarial examples -/

section Tests

/-- A nonuniform weight on the left carrier.-/
private def wL : Fin 2 → ℝ := ![2, 3]

/-- A nonuniform weight on the right carrier.-/
private def wR : Fin 3 → ℝ := ![1, 2, 3]

/-- A genuinely **signed** kernel between different carriers, not an indicator.-/
private def sk : RectKernel (Fin 2) (Fin 3) := fun x y => if x.val ≤ y.val then 1 else -1

-- Nonuniform weights on `Fin 2 × Fin 3`: the rectangle mass is `5 · 6 = 30`.

end Tests

end RegularityLemmata
