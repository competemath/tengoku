/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.AlmostConstant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analytic homogeneity

The `(δ, ε)`-homogeneous rectangle of Chavarria–Conant–Pillay, as restated by Conant–Terry
(*Quantitative analytic stable regularity*,
[arXiv:2607.21762](https://arxiv.org/abs/2607.21762), Definition A.1): `(A, B)` is
`(δ, ε)`-homogeneous for `f` when there are values `r, s ∈ [0,1]` such that, for `ε`-almost
all `a ∈ A`, the row `f a ·` is within `δ` of `r` on `ε`-almost all of `B`, and symmetrically
for columns at `s`. Their Proposition A.5 relates this to almost-constancy in both directions,
with a doubling of the `δ`-constant parameter:

* `RectKernel.isHomogeneousPair_of_isAlmostConstantPair` (A.5(a)): `ε²`-almost `2δ`-constant
  implies `(δ, ε)`-homogeneous;
* `RectKernel.isAlmostConstantPair_of_isHomogeneousPair` (A.5(b)): `(δ, ε)`-homogeneous
  implies `2ε`-almost `2δ`-constant.

## Frozen conventions

All predicates follow `RegularityLemmata/Finite/AlmostConstant.lean`: **subset form**, **no
decidability instances**, **strict `<`** in the closeness and mass clauses, **totalized on the empty
set**, and **no range or sign constraint inside the predicates**. In particular:

* `IsAlmostNearOn φ r δ ε V` reads "for `ε`-almost all `v ∈ V`, `φ v ≈_δ r`"; here
  `x ≈_δ r` is `|x - r| < δ` (strict, the paper's footnote 8 convention).
* `RectKernel.IsRowConcentrated f r δ ε A B` totalizes **both** empty sides: with only
  `A = ∅` totalized, `B = ∅` with `A ≠ ∅` would fail the mass clause at `ε ≤ 0`.
* `RectKernel.IsHomogeneousPair` is the kernel notion, namespaced under `RectKernel` so it
  is never confused with the relational `IsHomogeneousPair`; no indicator adapter between
  the two is stated here.

## Provenance

Definition A.1 and both directions of Proposition A.5 are **reformulated variants**, not exact
formalizations: the constants are preserved (`ε²`/`2δ` in (a), `2ε`/`2δ` in (b)), but the
statements extend the domains (real-valued kernels, arbitrary real parameters, and (b) with
no hypothesis at all — for `ε > 1` the conclusion is the trivial regime), localize the range
assumption (to the rectangle, in (a) only, where it places the common value in `[0,1]`), and
totalize empty rectangles. The paper's "main observation" (a `δ`-constant function is within
`δ / 2` of a common center) is `isDeltaConstantOn_iff_exists_center` in
`RegularityLemmata/Finite/AlmostConstant.lean`; (a) is then a row-wise Markov count and (b) a
union-of-fibers count.
-/

namespace RegularityLemmata

variable {α X Y : Type*} {φ : α → ℝ} {f : RectKernel X Y} {r δ δ' ε ε' : ℝ} {V : Finset α}
  {A : Finset X} {B : Finset Y}

/-! ### The predicates -/

/-- "For `ε`-almost all `v ∈ V`, `φ v ≈_δ r`": some subset carrying strictly more than a
`(1 − ε)`-fraction of `V` lies in the open `δ`-ball around `r`. Totalized on `V = ∅`.-/
def IsAlmostNearOn (φ : α → ℝ) (r δ ε : ℝ) (V : Finset α) : Prop :=
  V = ∅ ∨ ∃ W ⊆ V, (1 - ε) * (V.card : ℝ) < (W.card : ℝ) ∧ ∀ v ∈ W, |φ v - r| < δ

/-- Clause (i) of Definition A.1 at a fixed value `r`: for `ε`-almost all `a ∈ A`, the row
`f a ·` is `ε`-almost within `δ` of `r` on `B`. Totalized on **both** empty sides.-/
def RectKernel.IsRowConcentrated (f : RectKernel X Y) (r δ ε : ℝ) (A : Finset X)
    (B : Finset Y) : Prop :=
  A = ∅ ∨ B = ∅ ∨ ∃ A' ⊆ A, (1 - ε) * (A.card : ℝ) < (A'.card : ℝ) ∧
    ∀ a ∈ A', IsAlmostNearOn (fun b ↦ f a b) r δ ε B

/-- **Definition A.1**: `(A, B)` is `(δ, ε)`-homogeneous for `f` — row concentration at some
`r ∈ [0,1]`, and column concentration (row concentration of the transpose) at some
`s ∈ [0,1]`.-/
def RectKernel.IsHomogeneousPair (f : RectKernel X Y) (δ ε : ℝ) (A : Finset X)
    (B : Finset Y) : Prop :=
  (∃ r ∈ Set.Icc (0 : ℝ) 1, RectKernel.IsRowConcentrated f r δ ε A B) ∧
  (∃ s ∈ Set.Icc (0 : ℝ) 1, RectKernel.IsRowConcentrated (RectKernel.op f) s δ ε B A)

/-! ### Monotonicity and totalization -/

/-- Monotonicity in the closeness radius: `IsAlmostNearOn φ r δ ε V` implies
`IsAlmostNearOn φ r δ' ε V` whenever `δ ≤ δ'`. The witness subset is reused unchanged; the
open `δ`-ball around `r` sits inside the open `δ'`-ball. No sign condition on `δ`, `ε`.
House lemma, no source; consumed by `RectKernel.IsRowConcentrated.mono_delta`.
@isnad1 id=isalmost.2h7v.s5.49b54ac104b6 from=translated src=- shape=4ca0018f vocab=9211bbf5
-/
theorem IsAlmostNearOn.mono_delta (h : IsAlmostNearOn φ r δ ε V) (hδ : δ ≤ δ') :
    IsAlmostNearOn φ r δ' ε V := by
  rcases h with rfl | ⟨W, hWV, hcard, hnear⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨W, hWV, hcard, fun v hv ↦ lt_of_lt_of_le (hnear v hv) hδ⟩

/-- Monotonicity in the exceptional fraction: `IsAlmostNearOn φ r δ ε V` implies
`IsAlmostNearOn φ r δ ε' V` whenever `ε ≤ ε'`. The witness subset is reused; its strict mass
bound `(1 - ε) * |V| < |W|` weakens to `(1 - ε') * |V| < |W|`. No sign condition on `δ`,
`ε`, `ε'`. House lemma, no source; consumed by `RectKernel.IsRowConcentrated.mono_eps`.
@isnad1 id=isalmost.2h7v.s5.e0023828ace3 from=translated src=- shape=ae680a26 vocab=9211bbf5
-/
theorem IsAlmostNearOn.mono_eps (h : IsAlmostNearOn φ r δ ε V) (hε : ε ≤ ε') :
    IsAlmostNearOn φ r δ ε' V := by
  rcases h with rfl | ⟨W, hWV, hcard, hnear⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨W, hWV, lt_of_le_of_lt ?_ hcard, hnear⟩
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

/-- Totalization: `IsAlmostNearOn φ r δ ε ∅` holds for every `φ`, `r`, `δ`, `ε`, including
`ε = 0` and `δ ≤ 0`, by the first disjunct of the definition. House lemma, no source.
@isnad1 id=isalmost.0h5v.s4.aa08462e84b2 from=translated src=- shape=a09755c8 vocab=ee2ef102
-/
theorem isAlmostNearOn_empty (φ : α → ℝ) (r δ ε : ℝ) : IsAlmostNearOn φ r δ ε (∅ : Finset α) :=
  Or.inl rfl

/-- Monotonicity of row concentration in the closeness radius: `δ ≤ δ'` transports
`RectKernel.IsRowConcentrated f r δ ε A B` to radius `δ'`, row by row through
`IsAlmostNearOn.mono_delta`. The set of good rows is unchanged. No sign condition on the
parameters. House lemma, no source; consumed by `RectKernel.IsHomogeneousPair.mono_delta`.
@isnad1 id=isrowcon.2h9v.s5.47f950ab0821 from=translated src=- shape=f46a06a3 vocab=a5afe881
-/
theorem RectKernel.IsRowConcentrated.mono_delta (h : RectKernel.IsRowConcentrated f r δ ε A B)
    (hδ : δ ≤ δ') : RectKernel.IsRowConcentrated f r δ' ε A B := by
  rcases h with hA | hB | ⟨A', hA'A, hcard, hrows⟩
  · exact Or.inl hA
  · exact Or.inr (Or.inl hB)
  · exact Or.inr (Or.inr ⟨A', hA'A, hcard, fun a ha ↦ (hrows a ha).mono_delta hδ⟩)

/-- Monotonicity of row concentration in the exceptional fraction: `ε ≤ ε'` transports
`RectKernel.IsRowConcentrated f r δ ε A B` to fraction `ε'`. Note that `ε` plays two roles
in the predicate (the fraction of bad rows and the fraction of bad columns within a good
row); both weaken at once, the row count via the mass clause and the columns via
`IsAlmostNearOn.mono_eps`. No sign condition on the parameters. House lemma, no source;
consumed by `RectKernel.IsHomogeneousPair.mono_eps`.
@isnad1 id=isrowcon.2h9v.s5.649e8ba14be5 from=translated src=- shape=0f57b519 vocab=a5afe881
-/
theorem RectKernel.IsRowConcentrated.mono_eps (h : RectKernel.IsRowConcentrated f r δ ε A B)
    (hε : ε ≤ ε') : RectKernel.IsRowConcentrated f r δ ε' A B := by
  rcases h with hA | hB | ⟨A', hA'A, hcard, hrows⟩
  · exact Or.inl hA
  · exact Or.inr (Or.inl hB)
  · refine Or.inr (Or.inr ⟨A', hA'A, lt_of_le_of_lt ?_ hcard, fun a ha ↦ (hrows a ha).mono_eps hε⟩)
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

/-- Totalization on the row side: `RectKernel.IsRowConcentrated f r δ ε ∅ B` holds for every
`r`, `δ`, `ε`, `B`, by the first disjunct of the definition. House lemma, no source.
@isnad1 id=isrowcon.0h7v.s4.19b453eaef74 from=translated src=- shape=b3198eca vocab=76ac36e8
-/
theorem rectKernel_isRowConcentrated_empty_left (f : RectKernel X Y) (r δ ε : ℝ)
    (B : Finset Y) : RectKernel.IsRowConcentrated f r δ ε ∅ B :=
  Or.inl rfl

/-- Totalization on the column side: `RectKernel.IsRowConcentrated f r δ ε A ∅` holds for
every `r`, `δ`, `ε`, `A`, by the second disjunct. This is the case a row-only totalization
would get wrong at `ε ≤ 0` with `A ≠ ∅` (see the module docstring and the `Tests` section).
House lemma, no source.
@isnad1 id=isrowcon.0h7v.s4.cc0a35d1d978 from=translated src=- shape=d72e4811 vocab=76ac36e8
-/
theorem rectKernel_isRowConcentrated_empty_right (f : RectKernel X Y) (r δ ε : ℝ)
    (A : Finset X) : RectKernel.IsRowConcentrated f r δ ε A ∅ :=
  Or.inr (Or.inl rfl)

/-- Monotonicity of `(δ, ε)`-homogeneity in `δ`: `δ ≤ δ'` transports
`RectKernel.IsHomogeneousPair f δ ε A B` to `δ'`, keeping the same row value `r` and column
value `s` in `[0,1]`. Both clauses go through `RectKernel.IsRowConcentrated.mono_delta`.
No sign condition on the parameters. House lemma, no source (the paper takes this for
granted).
@isnad1 id=ishomoge.2h8v.s5.4945d84baa80 from=translated src=- shape=dd89bbf1 vocab=f1ce7642
-/
theorem RectKernel.IsHomogeneousPair.mono_delta (h : RectKernel.IsHomogeneousPair f δ ε A B)
    (hδ : δ ≤ δ') : RectKernel.IsHomogeneousPair f δ' ε A B :=
  ⟨let ⟨r, hr, hrow⟩ := h.1; ⟨r, hr, hrow.mono_delta hδ⟩,
   let ⟨s, hs, hcol⟩ := h.2; ⟨s, hs, hcol.mono_delta hδ⟩⟩

/-- Monotonicity of `(δ, ε)`-homogeneity in `ε`: `ε ≤ ε'` transports
`RectKernel.IsHomogeneousPair f δ ε A B` to `ε'`, keeping the same `r` and `s` in `[0,1]`.
Both clauses go through `RectKernel.IsRowConcentrated.mono_eps`. No sign condition on the
parameters. House lemma, no source (the paper takes this for granted).
@isnad1 id=ishomoge.2h8v.s5.ca6f358352be from=translated src=- shape=4893b072 vocab=f1ce7642
-/
theorem RectKernel.IsHomogeneousPair.mono_eps (h : RectKernel.IsHomogeneousPair f δ ε A B)
    (hε : ε ≤ ε') : RectKernel.IsHomogeneousPair f δ ε' A B :=
  ⟨let ⟨r, hr, hrow⟩ := h.1; ⟨r, hr, hrow.mono_eps hε⟩,
   let ⟨s, hs, hcol⟩ := h.2; ⟨s, hs, hcol.mono_eps hε⟩⟩

/-- **Exact transpose law**: swap the two clauses.
@isnad1 id=iff.0h7v.s5.27fa9c965b79 from=translated src=- shape=f77d334a vocab=5ea7f07e
-/
theorem RectKernel.isHomogeneousPair_op_iff :
    RectKernel.IsHomogeneousPair (RectKernel.op f) δ ε B A ↔
      RectKernel.IsHomogeneousPair f δ ε A B :=
  ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

/-- Totalization on the row side: `RectKernel.IsHomogeneousPair f δ ε ∅ B` holds for every
`δ`, `ε`, `B`, with `r = s = 0` as the (irrelevant) common values. The row clause is
`rectKernel_isRowConcentrated_empty_left`; the column clause, stated on the transpose with
`∅` as its column side, is `rectKernel_isRowConcentrated_empty_right`. House lemma, no
source.
@isnad1 id=ishomoge.0h6v.s4.447a0a4b9d1f from=translated src=- shape=f3165179 vocab=9551f186
-/
theorem rectKernel_isHomogeneousPair_empty_left (f : RectKernel X Y) (δ ε : ℝ) (B : Finset Y) :
    RectKernel.IsHomogeneousPair f δ ε ∅ B :=
  ⟨⟨0, ⟨le_rfl, zero_le_one⟩, Or.inl rfl⟩, ⟨0, ⟨le_rfl, zero_le_one⟩, Or.inr (Or.inl rfl)⟩⟩

/-- Totalization on the column side: `RectKernel.IsHomogeneousPair f δ ε A ∅` holds for
every `δ`, `ε`, `A`, with `r = s = 0`. Mirror image of
`rectKernel_isHomogeneousPair_empty_left` under `RectKernel.isHomogeneousPair_op_iff`.
House lemma, no source.
@isnad1 id=ishomoge.0h6v.s4.1041992dce51 from=translated src=- shape=d6044932 vocab=9551f186
-/
theorem rectKernel_isHomogeneousPair_empty_right (f : RectKernel X Y) (δ ε : ℝ)
    (A : Finset X) : RectKernel.IsHomogeneousPair f δ ε A ∅ :=
  ⟨⟨0, ⟨le_rfl, zero_le_one⟩, Or.inr (Or.inl rfl)⟩, ⟨0, ⟨le_rfl, zero_le_one⟩, Or.inl rfl⟩⟩

/-! ### Proposition A.5(a): almost constant ⇒ homogeneous -/

/-- The row half of A.5(a): from an `ε²`-almost `2δ`-constant rectangle, a value `r ∈ [0,1]`
at which the rows are concentrated. The common value is the center of the `2δ`-constant
witness; a row is good when it meets the witness in more than a `(1 − ε)`-fraction of `B`,
and the complement of the witness (fewer than `ε²|A||B|` points) contains at least `ε|B|`
points of every bad row, so fewer than `ε|A|` rows are bad.-/
private theorem RectKernel.exists_isRowConcentrated_of_isAlmostConstantPair (hε : 0 < ε)
    (hrange : IsUnitIntervalOnRectangle f A B)
    (h : IsAlmostConstantPair f (2 * δ) (ε * ε) A B) :
    ∃ r ∈ Set.Icc (0 : ℝ) 1, RectKernel.IsRowConcentrated f r δ ε A B := by
  classical
  rcases h with hAB | ⟨W, hWAB, hcard, hconst⟩
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    rcases Finset.product_eq_empty.mp hAB with hA | hB
    · exact Or.inl hA
    · exact Or.inr (Or.inl hB)
  rcases B.eq_empty_or_nonempty with rfl | hB
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, Or.inr (Or.inl rfl)⟩
  have hrangeW : ∀ p ∈ W, (fun p : X × Y ↦ f p.1 p.2) p ∈ Set.Icc (0 : ℝ) 1 := fun p hp ↦ by
    have hp' := Finset.mem_product.mp (hWAB hp)
    exact hrange p.1 hp'.1 p.2 hp'.2
  obtain ⟨r, hr, hnear⟩ := hconst.exists_center_mem_Icc hrangeW
  have hnear' : ∀ p ∈ W, |f p.1 p.2 - r| < δ := fun p hp ↦ by
    have := hnear p hp
    rwa [show 2 * δ / 2 = δ by ring] at this
  refine ⟨r, hr, ?_⟩
  -- the fiber of the witness over a row, and its projection to `B`
  set fib : X → Finset (X × Y) := fun a ↦ W.filter (fun p ↦ p.1 = a) with hfib
  set Wa : X → Finset Y := fun a ↦ (fib a).image Prod.snd with hWa
  have hWa_card : ∀ a, (Wa a).card = (fib a).card := fun a ↦
    Finset.card_image_of_injOn (fun p hp q hq hpq ↦ by
      have hp1 := (Finset.mem_filter.mp hp).2
      have hq1 := (Finset.mem_filter.mp hq).2
      exact Prod.ext (hp1.trans hq1.symm) hpq)
  have hWa_sub : ∀ a, Wa a ⊆ B := fun a b hb ↦ by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_product.mp (hWAB (Finset.mem_filter.mp hp).1)).2
  have hWa_near : ∀ a, ∀ b ∈ Wa a, |f a b - r| < δ := fun a b hb ↦ by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hpW, hpa⟩ := Finset.mem_filter.mp hp
    have := hnear' p hpW
    rwa [hpa] at this
  have hfib_le : ∀ a, (fib a).card ≤ B.card := fun a ↦ by
    rw [← hWa_card]
    exact Finset.card_le_card (hWa_sub a)
  set good : X → Prop := fun a ↦ (1 - ε) * (B.card : ℝ) < ((fib a).card : ℝ) with hgood
  refine Or.inr (Or.inr ⟨A.filter good, Finset.filter_subset _ _, ?_, fun a ha ↦ ?_⟩)
  · -- Markov: the witness is covered by the good rows (at most `|B|` each) and the bad rows
    -- (at most `(1 − ε)|B|` each).
    have hsum : (W.card : ℝ) = ∑ a ∈ A, ((fib a).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := A)
        (fun p hp ↦ (Finset.mem_product.mp (hWAB hp)).1)]
      push_cast
      rfl
    have hsplit := Finset.sum_filter_add_sum_filter_not A good (fun a ↦ ((fib a).card : ℝ))
    have hgoodsum : ∑ a ∈ A.filter good, ((fib a).card : ℝ) ≤
        ((A.filter good).card : ℝ) * B.card := by
      have := Finset.sum_le_card_nsmul (A.filter good) (fun a ↦ ((fib a).card : ℝ)) (B.card : ℝ)
        (fun a _ ↦ by exact_mod_cast hfib_le a)
      simpa [nsmul_eq_mul] using this
    have hbadsum : ∑ a ∈ A.filter (fun a ↦ ¬ good a), ((fib a).card : ℝ) ≤
        ((A.filter (fun a ↦ ¬ good a)).card : ℝ) * ((1 - ε) * B.card) := by
      have := Finset.sum_le_card_nsmul (A.filter (fun a ↦ ¬ good a))
        (fun a ↦ ((fib a).card : ℝ)) ((1 - ε) * B.card)
        (fun a ha ↦ not_lt.mp (Finset.mem_filter.mp ha).2)
      simpa [nsmul_eq_mul] using this
    have hcount : ((A.filter good).card : ℝ) + ((A.filter (fun a ↦ ¬ good a)).card : ℝ) =
        A.card := by
      exact_mod_cast Finset.card_filter_add_card_filter_not good
    have hbad : ((A.filter (fun a ↦ ¬ good a)).card : ℝ) = A.card - (A.filter good).card := by
      linarith
    rw [hbad] at hbadsum
    rw [Finset.card_product] at hcard
    push_cast at hcard
    have hBpos : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
    have key : ε * B.card * ((1 - ε) * A.card) < ε * B.card * ((A.filter good).card : ℝ) := by
      nlinarith
    exact lt_of_mul_lt_mul_left key (by positivity)
  · exact Or.inr ⟨Wa a, hWa_sub a, by rw [hWa_card]; exact (Finset.mem_filter.mp ha).2,
      hWa_near a⟩

/-- **Proposition A.5(a)** (reformulated variant): an `ε²`-almost `2δ`-constant rectangle is
`(δ, ε)`-homogeneous. The range hypothesis places the common values in `[0,1]`; the column
clause is the row clause of the transpose, through `isAlmostConstantPair_op_iff`.
@isnad1 id=ishomoge.3h7v.s6.4ebd913f4592 from=translated src=- shape=24bd00fc vocab=c8cdef25
-/
theorem RectKernel.isHomogeneousPair_of_isAlmostConstantPair (hε : 0 < ε)
    (hrange : IsUnitIntervalOnRectangle f A B)
    (h : IsAlmostConstantPair f (2 * δ) (ε * ε) A B) :
    RectKernel.IsHomogeneousPair f δ ε A B :=
  ⟨RectKernel.exists_isRowConcentrated_of_isAlmostConstantPair hε hrange h,
   RectKernel.exists_isRowConcentrated_of_isAlmostConstantPair hε
    (fun y hy x hx ↦ hrange x hx y hy) (isAlmostConstantPair_op_iff.mpr h)⟩

/-! ### Proposition A.5(b): homogeneous ⇒ almost constant -/

/-- **Proposition A.5(b)** (reformulated variant, no hypotheses): a `(δ, ε)`-homogeneous
rectangle is `2ε`-almost `2δ`-constant. Only the row clause is used: the union over the good
rows of their good column sets has more than `(1 − ε)²|A||B| ≥ (1 − 2ε)|A||B|` points when
`ε ≤ 1`, and for `ε > 1` the conclusion is the trivial regime.
@isnad1 id=isalmost.1h7v.s6.8fe2ddad5045 from=translated src=- shape=fad50fb1 vocab=a2b1b554
-/
theorem RectKernel.isAlmostConstantPair_of_isHomogeneousPair
    (h : RectKernel.IsHomogeneousPair f δ ε A B) :
    IsAlmostConstantPair f (2 * δ) (2 * ε) A B := by
  classical
  obtain ⟨⟨r, -, hrow⟩, -⟩ := h
  rcases hrow with hA | hB | ⟨A', hA'A, hcardA, hrows⟩
  · exact Or.inl (by rw [hA, Finset.empty_product])
  · exact Or.inl (by rw [hB, Finset.product_empty])
  rcases B.eq_empty_or_nonempty with rfl | hB
  · exact Or.inl (Finset.product_empty A)
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact Or.inl (Finset.empty_product B)
  have hchoice : ∀ a : X, ∃ Wa : Finset Y, a ∈ A' →
      Wa ⊆ B ∧ (1 - ε) * (B.card : ℝ) < (Wa.card : ℝ) ∧ ∀ b ∈ Wa, |f a b - r| < δ := fun a ↦ by
    by_cases ha : a ∈ A'
    · rcases hrows a ha with hB' | ⟨Wa, hWaB, hcard, hnear⟩
      · exact absurd hB' hB.ne_empty
      · exact ⟨Wa, fun _ ↦ ⟨hWaB, hcard, hnear⟩⟩
    · exact ⟨∅, fun h ↦ absurd h ha⟩
  choose Wa hWa using hchoice
  refine Or.inr ⟨A'.biUnion (fun a ↦ {a} ×ˢ Wa a), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, ha, hp⟩ := Finset.mem_biUnion.mp hp
    rw [Finset.mem_product, Finset.mem_singleton] at hp
    obtain ⟨rfl, hb⟩ := hp
    exact Finset.mem_product.mpr ⟨hA'A ha, (hWa _ ha).1 hb⟩
  · have hdisj : (A' : Set X).PairwiseDisjoint (fun a ↦ ({a} : Finset X) ×ˢ Wa a) := by
      intro a _ a' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp hp'
      rw [Finset.mem_product, Finset.mem_singleton] at hp hp'
      exact hne (hp.1.symm.trans hp'.1)
    rw [Finset.card_biUnion hdisj, Finset.card_product]
    push_cast
    simp only [Finset.card_product, Finset.card_singleton, one_mul]
    have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
    have hB0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
    by_cases hε1 : ε ≤ 1
    · have hA'ne : A'.Nonempty := by
        rw [← Finset.card_pos]
        have h0 : (0 : ℝ) ≤ (1 - ε) * A.card := mul_nonneg (by linarith) hA0
        exact_mod_cast lt_of_le_of_lt h0 hcardA
      have hsum : (A'.card : ℝ) * ((1 - ε) * B.card) < ∑ a ∈ A', ((Wa a).card : ℝ) := by
        have := Finset.sum_lt_sum_of_nonempty hA'ne (fun a ha ↦ (hWa a ha).2.1)
        simpa [Finset.sum_const, nsmul_eq_mul] using this
      have hB1 : (0 : ℝ) ≤ (1 - ε) * B.card := mul_nonneg (by linarith) hB0
      have h1 : (1 - ε) * A.card * ((1 - ε) * B.card) ≤ A'.card * ((1 - ε) * B.card) :=
        mul_le_mul_of_nonneg_right hcardA.le hB1
      nlinarith [mul_nonneg (mul_nonneg hA0 hB0) (sq_nonneg ε)]
    · have hε1 := not_le.mp hε1
      have hpos : (0 : ℝ) < A.card * B.card :=
        mul_pos (by exact_mod_cast Finset.card_pos.mpr hA)
          (by exact_mod_cast Finset.card_pos.mpr hB)
      have hneg : (1 - 2 * ε) * (A.card * B.card) < 0 := by nlinarith
      exact lt_of_lt_of_le hneg (Finset.sum_nonneg fun a _ ↦ Nat.cast_nonneg _)
  · intro p hp p' hp'
    obtain ⟨a, ha, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨a', ha', hp'⟩ := Finset.mem_biUnion.mp hp'
    rw [Finset.mem_product, Finset.mem_singleton] at hp hp'
    obtain ⟨rfl, hb⟩ := hp
    obtain ⟨rfl, hb'⟩ := hp'
    have h1 := (hWa _ ha).2.2 _ hb
    have h2 := (hWa _ ha').2.2 _ hb'
    rw [abs_lt] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ### Tests and adversarial examples -/

section Tests

-- Totalization: all three predicates hold on empty sides, unconditionally in the parameters.

/-- The `2 × 2` sharpness kernel: three entries `0`, one outlier `1`.-/
private def outlierKernel : RectKernel (Fin 2) (Fin 2) := fun a b ↦ if a = 1 ∧ b = 1 then 1 else 0

-- It is `1/2`-almost `1/2`-constant (three of four points; `3 > (1 − 1/2)·4 = 2`, strictly) …

end Tests

end RegularityLemmata
