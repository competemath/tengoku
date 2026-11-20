/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.RegularityLemmata.RegularityLemmata.Finite.PairDensity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Approximate homogeneity of a rectangle

A rectangle is `ε`-**homogeneous** for `R` when its density is within `ε` of one of the two
extremes: almost no related pairs, or almost all of them. Carriers are heterogeneous
(`R : α → β → Prop`), matching `RegularityLemmata/Finite/PairDensity.lean`.

The argument order is `R A B ε`, matching `IsUniformPair` rather than putting the tolerance
first — homogeneity is a property *of a rectangle*, parametrized by a tolerance.

**The predicate is instance-free.** `IsHomogeneousPair` elaborates for an arbitrary
`R : α → β → Prop` with no decidability, `DecidableEq`, or `Fintype` assumptions: the
decidability instance that `pairDensity` requires is supplied classically *inside* the
definition. Any ambient instance gives the same proposition — that is `isHomogeneousPair_def`,
which is also the interface every proof below uses (no proof unfolds the classical instance
directly). The zero-instance test at the end of the file pins this contract.

Three symmetries hold unconditionally, including on empty rectangles: monotonicity in `ε`,
invariance under transposing to `swapRel R`, and invariance under complementing `R`. The
last is worth noting: on an empty rectangle `R` and its complement both have density `0`, so
`pairDensity_not` does not apply there — but homogeneity is nevertheless preserved, because
the two sides of the equivalence become the *same* proposition.

Restriction is where the quantitative content lives. Homogeneity degrades under passing to a
subrectangle, by the **inverse relative masses of the two sides separately**: an
exceptional set of density `ε` can concentrate into a subrectangle occupying a `ρA · ρB`
fraction. The exact-homogeneity case `ε = 0` degrades not at all, and is stated separately.

This file imports only `PairDensity`. There is deliberately no partition-level predicate
here: importing `Finpartition` into the finite layer would invert the library's dependency
direction. A `AreHomogeneousPartitions` living above both layers is the right home for that,
if a consumer needs it.
-/

namespace RegularityLemmata

variable {α β : Type*} {R : α → β → Prop}
variable {A A' : Finset α} {B B' : Finset β} {ε ε' : ℝ}

/-- The rectangle `A ×ˢ B` is `ε`-homogeneous for `R`: its density is within `ε` of `0` or
of `1`. Instance-free: the decidability that `pairDensity` needs is supplied classically
inside; read the definition through `isHomogeneousPair_def` under any ambient instance.-/
def IsHomogeneousPair (R : α → β → Prop) (A : Finset α) (B : Finset β) (ε : ℝ) : Prop :=
  letI : DecidableRel R := fun a b => Classical.dec (R a b)
  pairDensity R A B ≤ ε ∨ 1 - ε ≤ pairDensity R A B

/-- The definitional reading, valid over **any** ambient decidability instance: the
classical instance inside `IsHomogeneousPair` is propositionally irrelevant.
@isnad1 id=iff.0h6v.s6.43f2cd0fd1d8 from=translated src=- shape=818bb4c5 vocab=a3c9837f
-/
theorem isHomogeneousPair_def [inst : DecidableRel R] :
    IsHomogeneousPair R A B ε ↔ pairDensity R A B ≤ ε ∨ 1 - ε ≤ pairDensity R A B := by
  unfold IsHomogeneousPair
  rw [show (fun a b => Classical.dec (R a b) : DecidableRel R) = inst from
    funext fun a => funext fun b => Subsingleton.elim _ _]

/-! ### Unconditional symmetries -/

/--
@isnad1 id=ishomoge.2h7v.s5.afa3a53c63bb from=translated src=- shape=e2e8986a vocab=0e9f013a
-/
theorem IsHomogeneousPair.mono (h : IsHomogeneousPair R A B ε) (hε : ε ≤ ε') :
    IsHomogeneousPair R A B ε' := by
  classical
  rw [isHomogeneousPair_def] at h ⊢
  rcases h with h | h
  · exact Or.inl (h.trans hε)
  · exact Or.inr (by linarith)

/-- Transposing swaps the carriers and preserves homogeneity.
@isnad1 id=iff.0h6v.s5.681a929128be from=translated src=- shape=f0d5c86d vocab=9310b3d1
-/
theorem isHomogeneousPair_swapRel_iff :
    IsHomogeneousPair (swapRel R) B A ε ↔ IsHomogeneousPair R A B ε := by
  classical
  rw [isHomogeneousPair_def, isHomogeneousPair_def, pairDensity_swapRel]

/-- Complementing the relation preserves homogeneity — **including on empty rectangles**,
where `pairDensity_not` is unavailable because both densities are `0`. There the two sides
are literally the same proposition; on a nonempty rectangle they exchange the two
disjuncts.
@isnad1 id=iff.0h6v.s5.906d027f33c6 from=translated src=- shape=5eed66b8 vocab=a56281e7
-/
theorem isHomogeneousPair_not_iff :
    IsHomogeneousPair (fun a b => ¬ R a b) A B ε ↔ IsHomogeneousPair R A B ε := by
  classical
  rcases A.eq_empty_or_nonempty with hA | hA
  · subst hA
    rw [isHomogeneousPair_def, isHomogeneousPair_def, pairDensity_empty_left,
      pairDensity_empty_left]
  · rcases B.eq_empty_or_nonempty with hB | hB
    · subst hB
      rw [isHomogeneousPair_def, isHomogeneousPair_def, pairDensity_empty_right,
        pairDensity_empty_right]
    · rw [isHomogeneousPair_def, isHomogeneousPair_def, pairDensity_not hA hB]
      constructor
      · rintro (h | h)
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)
      · rintro (h | h)
        · exact Or.inr (by linarith)
        · exact Or.inl (by linarith)

/-! ### Restriction -/

/-- The shared estimate behind both branches of `IsHomogeneousPair.restrict`: a raw-mass
bound on a relation over `A ×ˢ B` descends to a density bound on a subrectangle, degraded by
the two sides' inverse relative masses.

Guard-free in the subrectangle: if `A'` or `B'` is empty the density is `0`, which is below
the (nonnegative) right-hand side.
@isnad1 id=le.8h10v.s7.19e0b041de6b from=translated src=- shape=05009f4b vocab=a46404fa
-/
theorem pairDensity_restrict_le {S : α → β → Prop} [DecidableRel S] {c ρA ρB : ℝ}
    (hc : 0 ≤ c) (hρA : 0 < ρA) (hρB : 0 < ρB) (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hAc : ρA * (A.card : ℝ) ≤ (A'.card : ℝ)) (hBc : ρB * (B.card : ℝ) ≤ (B'.card : ℝ))
    (hS : (pairCount S A B : ℝ) ≤ c * (A.card : ℝ) * B.card) :
    pairDensity S A' B' ≤ c / (ρA * ρB) := by
  have hρ : (0 : ℝ) < ρA * ρB := mul_pos hρA hρB
  have hmass' : (0 : ℝ) ≤ (A'.card : ℝ) * B'.card := by positivity
  rcases eq_or_lt_of_le hmass' with hzero | hpos
  · rw [pairDensity_eq_count_div, ← hzero, div_zero]
    positivity
  · -- The subrectangle is realized, so both sides of the ambient rectangle are too.
    have hAp : (0 : ℝ) < (A'.card : ℝ) := by
      rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) A'.card) with h | h
      · exfalso; rw [← h, zero_mul] at hpos; exact lt_irrefl 0 hpos
      · exact h
    have hBp : (0 : ℝ) < (B'.card : ℝ) := by
      rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) B'.card) with h | h
      · exfalso; rw [← h, mul_zero] at hpos; exact lt_irrefl 0 hpos
      · exact h
    have hcount : (pairCount S A' B' : ℝ) ≤ c * (A.card : ℝ) * B.card :=
      le_trans (Nat.cast_le.mpr (pairCount_mono hA hB)) hS
    -- `ρAρB·|A||B| ≤ |A'||B'|`, so the ambient mass is controlled by the shrunken one.
    have hAn : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
    have hBn : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
    have hprod : (ρA * ρB) * ((A.card : ℝ) * B.card) ≤ (A'.card : ℝ) * B'.card := by
      calc (ρA * ρB) * ((A.card : ℝ) * B.card)
          = (ρA * (A.card : ℝ)) * (ρB * (B.card : ℝ)) := by ring
        _ ≤ (A'.card : ℝ) * (B'.card : ℝ) :=
            mul_le_mul hAc hBc (by positivity) (le_of_lt hAp)
    rw [pairDensity_eq_count_div, div_le_div_iff₀ hpos hρ]
    calc (pairCount S A' B' : ℝ) * (ρA * ρB)
        ≤ (c * (A.card : ℝ) * B.card) * (ρA * ρB) :=
          mul_le_mul_of_nonneg_right hcount hρ.le
      _ = c * ((ρA * ρB) * ((A.card : ℝ) * B.card)) := by ring
      _ ≤ c * ((A'.card : ℝ) * B'.card) := mul_le_mul_of_nonneg_left hprod hc

/-- **Exact homogeneity is closed under subrectangles.** At `ε = 0` there is no degradation:
a rectangle with no related pairs, or with every pair related, keeps that property on every
subrectangle. (An empty subrectangle lands in the first disjunct, since its density is `0`.)
@isnad1 id=ishomoge.3h7v.s6.64b1ba6fbc89 from=translated src=- shape=da9de945 vocab=0e9f013a
-/
theorem IsHomogeneousPair.subset_zero (h : IsHomogeneousPair R A B 0)
    (hA : A' ⊆ A) (hB : B' ⊆ B) : IsHomogeneousPair R A' B' 0 := by
  classical
  rw [isHomogeneousPair_def] at h ⊢
  have hmass : (0 : ℝ) ≤ (A.card : ℝ) * B.card := by positivity
  rcases h with h | h
  · -- No related pairs upstairs, hence none downstairs.
    left
    have hzero : (pairCount R A B : ℝ) ≤ 0 := by
      rw [pairCount_eq_pairDensity_mul]
      exact mul_nonpos_of_nonpos_of_nonneg h hmass
    have hzero' : pairCount R A B = 0 := by
      have := Nat.cast_nonneg (α := ℝ) (pairCount R A B)
      exact_mod_cast le_antisymm hzero this
    have : pairCount R A' B' = 0 :=
      Nat.le_zero.mp (hzero' ▸ pairCount_mono hA hB)
    rw [pairDensity_eq_count_div, this]
    simp
  · -- Every pair related upstairs, so the complement is empty downstairs too.
    rw [sub_zero] at h
    have hall : (A.card : ℝ) * B.card ≤ (pairCount R A B : ℝ) := by
      rw [pairCount_eq_pairDensity_mul]
      nlinarith [pairDensity_le_one (R := R) (A := A) (B := B)]
    have hnot : pairCount (fun a b => ¬ R a b) A B = 0 := by
      have hsum := pairCount_add_not (R := R) (A := A) (B := B)
      have hle : (A.card : ℝ) * B.card ≤ (pairCount R A B : ℝ) := hall
      have : pairCount R A B = A.card * B.card := by
        have h1 : pairCount R A B ≤ A.card * B.card := by omega
        have h2 : A.card * B.card ≤ pairCount R A B := by exact_mod_cast hle
        omega
      omega
    have hnot' : pairCount (fun a b => ¬ R a b) A' B' = 0 :=
      Nat.le_zero.mp (hnot ▸ pairCount_mono (R := fun a b => ¬ R a b) hA hB)
    rcases A'.eq_empty_or_nonempty with hAe | hAe
    · left; rw [hAe, pairDensity_empty_left]
    rcases B'.eq_empty_or_nonempty with hBe | hBe
    · left; rw [hBe, pairDensity_empty_right]
    right
    rw [sub_zero]
    have hd : pairDensity (fun a b => ¬ R a b) A' B' = 0 := by
      rw [pairDensity_eq_count_div, hnot']
      simp
    rw [pairDensity_not hAe hBe] at hd
    linarith

/-- **Quantitative restriction.** Homogeneity passes to a subrectangle occupying at least a
`ρA` fraction of the left side and a `ρB` fraction of the right, with the tolerance degraded
by `ρA · ρB` — the exceptional mass can concentrate by the inverse relative rectangle mass.

The two proportions are tracked **separately** rather than as a single rectangle fraction,
because a consumer that shrinks only one side should pay only that side's factor.
@isnad1 id=ishomoge.8h10v.s7.bade4a668ad8 from=translated src=- shape=bd0a8a31 vocab=dfa45780
-/
theorem IsHomogeneousPair.restrict {ρA ρB : ℝ} (h : IsHomogeneousPair R A B ε)
    (hε : 0 ≤ ε) (hρA : 0 < ρA) (hρB : 0 < ρB) (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hAc : ρA * (A.card : ℝ) ≤ (A'.card : ℝ)) (hBc : ρB * (B.card : ℝ) ≤ (B'.card : ℝ)) :
    IsHomogeneousPair R A' B' (ε / (ρA * ρB)) := by
  classical
  rw [isHomogeneousPair_def] at h ⊢
  rcases h with h | h
  · left
    exact pairDensity_restrict_le hε hρA hρB hA hB hAc hBc
      (pairCount_le_of_pairDensity_le h)
  · -- Sparse complement upstairs: bound its count, restrict, then convert back.
    have hnotcount : (pairCount (fun a b => ¬ R a b) A B : ℝ)
        ≤ ε * (A.card : ℝ) * B.card := by
      have hsum := pairCount_add_not (R := R) (A := A) (B := B)
      have hR : (1 - ε) * (A.card : ℝ) * B.card ≤ (pairCount R A B : ℝ) :=
        le_pairCount_of_le_pairDensity h
      have hcast : (pairCount R A B : ℝ) + (pairCount (fun a b => ¬ R a b) A B : ℝ)
          = (A.card : ℝ) * B.card := by exact_mod_cast congrArg (Nat.cast (R := ℝ)) hsum
      nlinarith [hR, hcast]
    have hnotd : pairDensity (fun a b => ¬ R a b) A' B' ≤ ε / (ρA * ρB) :=
      pairDensity_restrict_le hε hρA hρB hA hB hAc hBc hnotcount
    rcases A'.eq_empty_or_nonempty with hAe | hAe
    · left
      rw [hAe, pairDensity_empty_left]
      positivity
    rcases B'.eq_empty_or_nonempty with hBe | hBe
    · left
      rw [hBe, pairDensity_empty_right]
      positivity
    right
    rw [pairDensity_not hAe hBe] at hnotd
    linarith

/-! ### Perturbation -/

/-- Homogeneity is stable under density perturbation: if two rectangles have densities within
`γ`, homogeneity of one at `ε` gives homogeneity of the other at `ε + γ`.
@isnad1 id=ishomoge.2h9v.s6.56690766f9ff from=translated src=- shape=99c42ded vocab=2f24c636
-/
theorem IsHomogeneousPair.of_abs_pairDensity_sub_le [DecidableRel R] {γ : ℝ}
    (h : IsHomogeneousPair R A' B' ε)
    (hclose : |pairDensity R A B - pairDensity R A' B'| ≤ γ) :
    IsHomogeneousPair R A B (ε + γ) := by
  rw [isHomogeneousPair_def] at h ⊢
  rw [abs_le] at hclose
  rcases h with h | h
  · exact Or.inl (by linarith [hclose.2])
  · exact Or.inr (by linarith [hclose.1])

/-- Division form of the sub-rectangle comparison for growth by at most `k` elements per side:
the density moves by at most `2k(s + k)/s²` when the smaller rectangle has both sides of size
at least `s`. Generalizes `abs_pairDensity_sub_le_of_grow_one` (the case `k = 1`).
@isnad1 id=le.7h9v.s7.f01b328e04b3 from=translated src=- shape=6e723ba0 vocab=d3c1ea36
-/
theorem abs_pairDensity_sub_le_of_grow [DecidableRel R] [DecidableEq α] [DecidableEq β]
    {A' : Finset α} {B' : Finset β} {s k : ℕ} (hs : 0 < s)
    (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hA'c : s ≤ A'.card) (hB'c : s ≤ B'.card)
    (hAc : A.card ≤ A'.card + k) (hBc : B.card ≤ B'.card + k) :
    |pairDensity R A B - pairDensity R A' B'| ≤ 2 * k * ((s : ℝ) + k) / s ^ 2 := by
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have haR : (s : ℝ) ≤ (A'.card : ℝ) := by exact_mod_cast hA'c
  have hbR : (s : ℝ) ≤ (B'.card : ℝ) := by exact_mod_cast hB'c
  have hap : (0 : ℝ) < (A'.card : ℝ) := hsR.trans_le haR
  have hbp : (0 : ℝ) < (B'.card : ℝ) := hsR.trans_le hbR
  have hmass : (0 : ℝ) < (A'.card : ℝ) * (B'.card : ℝ) := mul_pos hap hbp
  have hdA : ((A \ A').card : ℝ) ≤ (k : ℝ) := by
    have h1 : (A \ A').card ≤ k := by
      rw [Finset.card_sdiff_of_subset hA]
      omega
    exact_mod_cast h1
  have hdB : ((B \ B').card : ℝ) ≤ (k : ℝ) := by
    have h1 : (B \ B').card ≤ k := by
      rw [Finset.card_sdiff_of_subset hB]
      omega
    exact_mod_cast h1
  have hAcR : (A.card : ℝ) ≤ (A'.card : ℝ) + k := by exact_mod_cast hAc
  have hBcR : (B.card : ℝ) ≤ (B'.card : ℝ) + k := by exact_mod_cast hBc
  -- Each discarded strip has mass at most `k` full rows or columns of the enlarged rectangle.
  have hstripA : ((A \ A').card : ℝ) * (B.card : ℝ) ≤ (k : ℝ) * ((B'.card : ℝ) + k) :=
    mul_le_mul hdA hBcR (Nat.cast_nonneg _) hkR
  have hstripB : (A.card : ℝ) * ((B \ B').card : ℝ) ≤ ((A'.card : ℝ) + k) * k :=
    mul_le_mul hAcR hdB (Nat.cast_nonneg _) (by positivity)
  -- Divide the multiplication-form comparison by the small rectangle's mass.
  have hstep : |pairDensity R A' B' - pairDensity R A B|
      ≤ ((k : ℝ) * ((B'.card : ℝ) + k) + ((A'.card : ℝ) + k) * k)
        / ((A'.card : ℝ) * (B'.card : ℝ)) := by
    rw [le_div_iff₀ hmass]
    calc |pairDensity R A' B' - pairDensity R A B| * ((A'.card : ℝ) * (B'.card : ℝ))
        ≤ ((A \ A').card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * ((B \ B').card : ℝ) :=
          abs_pairDensity_sub_mul_le hA hB
      _ ≤ (k : ℝ) * ((B'.card : ℝ) + k) + ((A'.card : ℝ) + k) * k := by linarith
  -- Worsen the bound to depend only on `s`: both sides are at least `s`.
  have hdiv : ((k : ℝ) * ((B'.card : ℝ) + k) + ((A'.card : ℝ) + k) * k)
      / ((A'.card : ℝ) * (B'.card : ℝ)) ≤ 2 * k * ((s : ℝ) + k) / (s : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hmass (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hkR hsR.le) hap.le) (sub_nonneg.mpr hbR),
      mul_nonneg (mul_nonneg (mul_nonneg hkR hsR.le) hbp.le) (sub_nonneg.mpr haR),
      mul_nonneg (mul_nonneg (mul_nonneg hkR hkR) (sub_nonneg.mpr haR)) (sub_nonneg.mpr hbR),
      mul_nonneg (mul_nonneg (mul_nonneg hkR hkR) hsR.le) (sub_nonneg.mpr haR),
      mul_nonneg (mul_nonneg (mul_nonneg hkR hkR) hsR.le) (sub_nonneg.mpr hbR)]
  calc |pairDensity R A B - pairDensity R A' B'|
      = |pairDensity R A' B' - pairDensity R A B| := abs_sub_comm _ _
    _ ≤ 2 * k * ((s : ℝ) + k) / (s : ℝ) ^ 2 := hstep.trans hdiv

/-- Division form of the sub-rectangle comparison: growing each side by at most one element
moves the density by at most `2 * (s + 1) / s ^ 2` when the smaller rectangle has both sides of
size at least `s`. This is the exact cost of absorbing one leftover element per block.
@isnad1 id=le.7h8v.s7.24d6b214b5d6 from=translated src=- shape=0e651417 vocab=d3c1ea36
-/
theorem abs_pairDensity_sub_le_of_grow_one [DecidableRel R] [DecidableEq α] [DecidableEq β]
    {s : ℕ} (hs : 0 < s)
    (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hA'c : s ≤ A'.card) (hB'c : s ≤ B'.card)
    (hAc : A.card ≤ A'.card + 1) (hBc : B.card ≤ B'.card + 1) :
    |pairDensity R A B - pairDensity R A' B'| ≤ 2 * ((s : ℝ) + 1) / s ^ 2 := by
  simpa using abs_pairDensity_sub_le_of_grow (k := 1) hs hA hB hA'c hB'c hAc hBc

/-! ### Endpoint regimes

The two trivial ends of the tolerance scale, stated so that consumers need not re-derive
them: at `1/2` every rectangle is homogeneous, and a one-point rectangle is homogeneous at
tolerance `0`. -/

/-- **Half is the trivial tolerance.** Every rectangle is `ε`-homogeneous once `1/2 ≤ ε`,
because a density in `[0,1]` is either at most `1/2` or at least `1/2`. No hypothesis on `R`,
`A`, or `B` — the empty rectangle included, where the guard-free density is `0`.
@isnad1 id=ishomoge.1h6v.s5.0c3c9ed28d76 from=translated src=- shape=54b4b852 vocab=5846e63a
-/
theorem isHomogeneousPair_of_half_le (R : α → β → Prop) (A : Finset α) (B : Finset β)
    (hε : (1 : ℝ) / 2 ≤ ε) : IsHomogeneousPair R A B ε := by
  classical
  rw [isHomogeneousPair_def]
  rcases le_or_gt (pairDensity R A B) (1 / 2) with h | h
  · exact Or.inl (h.trans hε)
  · exact Or.inr (by linarith)

/-- **A one-point rectangle is exactly homogeneous**: its density is `0` or `1`, so it is
`0`-homogeneous, hence `ε`-homogeneous for every `ε ≥ 0`.
@isnad1 id=ishomoge.0h5v.s5.fb5fd7a4d7c6 from=translated src=- shape=38110a68 vocab=91503355
-/
theorem isHomogeneousPair_singleton [DecidableEq α] [DecidableEq β] (R : α → β → Prop)
    (a : α) (b : β) : IsHomogeneousPair R {a} {b} 0 := by
  classical
  rw [isHomogeneousPair_def, pairDensity_singleton_left]
  by_cases h : R a b
  · refine Or.inr ?_
    rw [Finset.filter_singleton]
    simp [h]
  · refine Or.inl ?_
    rw [Finset.filter_singleton]
    simp [h]

/-! ### Relative growth

The perturbation theorem in **relative** form: when each side grows by at most a proportion of
itself, the density moves by a bound depending only on those proportions, not on any absolute
size. This is the neutral statement; ledger-specific instantiations (a particular `β`-schedule
and its arithmetic) belong to the developments that fix those constants, not here. -/

/-- **Relative-growth transfer.** If `A' ⊆ A` grows by at most a factor `1 + cX` and `B' ⊆ B`
by at most `1 + cY`, the pair density moves by at most `cX + cY + 2·cX·cY`.

The error is symmetric under swapping the carriers, which is the sense in which a single
output tolerance is the right shape: the asymmetry lives entirely in the two growth inputs.

**No sign hypothesis on `cX`, `cY` is needed.** Nonnegativity is forced: `A' ⊆ A` gives
`|A'| ≤ |A| ≤ (1 + cX)|A'|`, and `|A'| > 0` then yields `0 ≤ cX`. Stating it would be
redundant rather than defensive.
@isnad1 id=le.6h9v.s7.bf94bad79f04 from=translated src=- shape=fbbd807b vocab=67f72ddf
-/
theorem abs_pairDensity_sub_le_of_relative_grow [DecidableRel R] [DecidableEq α] [DecidableEq β]
    {A' : Finset α} {B' : Finset β} {cX cY : ℝ}
    (hA : A' ⊆ A) (hB : B' ⊆ B) (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty)
    (hAc : (A.card : ℝ) ≤ (1 + cX) * A'.card)
    (hBc : (B.card : ℝ) ≤ (1 + cY) * B'.card) :
    |pairDensity R A B - pairDensity R A' B'| ≤ cX + cY + 2 * cX * cY := by
  have hap : (0 : ℝ) < (A'.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA'ne
  have hbp : (0 : ℝ) < (B'.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hB'ne
  have hmass : (0 : ℝ) < (A'.card : ℝ) * (B'.card : ℝ) := mul_pos hap hbp
  -- Each discarded strip is a proportion of the small rectangle.
  have hdA : ((A \ A').card : ℝ) ≤ cX * A'.card := by
    have h : ((A \ A').card : ℝ) = (A.card : ℝ) - (A'.card : ℝ) := by
      rw [Finset.card_sdiff_of_subset hA, Nat.cast_sub (Finset.card_le_card hA)]
    rw [h]; nlinarith
  have hdB : ((B \ B').card : ℝ) ≤ cY * B'.card := by
    have h : ((B \ B').card : ℝ) = (B.card : ℝ) - (B'.card : ℝ) := by
      rw [Finset.card_sdiff_of_subset hB, Nat.cast_sub (Finset.card_le_card hB)]
    rw [h]; nlinarith
  have hbound : |pairDensity R A' B' - pairDensity R A B| * ((A'.card : ℝ) * (B'.card : ℝ))
      ≤ (cX + cY + 2 * cX * cY) * ((A'.card : ℝ) * (B'.card : ℝ)) :=
    calc |pairDensity R A' B' - pairDensity R A B| * ((A'.card : ℝ) * (B'.card : ℝ))
        ≤ ((A \ A').card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * ((B \ B').card : ℝ) :=
          abs_pairDensity_sub_mul_le hA hB
      _ ≤ (cX + cY + 2 * cX * cY) * ((A'.card : ℝ) * (B'.card : ℝ)) := by nlinarith
  rw [abs_sub_comm]
  exact le_of_mul_le_mul_right hbound hmass

/-! ### Tests and adversarial examples -/

section Tests

-- **Zero-instance smoke test**: the public statement elaborates for an arbitrary relation
-- with no `Fintype`, `DecidableEq`, or decidability assumptions whatsoever. This example is
-- the frozen contract; do not add instances to make a change to the definition compile.

end Tests

end RegularityLemmata
