import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Oscillation, midpoint, and Lemma 2.1 of the manuscript (vertical comparison)

Auditor's supplement (not part of the audited archive).

Section 2.1 of the manuscript defines, for a function `f` of the height and a vertical
interval `B`,

`osc_B f = max_B f - min_B f`,   `mid_B f = (max_B f + min_B f) / 2`,

where the extrema are over `y ∈ B`. All functions considered there take finitely many values,
so the extrema exist. Here `max_B f` and `min_B f` are `sSup (f '' B)` and `sInf (f '' B)`;
`maxOn_mem` and `minOn_mem` show that for a function with finitely many values on a nonempty
`B` they are attained, i.e. they are the maximum and the minimum. `osc_const_mul` is the
manuscript's "Clearly `osc_B (c f) = |c| osc_B f` for real `c`"; with these definitions of
the extrema it holds for every `B` and every `f`. `osc_neg` is its case `c = -1`, the
manuscript's "`osc_B (-g) = osc_B g`".

`osc_add_le` is the triangle inequality `osc_B (f + g) ≤ osc_B f + osc_B g`. It is proved as
in the manuscript, "because the maximum of `f+g` on `B` is at most `max_B f + max_B g`, and
its minimum is at least `min_B f + min_B g`": these two facts are `maxOn_add_le` and
`add_minOn_le`. `osc_sum_le` is the triangle inequality for finite sums. (The reverse
triangle inequality is in `StepOsc.lean`.)

Section 2.2 cuts `J` into blocks (`block`, `iUnion_block`, `block_disjoint`) and sets
`R^in = I × (B_2 ∪ ⋯ ∪ B_{b-1})`, the inner region. `iUnion_inner_blocks` shows that the
union `B_2 ∪ ⋯ ∪ B_{b-1}` of the inner blocks is the interval `[s + L, s + (b-1) L)`, and
`inner_blocks_nonempty` that this interval is not empty when `b ≥ 3`.

`vertical_comparison` is **Lemma 2.1** as stated: for `J` cut into `b` blocks
`B_1, …, B_b` of equal length, from bottom to top, and `f` with finitely many values on `J`,

`b · osc_J f ≥ Σ_ℓ osc_{B_ℓ} f + 2 |mid_{B_b} f - mid_{B_1} f|`.

The proof is the one of the manuscript, sentence by sentence:

* `maxOn_sub_minOn_le_osc`, `maxOn_sub_minOn_eq`: the first display. Its first line is
  `osc_J f ≥ max_{B_b} f - min_{B_1} f`
  `= (osc_{B_1} f + osc_{B_b} f)/2 + (mid_{B_b} f - mid_{B_1} f)`,
  and its second line is the same with `B_1` and `B_b` exchanged. "Since `J` contains `B_1`
  and `B_b`", the inequality holds, and the equality holds because "the extrema of `f` on a
  block `B` are `mid_B f ± ½ osc_B f`" (`maxOn_eq_mid_add`, `minOn_eq_mid_sub`);
* `half_osc_add_abs_mid_sub_le`: "Taking the larger of the two right-hand sides,
  `osc_J f ≥ (osc_{B_1} f + osc_{B_b} f)/2 + |mid_{B_b} f - mid_{B_1} f|`";
* `osc_mono`: "Also `osc_J f ≥ osc_{B_ℓ} f` for each of the remaining `b-2` blocks `B_ℓ`";
* `vertical_comparison_sets`: "Adding these `b-2` inequalities and twice the last display
  proves (4)."

It uses nothing about the blocks except that they are nonempty subsets of `J`
(`vertical_comparison_sets`). This file does not use the archive.
-/

namespace R56Audit

noncomputable section

variable {α : Type*}

/-- `max_B f`, as a supremum.-/
def maxOn (B : Set α) (f : α → ℝ) : ℝ := sSup (f '' B)

/-- `min_B f`, as an infimum.-/
def minOn (B : Set α) (f : α → ℝ) : ℝ := sInf (f '' B)

/-- The oscillation `osc_B f = max_B f - min_B f` of display (3).-/
def osc (B : Set α) (f : α → ℝ) : ℝ := maxOn B f - minOn B f

/-- The midpoint `mid_B f = (max_B f + min_B f) / 2` of display (3).-/
def mid (B : Set α) (f : α → ℝ) : ℝ := (maxOn B f + minOn B f) / 2

/-- "They take finitely many values, so these extrema exist": the supremum is a maximum.
@isnad1 id=ex.2h3v.s5.dd648eaf162c from=translated src=- shape=0df7b14d vocab=0de9799b
-/
lemma maxOn_mem {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite) :
    ∃ y ∈ B, f y = maxOn B f :=
  (hB.image f).csSup_mem hf

/-- The infimum is a minimum.
@isnad1 id=ex.2h3v.s5.a5822fe6f19b from=translated src=- shape=0df7b14d vocab=f6d6e408
-/
lemma minOn_mem {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite) :
    ∃ y ∈ B, f y = minOn B f :=
  (hB.image f).csInf_mem hf

/--
@isnad1 id=le.2h4v.s5.d95b883b3ff3 from=translated src=- shape=be00e523 vocab=00328a32
-/
lemma le_maxOn {B : Set α} {f : α → ℝ} (hf : (f '' B).Finite) {y : α} (hy : y ∈ B) :
    f y ≤ maxOn B f :=
  le_csSup hf.bddAbove (Set.mem_image_of_mem f hy)

/--
@isnad1 id=le.2h4v.s5.90de721a99a0 from=translated src=- shape=1b9858e2 vocab=fe0b4174
-/
lemma minOn_le {B : Set α} {f : α → ℝ} (hf : (f '' B).Finite) {y : α} (hy : y ∈ B) :
    minOn B f ≤ f y :=
  csInf_le hf.bddBelow (Set.mem_image_of_mem f hy)

/--
@isnad1 id=le.2h4v.s5.e0d148fba24a from=translated src=- shape=dd74d67b vocab=ebb44a4b
-/
lemma maxOn_le {B : Set α} {f : α → ℝ} (hB : B.Nonempty) {c : ℝ} (h : ∀ y ∈ B, f y ≤ c) :
    maxOn B f ≤ c := by
  apply csSup_le (hB.image f)
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy

/--
@isnad1 id=le.2h4v.s5.6b1abaff587e from=translated src=- shape=9de61e54 vocab=7d3de5f3
-/
lemma le_minOn {B : Set α} {f : α → ℝ} (hB : B.Nonempty) {c : ℝ} (h : ∀ y ∈ B, c ≤ f y) :
    c ≤ minOn B f := by
  apply le_csInf (hB.image f)
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy

/-- The extrema are `mid_B f ± osc_B f / 2`.
@isnad1 id=eq.0h3v.s5.cd2916b80018 from=translated src=- shape=b97821ff vocab=ae7b1364
-/
lemma maxOn_eq_mid_add (B : Set α) (f : α → ℝ) : maxOn B f = mid B f + osc B f / 2 := by
  unfold mid osc; ring

/--
@isnad1 id=eq.0h3v.s5.171bff32e988 from=translated src=- shape=b97821ff vocab=dc447568
-/
lemma minOn_eq_mid_sub (B : Set α) (f : α → ℝ) : minOn B f = mid B f - osc B f / 2 := by
  unfold mid osc; ring

/--
@isnad1 id=le.2h3v.s5.4b4b516ad2e2 from=translated src=- shape=1218c7c6 vocab=9195fbf6
-/
lemma minOn_le_maxOn {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite) :
    minOn B f ≤ maxOn B f := by
  obtain ⟨y, hy⟩ := hB
  exact (minOn_le hf hy).trans (le_maxOn hf hy)

/--
@isnad1 id=le.2h3v.s5.274b7c7934b3 from=translated src=- shape=8ccd9afd vocab=1059cec2
-/
lemma osc_nonneg {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite) :
    0 ≤ osc B f :=
  sub_nonneg.mpr (minOn_le_maxOn hB hf)

/-- A difference of two values on `B` is at most the oscillation.
@isnad1 id=le.3h5v.s5.fd7900952cec from=translated src=- shape=42133ceb vocab=aa78da73
-/
lemma sub_le_osc {B : Set α} {f : α → ℝ} (hf : (f '' B).Finite) {y y' : α} (hy : y ∈ B)
    (hy' : y' ∈ B) : f y - f y' ≤ osc B f := by
  have h1 := le_maxOn hf hy
  have h2 := minOn_le hf hy'
  unfold osc
  linarith

/-- The oscillation is the least bound for the differences of two values on `B`.
@isnad1 id=le.2h4v.s5.af8033478ab5 from=translated src=- shape=bc285a0d vocab=2dfbc823
-/
lemma osc_le {B : Set α} {f : α → ℝ} (hB : B.Nonempty) {c : ℝ}
    (h : ∀ y ∈ B, ∀ y' ∈ B, f y - f y' ≤ c) : osc B f ≤ c := by
  have h1 : maxOn B f ≤ minOn B f + c := by
    apply maxOn_le hB
    intro y hy
    have : f y - c ≤ minOn B f := le_minOn hB (fun y' hy' => by linarith [h y hy y' hy'])
    linarith
  unfold osc
  linarith

/-- The extrema over a subset lie between the extrema over the set.
@isnad1 id=le.3h4v.s5.85a71c16b96c from=translated src=- shape=3d44b86c vocab=c446d0ad
-/
lemma maxOn_mono {A B : Set α} {f : α → ℝ} (hA : A.Nonempty) (hAB : A ⊆ B)
    (hf : (f '' B).Finite) : maxOn A f ≤ maxOn B f :=
  maxOn_le hA fun _ hy => le_maxOn hf (hAB hy)

/--
@isnad1 id=le.3h4v.s5.e338c3db7a88 from=translated src=- shape=f0ea0162 vocab=6d01cdf9
-/
lemma minOn_anti {A B : Set α} {f : α → ℝ} (hA : A.Nonempty) (hAB : A ⊆ B)
    (hf : (f '' B).Finite) : minOn B f ≤ minOn A f :=
  le_minOn hA fun _ hy => minOn_le hf (hAB hy)

/--
@isnad1 id=eq.1h4v.s5.53a8cbac9591 from=translated src=- shape=7ff4b184 vocab=aeb3ca72
-/
lemma maxOn_congr {B : Set α} {f g : α → ℝ} (h : ∀ y ∈ B, f y = g y) :
    maxOn B f = maxOn B g := by
  unfold maxOn
  rw [Set.image_congr h]

/--
@isnad1 id=eq.1h4v.s5.3e7bf2cafa23 from=translated src=- shape=7ff4b184 vocab=5e201ab3
-/
lemma minOn_congr {B : Set α} {f g : α → ℝ} (h : ∀ y ∈ B, f y = g y) :
    minOn B f = minOn B g := by
  unfold minOn
  rw [Set.image_congr h]

/--
@isnad1 id=eq.1h4v.s5.4fb2b5afc787 from=translated src=- shape=7ff4b184 vocab=8f4169c0
-/
lemma osc_congr {B : Set α} {f g : α → ℝ} (h : ∀ y ∈ B, f y = g y) : osc B f = osc B g := by
  unfold osc
  rw [maxOn_congr h, minOn_congr h]

/--
@isnad1 id=eq.1h4v.s5.ed4bd34b3053 from=translated src=- shape=7ff4b184 vocab=298656d2
-/
lemma mid_congr {B : Set α} {f g : α → ℝ} (h : ∀ y ∈ B, f y = g y) : mid B f = mid B g := by
  unfold mid
  rw [maxOn_congr h, minOn_congr h]

/-- "Clearly `osc_B (c f) = |c| osc_B f` for real `c`." With the extrema defined as `sSup` and
`sInf`, this needs no hypothesis on `B` or on `f`.
@isnad1 id=eq.0h4v.s5.9d1d8c435b1f from=translated src=- shape=0a5a60ba vocab=e8c0483f
-/
theorem osc_const_mul (B : Set α) (f : α → ℝ) (c : ℝ) :
    osc B (fun y => c * f y) = |c| * osc B f := by
  unfold osc maxOn minOn
  simp only [sSup_image', sInf_image']
  rcases le_total 0 c with hc | hc
  · -- `c ≥ 0`: the maximum and the minimum are multiplied by `c`
    rw [← Real.mul_iSup_of_nonneg hc, ← Real.mul_iInf_of_nonneg hc, abs_of_nonneg hc]
    ring
  · -- `c ≤ 0`: the maximum of `c f` is `c` times the minimum of `f`, and conversely
    rw [← Real.mul_iInf_of_nonpos hc, ← Real.mul_iSup_of_nonpos hc, abs_of_nonpos hc]
    ring

/-- Adding a constant adds it to the maximum.
@isnad1 id=eq.2h4v.s5.304f7604fa18 from=translated src=- shape=548ee9da vocab=3b8fda62
-/
lemma maxOn_add_const {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (c : ℝ) : maxOn B (fun y => f y + c) = maxOn B f + c := by
  have hfc : ((fun y => f y + c) '' B).Finite := by
    have : (fun y => f y + c) '' B = (fun t => t + c) '' (f '' B) := by
      rw [Set.image_image]
    rw [this]
    exact hf.image _
  apply le_antisymm
  · exact maxOn_le hB fun y hy => by linarith [le_maxOn hf hy]
  · have : maxOn B f ≤ maxOn B (fun y => f y + c) - c :=
      maxOn_le hB fun y hy => by linarith [le_maxOn hfc hy]
    linarith

/-- Adding a constant adds it to the minimum.
@isnad1 id=eq.2h4v.s5.ae0a187e7fbf from=translated src=- shape=548ee9da vocab=2b23a7c3
-/
lemma minOn_add_const {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (c : ℝ) : minOn B (fun y => f y + c) = minOn B f + c := by
  have hfc : ((fun y => f y + c) '' B).Finite := by
    have : (fun y => f y + c) '' B = (fun t => t + c) '' (f '' B) := by
      rw [Set.image_image]
    rw [this]
    exact hf.image _
  apply le_antisymm
  · have : minOn B (fun y => f y + c) - c ≤ minOn B f :=
      le_minOn hB fun y hy => by linarith [minOn_le hfc hy]
    linarith
  · exact le_minOn hB fun y hy => by linarith [minOn_le hf hy]

/-- **Shift invariance**: adding a constant does not change the oscillation.
@isnad1 id=eq.2h4v.s5.7915db48beb8 from=translated src=- shape=f8db1dc5 vocab=e439be75
-/
lemma osc_add_const {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (c : ℝ) : osc B (fun y => f y + c) = osc B f := by
  unfold osc
  rw [maxOn_add_const hB hf, minOn_add_const hB hf]
  ring

/-- Adding a constant `c` adds `c` to the midpoint.
@isnad1 id=eq.2h4v.s5.d07d564f17e9 from=translated src=- shape=548ee9da vocab=c0b121e9
-/
lemma mid_add_const {B : Set α} {f : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (c : ℝ) : mid B (fun y => f y + c) = mid B f + c := by
  unfold mid
  rw [maxOn_add_const hB hf, minOn_add_const hB hf]
  ring

/-- "the maximum of `f+g` on `B` is at most `max_B f + max_B g`": the first half of the
manuscript's reason for the triangle inequality.
@isnad1 id=le.3h4v.s6.d0588dbfef0a from=translated src=- shape=cbddfc76 vocab=9788b5a3
-/
lemma maxOn_add_le {B : Set α} {f g : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (hg : (g '' B).Finite) : maxOn B (fun y => f y + g y) ≤ maxOn B f + maxOn B g :=
  -- every value of `f + g` on `B` is at most `max_B f + max_B g`
  maxOn_le hB fun _ hy => add_le_add (le_maxOn hf hy) (le_maxOn hg hy)

/-- "its minimum is at least `min_B f + min_B g`": the second half of the manuscript's reason
for the triangle inequality; "its" refers to `f+g` on `B`.
@isnad1 id=le.3h4v.s6.7185abdcb257 from=translated src=- shape=b197e87d vocab=7ba3043d
-/
lemma add_minOn_le {B : Set α} {f g : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (hg : (g '' B).Finite) : minOn B f + minOn B g ≤ minOn B (fun y => f y + g y) :=
  -- every value of `f + g` on `B` is at least `min_B f + min_B g`
  le_minOn hB fun _ hy => add_le_add (minOn_le hf hy) (minOn_le hg hy)

/-- **The triangle inequality** `osc_B (f + g) ≤ osc_B f + osc_B g`, "because the maximum of
`f+g` on `B` is at most `max_B f + max_B g`, and its minimum is at least `min_B f + min_B g`"
(`maxOn_add_le`, `add_minOn_le`).
@isnad1 id=le.3h4v.s6.f95c2178409c from=translated src=- shape=cbddfc76 vocab=b77c9a2c
-/
lemma osc_add_le {B : Set α} {f g : α → ℝ} (hB : B.Nonempty) (hf : (f '' B).Finite)
    (hg : (g '' B).Finite) : osc B (fun y => f y + g y) ≤ osc B f + osc B g := by
  -- the maximum of `f + g`, and its minimum
  have h1 := maxOn_add_le hB hf hg
  have h2 := add_minOn_le hB hf hg
  -- the oscillation is the maximum minus the minimum
  unfold osc
  linarith

/-- "`osc_B (-g) = osc_B g`": the case `c = -1` of `osc_B (c f) = |c| osc_B f`.
@isnad1 id=eq.0h3v.s4.f690bf4b1e91 from=translated src=- shape=ffce8661 vocab=d64b05e2
-/
lemma osc_neg (B : Set α) (g : α → ℝ) : osc B (fun y => -g y) = osc B g := by
  have h : (fun y => -g y) = fun y => -1 * g y := funext fun y => (neg_one_mul (g y)).symm
  rw [h, osc_const_mul, abs_neg, abs_one, one_mul]

/-- The triangle inequality for finite sums.
@isnad1 id=le.2h5v.s6.a25ccbb651e7 from=translated src=- shape=4eb89c53 vocab=3d317c20
-/
lemma osc_sum_le {ι : Type*} (s : Finset ι) {B : Set α} {f : ι → α → ℝ} (hB : B.Nonempty)
    (hf : ∀ k ∈ s, ((f k) '' B).Finite) :
    osc B (fun y => ∑ k ∈ s, f k y) ≤ ∑ k ∈ s, osc B (f k) :=
  osc_le hB fun y hy y' hy' => by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun k hk => sub_le_osc (hf k hk) hy hy'

/-- "By the triangle inequality for the oscillation,
`Σ_k osc_J a_k ≥ osc_J (Σ_k a_k) = b osc_J ā`": `b` times the oscillation of the average of
`b` functions is at most the sum of their oscillations.
@isnad1 id=le.2h4v.s6.293608514a6c from=translated src=- shape=87a5786e vocab=344806b7
-/
lemma card_mul_osc_avg_le {ι : Type*} [Fintype ι] [Nonempty ι] {B : Set α} {f : ι → α → ℝ}
    (hB : B.Nonempty) (hf : ∀ k, ((f k) '' B).Finite) :
    (Fintype.card ι : ℝ) * osc B (fun y => (∑ k, f k y) / Fintype.card ι) ≤
      ∑ k, osc B (f k) := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  -- `Σ_k f_k` is `b` times the average, and `osc_B (b f) = b osc_B f`
  have hsum : (fun y => ∑ k, f k y) =
      fun y => (Fintype.card ι : ℝ) * ((∑ k, f k y) / Fintype.card ι) := by
    funext y
    field_simp
  calc (Fintype.card ι : ℝ) * osc B (fun y => (∑ k, f k y) / Fintype.card ι)
      = osc B (fun y => (Fintype.card ι : ℝ) * ((∑ k, f k y) / Fintype.card ι)) := by
        rw [osc_const_mul, abs_of_pos hc]
    _ = osc B (fun y => ∑ k, f k y) := by rw [← hsum]
    _ ≤ ∑ k, osc B (f k) := osc_sum_le Finset.univ hB fun k _ => hf k

/-! ### Blocks -/

/-- The block `B_{ℓ+1} = [s + ℓ L, s + (ℓ+1) L)` of the vertical interval
`J = [s, s + b L)`: closed at the bottom, open at the top. Blocks are numbered from `0` here
and from `1` in the manuscript.-/
def block (s L : ℝ) (ℓ : ℕ) : Set ℝ := Set.Ico (s + ℓ * L) (s + (ℓ + 1) * L)

/--
@isnad1 id=nonempty.1h3v.s4.b9ac1d37e5b1 from=translated src=- shape=3c8ae4b1 vocab=19012c4c
-/
lemma block_nonempty (s : ℝ) {L : ℝ} (hL : 0 < L) (ℓ : ℕ) : (block s L ℓ).Nonempty :=
  ⟨s + ℓ * L, ⟨le_rfl, by nlinarith⟩⟩

/--
@isnad1 id=le.2h4v.s5.623d105a558e from=translated src=- shape=2b43658b vocab=71bfbb07
-/
lemma block_subset (s : ℝ) {L : ℝ} (hL : 0 < L) {b ℓ : ℕ} (hℓ : ℓ < b) :
    block s L ℓ ⊆ Set.Ico s (s + b * L) := by
  rintro y ⟨h1, h2⟩
  have h0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have hb : (ℓ : ℝ) + 1 ≤ b := by exact_mod_cast hℓ
  constructor
  · nlinarith
  · nlinarith

/-- The blocks partition `J`.
@isnad1 id=eq.1h3v.s5.bc0feeac6bb1 from=translated src=- shape=d6a1304b vocab=bfb8921b
-/
lemma iUnion_block (s : ℝ) {L : ℝ} (hL : 0 < L) (b : ℕ) :
    ⋃ ℓ : Fin b, block s L ℓ = Set.Ico s (s + b * L) := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun ℓ => block_subset s hL ℓ.isLt
  · rintro y ⟨h1, h2⟩
    have hq : 0 ≤ (y - s) / L := div_nonneg (by linarith) hL.le
    have hlt : (y - s) / L < b := (div_lt_iff₀ hL).mpr (by linarith)
    have hfl : ⌊(y - s) / L⌋₊ < b := (Nat.floor_lt hq).mpr hlt
    refine Set.mem_iUnion.mpr ⟨⟨⌊(y - s) / L⌋₊, hfl⟩, ?_⟩
    have hle : (⌊(y - s) / L⌋₊ : ℝ) ≤ (y - s) / L := Nat.floor_le hq
    have hlt' : (y - s) / L < ⌊(y - s) / L⌋₊ + 1 := Nat.lt_floor_add_one _
    constructor
    · have := (le_div_iff₀ hL).mp hle
      change s + (⌊(y - s) / L⌋₊ : ℝ) * L ≤ y
      linarith
    · have := (div_lt_iff₀ hL).mp hlt'
      change y < s + ((⌊(y - s) / L⌋₊ : ℝ) + 1) * L
      linarith

/--
@isnad1 id=disjoint.2h4v.s6.abcdebb2d20a from=translated src=- shape=328115bb vocab=064f5656
-/
lemma block_disjoint (s : ℝ) {L : ℝ} (hL : 0 < L) {ℓ ℓ' : ℕ} (h : ℓ ≠ ℓ') :
    Disjoint (block s L ℓ) (block s L ℓ') := by
  wlog hlt : ℓ < ℓ' generalizing ℓ ℓ'
  · exact (this h.symm (lt_of_le_of_ne (not_lt.mp hlt) h.symm)).symm
  rw [Set.disjoint_left]
  rintro y ⟨-, h2⟩ ⟨h3, -⟩
  have : (ℓ : ℝ) + 1 ≤ ℓ' := by exact_mod_cast hlt
  nlinarith

/-- `B_2 ∪ ⋯ ∪ B_{b-1}`, the union of the inner blocks (indices `1, …, b-2` here), is the
interval `[s + L, s + (b-1) L)`. The inner region of the manuscript is
`R^in = I × (B_2 ∪ ⋯ ∪ B_{b-1})`; it "is `R` without its bottom and top strips".
@isnad1 id=eq.2h3v.s7.5eafba7ea438 from=translated src=- shape=1c746690 vocab=98a57e00
-/
theorem iUnion_inner_blocks (s : ℝ) {L : ℝ} (hL : 0 < L) {b : ℕ} (hb : 2 ≤ b) :
    ⋃ ℓ ∈ Finset.Ico 1 (b - 1), block s L ℓ = Set.Ico (s + L) (s + ((b : ℝ) - 1) * L) := by
  apply Set.Subset.antisymm
  · -- the blocks `B_2, …, B_{b-1}` lie in `[s + L, s + (b-1) L)`
    refine Set.iUnion₂_subset fun ℓ hℓ => ?_
    rw [Finset.mem_Ico] at hℓ
    rintro y ⟨h1, h2⟩
    have h1' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.1
    have h2' : (ℓ : ℝ) + 1 ≤ (b : ℝ) - 1 := by
      have h : ℓ + 1 + 1 ≤ b := by omega
      have h' : ((ℓ + 1 + 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast h
      push_cast at h'
      linarith
    constructor <;> nlinarith
  · -- a height in `[s + L, s + (b-1) L)` lies in one of the blocks of `J`, and this block
    -- is neither `B_1` nor `B_b`
    rintro y ⟨h1, h2⟩
    have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
    have hy : y ∈ Set.Ico s (s + b * L) := ⟨by linarith, by nlinarith⟩
    rw [← iUnion_block s hL b] at hy
    obtain ⟨ℓ, hℓ1, hℓ2⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion₂.mpr ⟨ℓ, Finset.mem_Ico.mpr ⟨?_, ?_⟩, hℓ1, hℓ2⟩
    · -- it is not the bottom block `B_1 = [s, s + L)`
      by_contra h0
      have h0' : (ℓ : ℕ) = 0 := by omega
      rw [h0'] at hℓ2
      simp only [Nat.cast_zero, zero_add, one_mul] at hℓ2
      linarith
    · -- it is not the top block `B_b = [s + (b-1) L, s + b L)`
      by_contra hlast
      have hlast' : (b : ℝ) - 1 ≤ (ℓ : ℕ) := by
        have h : b ≤ (ℓ : ℕ) + 1 := by omega
        have h' : (b : ℝ) ≤ ((ℓ : ℕ) : ℝ) + 1 := by exact_mod_cast h
        linarith
      nlinarith

/-- "It is `R` without its bottom and top strips, and it is not empty because `b ≥ 3`": the
set `B_2 ∪ ⋯ ∪ B_{b-1} = [s + L, s + (b-1) L)` of the heights of the inner region is not
empty.
@isnad1 id=nonempty.2h3v.s6.86f0a4351b78 from=translated src=- shape=ad5ebdb8 vocab=0d2f258d
-/
theorem inner_blocks_nonempty (s : ℝ) {L : ℝ} (hL : 0 < L) {b : ℕ} (hb : 3 ≤ b) :
    (Set.Ico (s + L) (s + ((b : ℝ) - 1) * L)).Nonempty := by
  have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
  exact Set.nonempty_Ico.mpr (by nlinarith)

/-! ### Lemma 2.1 -/

/-- "Also `osc_J f ≥ osc_{B_ℓ} f` for each of the remaining `b-2` blocks `B_ℓ`": the oscillation
on a nonempty subset `A` of `J` is at most the oscillation on `J`.
@isnad1 id=le.3h4v.s5.3db968067db7 from=translated src=- shape=3d44b86c vocab=1059cec2
-/
lemma osc_mono {A J : Set α} {f : α → ℝ} (hA : A.Nonempty) (hAJ : A ⊆ J)
    (hf : (f '' J).Finite) : osc A f ≤ osc J f := by
  -- the extrema of `f` on `A` lie between its extrema on `J`
  have h1 := maxOn_mono hA hAJ hf
  have h2 := minOn_anti hA hAJ hf
  unfold osc
  linarith

/-- The inequality in the first display of the proof of Lemma 2.1, for two nonempty subsets
`A` (the bottom block `B_1`) and `C` (the top block `B_b`) of `J`: "Since `J` contains `B_1`
and `B_b`, \[…\] `osc_J f ≥ max_{B_b} f - min_{B_1} f`". With `A` and `C` exchanged, it is the
inequality "`osc_J f ≥ max_{B_1} f - min_{B_b} f`" of the second line.
@isnad1 id=le.5h5v.s6.83dc77a2c6e8 from=translated src=- shape=f0c2f0e1 vocab=b08e5c6b
-/
lemma maxOn_sub_minOn_le_osc {A C J : Set α} {f : α → ℝ} (hA : A.Nonempty) (hC : C.Nonempty)
    (hAJ : A ⊆ J) (hCJ : C ⊆ J) (hf : (f '' J).Finite) : maxOn C f - minOn A f ≤ osc J f := by
  -- the maximum on `C` is at most the maximum on `J`, and the minimum on `A` is at least the
  -- minimum on `J`
  have h1 := maxOn_mono hC hCJ hf
  have h2 := minOn_anti hA hAJ hf
  unfold osc
  linarith

/-- The equality in the first display of the proof of Lemma 2.1, for two sets `A` (the bottom
block `B_1`) and `C` (the top block `B_b`): since "the extrema of `f` on a block `B` are
`mid_B f ± ½ osc_B f`",
"`max_{B_b} f - min_{B_1} f = (osc_{B_1} f + osc_{B_b} f)/2 + (mid_{B_b} f - mid_{B_1} f)`".
With `A` and `C` exchanged, it is the equality of the second line of that display: its
right-hand side `(osc_{B_b} f + osc_{B_1} f)/2 + (mid_{B_1} f - mid_{B_b} f)` is the
manuscript's `(osc_{B_1} f + osc_{B_b} f)/2 - (mid_{B_b} f - mid_{B_1} f)`.
@isnad1 id=eq.0h4v.s6.bcae7474e9c6 from=translated src=- shape=823a870c vocab=4d4f2a3a
-/
lemma maxOn_sub_minOn_eq (A C : Set α) (f : α → ℝ) :
    maxOn C f - minOn A f = (osc A f + osc C f) / 2 + (mid C f - mid A f) := by
  -- `max_C f = mid_C f + ½ osc_C f` and `min_A f = mid_A f - ½ osc_A f`
  rw [maxOn_eq_mid_add C f, minOn_eq_mid_sub A f]
  ring

/-- The first part of the proof of Lemma 2.1, for two nonempty subsets `A` (the bottom block
`B_1`) and `C` (the top block `B_b`) of `J`:
"`osc_J f ≥ (osc_{B_1} f + osc_{B_b} f)/2 + |mid_{B_b} f - mid_{B_1} f|`".
@isnad1 id=le.5h5v.s6.4f859083a877 from=translated src=- shape=8315b678 vocab=b23bfd26
-/
theorem half_osc_add_abs_mid_sub_le {A C J : Set α} {f : α → ℝ} (hA : A.Nonempty)
    (hC : C.Nonempty) (hAJ : A ⊆ J) (hCJ : C ⊆ J) (hf : (f '' J).Finite) :
    (osc A f + osc C f) / 2 + |mid C f - mid A f| ≤ osc J f := by
  -- the first line of the first display, `osc_J f ≥ max_{B_b} f - min_{B_1} f`
  -- `= (osc_{B_1} f + osc_{B_b} f)/2 + (mid_{B_b} f - mid_{B_1} f)`
  have h1 : (osc A f + osc C f) / 2 + (mid C f - mid A f) ≤ osc J f :=
    (maxOn_sub_minOn_eq A C f).symm.trans_le (maxOn_sub_minOn_le_osc hA hC hAJ hCJ hf)
  -- the second line, `osc_J f ≥ max_{B_1} f - min_{B_b} f`
  -- `= (osc_{B_1} f + osc_{B_b} f)/2 - (mid_{B_b} f - mid_{B_1} f)`: the two blocks exchanged
  have h2 : (osc A f + osc C f) / 2 - (mid C f - mid A f) ≤ osc J f := by
    have h := (maxOn_sub_minOn_eq C A f).symm.trans_le
      (maxOn_sub_minOn_le_osc hC hA hCJ hAJ hf)
    linarith
  -- "Taking the larger of the two right-hand sides"
  rcases le_total 0 (mid C f - mid A f) with H | H
  · rw [abs_of_nonneg H]
    exact h1
  · rw [abs_of_nonpos H]
    linarith

/-- **Lemma 2.1** for arbitrary nonempty subsets `B_1, …, B_b` of a set `J` in place of the
blocks of an interval: if `f` has finitely many values on `J`, then

`b · osc_J f ≥ Σ_ℓ osc_{B_ℓ} f + 2 |mid_{B_b} f - mid_{B_1} f|`.

The proof of the manuscript uses nothing else about the blocks.
@isnad1 id=le.4h5v.s7.9198fb1799a2 from=translated src=- shape=3913cbb4 vocab=a499c65c
-/
theorem vertical_comparison_sets {b : ℕ} (hb : 2 ≤ b) (J : Set α) (B : Fin b → Set α)
    (hne : ∀ ℓ, (B ℓ).Nonempty) (hsub : ∀ ℓ, B ℓ ⊆ J) (f : α → ℝ) (hf : (f '' J).Finite) :
    ∑ ℓ : Fin b, osc (B ℓ) f +
        2 * |mid (B ⟨b - 1, by omega⟩) f - mid (B ⟨0, by omega⟩) f| ≤ b * osc J f := by
  classical
  -- the bottom block and the top block are different blocks
  have hfirst : (⟨0, by omega⟩ : Fin b) ≠ ⟨b - 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  -- "`osc_J f ≥ (osc_{B_1} f + osc_{B_b} f)/2 + |mid_{B_b} f - mid_{B_1} f|`"
  have h2 := half_osc_add_abs_mid_sub_le (hne (⟨0, by omega⟩ : Fin b))
    (hne (⟨b - 1, by omega⟩ : Fin b)) (hsub _) (hsub _) hf
  -- "Also `osc_J f ≥ osc_{B_ℓ} f` for each of the remaining `b-2` blocks `B_ℓ`."
  have h1 : ∀ ℓ, osc (B ℓ) f ≤ osc J f := fun ℓ => osc_mono (hne ℓ) (hsub ℓ) hf
  have hrest : ∑ ℓ ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin b)).erase ⟨b - 1, by omega⟩,
      osc (B ℓ) f ≤ ((b : ℝ) - 2) * osc J f := by
    calc ∑ ℓ ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin b)).erase ⟨b - 1, by omega⟩, osc (B ℓ) f
        ≤ ∑ _ℓ ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin b)).erase ⟨b - 1, by omega⟩, osc J f :=
          Finset.sum_le_sum fun ℓ _ => h1 ℓ
      _ = ((b : ℝ) - 2) * osc J f := by
          rw [Finset.sum_const, Finset.card_erase_of_mem
            (Finset.mem_erase.mpr ⟨hfirst.symm, Finset.mem_univ _⟩),
            Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          have : ((b - 1 - 1 : ℕ) : ℝ) = (b : ℝ) - 2 := by
            rw [Nat.sub_sub, Nat.cast_sub hb]
            norm_num
          rw [this]
  -- "Adding these `b-2` inequalities and twice the last display proves (4)."
  have e1 := Finset.add_sum_erase Finset.univ (fun ℓ : Fin b => osc (B ℓ) f)
    (Finset.mem_univ (⟨0, by omega⟩ : Fin b))
  have e2 := Finset.add_sum_erase (Finset.univ.erase (⟨0, by omega⟩ : Fin b))
    (fun ℓ : Fin b => osc (B ℓ) f) (Finset.mem_erase.mpr ⟨hfirst.symm, Finset.mem_univ _⟩)
  linarith

/-- **Lemma 2.1 (vertical comparison)**, display (4). Partition `J = [s, s + b L)` into
blocks `B_1, …, B_b` of equal length `L`, from bottom to top, and let `f` be a function on
`J` with finitely many values. Then

`b · osc_J f ≥ Σ_{ℓ=1}^{b} osc_{B_ℓ} f + 2 |mid_{B_b} f - mid_{B_1} f|`.

Only `b ≥ 2` is used (the manuscript has `b ≥ 3` throughout).
@isnad1 id=le.3h4v.s7.51f18a9fa97d from=translated src=- shape=88b474d5 vocab=c5d1769a
-/
theorem vertical_comparison {b : ℕ} (hb : 2 ≤ b) (s : ℝ) {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ)
    (hf : (f '' Set.Ico s (s + b * L)).Finite) :
    ∑ ℓ : Fin b, osc (block s L ℓ) f +
        2 * |mid (block s L (b - 1)) f - mid (block s L 0) f| ≤
      b * osc (Set.Ico s (s + b * L)) f :=
  vertical_comparison_sets hb (Set.Ico s (s + b * L)) (fun ℓ : Fin b => block s L ℓ)
    (fun ℓ => block_nonempty s hL ℓ) (fun ℓ => block_subset s hL ℓ.isLt) f hf

end

end R56Audit
