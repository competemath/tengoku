import Tengoku.CollatzGeneralizedNaturalDensity.GGMCollatz.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The assembly of (A), part 1: probabilistic tools

Basic identities and inequalities for expectations of indicator functions, with respect to
`Family.expect` and `Family.dTV` of the statement (tao-collatz's conventions).

* `expect_indicator`: `E[1_E] = μ(E)` (the real value of the outer measure).
* `expect_map_indicator`: the expectation under a pushforward law is the expectation of the preimage.
* `abs_expect_indicator_sub_le_dTV`: the difference of the probabilities of an event is at most the
  total variation.

The proof of `abs_expect_indicator_sub_le_dTV` is derived from the theorem of the same name in
`TaoCollatz/Prob/Basic.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2, rewritten for
`Family.expect` and `Family.dTV` of the statement.
-/

namespace GGMCollatz

namespace Asm

variable {α : Type*}

/-- The expectation of an indicator function is the real value of the outer measure.
@isnad1 id=eq.0h3v.s5.c581ac0da478 from=translated src=- shape=8c303da7 vocab=99bc3fbf
-/
theorem expect_indicator (μ : PMF α) (E : Set α) :
    Family.expect μ (E.indicator 1) = (μ.toOuterMeasure E).toReal := by
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq]
  · unfold Family.expect
    refine tsum_congr fun a => ?_
    by_cases h : a ∈ E <;> simp [h]
  · intro a
    by_cases h : a ∈ E <;> simp [h, PMF.apply_ne_top]

/--
@isnad1 id=ne.0h3v.s4.3594b91d4056 from=translated src=- shape=5f260609 vocab=c2ded12e
-/
theorem toOuterMeasure_ne_top (μ : PMF α) (E : Set α) : μ.toOuterMeasure E ≠ ⊤ := by
  rw [PMF.toOuterMeasure_apply]; exact μ.tsum_coe_indicator_ne_top E

/--
@isnad1 id=le.0h3v.s5.219425d2c9e5 from=translated src=- shape=878d82d4 vocab=8b7e78b1
-/
theorem toOuterMeasure_le_one (μ : PMF α) (E : Set α) : μ.toOuterMeasure E ≤ 1 := by
  rw [PMF.toOuterMeasure_apply, ← μ.tsum_coe]
  exact ENNReal.tsum_le_tsum fun a => Set.indicator_le_self E μ a

/--
@isnad1 id=le.0h3v.s5.65b4f7ad2048 from=translated src=- shape=9fb3c0d4 vocab=55a29bd2
-/
theorem expect_indicator_nonneg (μ : PMF α) (E : Set α) :
    0 ≤ Family.expect μ (E.indicator 1) := by
  rw [expect_indicator]; exact ENNReal.toReal_nonneg

/--
@isnad1 id=le.0h3v.s5.c66b18958468 from=translated src=- shape=a7a884a8 vocab=55a29bd2
-/
theorem expect_indicator_le_one (μ : PMF α) (E : Set α) :
    Family.expect μ (E.indicator 1) ≤ 1 := by
  rw [expect_indicator]
  have h := toOuterMeasure_le_one μ E
  have := ENNReal.toReal_mono ENNReal.one_ne_top h
  simpa using this

/-- The probabilities of two disjoint events add.
@isnad1 id=eq.1h4v.s7.abd40d28ad10 from=translated src=- shape=80316206 vocab=83579eb2
-/
theorem expect_indicator_union (μ : PMF α) {E G : Set α} (h : Disjoint E G) :
    Family.expect μ ((E ∪ G).indicator 1) =
      Family.expect μ (E.indicator 1) + Family.expect μ (G.indicator 1) := by
  rw [expect_indicator, expect_indicator, expect_indicator, ← ENNReal.toReal_add
    (toOuterMeasure_ne_top μ E) (toOuterMeasure_ne_top μ G)]
  congr 1
  simp only [PMF.toOuterMeasure_apply]
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun a => ?_
  rw [Set.indicator_union_of_disjoint h]

/-- Monotonicity.
@isnad1 id=le.1h4v.s6.e86a8e62e2ab from=translated src=- shape=5ab07be8 vocab=55a29bd2
-/
theorem expect_indicator_mono (μ : PMF α) {E G : Set α} (h : E ⊆ G) :
    Family.expect μ (E.indicator 1) ≤ Family.expect μ (G.indicator 1) := by
  rw [expect_indicator, expect_indicator]
  exact ENNReal.toReal_mono (toOuterMeasure_ne_top μ G) (μ.toOuterMeasure.mono h)

/-- The expectation under a pushforward law is the expectation of the preimage.
@isnad1 id=eq.0h5v.s6.81250148fd7e from=translated src=- shape=049ce50b vocab=f8dd3c59
-/
theorem expect_map_indicator {β : Type*} (μ : PMF α) (φ : α → β) (E : Set β) :
    Family.expect (μ.map φ) (E.indicator 1) = Family.expect μ ((φ ⁻¹' E).indicator 1) := by
  rw [expect_indicator, expect_indicator, PMF.toOuterMeasure_map_apply]

open Classical in
/-- Point-mass distribution.
@isnad1 id=eq.0h3v.s6.31a6d5f97627 from=translated src=- shape=2edeed98 vocab=0b110733
-/
theorem expect_pure_indicator (a : α) (E : Set α) :
    Family.expect (PMF.pure a) (E.indicator 1) = if a ∈ E then 1 else 0 := by
  rw [expect_indicator, PMF.toOuterMeasure_pure_apply]
  split_ifs <;> simp

/-- The difference of the probabilities of an event is at most the total variation (derived from
tao-collatz's `abs_expect_indicator_sub_le_dTV`).
@isnad1 id=le.0h4v.s6.f7c756ca6921 from=translated src=- shape=06dadadc vocab=f4966b1d
-/
theorem abs_expect_indicator_sub_le_dTV (p q : PMF α) (E : Set α) :
    |Family.expect p (E.indicator 1) - Family.expect q (E.indicator 1)| ≤ Family.dTV p q := by
  have hp : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)
  have hq : Summable fun a => (q a).toReal :=
    ENNReal.summable_toReal (by rw [q.tsum_coe]; exact ENNReal.one_ne_top)
  have hnn : ∀ (r : PMF α) (a : α), 0 ≤ (r a).toReal * Set.indicator E 1 a := fun r a =>
    mul_nonneg ENNReal.toReal_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) a)
  have hle : ∀ (r : PMF α) (a : α), (r a).toReal * Set.indicator E 1 a ≤ (r a).toReal := by
    intro r a
    by_cases h : a ∈ E
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h, ENNReal.toReal_nonneg]
  have hpE : Summable fun a => (p a).toReal * Set.indicator E 1 a :=
    Summable.of_nonneg_of_le (hnn p) (hle p) hp
  have hqE : Summable fun a => (q a).toReal * Set.indicator E 1 a :=
    Summable.of_nonneg_of_le (hnn q) (hle q) hq
  have hkey : ∀ a,
      |(p a).toReal * Set.indicator E 1 a - (q a).toReal * Set.indicator E 1 a|
        ≤ |(p a).toReal - (q a).toReal| := by
    intro a
    rw [← sub_mul, abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    by_cases h : a ∈ E
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  unfold Family.expect Family.dTV
  rw [← hpE.tsum_sub hqE]
  calc |∑' a, ((p a).toReal * Set.indicator E 1 a - (q a).toReal * Set.indicator E 1 a)|
      ≤ ∑' a, |(p a).toReal * Set.indicator E 1 a - (q a).toReal * Set.indicator E 1 a| := by
        have h := norm_tsum_le_tsum_norm
          (f := fun a => (p a).toReal * Set.indicator E 1 a
            - (q a).toReal * Set.indicator E 1 a)
          (by simpa only [Real.norm_eq_abs] using (hpE.sub hqE).abs)
        simpa only [Real.norm_eq_abs] using h
    _ ≤ ∑' a, |(p a).toReal - (q a).toReal| :=
        ((hpE.sub hqE).abs).tsum_le_tsum hkey ((hp.sub hq).abs)

end Asm

end GGMCollatz
