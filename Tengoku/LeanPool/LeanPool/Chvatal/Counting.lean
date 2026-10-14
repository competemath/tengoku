/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Tengoku.LeanPool.LeanPool.Chvatal.Family
public import Tengoku.LeanPool.LeanPool.Chvatal.Boolean

public import Tengoku

/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# The counting reduction in Section 4

The indicator-function identities in this file translate between set families
and the cube's uniform probability measure. They are the elementary counting
steps in Section 4 of arXiv:2609.19123.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Chvatal
namespace Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real-valued indicator `𝟙_B` of a family, used in Section 4. -/
def indicator (B : Family ι) (x : Finset ι) : ℝ := if x ∈ B then 1 else 0

omit [Fintype ι] in
/-- Evaluating the Section 4 indicator at a member of its family.
@isnad1 id=eq.1h3v.s5.6b12e759fc35 from=translated src=- shape=3f7a55bd vocab=6d1c244e
-/
@[simp] theorem indicator_of_mem {B : Family ι} {x : Finset ι} (hx : x ∈ B) :
    B.indicator x = 1 := by simp [indicator, hx]

omit [Fintype ι] in
/-- Evaluating the Section 4 indicator outside its family.
@isnad1 id=eq.1h3v.s5.05b561bb6b70 from=translated src=- shape=6956a64e vocab=6d1c244e
-/
@[simp] theorem indicator_of_not_mem {B : Family ι} {x : Finset ι} (hx : x ∉ B) :
    B.indicator x = 0 := by simp [indicator, hx]

/-- The expectation of a family indicator is its density in the Boolean cube,
the normalization used in both counting formulas in Section 4.
@isnad1 id=eq.0h2v.s5.5b6badda5d63 from=translated src=- shape=3f93083e vocab=39bb4c53
-/
theorem cubeMean_indicator (B : Family ι) :
    cubeMean B.indicator = B.card / (Fintype.card (Finset ι) : ℝ) := by
  simp [cubeMean, indicator]

omit [Fintype ι] in
/-- The pointwise product of two family indicators counts their intersection,
as used in the covariance calculation in Section 4.
@isnad1 id=eq.0h3v.s5.ce45b4a913dd from=translated src=- shape=0f773955 vocab=07ba1d06
-/
theorem indicator_inter (D B : Family ι) :
    (D ∩ B).indicator = fun x => D.indicator x * B.indicator x := by
  funext x
  by_cases hD : x ∈ D <;> by_cases hB : x ∈ B <;> simp [indicator, hD, hB]

/-- Complementing family membership gives the function `1 - 𝟙_D` of Section 4.
@isnad1 id=eq.0h2v.s6.4e77c31939af from=translated src=- shape=00e17072 vocab=0841e74c
-/
theorem indicator_compl (D : Family ι) :
    Dᶜ.indicator = fun x => 1 - D.indicator x := by
  funext x
  by_cases hx : x ∈ D <;> simp [indicator, hx]

omit [Fintype ι] in
/-- An increasing family has an increasing indicator, as used for `g = 𝟙_B`
in Section 4.
@isnad1 id=monotone.1h2v.s4.7d701dd2dd8a from=translated src=- shape=02f8a7ba vocab=fff8754a
-/
theorem IsIncreasing.monotone_indicator {B : Family ι} (hB : B.IsIncreasing) :
    Monotone B.indicator := by
  intro x y hxy
  by_cases hx : x ∈ B
  · have hy : y ∈ B := hB hxy hx
    simp [indicator, hx, hy]
  · simp only [indicator, ite_eq_right hx]
    split_ifs <;> norm_num

omit [Fintype ι] in
/-- For a hereditary family, the function `f = 1 - 𝟙_D` in Section 4 is
increasing.
@isnad1 id=monotone.1h2v.s5.0abb0965aece from=translated src=- shape=97f6c7f2 vocab=b56ae442
-/
theorem IsHereditary.monotone_one_sub_indicator {D : Family ι}
    (hD : D.IsHereditary) : Monotone (fun x => 1 - D.indicator x) := by
  intro x y hxy
  by_cases hy : y ∈ D
  · have hx : x ∈ D := hD hxy hy
    simp [indicator, hx, hy]
  · by_cases hx : x ∈ D <;> simp [indicator, hx, hy]

/-- The indicator of an antipodal family is self-dual, giving the antipodality
hypothesis for `g` in the application of Corollary 1.3.
@isnad1 id=eq.1h2v.s5.587f934e18b3 from=translated src=- shape=7bca363b vocab=3f3b747d
-/
theorem IsAntipodal.dual_indicator {B : Family ι} (hB : B.IsAntipodal) :
    Chvatal.dual B.indicator = B.indicator := by
  funext x
  by_cases hx : x ∈ B
  · simp [Chvatal.dual, indicator, hx, (hB x).mp hx]
  · have hxc : xᶜ ∈ B := by
      by_contra hxc
      exact hx ((hB x).mpr hxc)
    simp [Chvatal.dual, indicator, hx, hxc]

/-- Family duality and Boolean-function duality agree under indicators, as
used when translating the families in Sections 3 and 4.
@isnad1 id=eq.0h2v.s5.d9cb2c13b9c0 from=translated src=- shape=fedf3d09 vocab=10241908
-/
theorem indicator_dual (B : Family ι) :
    B.dual.indicator = Chvatal.dual B.indicator := by
  funext x
  by_cases hx : xᶜ ∈ B <;> simp [indicator, Chvatal.dual, hx]

/-- An antipodal family has uniform density one half, the input to Section 4's
covariance calculation.
@isnad1 id=eq.1h2v.s5.4b1ac95c03e3 from=translated src=- shape=e3ef45cf vocab=5b0d1f6e
-/
theorem IsAntipodal.cubeMean_indicator {B : Family ι} (hB : B.IsAntipodal) :
    cubeMean B.indicator = 1 / 2 := by
  have hmean := cubeMean_dual B.indicator
  rw [hB.dual_indicator] at hmean
  linarith

/-- The first counting identity in Section 4: for `f = 1 - 𝟙_D` and
`g = 𝟙_B`, with `B` antipodal, covariance is
`(|D| / 2 - |D ∩ B|) / 2^n`. Heredity is unnecessary for this identity.
@isnad1 id=eq.1h3v.s6.e3dadc62c6bc from=translated src=- shape=fc5403b2 vocab=b7659ce8
-/
theorem covariance_one_sub_indicator {D B : Family ι} (hB : B.IsAntipodal) :
    covariance (fun x => 1 - D.indicator x) B.indicator =
      ((D.card : ℝ) / 2 - (D ∩ B).card) / Fintype.card (Finset ι) := by
  have hprod : (fun x => (1 - D.indicator x) * B.indicator x) =
      fun x => B.indicator x - (D ∩ B).indicator x := by
    rw [indicator_inter]
    funext x
    ring
  rw [covariance, hprod, cubeMean_sub, cubeMean_sub, cubeMean_const,
    hB.cubeMean_indicator, cubeMean_indicator, cubeMean_indicator]
  ring

/-- The converse indicator bridge in Section 4: a self-dual family indicator
comes from an antipodal family.
@isnad1 id=iff.0h2v.s5.dc9d146d3b87 from=translated src=- shape=2cb4dc84 vocab=3f3b747d
-/
theorem isAntipodal_iff_dual_indicator (B : Family ι) :
    B.IsAntipodal ↔ Chvatal.dual B.indicator = B.indicator := by
  refine ⟨IsAntipodal.dual_indicator, ?_⟩
  intro h x
  have hx := congrFun h x
  by_cases hmem : x ∈ B <;> by_cases hcomp : xᶜ ∈ B <;>
    simp_all [Chvatal.dual, indicator]

/-- The support of the value one, used in Section 4 to pass from increasing
Boolean functions back to set families. -/
def oneSupport (f : Finset ι → ℝ) : Family ι := by
  classical
  exact Finset.univ.filter (fun x => f x = 1)

omit [DecidableEq ι] in
/-- Membership in the support used in Section 4's converse implication.
@isnad1 id=iff.0h3v.s5.32cd4d018cc8 from=translated src=- shape=8e85c9e3 vocab=841e72c0
-/
@[simp] theorem mem_oneSupport {f : Finset ι → ℝ} {x : Finset ι} :
    x ∈ oneSupport f ↔ f x = 1 := by
  classical
  simp [oneSupport]

/-- Taking the indicator of a Boolean function's support recovers the function,
as required in Section 4's converse construction.
@isnad1 id=eq.1h2v.s5.72a14f0c6da4 from=translated src=- shape=d4e25955 vocab=1b05568e
-/
theorem indicator_oneSupport {f : Finset ι → ℝ}
    (hf : ∀ x, f x = 0 ∨ f x = 1) : (oneSupport f).indicator = f := by
  funext x
  rcases hf x with hx | hx <;> simp [indicator, hx]

omit [DecidableEq ι] in
/-- The support of an increasing Boolean function is an increasing family,
the first family construction in Section 4's converse.
@isnad1 id=isincrea.2h2v.s5.027de10ff665 from=translated src=- shape=9a9dbbbd vocab=820194df
-/
theorem isIncreasing_oneSupport {f : Finset ι → ℝ}
    (hf : ∀ x, f x = 0 ∨ f x = 1) (hm : Monotone f) :
    (oneSupport f).IsIncreasing := by
  intro x y hxy hx
  have hx' : f x = 1 := mem_oneSupport.mp hx
  rcases hf y with hy | hy
  · have := hm hxy
    rw [hx', hy] at this
    norm_num at this
  · exact mem_oneSupport.mpr hy

/-- The complement of an increasing family is hereditary, used for
`D = supp (1 - f)` in Section 4's converse.
@isnad1 id=isheredi.1h2v.s5.af02c3864d42 from=translated src=- shape=42071d83 vocab=1ec07109
-/
theorem IsIncreasing.isHereditary_compl {B : Family ι} (hB : B.IsIncreasing) :
    Bᶜ.IsHereditary := by
  intro x y hxy hy
  simp only [Finset.mem_coe, Finset.mem_compl] at hy ⊢
  exact fun hx => hy (hB hxy hx)

omit [Fintype ι] in
/-- A family indicator is Boolean-valued, as required when invoking
Corollary 1.3 in Section 4.
@isnad1 id=isboolea.0h2v.s3.dd0bb7445ed3 from=translated src=- shape=ed10201d vocab=80bf6d17
-/
theorem isBoolean_indicator (B : Family ι) : IsBoolean B.indicator := by
  intro x
  by_cases hx : x ∈ B <;> simp [indicator, hx]

omit [Fintype ι] in
/-- The complement indicator `1 - 𝟙_D` used in Section 4 is Boolean-valued.
@isnad1 id=isboolea.0h2v.s4.321abfd2e1f2 from=translated src=- shape=d394592b vocab=3637a404
-/
theorem isBoolean_one_sub_indicator (D : Family ι) :
    IsBoolean (fun x => 1 - D.indicator x) := by
  intro x
  by_cases hx : x ∈ D <;> simp [indicator, hx]

/-- Each coordinate sign has uniform mean zero, the cancellation used to count
influences in Section 4.
@isnad1 id=eq.0h2v.s4.954ec3e5462f from=translated src=- shape=6cdb3b85 vocab=7f08cdcd
-/
theorem cubeMean_coordinateSign (i : ι) : cubeMean (coordinateSign i) = 0 := by
  have heq : coordinateSign i = fun x => -walsh {i} x := by
    funext x
    rw [walsh_singleton]
    by_cases hx : i ∈ x <;> simp [coordinateSign, hx]
  rw [heq, cubeMean_neg, cubeMean_walsh_of_nonempty (Finset.singleton_nonempty i), neg_zero]

/-- The second counting identity in Section 4: the influence of `1 - 𝟙_D`
is twice the number of boundary edges in coordinate `i`, divided by `2^n`.
The numerator is `|D| - 2 |D_i|`.
@isnad1 id=eq.1h3v.s6.0b2d74448a8d from=translated src=- shape=99ff7cce vocab=23ab115f
-/
theorem influence_one_sub_indicator {D : Family ι} (hD : D.IsHereditary) (i : ι) :
    influence (fun x => 1 - D.indicator x) i =
      2 * ((D.card : ℝ) - 2 * (D.star i).card) / Fintype.card (Finset ι) := by
  rw [influence_eq_signed_mean (isBoolean_one_sub_indicator D)
    hD.monotone_one_sub_indicator]
  have heq : (fun x => coordinateSign i x * (1 - D.indicator x)) =
      fun x => coordinateSign i x - (2 * (D.star i).indicator x - D.indicator x) := by
    funext x
    by_cases hmem : x ∈ D <;> by_cases hi : i ∈ x <;>
      norm_num [coordinateSign, indicator, mem_star, hmem, hi]
  rw [heq, cubeMean_sub, cubeMean_coordinateSign, cubeMean_sub,
    cubeMean_mul_left, cubeMean_indicator, cubeMean_indicator]
  ring

/-- The coordinatewise form of equation (17) in Section 4. Taking the minimum
influence and the maximum star size yields the displayed equation in the paper.
@isnad1 id=eq.2h4v.s7.bb6aeb39f2a3 from=translated src=- shape=008c6137 vocab=68400321
-/
theorem covariance_sub_quarter_influence {D B : Family ι}
    (hD : D.IsHereditary) (hB : B.IsAntipodal) (i : ι) :
    covariance (fun x => 1 - D.indicator x) B.indicator -
      influence (fun x => 1 - D.indicator x) i / 4 =
      ((D.star i).card - (D ∩ B).card : ℝ) / Fintype.card (Finset ι) := by
  rw [covariance_one_sub_indicator hB, influence_one_sub_indicator hD]
  ring

/-- Equation (17) of Section 4, with its finite minimum of influences and
maximum of star cardinalities. A nonempty coordinate type makes the minimum
well-defined.
@isnad1 id=eq.2h3v.s7.7e13514e8b30 from=translated src=- shape=38c2e41b vocab=0e76dfea
-/
theorem covariance_sub_quarter_min_influence [Nonempty ι] {D B : Family ι}
    (hD : D.IsHereditary) (hB : B.IsAntipodal) :
    covariance (fun x => 1 - D.indicator x) B.indicator -
      (Finset.univ.inf' Finset.univ_nonempty (influence (fun x => 1 - D.indicator x))) / 4 =
      (((Finset.univ.sup fun i => (D.star i).card : ℕ) : ℝ) - (D ∩ B).card) /
        Fintype.card (Finset ι) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : ι => (D.star i).card) Finset.univ_nonempty
  have hmax : (Finset.univ.sup fun j => (D.star j).card) = (D.star i).card := by
    exact le_antisymm (Finset.sup_le hi) (Finset.le_sup (f := fun j => (D.star j).card)
      (Finset.mem_univ i))
  have hmin : Finset.univ.inf' Finset.univ_nonempty
      (influence (fun x => 1 - D.indicator x)) =
      influence (fun x => 1 - D.indicator x) i := by
    apply le_antisymm (Finset.inf'_le _ (Finset.mem_univ i))
    apply Finset.le_inf'
    intro j hj
    rw [influence_one_sub_indicator hD, influence_one_sub_indicator hD]
    apply div_le_div_of_nonneg_right _ (cube_card_pos (ι := ι)).le
    have hij : ((D.star j).card : ℝ) ≤ (D.star i).card := by exact_mod_cast hi j hj
    linarith
  rw [hmax, hmin]
  exact covariance_sub_quarter_influence hD hB i

/-- Equation (17) turns a coordinate's influence bound into the corresponding
star bound, in either direction.
@isnad1 id=iff.2h4v.s7.28735fa8e019 from=translated src=- shape=31434491 vocab=15904d37
-/
theorem influence_le_four_covariance_iff {D B : Family ι}
    (hD : D.IsHereditary) (hB : B.IsAntipodal) (i : ι) :
    influence (fun x => 1 - D.indicator x) i ≤
        4 * covariance (fun x => 1 - D.indicator x) B.indicator ↔
      (D ∩ B).card ≤ (D.star i).card := by
  have heq := covariance_sub_quarter_influence hD hB i
  constructor
  · intro h
    have hdiv : 0 ≤ ((D.star i).card - (D ∩ B).card : ℝ) /
        Fintype.card (Finset ι) := by rw [← heq]; linarith
    have hnum := (le_div_iff₀ (cube_card_pos (ι := ι))).mp hdiv
    simp only [zero_mul] at hnum
    exact_mod_cast sub_nonneg.mp hnum
  · intro h
    have hreal : ((D ∩ B).card : ℝ) ≤ (D.star i).card := by exact_mod_cast h
    have hdiv := div_nonneg (sub_nonneg.mpr hreal) (le_of_lt (cube_card_pos (ι := ι)))
    rw [← heq] at hdiv
    linarith

omit [Fintype ι] in
/-- The star property asserted for each hereditary family in Theorem 1.1:
every intersecting subfamily is no larger than some star. -/
def HasStarProperty (D : Family ι) : Prop :=
  ∀ A : Family ι, A ⊆ D → A.IsIntersecting → ∃ i : ι, A.card ≤ (D.star i).card

end Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The antipodal correlation assertion of Corollary 1.3, expressed with a
coordinate attaining a bound instead of a finite minimum. On a nonempty ground
type this is exactly `Cov(f,g) ≥ (1/4) min_i Inf_i[f]`. This is a proposition,
not an assumption introduced into the logical environment. -/
def AntipodalCorrelationBound (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ f g : Finset ι → ℝ, IsBoolean f → Monotone f → IsBoolean g → Monotone g →
    dual g = g → ∃ i : ι, influence f i ≤ 4 * covariance f g

/-- Theorem 1.1 deduced from Corollary 1.3, exactly as in Section 4. The analytic
correlation theorem is an explicit hypothesis: this declaration does not claim
to prove that analytic assertion.
@isnad1 id=hasstarp.2h2v.s4.d5a5d9ffa84a from=translated src=- shape=fc688b40 vocab=0167bc62
-/
theorem chvatal_of_antipodal_correlation [Nonempty ι]
    (hcorr : AntipodalCorrelationBound ι) {D : Family ι} (hD : D.IsHereditary) :
    D.HasStarProperty := by
  intro A hAD hA
  apply Family.exists_star_bound_of_maximal (D := D) (A := A) ?_ hAD hA
  intro B hB
  obtain ⟨i, hi⟩ := hcorr (fun x => 1 - D.indicator x) B.indicator
    (Family.isBoolean_one_sub_indicator D) hD.monotone_one_sub_indicator
    (Family.isBoolean_indicator B) hB.isIncreasing.monotone_indicator
    hB.isAntipodal.dual_indicator
  exact ⟨i, (Family.influence_le_four_covariance_iff hD hB.isAntipodal i).mp hi⟩

/-- Section 4's converse: a star bound for every hereditary family implies the
antipodal correlation bound, using `D = supp(1-f)` and `B = supp(g)`.
@isnad1 id=antipoda.1h1v.s4.81a9b00cf39d from=translated src=- shape=743e1817 vocab=a4346887
-/
theorem antipodal_correlation_of_chvatal
    (hstar : ∀ D : Family ι, D.IsHereditary → D.HasStarProperty) :
    AntipodalCorrelationBound ι := by
  intro f g hf hfm hg hgm hdual
  let D : Family ι := (Family.oneSupport f)ᶜ
  let B : Family ι := Family.oneSupport g
  have hD : D.IsHereditary :=
    (Family.isIncreasing_oneSupport hf hfm).isHereditary_compl
  have hfD : (fun x => 1 - D.indicator x) = f := by
    dsimp [D]
    rw [Family.indicator_compl, Family.indicator_oneSupport hf]
    funext x
    ring
  have hgB : B.indicator = g := Family.indicator_oneSupport hg
  have hincB : B.IsIncreasing := Family.isIncreasing_oneSupport hg hgm
  have hantiB : B.IsAntipodal := by
    rw [Family.isAntipodal_iff_dual_indicator, hgB]
    exact hdual
  have hint : (D ∩ B).IsIntersecting :=
    (hincB.isIntersecting_of_isAntipodal hantiB).mono Finset.inter_subset_right
  obtain ⟨i, hi⟩ := hstar D hD (D ∩ B) Finset.inter_subset_left hint
  have hbound := (Family.influence_le_four_covariance_iff hD hantiB i).mpr hi
  rw [hfD, hgB] at hbound
  exact ⟨i, hbound⟩

/-- The equivalence recalled in Section 4 between Chvátal's star assertion and
Corollary 1.3's antipodal correlation assertion. Both sides remain explicit
propositions; no direction relies on an unproved result.
@isnad1 id=iff.0h1v.s4.447ca444b47b from=translated src=- shape=14216226 vocab=0167bc62
-/
theorem chvatal_iff_antipodal_correlation [Nonempty ι] :
    (∀ D : Family ι, D.IsHereditary → D.HasStarProperty) ↔
      AntipodalCorrelationBound ι :=
  ⟨antipodal_correlation_of_chvatal,
    fun h _ hD => chvatal_of_antipodal_correlation h hD⟩

end Chvatal
