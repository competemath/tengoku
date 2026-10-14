/-
Copyright (c) 2026 Chvátal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/
module

public import Tengoku.LeanPool.LeanPool.Chvatal.Weighted

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
# The signed Boolean formulation

The final paragraph of Section 5 of arXiv:2609.19123 changes conventions from
`{0,1}`-valued functions to `{-1,1}`-valued functions by `h = 2g - 1`.
This file verifies that conversion, the positive-part and Fourier identities,
and the resulting signed version of the weighted star inequality.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A signed Boolean function, with values in `{-1,1}`, as in Section 5's
comparison with Friedgut–Kahn–Kalai–Keller. -/
def IsSignedBoolean (h : Finset ι → ℝ) : Prop := ∀ x, h x = -1 ∨ h x = 1

/-- The convention change `h = 2g - 1` in the final paragraph of Section 5. -/
def signLift (g : Finset ι → ℝ) (x : Finset ι) : ℝ := 2 * g x - 1

/-- The inverse convention change `g = (h + 1) / 2` in Section 5. -/
def booleanPart (h : Finset ι → ℝ) (x : Finset ι) : ℝ := (h x + 1) / 2

omit [Fintype ι] [DecidableEq ι] in
/-- The signed lift followed by the Boolean conversion is the identity.
@isnad1 id=eq.0h2v.s4.b2d58e62576c from=translated src=- shape=deaf87fd vocab=093d7769
-/
@[simp] theorem booleanPart_signLift (g : Finset ι → ℝ) : booleanPart (signLift g) = g := by
  funext x
  simp only [booleanPart, signLift]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The Boolean conversion followed by the signed lift is the identity.
@isnad1 id=eq.0h2v.s4.effd3cacacee from=translated src=- shape=deaf87fd vocab=093d7769
-/
@[simp] theorem signLift_booleanPart (h : Finset ι → ℝ) : signLift (booleanPart h) = h := by
  funext x
  simp only [booleanPart, signLift]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- Section 5: a Boolean function becomes a `{-1,1}`-valued function.
@isnad1 id=issigned.1h2v.s4.91df98c1659a from=translated src=- shape=298b3b1b vocab=2b767f8b
-/
theorem IsBoolean.signLift {g : Finset ι → ℝ} (hg : IsBoolean g) :
    IsSignedBoolean (signLift g) := by
  intro x
  rcases hg x with hx | hx <;> norm_num [Chvatal.signLift, hx]

omit [Fintype ι] [DecidableEq ι] in
/-- Conversely every signed Boolean function gives an ordinary Boolean function,
so the closing signed formulation has the same scope as the Boolean one.
@isnad1 id=isboolea.1h2v.s4.07cc646f0809 from=translated src=- shape=298b3b1b vocab=cceba3eb
-/
theorem IsSignedBoolean.booleanPart {h : Finset ι → ℝ} (hh : IsSignedBoolean h) :
    IsBoolean (booleanPart h) := by
  intro x
  rcases hh x with hx | hx <;> simp [Chvatal.booleanPart, hx]

omit [Fintype ι] [DecidableEq ι] in
/-- The convention change in Section 5 preserves increasing functions.
@isnad1 id=monotone.1h2v.s5.21ac043b7b2a from=translated src=- shape=f67266ee vocab=6ad33fe7
-/
theorem monotone_signLift {g : Finset ι → ℝ} (hg : Monotone g) :
    Monotone (signLift g) := by
  intro x y hxy
  dsimp [signLift]
  linarith [hg hxy]

omit [Fintype ι] [DecidableEq ι] in
/-- The inverse convention change also preserves increasing functions.
@isnad1 id=monotone.1h2v.s5.8581046c8233 from=translated src=- shape=f67266ee vocab=82e64419
-/
theorem monotone_booleanPart {h : Finset ι → ℝ} (hh : Monotone h) :
    Monotone (booleanPart h) := by
  intro x y hxy
  dsimp [booleanPart]
  linarith [hh hxy]

/-- Section 5: a self-dual Boolean function lifts to an odd function under
antipodal complementation, `h(xᶜ) = -h(x)`.
@isnad1 id=eq.1h3v.s5.93a6a58b88c4 from=translated src=- shape=f7946a1d vocab=c30985e8
-/
theorem signLift_compl {g : Finset ι → ℝ} (hg : dual g = g) (x : Finset ι) :
    signLift g xᶜ = -signLift g x := by
  have hx := congrFun hg x
  dsimp [dual] at hx
  dsimp [signLift]
  linarith

/-- The inverse of the preceding antipodality conversion.
@isnad1 id=eq.1h2v.s5.6133ad24edd2 from=translated src=- shape=ac48fbe5 vocab=716cd961
-/
theorem dual_booleanPart {h : Finset ι → ℝ} (hh : ∀ x, h xᶜ = -h x) :
    dual (booleanPart h) = booleanPart h := by
  funext x
  simp only [dual, booleanPart, hh]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The identity `h_+² = g` explicitly stated in the final paragraph of Section 5.
@isnad1 id=eq.1h3v.s5.2ee3e3650f53 from=translated src=- shape=c1fa6191 vocab=a83777f2
-/
theorem signLift_positivePart_sq {g : Finset ι → ℝ} (hg : IsBoolean g) (x : Finset ι) :
    max (signLift g x) 0 ^ 2 = g x := by
  rcases hg x with hx | hx <;> norm_num [signLift, hx]

omit [Fintype ι] [DecidableEq ι] in
/-- The positive-part identity for an arbitrary signed Boolean function.
@isnad1 id=eq.1h3v.s5.fccb7da624ad from=translated src=- shape=5f43b233 vocab=8e78b17a
-/
theorem IsSignedBoolean.positivePart_sq {h : Finset ι → ℝ} (hh : IsSignedBoolean h)
    (x : Finset ι) : max (h x) 0 ^ 2 = Chvatal.booleanPart h x := by
  rcases hh x with hx | hx <;> norm_num [Chvatal.booleanPart, hx]

/-- Fourier coefficients under the affine convention change of Section 5,
including the exceptional constant coefficient.
@isnad1 id=eq.0h3v.s6.856184b502da from=translated src=- shape=2ed89d8f vocab=bf74396f
-/
theorem fourier_signLift (g : Finset ι → ℝ) (S : Finset ι) :
    fourier (signLift g) S = 2 * fourier g S - if S = ∅ then 1 else 0 := by
  change fourier (fun x => 2 * g x - 1) S = _
  rw [fourier_sub, fourier_const]
  congr 1
  simp only [fourier, mul_assoc, cubeMean_mul_left]

/-- Section 5's formula `ĥ(S) = 2ĝ(S)` for every nonempty Fourier index.
@isnad1 id=eq.1h3v.s5.9d70d1cdd82c from=translated src=- shape=d3ffa9a0 vocab=c6872889
-/
theorem fourier_signLift_of_nonempty (g : Finset ι → ℝ) {S : Finset ι}
    (hS : S.Nonempty) : fourier (signLift g) S = 2 * fourier g S := by
  simp [fourier_signLift, hS.ne_empty]

/-- The coefficients in the final displayed equation of Section 5, in the
signed Boolean convention. Choosing `orderedSelector` gives the paper's order. -/
def signedSpectralWeights (h : Finset ι → ℝ) (select : Finset ι → ι) (i : ι) : ℝ :=
  ∑ S ∈ Finset.univ.erase ∅, if select S = i then fourier h S ^ 2 else 0

/-- Section 5: the signed Fourier formula gives exactly the same coefficients
`λ_i` as Proposition 5.3, with its factor of four absorbed by the convention change.
@isnad1 id=eq.0h4v.s5.6f6f74f02795 from=translated src=- shape=35214770 vocab=f6ecc6bc
-/
theorem spectralWeights_eq_signed (g : Finset ι → ℝ) (select : Finset ι → ι) (i : ι) :
    spectralWeights g select i = signedSpectralWeights (signLift g) select i := by
  rw [spectralWeights, signedSpectralWeights, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [fourier_signLift_of_nonempty g
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1)]
  split_ifs <;> ring

/-- Nonnegativity of the signed coefficients in the closing Section 5 formulation.
@isnad1 id=le.0h4v.s5.fc0d6f26880f from=translated src=- shape=bcd0e99d vocab=6c045006
-/
theorem signedSpectralWeights_nonneg (h : Finset ι → ℝ) (select : Finset ι → ι) (i : ι) :
    0 ≤ signedSpectralWeights h select i := by
  exact Finset.sum_nonneg fun S _ => by split_ifs <;> positivity

/-- The signed coefficients sum to one for every antipodal signed Boolean function.
@isnad1 id=eq.2h3v.s6.420d39cc1a2a from=translated src=- shape=324474f5 vocab=55964a8d
-/
theorem sum_signedSpectralWeights {h : Finset ι → ℝ} (hh : IsSignedBoolean h)
    (hanti : ∀ x, h xᶜ = -h x) (select : Finset ι → ι) :
    (∑ i, signedSpectralWeights h select i) = 1 := by
  have hsum := sum_spectralWeights hh.booleanPart (dual_booleanPart hanti) select
  simpa only [spectralWeights_eq_signed, signLift_booleanPart] using hsum

/-- The weighted star inequality in the signed Boolean convention of Section 5's
closing paragraph. Its left side uses exactly the stated positive-part square,
and its coefficients use the stated squared signed Fourier coefficients.
@isnad1 id=le.6h4v.s7.23fe187f857b from=translated src=- shape=4f90bfe9 vocab=e3014229
-/
theorem signed_weighted_star_bound [Nonempty ι] {h : Finset ι → ℝ}
    (hh : IsSignedBoolean h) (hm : Monotone h) (hanti : ∀ x, h xᶜ = -h x)
    (select : Finset ι → ι) (hselect : ∀ S : Finset ι, S.Nonempty → select S ∈ S)
    (ω : Finset ι → ℝ) (hω : ∀ x, 0 ≤ ω x) (hωanti : Antitone ω) :
    (∑ x, max (h x) 0 ^ 2 * ω x) ≤
      ∑ i, signedSpectralWeights h select i * ∑ x ∈ Family.star Finset.univ i, ω x := by
  let B := Family.oneSupport (booleanPart h)
  have hBindicator : B.indicator = booleanPart h := Family.indicator_oneSupport hh.booleanPart
  have hBmono : B.IsIncreasing := Family.isIncreasing_oneSupport hh.booleanPart
    (monotone_booleanPart hm)
  have hBanti : B.IsAntipodal := by
    rw [Family.isAntipodal_iff_dual_indicator, hBindicator]
    exact dual_booleanPart hanti
  have hbound := weighted_star_mixture_bound
    (hBmono.isMaximalIntersecting_of_isAntipodal hBanti) select hselect ω hω hωanti
  rw [hBindicator] at hbound
  simp only [spectralWeights_eq_signed, signLift_booleanPart] at hbound
  have hsum : (∑ x, max (h x) 0 ^ 2 * ω x) = ∑ x ∈ B, ω x := by
    simp_rw [hh.positivePart_sq]
    rw [← hBindicator, sum_indicator_mul]
  rw [hsum]
  exact hbound

end Chvatal
