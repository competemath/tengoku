/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/
module

public import Tengoku.LeanPool.LeanPool.Chvatal.Spectral

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
# Sharpness and the two-coordinate counterexample

This file formalizes Proposition 5.1 and Remark 5.2 of arXiv:2609.19123.
The AND function is the indicator of the top cube point; OR is its dual.
-/

@[expose] public section

open scoped BigOperators symmDiff

noncomputable section

namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The function `AND_n` in Section 5: all coordinates must equal one. -/
def andFunction (x : Finset ι) : ℝ := if x = Finset.univ then 1 else 0

/-- The function `OR_n` in Section 5, defined as the dual of `AND_n`. -/
def orFunction : Finset ι → ℝ := dual andFunction

/-- AND is Boolean, as required for the sharpness examples in Section 5.
@isnad1 id=isboolea.0h1v.s3.a5ddbd9996eb from=translated src=- shape=4c9b52a8 vocab=359a7189
-/
theorem isBoolean_andFunction : IsBoolean (andFunction (ι := ι)) := by
  intro x
  simp only [andFunction]
  split_ifs <;> simp

/-- AND is increasing, as required for Proposition 5.1.
@isnad1 id=monotone.0h1v.s4.7c2e273f4142 from=translated src=- shape=11100875 vocab=0deb6100
-/
theorem monotone_andFunction : Monotone (andFunction (ι := ι)) := by
  intro x y hxy
  by_cases hx : x = Finset.univ
  · subst x
    have hy : y = Finset.univ := Finset.univ_subset_iff.mp hxy
    simp [hy, andFunction]
  · simp only [andFunction, ite_eq_right hx]
    split_ifs <;> norm_num

/-- OR is Boolean, as required for Remark 5.2.
@isnad1 id=isboolea.0h1v.s3.293d910cfc45 from=translated src=- shape=4c9b52a8 vocab=18c5a16b
-/
theorem isBoolean_orFunction : IsBoolean (orFunction (ι := ι)) :=
  isBoolean_andFunction.dual

/-- OR is increasing, as required for Remark 5.2.
@isnad1 id=monotone.0h1v.s4.1c8b88da29eb from=translated src=- shape=11100875 vocab=0c032991
-/
theorem monotone_orFunction : Monotone (orFunction (ι := ι)) :=
  monotone_dual monotone_andFunction

/-- Integrating against AND evaluates at the top point, the counting calculation
in Proposition 5.1.
@isnad1 id=eq.0h2v.s5.7739eebaa230 from=translated src=- shape=2c718cc1 vocab=81171a3b
-/
theorem cubeMean_andFunction_mul (g : Finset ι → ℝ) :
    cubeMean (fun x => andFunction x * g x) =
      g Finset.univ / Fintype.card (Finset ι) := by
  simp [cubeMean, andFunction, ite_mul]

/-- The quantity `a = 2^{-n}` in Proposition 5.1 is the mean of AND.
@isnad1 id=eq.0h1v.s5.49e40247eebb from=translated src=- shape=353c401c vocab=7a6398e1
-/
theorem cubeMean_andFunction :
    cubeMean (andFunction (ι := ι)) = 1 / Fintype.card (Finset ι) := by
  simp [cubeMean, andFunction]

/-- Every coordinate of AND has influence `2a`, as computed in Proposition 5.1.
@isnad1 id=eq.0h2v.s5.e030140344f9 from=translated src=- shape=26b489f7 vocab=b80936af
-/
theorem influence_andFunction (i : ι) :
    influence andFunction i = 2 / Fintype.card (Finset ι) := by
  have ht : (Finset.univ : Finset ι) ∆ {i} ≠ Finset.univ := by
    intro h
    have hi : i ∈ (Finset.univ : Finset ι) ∆ {i} := h.symm ▸ Finset.mem_univ i
    simp [Finset.mem_symmDiff] at hi
  have hp (x : Finset ι) : (andFunction x - andFunction (x ∆ {i})) ^ 2 =
      andFunction x + andFunction (x ∆ {i}) := by
    by_cases hx : x = Finset.univ
    · subst x
      simp [andFunction, ht]
    · simp only [andFunction, ite_eq_right hx]
      split_ifs <;> norm_num
  unfold influence
  simp_rw [hp]
  rw [cubeMean_add, cubeMean_symmDiff, cubeMean_andFunction]
  ring

/-- AND has the same maximum influence on every nonempty Fourier index.
@isnad1 id=eq.1h2v.s5.ffe43407f3c2 from=translated src=- shape=4bf6753a vocab=b3b2946f
-/
theorem maxInfluence_andFunction {S : Finset ι} (hS : S.Nonempty) :
    maxInfluence andFunction S = 2 / Fintype.card (Finset ι) := by
  rw [maxInfluence_of_nonempty _ hS]
  simp_rw [influence_andFunction]
  exact Finset.sup'_const hS (2 / (Fintype.card (Finset ι) : ℝ))

/-- Proposition 5.1: the AND spectral weight is `2a` times the variance of `g`.
@isnad1 id=eq.0h2v.s5.4f81d5870710 from=translated src=- shape=a549daab vocab=9373e9d1
-/
theorem spectralWeight_andFunction (g : Finset ι → ℝ) :
    spectralWeight andFunction g =
      (2 / Fintype.card (Finset ι)) * covariance g g := by
  rw [spectralWeight_eq_sum_nonempty, covariance_fourier, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [maxInfluence_andFunction
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1)]
  ring

omit [DecidableEq ι] in
/-- The variance of a Boolean function is `b(1-b)`, the Parseval calculation
used in Proposition 5.1.
@isnad1 id=eq.1h2v.s5.7ac356ca6c29 from=translated src=- shape=736e6b8a vocab=e5274cf6
-/
theorem covariance_self_boolean {g : Finset ι → ℝ} (hg : IsBoolean g) :
    covariance g g = cubeMean g * (1 - cubeMean g) := by
  have hsq : (fun x => g x * g x) = g := by
    funext x
    simpa [pow_two] using hg.sq x
  rw [covariance, hsq]
  ring

/-- The covariance of AND with any function, prior to using the endpoint values
in Proposition 5.1.
@isnad1 id=eq.0h2v.s6.b2642d82bb29 from=translated src=- shape=b31422f1 vocab=f6f2127f
-/
theorem covariance_andFunction (g : Finset ι → ℝ) :
    covariance andFunction g =
      (1 / Fintype.card (Finset ι)) * (g Finset.univ - cubeMean g) := by
  rw [covariance, cubeMean_andFunction_mul, cubeMean_andFunction]
  ring

/-- The covariance of AND with the dual, in the endpoint form used by
Proposition 5.1.
@isnad1 id=eq.0h2v.s6.7f0a2f97f22a from=translated src=- shape=0b3fb8d3 vocab=1ca8ba2d
-/
theorem covariance_andFunction_dual (g : Finset ι → ℝ) :
    covariance andFunction (dual g) =
      (1 / Fintype.card (Finset ι)) * (cubeMean g - g ∅) := by
  rw [covariance_andFunction, cubeMean_dual]
  simp only [dual, Finset.compl_univ]
  ring

omit [DecidableEq ι] in
/-- An increasing Boolean function is constant or has the two endpoint values
used in the nonconstant case of Proposition 5.1.
@isnad1 id=or.2h2v.s6.6daced56ce79 from=translated src=- shape=00a56106 vocab=2bb95368
-/
theorem monotone_boolean_endpoints {g : Finset ι → ℝ} (hg : IsBoolean g)
    (hm : Monotone g) :
    g = (fun _ => 0) ∨ g = (fun _ => 1) ∨ (g ∅ = 0 ∧ g Finset.univ = 1) := by
  rcases hg Finset.univ with htop | htop
  · left
    funext x
    have hle := hm (Finset.subset_univ x)
    have hnonneg := hg.nonneg x
    simp only [htop] at hle
    linarith
  · rcases hg ∅ with hbot | hbot
    · exact Or.inr (Or.inr ⟨hbot, htop⟩)
    · right; left
      funext x
      have hle := hm (Finset.empty_subset x)
      rcases hg x with hx | hx
      · rw [hbot, hx] at hle
        norm_num at hle
      · exact hx

/-- Proposition 5.1: AND attains equality in the harmonic correlation bound
for every increasing Boolean second function, including constant functions.
@isnad1 id=eq.2h2v.s6.3c22b10538eb from=translated src=- shape=da1c41ef vocab=d7afd3f9
-/
theorem andFunction_sharp {g : Finset ι → ℝ} (hg : IsBoolean g) (hm : Monotone g) :
    spectralWeight andFunction g =
      2 * covariance andFunction g * covariance andFunction (dual g) /
        (covariance andFunction g + covariance andFunction (dual g)) := by
  rw [spectralWeight_andFunction, covariance_self_boolean hg,
    covariance_andFunction, covariance_andFunction_dual]
  rcases monotone_boolean_endpoints hg hm with h | h | ⟨hbot, htop⟩
  · subst g
    simp
  · subst g
    simp
  · rw [hbot, htop]
    have hN : (Fintype.card (Finset ι) : ℝ) ≠ 0 := ne_of_gt cube_card_pos
    have hsum : (1 / (Fintype.card (Finset ι) : ℝ)) * (1 - cubeMean g) +
        (1 / (Fintype.card (Finset ι) : ℝ)) * (cubeMean g - 0) =
        1 / Fintype.card (Finset ι) := by ring
    rw [hsum]
    field_simp
    ring

/-- The mean of OR is `1 - 2^{-n}`, used in Remark 5.2.
@isnad1 id=eq.0h1v.s5.7187378a2a9c from=translated src=- shape=8f2e6294 vocab=b069a4e2
-/
theorem cubeMean_orFunction :
    cubeMean (orFunction (ι := ι)) = 1 - 1 / Fintype.card (Finset ι) := by
  rw [orFunction, cubeMean_dual, cubeMean_andFunction]

/-- OR vanishes at the bottom cube point, including in dimension zero.
@isnad1 id=eq.0h1v.s4.765c1a937d74 from=translated src=- shape=05d4bbd4 vocab=2f80a504
-/
@[simp] theorem orFunction_empty : orFunction (∅ : Finset ι) = 0 := by
  simp [orFunction, dual, andFunction]

/-- OR is one at the top when there is at least one coordinate.
@isnad1 id=eq.0h1v.s4.cf784b068032 from=translated src=- shape=080835ac vocab=7b903ce5
-/
@[simp] theorem orFunction_univ [Nonempty ι] :
    orFunction (Finset.univ : Finset ι) = 1 := by
  simp [orFunction, dual, andFunction, Finset.univ_nonempty.ne_empty.symm]

/-- Remark 5.2: the exact two-coordinate AND/OR counterexample. The spectral
weight exceeds covariance, so removing antipodality from the stronger bound fails.
@isnad1 id=and.0h0v.s8.4a2cccb9fd1d from=translated src=- shape=a9a34283 vocab=7d45309f
-/
theorem and_or_two_example :
    covariance (andFunction (ι := Fin 2)) orFunction = 1 / 16 ∧
    covariance (andFunction (ι := Fin 2)) (dual orFunction) = 3 / 16 ∧
    spectralWeight (andFunction (ι := Fin 2)) orFunction = 3 / 32 ∧
    covariance (andFunction (ι := Fin 2)) orFunction <
      spectralWeight (andFunction (ι := Fin 2)) orFunction := by
  norm_num [covariance_andFunction, covariance_andFunction_dual,
    spectralWeight_andFunction, covariance_self_boolean isBoolean_orFunction,
    cubeMean_orFunction, Fintype.card_finset]
  norm_num [dual]

/-- On a single coordinate AND is antipodal, providing the extremizer for the
optimal constant asserted in Proposition 5.1.
@isnad1 id=eq.0h0v.s6.331baa83f85e from=translated src=- shape=ef4a5786 vocab=1461aa83
-/
theorem andFunction_one_antipodal :
    dual (andFunction (ι := Fin 1)) = andFunction := by
  have heq (x : Finset (Fin 1)) : x = Finset.univ ↔ (0 : Fin 1) ∈ x := by
    constructor
    · intro h; simp [h]
    · intro h
      apply Finset.eq_univ_of_forall
      intro i
      simpa only [Subsingleton.elim i 0] using h
  funext x
  simp only [dual, andFunction, heq, Finset.mem_compl]
  by_cases hx : (0 : Fin 1) ∈ x <;> simp [hx]

/-- The one-coordinate extremizer has covariance one quarter and influence one,
so the coefficient in Corollary 1.3 cannot be increased.
@isnad1 id=and.0h0v.s7.4ee3f2c7c5ce from=translated src=- shape=0700eedf vocab=36204c3b
-/
theorem andFunction_one_values :
    covariance (andFunction (ι := Fin 1)) andFunction = 1 / 4 ∧
      influence (andFunction (ι := Fin 1)) 0 = 1 := by
  rw [covariance_self_boolean isBoolean_andFunction, cubeMean_andFunction,
    influence_andFunction]
  norm_num [Fintype.card_finset]

/-- Proposition 5.1, antipodal case: AND attains the factor one quarter for
every coordinate and every increasing antipodal Boolean second function.
@isnad1 id=eq.3h3v.s6.c446d729d89a from=translated src=- shape=496dc531 vocab=c26647c8
-/
theorem andFunction_antipodal_sharp {g : Finset ι → ℝ} (hg : IsBoolean g)
    (hm : Monotone g) (hdual : dual g = g) (i : ι) :
    covariance andFunction g = influence andFunction i / 4 := by
  have h := andFunction_sharp hg hm
  rw [hdual, harmonic_self] at h
  rw [← h, spectralWeight_andFunction, variance_eq_quarter_of_antipodal hg hdual,
    influence_andFunction]
  ring

/-- Proposition 5.1, optimality: a coefficient valid for all increasing Boolean
pairs with an antipodal second function, even just on the one-coordinate cube,
cannot exceed `1/4`. The finite infimum is the minimum influence from (2).
@isnad1 id=le.1h1v.s7.1e02eb06d948 from=translated src=- shape=7590beb9 vocab=7ffa8240
-/
theorem quarter_coefficient_optimal (c : ℝ)
    (hc : ∀ (f g : Finset (Fin 1) → ℝ), IsBoolean f → Monotone f →
      IsBoolean g → Monotone g → dual g = g →
        c * Finset.univ.inf' Finset.univ_nonempty (influence f) ≤ covariance f g) :
    c ≤ 1 / 4 := by
  have h := hc andFunction andFunction isBoolean_andFunction monotone_andFunction
    isBoolean_andFunction monotone_andFunction andFunction_one_antipodal
  rw [andFunction_one_values.1] at h
  simp_rw [influence_andFunction] at h
  norm_num [Fintype.card_finset] at h
  exact h

end Chvatal
