/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Complex.JensenFormula

/-!
# The Logarithmic Counting Function of Value Distribution Theory

For nontrivially normed fields `𝕜`, this file defines the logarithmic counting function of a
meromorphic function defined on `𝕜`.  Also known as the `Nevanlinna counting function`, this is one
of the three main functions used in Value Distribution Theory.

The logarithmic counting function of a meromorphic function `f` is a logarithmically weighted
measure of the number of times the function `f` takes a given value `a` within the disk `∣z∣ ≤ r`,
taking multiplicities into account.

See Section VI.1 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

## Implementation Notes

- This file defines the logarithmic counting function first for functions with locally finite
  support on `𝕜` and then specializes to the setting where the function with locally finite support
  is the pole or zero-divisor of a meromorphic function.

- Even though value distribution theory is best developed for meromorphic functions on the complex
  plane (and therefore placed in the complex analysis section of Mathlib), we introduce the
  logarithmic counting function for arbitrary normed fields.

## TODO

- Discuss the logarithmic counting function for rational functions, add a forward reference to the
  upcoming converse, formulated in terms of the Nevanlinna height.
-/

@[expose] public section

open Filter Function MeromorphicOn Metric Real Set

/-!
## Supporting Notation
-/

namespace Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E]

/--
Shorthand notation for the restriction of a function with locally finite support to the closed unit
ball of radius `r`.
-/
noncomputable def toClosedBall (r : ℝ) :
    locallyFinsupp E ℤ →+ locallyFinsuppWithin (closedBall (0 : E) |r|) ℤ := by
  apply restrictMonoidHom
  tauto

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h4v.s9.e1134464a3f6 from=seed src=0 shape=9e669268 vocab=160c293f
-/
@[simp]
lemma toClosedBall_eval_within {r : ℝ} {z : E} (f : locallyFinsupp E ℤ)
    (ha : z ∈ closedBall 0 |r|) :
    toClosedBall r f z = f z := by
  unfold toClosedBall
  simp_all [restrict_apply]

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h2v.s9.50f87542bb68 from=seed src=0 shape=39d268cb vocab=d237ddbc
-/
@[simp]
lemma toClosedBall_divisor {r : ℝ} {f : ℂ → ℂ} (h : Meromorphic f) :
    (divisor f (closedBall 0 |r|)) = (locallyFinsuppWithin.toClosedBall r) (divisor f univ) := by
  simp_all [locallyFinsuppWithin.toClosedBall]

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=le.0h3v.s9.c0985c8e663b from=seed src=0 shape=cc2f9080 vocab=17b651c5
-/
lemma toClosedBall_support_subset_closedBall {E : Type*} [NormedAddCommGroup E] {r : ℝ}
    (f : locallyFinsupp E ℤ) :
    (toClosedBall r f).support ⊆ closedBall 0 |r| := by
  simp_all [toClosedBall, restrict_apply]

/-!
## The Logarithmic Counting Function of a Function with Locally Finite Support
-/

/--
Definition of the logarithmic counting function, as a group morphism mapping functions `D` with
locally finite support to maps `ℝ → ℝ`.  Given `D`, the result map `logCounting D` takes `r : ℝ` to
a logarithmically weighted measure of values that `D` takes within the disk `∣z∣ ≤ r`.

Implementation Note: In case where `z = 0`, the term `log (r * ‖z‖⁻¹)` evaluates to zero, which is
typically different from `log r - log ‖z‖ = log r`. The summand `(D 0) * log r` compensates this,
producing cleaner formulas when the logarithmic counting function is used in the main theorems of
Value Distribution Theory.  We refer the reader to page 164 of [Lang: Introduction to Complex
Hyperbolic Spaces](https://link.springer.com/book/10.1007/978-1-4757-1945-1) for more details, and
to the lemma `countingFunction_finsum_eq_finsum_add` in
`Mathlib/Analysis/Complex/JensenFormula.lean` for a formal statement.
-/
noncomputable def logCounting {E : Type*} [NormedAddCommGroup E] [ProperSpace E] :
    locallyFinsupp E ℤ →+ (ℝ → ℝ) where
  toFun D := fun r ↦ ∑ᶠ z, D.toClosedBall r z * log (r * ‖z‖⁻¹) + (D 0) * log r
  map_zero' := by aesop
  map_add' D₁ D₂ := by
    simp only [map_add, coe_add, Pi.add_apply, Int.cast_add]
    ext r
    have {A B C D : ℝ} : A + B + (C + D) = A + C + (B + D) := by ring
    rw [Pi.add_apply, this]
    congr 1
    · have h₁s : ((D₁.toClosedBall r).support ∪ (D₂.toClosedBall r).support).Finite := by
        apply Set.finite_union.2
        constructor
        <;> apply finiteSupport _ (isCompact_closedBall 0 |r|)
      repeat
        rw [finsum_eq_sum_of_support_subset (s := h₁s.toFinset)]
        try simp_rw [← Finset.sum_add_distrib, ← add_mul]
      repeat
        intro x hx
        by_contra
        simp_all
    · ring

/--
Evaluation of the logarithmic counting function at zero yields zero.
@isnad1 id=eq.0h2v.s8.f2ffc7e53c88 from=seed src=0 shape=0ddf3104 vocab=f55442eb
-/
@[simp] lemma logCounting_eval_zero {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsupp E ℤ) :
    logCounting D 0 = 0 := by
  simp [logCounting]

set_option backward.isDefEq.respectTransparency.types false in
/--
The logarithmic counting function of a singleton indicator is asymptotically equal to
`log · - log ‖e‖`.
@isnad1 id=eq.1h4v.s8.f0c501a54793 from=seed src=0 shape=6f8168c3 vocab=d972de1c
-/
@[simp] lemma logCounting_single_eq_log_sub_const [DecidableEq E] [ProperSpace E] {e : E} {r : ℝ}
    {n : ℤ} (hr : ‖e‖ ≤ r) :
    logCounting (single e n) r = n * (log r - log ‖e‖) := by
  simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [finsum_eq_sum_of_support_subset _ (s := (finite_singleton e).toFinset)
    (by simp_all [toClosedBall, restrict_apply, single_apply])]
  simp only [toFinite_toFinset, toFinset_singleton, Finset.sum_singleton]
  rw [toClosedBall_eval_within _ (by simpa [abs_of_nonneg ((norm_nonneg e).trans hr)])]
  by_cases he : 0 = e
  · simp [← he, single_apply]
  · simp only [single_apply, he, reduceIte, Int.cast_zero, zero_mul, add_zero,
      log_mul (ne_of_lt (lt_of_lt_of_le (norm_pos_iff.mpr (he ·.symm)) hr)).symm
      (inv_ne_zero (norm_ne_zero_iff.mpr (he ·.symm))), log_inv]
    grind

/-!
### Elementary Properties of Logarithmic Counting Functions
-/

set_option backward.isDefEq.respectTransparency.types false in
/--
The logarithmic counting function is even.
@isnad1 id=even.0h2v.s8.59c1a4377634 from=seed src=0 shape=8ecb7192 vocab=b8f78daf
-/
lemma logCounting_even [ProperSpace E] (D : locallyFinsupp E ℤ) :
    (logCounting D).Even := fun r ↦ by simp [logCounting, toClosedBall, restrict_apply]

/--
The logarithmic counting function is monotonous.
@isnad1 id=monotone.1h2v.s8.67ae1985f7cc from=seed src=0 shape=b3aa8bb8 vocab=d36e5fff
-/
lemma logCounting_mono [ProperSpace E] {D : locallyFinsupp E ℤ} (hD : 0 ≤ D) :
    MonotoneOn (logCounting D) (Ioi 0) := by
  intro a ha b hb _
  simp_all only [mem_Ioi, logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  gcongr
  · let s := (toClosedBall b D).support
    have hs : s.Finite := (toClosedBall b D).finiteSupport (isCompact_closedBall 0 |b|)
    repeat rw [finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    · gcongr 1 with z hz
      by_cases h₂z : z = 0
      · simp [h₂z]
      · have := (toClosedBall_support_subset_closedBall D (hs.mem_toFinset.1 hz))
        rw [toClosedBall_eval_within _ this]
        by_cases h₃z : z ∈ closedBall 0 |a|
        · rw [toClosedBall_eval_within _ h₃z]
          gcongr
          exact Int.cast_nonneg (hD z)
        · simp only [h₃z, not_false_eq_true, apply_eq_zero_of_notMem, Int.cast_zero, zero_mul,
            ge_iff_le]
          apply mul_nonneg (Int.cast_nonneg (hD z)) (log_nonneg _)
          apply (le_mul_inv_iff₀ (norm_pos_iff.mpr h₂z)).2
          simp_all [abs_of_pos hb]
    · intro z
      aesop
    · intro z
      simp only [support_mul, mem_inter_iff, mem_support, ne_eq, Int.cast_eq_zero, log_eq_zero,
        mul_eq_zero, inv_eq_zero, norm_eq_zero, not_or, Finite.coe_toFinset, and_imp, s]
      intro h₁ _ _ _ _
      have : z ∈ closedBall 0 |a| := mem_of_indicator_ne_zero h₁
      rw [toClosedBall_eval_within _ this] at h₁
      rwa [toClosedBall_eval_within]
      · simp_all only [abs_of_pos ha, mem_closedBall, dist_zero_right, abs_of_pos hb]
        linarith
  · exact Int.cast_nonneg (hD 0)

/--
The logarithmic counting function of a positive function with locally finite support is
asymptotically strictly monotone.
@isnad1 id=strictmo.1h3v.s8.2b31084c9f94 from=seed src=0 shape=5bf279f6 vocab=c034f24b
-/
lemma logCounting_strictMono [DecidableEq E] [ProperSpace E] {D : locallyFinsupp E ℤ} {e : E}
    (hD : single e 1 ≤ D) :
    StrictMonoOn (logCounting D) (Ioi ‖e‖) := by
  rw [(by aesop : logCounting D = logCounting (single e 1) + logCounting (D - single e 1))]
  apply StrictMonoOn.add_monotone
  · intro a ha b hb hab
    rw [mem_Ioi] at ha hb
    rw [logCounting_single_eq_log_sub_const ha.le, logCounting_single_eq_log_sub_const hb.le]
    gcongr
    exact (norm_nonneg e).trans_lt ha
  · intro a ha b hb hab
    apply logCounting_mono _ _ ((norm_nonneg e).trans_lt hb) hab
    · simp [hD]
    · simpa [mem_Ioi] using (norm_nonneg e).trans_lt ha

/--
For `1 ≤ r`, the logarithmic counting function is non-negative.
@isnad1 id=le.2h3v.s8.1861405829cb from=seed src=0 shape=a21df7bd vocab=825ac07a
-/
theorem logCounting_nonneg {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f : locallyFinsupp E ℤ} {r : ℝ} (h : 0 ≤ f) (hr : 1 ≤ r) :
    0 ≤ logCounting f r := by
  have h₃r : 0 < r := by linarith
  suffices ∀ z, 0 ≤ toClosedBall r f z * log (r * ‖z‖⁻¹) from
    add_nonneg (finsum_nonneg this) <| mul_nonneg (by simpa using h 0) (log_nonneg hr)
  intro a
  by_cases h₁a : a = 0
  · simp_all
  by_cases h₂a : a ∈ closedBall 0 |r|
  · refine mul_nonneg ?_ <| log_nonneg ?_
    · simpa [h₂a] using h a
    · simpa [mul_comm r, one_le_inv_mul₀ (norm_pos_iff.mpr h₁a), abs_of_pos h₃r] using h₂a
  · simp [apply_eq_zero_of_notMem ((toClosedBall r) _) h₂a]

/--
For `1 ≤ r`, the logarithmic counting function respects the `≤` relation.
@isnad1 id=le.2h4v.s9.4f0f6adc3e14 from=seed src=0 shape=05b5668d vocab=825ac07a
-/
theorem logCounting_le {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f₁ f₂ : locallyFinsupp E ℤ} {r : ℝ} (h : f₁ ≤ f₂) (hr : 1 ≤ r) :
    logCounting f₁ r ≤ logCounting f₂ r := by
  rw [← sub_nonneg] at h ⊢
  simpa using logCounting_nonneg h hr

/--
The logarithmic counting function respects the `≤` relation asymptotically.
@isnad1 id=eventual.1h3v.s9.ce592ec1ff58 from=seed src=0 shape=52118bf9 vocab=47b50ff5
-/
theorem logCounting_eventuallyLE {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f₁ f₂ : locallyFinsupp E ℤ} (h : f₁ ≤ f₂) :
    logCounting f₁ ≤ᶠ[atTop] logCounting f₂ := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr ↦ logCounting_le h hr

end Function.locallyFinsuppWithin

/-!
## The Logarithmic Counting Function of a Meromorphic Function
-/

namespace ValueDistribution

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

variable (f a) in
/--
The logarithmic counting function of a meromorphic function.

If `f : 𝕜 → E` is meromorphic and `a : WithTop E` is any value, this is a logarithmically weighted
measure of the number of times the function `f` takes a given value `a` within the disk `∣z∣ ≤ r`,
taking multiplicities into account.  In the special case where `a = ⊤`, it counts the poles of `f`.
-/
noncomputable def logCounting : ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact (divisor f univ)⁻.logCounting
  · exact (divisor (f · - a.untop₀) univ)⁺.logCounting

/--
Relation between `ValueDistribution.logCounting` and `locallyFinsuppWithin.logCounting`.
-/
lemma _root_.locallyFinsuppWithin.logCounting_divisor {f : ℂ → ℂ} :
    locallyFinsuppWithin.logCounting (divisor f univ) = logCounting f 0 - logCounting f ⊤ := by
  simp [logCounting, ← locallyFinsuppWithin.logCounting.map_sub]

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` is the logarithmic
counting function for the zeros of `f - a₀`.
@isnad1 id=eq.0h4v.s9.ec7504e2866f from=seed src=0 shape=b7700f73 vocab=978d3826
-/
lemma logCounting_coe :
    logCounting f a₀ = (divisor (f · - a₀) univ)⁺.logCounting := by
  simp [logCounting]

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` equals the logarithmic
counting function for the zeros of `f - a₀`.
@isnad1 id=eq.0h4v.s6.80146892b445 from=seed src=0 shape=f1b7f52e vocab=edd6471b
-/
lemma logCounting_coe_eq_logCounting_sub_const_zero :
    logCounting f a₀ = logCounting (f - fun _ ↦ a₀) 0 := by
  simp [logCounting]

/--
The logarithmic counting function `logCounting f 0` is the logarithmic counting function associated
with the zero-divisor of `f`.
@isnad1 id=eq.0h3v.s9.b894cff88440 from=seed src=0 shape=9ddf2b91 vocab=20a4519b
-/
lemma logCounting_zero :
    logCounting f 0 = (divisor f univ)⁺.logCounting := by
  simp [logCounting]

/--
The logarithmic counting function `logCounting f ⊤` is the logarithmic counting function associated
with the pole-divisor of `f`.
@isnad1 id=eq.0h3v.s9.5651f3b8f375 from=seed src=0 shape=1e166683 vocab=2187b350
-/
lemma logCounting_top :
    logCounting f ⊤ = (divisor f univ)⁻.logCounting := by
  simp [logCounting]

/--
Evaluation of the logarithmic counting function at zero yields zero.
@isnad1 id=eq.0h4v.s6.97e33afafde3 from=seed src=0 shape=eedcc274 vocab=e464ad66
-/
@[simp] lemma logCounting_eval_zero :
    logCounting f a 0 = 0 := by
  by_cases h : a = ⊤ <;> simp [logCounting, h]

/--
The logarithmic counting function associated with the divisor of `f` is the difference between
`logCounting f 0` and `logCounting f ⊤`.
@isnad1 id=eq.0h3v.s8.259aad2a87d4 from=seed src=0 shape=7fd17455 vocab=e01ec88e
-/
theorem log_counting_zero_sub_logCounting_top {f : 𝕜 → E} :
    (divisor f univ).logCounting = logCounting f 0 - logCounting f ⊤ := by
  rw [← posPart_sub_negPart (divisor f univ), logCounting_zero, logCounting_top, map_sub]

/--
The logarithmic counting function of a constant function is zero.
@isnad1 id=eq.0h4v.s6.1b1e87becfb4 from=seed src=0 shape=004653c2 vocab=e464ad66
-/
@[simp] theorem logCounting_const {c : E} {e : WithTop E} :
    logCounting (fun _ ↦ c : 𝕜 → E) e = 0 := by
  simp [logCounting]

/--
The logarithmic counting function of the constant function zero is zero.
@isnad1 id=eq.0h3v.s6.5bb0cb110b11 from=seed src=0 shape=736fe81d vocab=e464ad66
-/
@[simp] theorem logCounting_const_zero {e : WithTop E} :
    logCounting (0 : 𝕜 → E) e = 0 := logCounting_const

/--
The logarithmic counting function is even.
@isnad1 id=even.0h4v.s5.1af50bfc16ec from=seed src=0 shape=843a3247 vocab=c8e092e6
-/
theorem logCounting_even {f : 𝕜 → E} {e : WithTop E} :
    (logCounting f e).Even := by
  intro r
  by_cases h : e = ⊤ <;> simp [logCounting, h, locallyFinsuppWithin.logCounting_even _ r]

/--
The logarithmic counting function is monotonous.
@isnad1 id=monotone.0h4v.s6.68d7aed5b9db from=seed src=0 shape=bc8dcf05 vocab=391ba6d7
-/
theorem logCounting_monotoneOn {f : 𝕜 → E} {e : WithTop E} :
    MonotoneOn (logCounting f e) (Ioi 0) := by
  by_cases h : e = ⊤ <;>
    simpa [logCounting, h] using locallyFinsuppWithin.logCounting_mono (by positivity)

/--
For `1 ≤ r`, the logarithmic counting function is non-negative.
@isnad1 id=le.1h5v.s6.476cca6b5b90 from=seed src=0 shape=ec32f23d vocab=cb2df533
-/
theorem logCounting_nonneg {r : ℝ} {f : 𝕜 → E} {e : WithTop E} (hr : 1 ≤ r) :
    0 ≤ logCounting f e r := by
  by_cases h : e = ⊤
  · simp [logCounting, h, locallyFinsuppWithin.logCounting_nonneg
      (negPart_nonneg (divisor f univ)) hr]
  · simp [logCounting, h, locallyFinsuppWithin.logCounting_nonneg
      (posPart_nonneg (divisor (f · - e.untop₀) univ)) hr]

/--
The logarithmic counting function is asymptotically non-negative.
@isnad1 id=eventual.0h4v.s6.5c0ed345609a from=seed src=0 shape=1b478e7d vocab=5b59779b
-/
theorem logCounting_eventually_nonneg {f : 𝕜 → E} {e : WithTop E} :
    0 ≤ᶠ[atTop] logCounting f e := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr ↦ by simp [logCounting_nonneg hr]

/-!
## Elementary Properties of the Logarithmic Counting Function
-/

/--
If two functions differ only on a discrete set, then their logarithmic counting
functions agree.
@isnad1 id=eq.1h3v.s6.834cc45ef712 from=seed src=0 shape=30f2e51a vocab=54a82894
-/
theorem logCounting_congr_codiscrete [NormedSpace ℂ E] {f g : ℂ → E} (hfg : f =ᶠ[codiscrete ℂ] g) :
    logCounting f = logCounting g := by
  ext a : 1
  by_cases h : a = ⊤
  · simp only [logCounting, h, ↓reduceDIte]
    congr 2
    exact divisor_congr_codiscreteWithin hfg isOpen_univ
  · simp only [logCounting, h, ↓reduceDIte]
    congr 2
    apply divisor_congr_codiscreteWithin _ isOpen_univ
    filter_upwards [hfg] using by simp

/--
Relation between the logarithmic counting functions of `f` and of `f⁻¹`.
@isnad1 id=eq.0h2v.s7.7c114e38eb1b from=seed src=0 shape=baf22de1 vocab=6e160e7a
-/
@[simp] theorem logCounting_inv {f : 𝕜 → 𝕜} :
     logCounting f⁻¹ ⊤ = logCounting f 0 := by
  simp [logCounting_zero, logCounting_top]

/--
Adding an analytic function does not change the logarithmic counting function for the poles.
@isnad1 id=eq.2h4v.s7.453a77a99bf1 from=seed src=0 shape=33e2417c vocab=4b91b870
-/
theorem logCounting_add_analyticOn (hf : Meromorphic f) (hg : AnalyticOn 𝕜 g univ) :
    logCounting (f + g) ⊤ = logCounting f ⊤ := by
  simp only [logCounting, ↓reduceDIte]
  rw [hf.meromorphicOn.negPart_divisor_add_of_analyticNhdOn_right
    (isOpen_univ.analyticOn_iff_analyticOnNhd.1 hg)]

/--
Special case of `logCounting_add_analyticOn`: Adding a constant does not change the logarithmic
counting function for the poles.
@isnad1 id=eq.1h4v.s6.c685494f38f4 from=seed src=0 shape=476e56e5 vocab=494cf406
-/
@[simp] theorem logCounting_add_const (hf : Meromorphic f) :
    logCounting (f + fun _ ↦ a₀) ⊤ = logCounting f ⊤ := by
  apply logCounting_add_analyticOn hf analyticOn_const

/--
Special case of `logCounting_add_analyticOn`: Subtracting a constant does not change the logarithmic
counting function for the poles.
@isnad1 id=eq.1h4v.s6.e9ec75dd8e32 from=seed src=0 shape=476e56e5 vocab=e342a98f
-/
@[simp] theorem logCounting_sub_const (hf : Meromorphic f) :
    logCounting (f - fun _ ↦ a₀) ⊤ = logCounting f ⊤ := by
  simpa [sub_eq_add_neg] using! logCounting_add_const hf

/-!
## Behaviour under Arithmetic Operations
-/

/--
For `1 ≤ r`, the logarithmic counting function for the poles of `f + g` is less than or equal to the
sum of the logarithmic counting functions for the poles of `f` and `g`, respectively.
@isnad1 id=le.3h5v.s7.20b57004c2ae from=seed src=0 shape=2017363b vocab=27723b92
-/
theorem logCounting_add_top_le {f₁ f₂ : 𝕜 → E} {r : ℝ} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) (hr : 1 ≤ r) :
    logCounting (f₁ + f₂) ⊤ r ≤ (logCounting f₁ ⊤ + logCounting f₂ ⊤) r := by
  simp only [logCounting, ↓reduceDIte]
  rw [← locallyFinsuppWithin.logCounting.map_add]
  exact locallyFinsuppWithin.logCounting_le
    (negPart_divisor_add_le_add h₁f₁.meromorphicOn h₁f₂.meromorphicOn) hr

/--
Asymptotically, the logarithmic counting function for the poles of `f + g` is less than or equal to
the sum of the logarithmic counting functions for the poles of `f` and `g`, respectively.
@isnad1 id=eventual.2h4v.s7.2181818eb502 from=seed src=0 shape=5a2b9ea3 vocab=a3baa6c0
-/
theorem logCounting_add_top_eventuallyLE {f₁ f₂ : 𝕜 → E} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) :
    logCounting (f₁ + f₂) ⊤ ≤ᶠ[atTop] logCounting f₁ ⊤ + logCounting f₂ ⊤ := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr ↦ logCounting_add_top_le h₁f₁ h₁f₂ hr

/--
For `1 ≤ r`, the logarithmic counting function for the poles of a sum `∑ a ∈ s, f a` is less than or
equal to the sum of the logarithmic counting functions for the poles of the `f ·`.
@isnad1 id=le.2h6v.s7.d8da5826e160 from=seed src=0 shape=d7b7e4ae vocab=13b5b53b
-/
theorem logCounting_sum_top_le {α : Type*} (s : Finset α) (f : α → 𝕜 → E) {r : ℝ}
    (h₁f : ∀ a ∈ s, Meromorphic (f a)) (hr : 1 ≤ r) :
    logCounting (∑ a ∈ s, f a) ⊤ r ≤ (∑ a ∈ s, (logCounting (f a) ⊤)) r := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s ha hs =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc logCounting (f a + ∑ x ∈ s, f x) ⊤ r
      _ ≤ (logCounting (f a) ⊤ + logCounting (∑ x ∈ s, f x) ⊤) r :=
        logCounting_add_top_le (h₁f a (Finset.mem_insert_self a s))
          (Meromorphic.sum (fun σ hσ ↦ h₁f σ (Finset.mem_insert_of_mem hσ))) hr
      _ ≤ (logCounting (f a) ⊤ + ∑ x ∈ s, logCounting (f x) ⊤) r :=
        add_le_add (by trivial) (hs (fun a ha ↦ h₁f a (Finset.mem_insert_of_mem ha)))

/--
Asymptotically, the logarithmic counting function for the poles of a sum `∑ a ∈ s, f a` is less than
or equal to the sum of the logarithmic counting functions for the poles of the `f ·`.
@isnad1 id=eventual.1h5v.s7.5cad6e8a682d from=seed src=0 shape=c21c1a2e vocab=b7a9c153
-/
theorem logCounting_sum_top_eventuallyLE {α : Type*} (s : Finset α) (f : α → 𝕜 → E)
    (h₁f : ∀ a ∈ s, Meromorphic (f a)) :
    logCounting (∑ a ∈ s, f a) ⊤ ≤ᶠ[atTop] ∑ a ∈ s, (logCounting (f a) ⊤) := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr ↦ logCounting_sum_top_le s f h₁f hr

/--
For `1 ≤ r`, the logarithmic counting function for the zeros of `f * g` is less than or equal to the
sum of the logarithmic counting functions for the zeros of `f` and `g`, respectively.

Note: The statement proven here is found at the top of page 169 of [Lang: Introduction to Complex
Hyperbolic Spaces](https://link.springer.com/book/10.1007/978-1-4757-1945-1) where it is written as
an inequality between functions. This could be interpreted as claiming that the inequality holds for
ALL values of `r`, which is not true. For a counterexample, take `f₁ : z → z` and `f₂ : z → z⁻¹`.
Then,

- `logCounting f₁ 0 = log`
- `logCounting f₂ 0 = 0`
- `logCounting (f₁ * f₂) 0 = 0`

But `log r` is negative for small `r`.
@isnad1 id=le.5h4v.s8.0e2bc6725d97 from=seed src=0 shape=e04b0afc vocab=4586c167
-/
theorem logCounting_mul_zero_le {f₁ f₂ : 𝕜 → 𝕜} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) 0 r ≤ (logCounting f₁ 0 + logCounting f₂ 0) r := by
  simp only [logCounting, WithTop.zero_ne_top, reduceDIte, WithTop.untop₀_zero, sub_zero]
  rw [divisor_mul h₁f₁.meromorphicOn h₁f₂.meromorphicOn (fun z _ ↦ h₂f₁ z) (fun z _ ↦ h₂f₂ z),
    ← locallyFinsuppWithin.logCounting.map_add]
  apply locallyFinsuppWithin.logCounting_le _ hr
  apply locallyFinsuppWithin.posPart_add

/--
Asymptotically, the logarithmic counting function for the zeros of `f * g` is less than or equal to
the sum of the logarithmic counting functions for the zeros of `f` and `g`, respectively.
@isnad1 id=eventual.4h3v.s8.265255cef37a from=seed src=0 shape=0caee45a vocab=ca37940c
-/
theorem logCounting_mul_zero_eventuallyLE {f₁ f₂ : 𝕜 → 𝕜}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) 0 ≤ᶠ[atTop] logCounting f₁ 0 + logCounting f₂ 0 := by
  filter_upwards [eventually_ge_atTop 1] using
    fun _ hr ↦ logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
For `1 ≤ r`, the logarithmic counting function for the poles of `f * g` is less than or equal to the
sum of the logarithmic counting functions for the poles of `f` and `g`, respectively.
@isnad1 id=le.5h4v.s8.1237eba72bc9 from=seed src=0 shape=7a5b4d93 vocab=4586c167
-/
theorem logCounting_mul_top_le {f₁ f₂ : 𝕜 → 𝕜} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) ⊤ r ≤ (logCounting f₁ ⊤ + logCounting f₂ ⊤) r := by
  simp only [logCounting, reduceDIte]
  rw [divisor_mul h₁f₁.meromorphicOn h₁f₂.meromorphicOn (fun z _ ↦ h₂f₁ z) (fun z _ ↦ h₂f₂ z),
    ← locallyFinsuppWithin.logCounting.map_add]
  apply locallyFinsuppWithin.logCounting_le _ hr
  apply locallyFinsuppWithin.negPart_add

/--
Asymptotically, the logarithmic counting function for the zeros of `f * g` is less than or equal to
the sum of the logarithmic counting functions for the zeros of `f` and `g`, respectively.
@isnad1 id=eventual.4h3v.s8.33cf360e0053 from=seed src=0 shape=7dd8b43a vocab=ca37940c
-/
theorem logCounting_mul_top_eventuallyLE {f₁ f₂ : 𝕜 → 𝕜}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    logCounting (f₁ * f₂) ⊤ ≤ᶠ[atTop] logCounting f₁ ⊤ + logCounting f₂ ⊤ := by
  filter_upwards [eventually_ge_atTop 1] using
    fun _ hr ↦ logCounting_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
For natural numbers `n`, the logarithmic counting function for the zeros of `f ^ n` equals `n`
times the logarithmic counting function for the zeros of `f`.
@isnad1 id=eq.1h3v.s7.930f5cfde34f from=seed src=0 shape=6b39b447 vocab=b05bf2f0
-/
@[simp] theorem logCounting_pow_zero {f : 𝕜 → 𝕜} {n : ℕ} (hf : Meromorphic f) :
    logCounting (f ^ n) 0 = n • logCounting f 0 := by
  simp [logCounting, divisor_fun_pow hf.meromorphicOn n]

/--
For natural numbers `n`, the logarithmic counting function for the poles of `f ^ n` equals `n` times
the logarithmic counting function for the poles of `f`.
@isnad1 id=eq.1h3v.s7.930faac368d1 from=seed src=0 shape=49245c7c vocab=2769ba0e
-/
@[simp] theorem logCounting_pow_top {f : 𝕜 → 𝕜} {n : ℕ} (hf : Meromorphic f) :
    logCounting (f ^ n) ⊤ = n • logCounting f ⊤ := by
  simp [logCounting, divisor_pow hf.meromorphicOn n]

end ValueDistribution

/-!
## Representation by Integrals

For `𝕜 = ℂ`, the theorems below describe the logarithmic counting function in terms of circle
averages.
-/

/--
Over the complex numbers, present the logarithmic counting function attached to the divisor of a
meromorphic function `f` as a circle average over `log ‖f ·‖`.

This is a reformulation of Jensen's formula of complex analysis. See
`MeromorphicOn.circleAverage_log_norm` for Jensen's formula in the original context.
@isnad1 id=eq.2h2v.s8.364d906523e7 from=seed src=0 shape=43dd6b14 vocab=b37faee3
-/
theorem Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const {R : ℝ}
    {f : ℂ → ℂ} (h : Meromorphic f) (hR : R ≠ 0) :
    logCounting (divisor f univ) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have h₁f : MeromorphicOn f (closedBall 0 |R|) := by tauto
  simp only [MeromorphicOn.circleAverage_log_norm hR h₁f, logCounting, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, zero_sub, norm_neg, add_sub_cancel_right]
  congr 1
  · simp_all
  · rw [divisor_apply, divisor_apply]
    all_goals aesop

/--
Variant of `locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const`, using
`ValueDistribution.logCounting` instead of `locallyFinsuppWithin.logCounting`.
@isnad1 id=eq.2h2v.s7.c5ec612ef698 from=seed src=0 shape=e64dd9d0 vocab=219ff817
-/
theorem ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const {R : ℝ}
    {f : ℂ → ℂ} (h : Meromorphic f) (hR : R ≠ 0) :
    (logCounting f 0 - logCounting f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  rw [← locallyFinsuppWithin.logCounting_divisor]
  exact locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const h hR
