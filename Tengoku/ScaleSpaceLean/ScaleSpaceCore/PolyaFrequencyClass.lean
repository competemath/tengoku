/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.Seed.Probability.Moments.ComplexMGF
import Tengoku.Seed.Analysis.Complex.Trigonometric
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Summable
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv
import Tengoku.Seed.Analysis.SpecialFunctions.Sqrt
import Tengoku.Seed.Analysis.Analytic.OfScalars
import Tengoku.Seed.Analysis.Analytic.Uniqueness
import Tengoku.Seed.Analysis.Normed.Ring.InfiniteSum
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Topology.Algebra.InfiniteSum.NatInt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Karlin's class `E₂*` and the bilateral Laplace transform

Home: none (Karlin's class `E₂*` at its own generality, not the symmetry reduction
`PowerSumSymmetry` states for `line/selection:prop:polya-frequency`; ref: @karlin1968total, Ch. 7 §§1–2)

Karlin (*Total Positivity* I, 1968) characterises Pólya-frequency densities on the line through
the reciprocal of their bilateral Laplace transform `φ(s) = ∫ e^{-su} f(u) du`:

* Prop. 1.4, p. 333: the Laplace transform of a PF density exists in an open strip containing
  the imaginary axis;
* (2.2), p. 336: the class `E₂` of entire functions
  `e^{-γs² + δs} s^k ∏ (1 + a_i s) e^{-a_i s}` with `γ ≥ 0`, `δ` and `a_i` real and
  `∑ a_i² < ∞`; `E₂*` is the subclass with `ψ(0) = 1`, so `k = 0` and there is no constant;
* Thm. 3.2(a), p. 345: a density is PF if and only if `1/φ` is of class `E₂*` with
  `γ + ∑ a_i² > 0`.

This module states Karlin's two objects with his sign convention and proves the facts a
consumer needs to read an `E₂*` function as an exponent on the imaginary axis, all from Mathlib
alone:

* `bilateralLaplace`, with its bridges to `ProbabilityTheory.complexMGF`, to `charFun` on the
  imaginary axis, and to the real integral on the real axis;
* `polyaE2`, the `E₂*` function as a map `ℂ → ℂ`, whose defining product is multipliable at
  every point once `∑ a_j² < ∞` (`multipliable_polyaE2_factor`);
* `pairSeq`, the `±` pairing of a parameter sequence, and the value of `polyaE2` on the
  imaginary axis at a paired sequence (`polyaE2_pairSeq_mul_I`) — the sufficiency direction;
* the real-axis logarithmic form (`polyaE2_ofReal`), the modulus on the imaginary axis
  (`norm_polyaE2_mul_I`), and the symmetry reduction: evenness of `polyaE2` near `0` forces
  `δ = 0` and the vanishing of every odd power sum `∑ a_j^{2k+3}`
  (`polyaE2_even_imp_oddPowerSums`) — the necessity direction.

Nothing here is holomorphic. The real axis and the imaginary axis are treated separately, and
the symmetry reduction is read off a real power series, so no analytic continuation is used.
-/

namespace ScaleSpace

open Complex MeasureTheory

/-! ### The bilateral Laplace transform -/

/-- Karlin's bilateral Laplace transform of a measure on the line, with his sign:
`∫ e^{-su} dμ(u)` (*Total Positivity* I, Prop. 1.4, p. 333). Off the strip where the integrand
is integrable the value is Mathlib's junk value `0`.-/
noncomputable def bilateralLaplace (μ : Measure ℝ) (s : ℂ) : ℂ := ∫ x, cexp (-s * x) ∂μ

/-- The bilateral Laplace transform is Mathlib's complex moment generating function of the
identity, evaluated at `-s`.
@isnad1 id=eq.0h2v.s4.fc18903249b5 from=translated src=- shape=4468cf62 vocab=13fbee75
-/
theorem bilateralLaplace_eq_complexMGF (μ : Measure ℝ) (s : ℂ) :
    bilateralLaplace μ s = ProbabilityTheory.complexMGF id μ (-s) := rfl

/-- On the imaginary axis the bilateral Laplace transform is the characteristic function at the
reflected frequency: `L(iω) = charFun μ (-ω)`.
@isnad1 id=eq.0h2v.s5.f7ff52c3b1f2 from=translated src=- shape=7ead864e vocab=18136d60
-/
theorem bilateralLaplace_ofReal_mul_I (μ : Measure ℝ) (ω : ℝ) :
    bilateralLaplace μ (ω * I) = charFun μ (-ω) := by
  rw [bilateralLaplace_eq_complexMGF, ← ProbabilityTheory.complexMGF_id_mul_I]
  congr 1; push_cast; ring

/-- On the real axis the bilateral Laplace transform is the real integral `∫ e^{-xy} dμ(y)`.
@isnad1 id=eq.0h2v.s5.15ccc4b57c98 from=translated src=- shape=b96b05c5 vocab=a3ef3619
-/
theorem bilateralLaplace_ofReal (μ : Measure ℝ) (x : ℝ) :
    bilateralLaplace μ x = ((∫ y, Real.exp (-x * y) ∂μ : ℝ) : ℂ) := by
  rw [bilateralLaplace, ← integral_complex_ofReal]
  congr 1 with y
  simp [ofReal_exp]

/-- A reflection-invariant measure has an even bilateral Laplace transform.
@isnad1 id=eq.1h2v.s5.5bad013e1e6f from=translated src=- shape=b69e8384 vocab=3023ef76
-/
theorem bilateralLaplace_neg_of_map_neg {μ : Measure ℝ} (h : μ.map (fun x => -x) = μ)
    (s : ℂ) : bilateralLaplace μ (-s) = bilateralLaplace μ s := by
  conv_rhs => rw [bilateralLaplace, ← h]
  rw [integral_map measurable_neg.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
  simp only [bilateralLaplace]
  congr 1 with x
  push_cast; ring_nf

/-! ### The class `E₂*` -/

/-- Karlin's class `E₂*` as a function `ℂ → ℂ` (*Total Positivity* I, (2.2), p. 336):
`ψ(s) = e^{-γs² + δs} ∏_j (1 + a_j s) e^{-a_j s}`. The normalisation `ψ(0) = 1` of `E₂*` is
what removes the factor `s^k` and the constant of `E₂`; a finite parameter family is padded
by zeros. The product is multipliable at every `s` once `∑ a_j² < ∞`
(`multipliable_polyaE2_factor`), so the `tprod` is not a junk value there.-/
noncomputable def polyaE2 (γ δ : ℝ) (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  cexp (-(γ : ℂ) * s ^ 2 + δ * s) * ∏' j, (1 + (a j : ℂ) * s) * cexp (-((a j : ℂ) * s))

/-- The Weierstrass factor estimate: `‖(1 + w) e^{-w} - 1‖ ≤ e ‖w‖²` for `‖w‖ ≤ 1`.
@isnad1 id=le.1h1v.s6.ce8ecdef043a from=translated src=- shape=bafaf9a9 vocab=a9bc9a9d
-/
theorem norm_one_add_mul_cexp_neg_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(1 + w) * cexp (-w) - 1‖ ≤ Real.exp 1 * ‖w‖ ^ 2 := by
  have h1 : (1 + w) * cexp (-w) - 1 = -(cexp (-w) * (cexp w - 1 - w)) := by
    have : cexp (-w) * cexp w = 1 := by rw [← Complex.exp_add]; simp
    linear_combination this
  rw [h1, norm_neg, norm_mul]
  have h2 : ‖cexp (-w)‖ ≤ Real.exp 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (by rw [norm_neg]; exact hw))
  exact mul_le_mul h2 (Complex.norm_exp_sub_one_sub_id_le hw) (norm_nonneg _)
    (Real.exp_pos 1).le

/-- The factors of `polyaE2` are summably close to `1` when `∑ a_j² < ∞`.
@isnad1 id=summable.1h2v.s6.030499daa954 from=translated src=- shape=0d6e466d vocab=b21a09f9
-/
theorem summable_norm_polyaE2_factor_sub_one {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2)
    (s : ℂ) : Summable fun j => ‖(1 + (a j : ℂ) * s) * cexp (-((a j : ℂ) * s)) - 1‖ := by
  have hev : ∀ᶠ j in Filter.cofinite, a j ^ 2 * ‖s‖ ^ 2 ≤ 1 :=
    (ha.mul_right (‖s‖ ^ 2)).tendsto_cofinite_zero.eventually_le_const one_pos
  refine Summable.of_norm_bounded_eventually (ha.mul_left (Real.exp 1 * ‖s‖ ^ 2)) ?_
  filter_upwards [hev] with j hj
  have hn : ‖(a j : ℂ) * s‖ ^ 2 = a j ^ 2 * ‖s‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hle : ‖(a j : ℂ) * s‖ ≤ 1 := by
    rw [← hn] at hj
    exact (sq_le_one_iff₀ (norm_nonneg _)).mp hj
  rw [norm_norm]
  calc _ ≤ Real.exp 1 * ‖(a j : ℂ) * s‖ ^ 2 := norm_one_add_mul_cexp_neg_sub_one_le hle
    _ = _ := by rw [hn]; ring

/-- **Multipliability of the `E₂*` product.** For `∑ a_j² < ∞` the product defining `polyaE2`
converges at every complex `s` (*Total Positivity* I, (2.2), p. 336).
@isnad1 id=multipli.1h2v.s6.f26627da5cc3 from=translated src=- shape=dce7d5db vocab=5499e80d
-/
theorem multipliable_polyaE2_factor {a : ℕ → ℝ} (ha : Summable fun j => a j ^ 2) (s : ℂ) :
    Multipliable fun j => (1 + (a j : ℂ) * s) * cexp (-((a j : ℂ) * s)) := by
  simpa only [add_sub_cancel] using
    multipliable_one_add_of_summable (summable_norm_polyaE2_factor_sub_one ha s)

/-- A multipliable real product is carried to `ℂ` factor by factor.
@isnad1 id=eq.1h1v.s5.4c89dce21721 from=translated src=- shape=8c491560 vocab=eebf55a0
-/
theorem ofReal_tprod_of_multipliable {f : ℕ → ℝ} (hf : Multipliable f) :
    ((∏' j, f j : ℝ) : ℂ) = ∏' j, (f j : ℂ) :=
  ((hf.hasProd.map Complex.ofRealHom Complex.continuous_ofReal).tprod_eq).symm

/-! ### The `±` pairing (sufficiency) -/

/-- The `±` pairing of a parameter sequence: `pairSeq lam (2k) = lam k` and
`pairSeq lam (2k+1) = -lam k`. An `E₂*` function with these parameters and `δ = 0` is real and
even, and on the imaginary axis it is the exponential of a Pólya-frequency exponent
(`polyaE2_pairSeq_mul_I`).-/
def pairSeq (lam : ℕ → ℝ) : ℕ → ℝ := fun n => if Even n then lam (n / 2) else -lam (n / 2)

/--
@isnad1 id=eq.0h2v.s4.8134fd539542 from=translated src=- shape=bca5466d vocab=f563391f
-/
@[simp] theorem pairSeq_two_mul (lam : ℕ → ℝ) (k : ℕ) : pairSeq lam (2 * k) = lam k := by
  have h2 : 2 * k / 2 = k := by omega
  change (if Even (2 * k) then lam (2 * k / 2) else -lam (2 * k / 2)) = lam k
  rw [ite_eq_left (even_two_mul k), h2]

/--
@isnad1 id=eq.0h2v.s5.4c59ee02f9f3 from=translated src=- shape=8fddf870 vocab=1917ba68
-/
@[simp] theorem pairSeq_two_mul_add_one (lam : ℕ → ℝ) (k : ℕ) :
    pairSeq lam (2 * k + 1) = -lam k := by
  have h2 : (2 * k + 1) / 2 = k := by omega
  change (if Even (2 * k + 1) then lam ((2 * k + 1) / 2) else -lam ((2 * k + 1) / 2)) = -lam k
  rw [ite_eq_right (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)), h2]

/-- **The `E₂*` function of a paired sequence on the imaginary axis.** With `δ = 0` and
parameters `pairSeq lam`, each pair of factors multiplies to `1 + lam_i² ω²`, so
`ψ(iω) = exp (γ ω² + ∑ log (1 + lam_i² ω²))` — real, positive, and the exponential of a
Pólya-frequency exponent (*Total Positivity* I, (2.2), p. 336).
@isnad1 id=eq.1h3v.s7.bcc0a92f32b2 from=translated src=- shape=d96f8736 vocab=264eda13
-/
theorem polyaE2_pairSeq_mul_I {lam : ℕ → ℝ} (hl : Summable fun i => lam i ^ 2) (γ ω : ℝ) :
    polyaE2 γ 0 (pairSeq lam) (ω * I) =
      ((Real.exp (γ * ω ^ 2 + ∑' i, Real.log (1 + lam i ^ 2 * ω ^ 2)) : ℝ) : ℂ) := by
  unfold polyaE2
  set f : ℕ → ℂ := fun n =>
    (1 + (pairSeq lam n : ℂ) * (ω * I)) * cexp (-((pairSeq lam n : ℂ) * (ω * I))) with hf
  have hl' : Summable fun i => (-lam i) ^ 2 := by simpa [neg_sq] using hl
  have he : Multipliable fun k => f (2 * k) := by
    refine (multipliable_polyaE2_factor hl ((ω : ℂ) * I)).congr fun k => ?_
    simp only [hf, pairSeq_two_mul]
  have ho : Multipliable fun k => f (2 * k + 1) := by
    refine (multipliable_polyaE2_factor hl' ((ω : ℂ) * I)).congr fun k => ?_
    simp only [hf, pairSeq_two_mul_add_one]
  have hpair : ∀ k, f (2 * k) * f (2 * k + 1) = ((1 + lam k ^ 2 * ω ^ 2 : ℝ) : ℂ) := by
    intro k
    simp only [hf, pairSeq_two_mul, pairSeq_two_mul_add_one, ofReal_neg]
    have hexp : cexp (-((lam k : ℂ) * (ω * I))) * cexp (-(-(lam k : ℂ) * (ω * I))) = 1 := by
      rw [← Complex.exp_add,
        show -((lam k : ℂ) * (ω * I)) + -(-(lam k : ℂ) * (ω * I)) = 0 by ring, Complex.exp_zero]
    rw [ofReal_add, ofReal_one, ofReal_mul, ofReal_pow, ofReal_pow]
    linear_combination (1 - (lam k : ℂ) ^ 2 * (ω : ℂ) ^ 2 * I ^ 2) * hexp
      - (lam k : ℂ) ^ 2 * (ω : ℂ) ^ 2 * I_sq
  have hreal : Multipliable fun k => (1 + lam k ^ 2 * ω ^ 2) :=
    Real.multipliable_one_add_of_summable (hl.mul_right _)
  have hsumlog : Summable fun k => Real.log (1 + lam k ^ 2 * ω ^ 2) :=
    Real.summable_log_one_add_of_summable (hl.mul_right _)
  have h1 : (∏' k, f (2 * k)) * ∏' k, f (2 * k + 1) = ∏' n, f n := tprod_even_mul_odd he ho
  have h2 : ∏' k, f (2 * k) * f (2 * k + 1) = (∏' k, f (2 * k)) * ∏' k, f (2 * k + 1) :=
    he.tprod_mul ho
  have hprod : ∏' n, f n = ((∏' k, (1 + lam k ^ 2 * ω ^ 2) : ℝ) : ℂ) := by
    rw [← h1, ← h2, tprod_congr hpair, ofReal_tprod_of_multipliable hreal]
  have hlog : Real.exp (∑' i, Real.log (1 + lam i ^ 2 * ω ^ 2)) =
      ∏' k, (1 + lam k ^ 2 * ω ^ 2) :=
    Real.rexp_tsum_eq_tprod (fun k => by positivity) hsumlog
  rw [hprod, ← hlog, Real.exp_add, ofReal_mul]
  congr 1
  rw [ofReal_exp]
  congr 1
  push_cast
  linear_combination (-(γ : ℂ) * (ω : ℂ) ^ 2) * I_sq

/-! ### The real axis, the imaginary axis, and the symmetry reduction (necessity) -/

end ScaleSpace
