import Tengoku
import Tengoku.Xilab.XiLab.Kernel
import Tengoku.Xilab.XiLab.FGrowth
import Tengoku.Xilab.XiLab.Evenness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms XiLab.F_ofReal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.setIntegral_Phi_mul_rsinh_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.F_pos_of_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.F_ne_zero_of_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.F_ne_zero_of_real_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.F_conj` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.F_starRingEnd` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.F_zero_eq_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.zero_quartet` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.im_ne_zero_of_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.re_ne_zero_and_im_ne_zero_of_zero` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# XiLab.Symmetry — real-axis nonvanishing, conjugate symmetry, and the zero quartets

Consumes `XiLab/Kernel.lean`
(`Phi_pos`, `integrableOn_Phi_mul_rsinh`, `F`) and `XiLab/FGrowth.lean` (`F_neg`).

## Main results

* `XiLab.F_ofReal` — on the real axis the odd channel is *real*:
  `F(x) = ↑(2 ∫₀^∞ Φ(u) sinh(xu) du)` for `x : ℝ`.
* `XiLab.F_pos_of_pos` — `0 < (F x).re` for real `x > 0`.  The integrand
  `Φ(u) sinh(xu)` is strictly positive on all of `(0,∞)`, and `(0,∞)` has infinite
  measure, so the set integral is strictly positive.
* `XiLab.F_ne_zero_of_real_ne_zero` — `F x ≠ 0` for every real `x ≠ 0`.  This is the
  "no zero has vanishing imaginary part" half of Theorem 3.3.
* `XiLab.F_conj` — `F(w̄) = conj (F w)`.  `Φ` is real-valued, so conjugation passes
  through the integral.
* `XiLab.zero_quartet` — combining `F_conj` with `F_neg`, the zeros of `F` come in
  quartets `±w, ±w̄`.
* `XiLab.F_zero_eq_zero` — `F 0 = 0`.  Simplicity of that zero is **not** proved; see
  the note above `zero_quartet` for exactly what is missing.

## What is NOT here

Nonvanishing on the **imaginary** axis (`F (i t) ≠ 0` for real `t ≠ 0`) needs strict
monotone decrease of `Φ` on `[0,∞)` — Wintner's theorem — and is owned by
`XiLab/Wintner.lean` (conditionally) and `XiLab/Evenness.lean` (the `[0,∞)` upgrade).  It
is imported and used only to state the packaged Theorem 3.3 conclusion
`re w ≠ 0 ∧ im w ≠ 0`.  Every theorem in this file is `sorry`-free; see the axiom audit at
the bottom.

## Implementation note — why the positivity goes through the *real* integral

`F` is defined as a `ℂ`-valued Bochner integral, and `Complex.sinh (↑x * ↑u)` is
`↑(Real.sinh (x*u))` only after a cast juggle.  Rather than fight the cast inside the
measure-theoretic API, `F_ofReal` moves the whole integral to `ℝ` once
(`integral_complex_ofReal`), after which
`MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae` applies verbatim to the real
integrand, whose integrability is already `Kernel.integrableOn_Phi_mul_rsinh`.

The support condition is the pleasant part: the integrand is *strictly* positive at
**every** point of `(0,∞)` (not merely a.e.), so
`support f ∩ Ioi 0 = Ioi 0` and `volume (Ioi 0) = ∞ > 0`.  No Lebesgue-point or
continuity argument is needed.
-/

open scoped Real ComplexConjugate
open MeasureTheory Set Filter Topology

namespace XiLab

/-! ### `F` restricted to the real axis -/

/-- The odd-channel integrand at a **real** argument is the coercion of a real function.
@isnad1 id=eq.0h2v.s5.1dcc9090546a from=translated src=- shape=ff6a0751 vocab=7cc22716
-/
lemma integrand_ofReal (x u : ℝ) :
    (Phi u : ℂ) * Complex.sinh ((x : ℂ) * (u : ℂ))
      = ((Phi u * Real.sinh (x * u) : ℝ) : ℂ) := by
  have hxu : (x : ℂ) * (u : ℂ) = ((x * u : ℝ) : ℂ) := by push_cast; ring
  rw [hxu, ← Complex.ofReal_sinh, ← Complex.ofReal_mul]

/-- **`F` is real on the real axis.**  `F(x) = 2 ∫₀^∞ Φ(u) sinh(xu) du`, an honest real
number, coerced into `ℂ`.
@isnad1 id=eq.0h1v.s6.84d85d73aeff from=translated src=- shape=4050d475 vocab=bd1dcccd
-/
theorem F_ofReal (x : ℝ) :
    F (x : ℂ) = ((2 * ∫ u in Ioi (0:ℝ), Phi u * Real.sinh (x * u) : ℝ) : ℂ) := by
  simp only [F, integrand_ofReal]
  rw [integral_complex_ofReal]
  push_cast
  ring

/-- The real integral `∫₀^∞ Φ(u) sinh(xu) du` is **strictly positive** for `x > 0`.

Both factors are strictly positive on `(0,∞)`: `Φ(u) > 0` is `Kernel.Phi_pos` and
`sinh(xu) > 0` is `Real.sinh_pos_iff`.  Hence the support of the integrand contains all
of `(0,∞)`, which has infinite Lebesgue measure.
@isnad1 id=lt.1h1v.s6.356e1d8c2eb5 from=translated src=- shape=a47a1ef2 vocab=d7e04e5e
-/
theorem setIntegral_Phi_mul_rsinh_pos {x : ℝ} (hx : 0 < x) :
    0 < ∫ u in Ioi (0:ℝ), Phi u * Real.sinh (x * u) := by
  have hpos : ∀ u ∈ Ioi (0:ℝ), 0 < Phi u * Real.sinh (x * u) := by
    intro u hu
    have hu0 : (0:ℝ) < u := mem_Ioi.mp hu
    exact mul_pos (Phi_pos hu0.le) (Real.sinh_pos_iff.mpr (mul_pos hx hu0))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] fun u : ℝ => Phi u * Real.sinh (x * u) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact (hpos u hu).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg (integrableOn_Phi_mul_rsinh x)]
  have hsupp : Function.support (fun u : ℝ => Phi u * Real.sinh (x * u)) ∩ Ioi (0:ℝ)
      = Ioi (0:ℝ) :=
    Set.inter_eq_right.mpr fun u hu => ne_of_gt (hpos u hu)
  rw [hsupp, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- **Strict positivity of `F` on the positive real axis.**
@isnad1 id=lt.1h1v.s4.15d10aebe1cc from=translated src=- shape=35dab86f vocab=d8886d15
-/
theorem F_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < (F (x : ℂ)).re := by
  rw [F_ofReal, Complex.ofReal_re]
  have := setIntegral_Phi_mul_rsinh_pos hx
  linarith

/-- `F` does not vanish anywhere on the positive real axis.
@isnad1 id=ne.1h1v.s4.b341771be78a from=translated src=- shape=ac540e28 vocab=b0f3c6ae
-/
theorem F_ne_zero_of_pos {x : ℝ} (hx : 0 < x) : F (x : ℂ) ≠ 0 := by
  intro h
  have := F_pos_of_pos hx
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

/-- **Theorem 3.3, real-axis half.**  `F` has no zero on `ℝ \ {0}`; equivalently, every
nonzero zero of `F` has nonzero imaginary part.  For `x < 0` this is oddness
(`FGrowth.F_neg`) applied to `-x > 0`.
@isnad1 id=ne.1h1v.s4.61c4f114f091 from=translated src=- shape=f3035aa9 vocab=2abebef8
-/
theorem F_ne_zero_of_real_ne_zero {x : ℝ} (hx : x ≠ 0) : F (x : ℂ) ≠ 0 := by
  rcases hx.lt_or_gt with h | h
  · have hneg : F ((-x : ℝ) : ℂ) = -F (x : ℂ) := by
      rw [Complex.ofReal_neg, F_neg]
    intro hF
    have hp := F_ne_zero_of_pos (neg_pos.mpr h)
    rw [hneg, hF, neg_zero] at hp
    exact hp rfl
  · exact F_ne_zero_of_pos h

/-! ### Conjugate symmetry -/

/-- Pointwise conjugate symmetry of the integrand: `Φ` is real, and `sinh` commutes with
conjugation (`Complex.sinh_conj`).
@isnad1 id=eq.0h2v.s6.5b4bc0690bee from=translated src=- shape=e6ce7279 vocab=a7d926f5
-/
lemma conj_integrand (w : ℂ) (u : ℝ) :
    conj ((Phi u : ℂ) * Complex.sinh (w * u))
      = (Phi u : ℂ) * Complex.sinh ((conj w) * u) := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.sinh_conj, map_mul, Complex.conj_ofReal]

/-- **Conjugate symmetry of the odd channel.**  `F(w̄) = conj (F w)`.

The kernel `Φ` is real-valued, so `conj` passes through the Bochner integral
(`integral_conj`) and lands on `sinh` alone.
@isnad1 id=eq.0h1v.s6.d2450d8e44ae from=translated src=- shape=808f42d9 vocab=a7d29ac3
-/
theorem F_conj (w : ℂ) : F (conj w) = conj (F w) := by
  have hint : conj (∫ u in Ioi (0:ℝ), (Phi u : ℂ) * Complex.sinh (w * u))
      = ∫ u in Ioi (0:ℝ), (Phi u : ℂ) * Complex.sinh ((conj w) * u) := by
    rw [← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall (conj_integrand w))
  unfold F
  rw [map_mul, hint, map_ofNat]

/-- Restatement of `F_conj` with `starRingEnd` written out, matching the target
signature requested for this file.
@isnad1 id=eq.0h1v.s6.d2450d8e44ae from=translated src=- shape=808f42d9 vocab=a7d29ac3
-/
theorem F_starRingEnd (w : ℂ) : F (starRingEnd ℂ w) = starRingEnd ℂ (F w) := F_conj w

/-! ### The zero at the origin -/

/-- `F 0 = 0`: the odd channel kills the constant mode.
@isnad1 id=eq.0h0v.s3.38b8d23a004d from=translated src=- shape=3c26ae4f vocab=6ddee84b
-/
@[simp] theorem F_zero_eq_zero : F 0 = 0 := by
  simp [F]

/-! Simplicity of the zero at the origin is **not** proved here.  It amounts to
`F'(0) = 2 ∫₀^∞ u Φ(u) du ≠ 0`, and while the integrand is strictly positive on `(0,∞)`
so the integral is positive by the same argument as `setIntegral_Phi_mul_rsinh_pos`,
identifying that integral with `F'(0)` needs the differentiation-under-the-integral
computation of `Kernel.differentiableAt_integral_Phi_sinh` in *evaluated* form, which
that file does not expose.  Left undone rather than sketched. -/

/-! ### The quartet structure -/

/-- **Theorem 3.3, symmetry half.**  The zeros of `F` come in quartets `±w, ±w̄`.
@isnad1 id=and.1h1v.s6.45c4209dfa72 from=translated src=- shape=f10c310d vocab=22828cf7
-/
theorem zero_quartet {w : ℂ} (hw : F w = 0) :
    F (-w) = 0 ∧ F (starRingEnd ℂ w) = 0 ∧ F (-(starRingEnd ℂ w)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [F_neg, hw, neg_zero]
  · rw [F_starRingEnd, hw, map_zero]
  · rw [F_neg, F_starRingEnd, hw, map_zero, neg_zero]

/-- Every nonzero zero of `F` has **nonzero imaginary part**.  (The companion statement
for the real part needs `XiLab/Wintner.lean` + `XiLab/Evenness.lean`; see
`re_ne_zero_and_im_ne_zero_of_zero`.)
@isnad1 id=ne.2h1v.s5.3cc1b9b3139d from=translated src=- shape=592b62fc vocab=6d0cbc93
-/
theorem im_ne_zero_of_zero {w : ℂ} (hw : F w = 0) (hne : w ≠ 0) : w.im ≠ 0 := by
  intro him
  have hre : w = ((w.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hrene : w.re ≠ 0 := by
    intro h
    apply hne
    rw [hre, h, Complex.ofReal_zero]
  exact F_ne_zero_of_real_ne_zero hrene (hre ▸ hw)

/-! ### The imaginary axis

Nonvanishing of `F` on the imaginary axis is the Wintner half of Theorem 3.3.  It rests on
strict monotone decrease of `Φ` on `[0,∞)`, which is `XiLab/Wintner.lean`'s
`F_ne_zero_of_imag_of_strictAntiOn` fed by `XiLab/Evenness.lean`'s
`Phi_strictAntiOn_Ici_zero`.  Note the argument order: `Wintner` states its conclusion for
`F (↑t * I)` while the natural normal form here is `F (I * ↑t)`; `hw'` below is written in
the `↑t * I` orientation so the two match without a `mul_comm` rewrite. -/

/-- **Theorem 3.3, packaged.**  Every nonzero zero of `F` has both coordinates nonzero.
@isnad1 id=and.2h1v.s5.b6c21dc1c8b9 from=translated src=- shape=3e2a8625 vocab=3d7e93ae
-/
theorem re_ne_zero_and_im_ne_zero_of_zero {w : ℂ} (hw : F w = 0) (hne : w ≠ 0) :
    w.re ≠ 0 ∧ w.im ≠ 0 := by
  refine ⟨?_, im_ne_zero_of_zero hw hne⟩
  intro hre
  have hw' : w = (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  have hime : w.im ≠ 0 := im_ne_zero_of_zero hw hne
  exact F_ne_zero_of_imag_of_strictAntiOn Phi_strictAntiOn_Ici_zero hime (hw' ▸ hw)

end XiLab

/-! ### Target signatures, pinned verbatim -/

/-! ### Axiom audit

There is no `sorry` left anywhere in this file.  Every result below — including the
packaged `XiLab.re_ne_zero_and_im_ne_zero_of_zero` — depends solely on `propext`,
`Classical.choice`, `Quot.sound`. -/
section AxiomAudit
end AxiomAudit
