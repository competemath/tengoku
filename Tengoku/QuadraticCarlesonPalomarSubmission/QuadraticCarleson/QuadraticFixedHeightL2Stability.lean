/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.QuadraticFixedHeightAveragingNorm
import Tengoku.Seed.MeasureTheory.Function.LpSpace.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stability of the genuine fixed-height quadratic maximal operator

The real-modulation supremum is unchanged, pointwise everywhere, by changing
the input on a null set. Its real-valued representative has the same L² decay
and satisfies a quantitative difference estimate. These are consequences of
the proved c = 2 estimate, not additional hypotheses on the operator.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson

/-- Null modifications of the input do not change any output point.
@isnad1 id=eq.1h3v.s5.31f45b8e5045 from=translated src=- shape=c331f84e vocab=0c40a1ee
-/
theorem paperFixedHeightQuadraticMaximal_congr_ae (height : ℕ)
    {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g) :
    paperFixedHeightQuadraticMaximal height f =
      paperFixedHeightQuadraticMaximal height g := by
  rw [paperFixedHeightQuadraticMaximal_eq_real, paperFixedHeightQuadraticMaximal_eq_real]
  funext x
  apply iSup_congr
  intro lam
  congr 1
  exact integral_congr_ae (hfg.mono fun t ht ↦ by dsimp only; rw [ht])

/--
@isnad1 id=hascompa.1h2v.s4.b83e1b647161 from=translated src=- shape=deab8f17 vocab=8383bb42
-/
theorem hasCompactSupport_fixedHeightQuadraticKernel
    (lam : ℝ) (height : ℕ) (hlam : lam ≠ 0) :
    HasCompactSupport (fixedHeightQuadraticKernel lam height hlam) := by
  exact (hasCompactSupport_complex_dyadicPsi
    (oscillatoryScaleIndex lam height hlam)).mul_right

/-- At every point the individual integrals are genuine Bochner integrals.
@isnad1 id=integrab.2h4v.s7.fafd87a6142e from=translated src=- shape=a4e51acc vocab=3267822f
-/
theorem integrable_fixedHeightQuadraticKernel_row (height : ℕ)
    (lam : ℝ) (hlam : lam ≠ 0) {f : ℝ → ℂ} (hf : MemLp f 2) (x : ℝ) :
    Integrable (fun t ↦ fixedHeightQuadraticKernel lam height hlam (x - t) * f t) :=
  integrable_convolution_row_of_memLp (continuous_fixedHeightQuadraticKernel lam height hlam)
    (hasCompactSupport_fixedHeightQuadraticKernel lam height hlam) hf x

/--
@isnad1 id=le.2h4v.s7.4ddfe9033097 from=translated src=- shape=75ab11aa vocab=4243dfb4
-/
theorem paperFixedHeightQuadraticMaximal_add_le (height : ℕ)
    {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) (x : ℝ) :
    paperFixedHeightQuadraticMaximal height (f + g) x ≤
      paperFixedHeightQuadraticMaximal height f x +
        paperFixedHeightQuadraticMaximal height g x := by
  simp only [paperFixedHeightQuadraticMaximal_eq_real, realFixedHeightQuadraticMaximal]
  apply iSup_le
  intro lam
  simp only [Pi.add_apply, mul_add]
  rw [integral_add (integrable_fixedHeightQuadraticKernel_row height _ _ hf x)
    (integrable_fixedHeightQuadraticKernel_row height _ _ hg x)]
  exact (enorm_add_le _ _).trans (add_le_add
    (le_iSup (fun lam : {lam : ℝ // lam ≠ 0} ↦
      ‖∫ t, fixedHeightQuadraticKernel lam.val height lam.property (x - t) * f t‖ₑ) lam)
    (le_iSup (fun lam : {lam : ℝ // lam ≠ 0} ↦
      ‖∫ t, fixedHeightQuadraticKernel lam.val height lam.property (x - t) * g t‖ₑ) lam))

/--
@isnad1 id=eq.0h2v.s4.e2f26fb2ce30 from=translated src=- shape=10b66584 vocab=9018df2f
-/
theorem paperFixedHeightQuadraticMaximal_neg (height : ℕ) (f : ℝ → ℂ) :
    paperFixedHeightQuadraticMaximal height (-f) =
      paperFixedHeightQuadraticMaximal height f := by
  funext x
  simp only [paperFixedHeightQuadraticMaximal_eq_real, realFixedHeightQuadraticMaximal,
    Pi.neg_apply, mul_neg, integral_neg, enorm_neg]

/-- Exact complex scalar homogeneity of the unrestricted real supremum.
@isnad1 id=eq.0h4v.s6.08210f7b76eb from=translated src=- shape=2e2026d0 vocab=f6215a25
-/
theorem paperFixedHeightQuadraticMaximal_const_mul (height : ℕ)
    (f : ℝ → ℂ) (c : ℂ) (x : ℝ) :
    paperFixedHeightQuadraticMaximal height (fun t ↦ c * f t) x =
      ‖c‖ₑ * paperFixedHeightQuadraticMaximal height f x := by
  simp only [paperFixedHeightQuadraticMaximal_eq_real, realFixedHeightQuadraticMaximal]
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro lam
  have hi : (∫ t, fixedHeightQuadraticKernel lam.val height lam.property (x - t) *
      (c * f t)) = c * ∫ t,
        fixedHeightQuadraticKernel lam.val height lam.property (x - t) * f t := by
    simp_rw [mul_left_comm _ c]
    exact integral_const_mul c _
  rw [hi, enorm_mul]

/--
@isnad1 id=le.2h4v.s7.cc2681ccf19a from=translated src=- shape=d3e2e136 vocab=b534ce9b
-/
theorem paperFixedHeightQuadraticMaximal_le_add_sub (height : ℕ)
    {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) (x : ℝ) :
    paperFixedHeightQuadraticMaximal height f x ≤
      paperFixedHeightQuadraticMaximal height g x +
        paperFixedHeightQuadraticMaximal height (f - g) x := by
  have h := paperFixedHeightQuadraticMaximal_add_le height hg (hf.sub hg) x
  simpa only [add_sub_cancel] using h

/--
@isnad1 id=eventual.1h2v.s6.b9c4494fbf06 from=translated src=- shape=417a3eed vocab=8dcb2286
-/
theorem ae_paperFixedHeightQuadraticMaximal_lt_top (height : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    ∀ᵐ x, paperFixedHeightQuadraticMaximal height f x < ∞ := by
  have hnorm := (memLp_paperFixedHeightQuadraticMaximal height hf).eLpNorm_lt_top
  have hsq : (∫⁻ x, paperFixedHeightQuadraticMaximal height f x ^ 2) < ∞ := by
    simpa only [eLpNorm_two_sq_lintegral, enorm_eq_self] using
      ENNReal.pow_lt_top (n := 2) hnorm
  have ha := ae_lt_top
    ((measurable_paperFixedHeightQuadraticMaximal height hf).pow_const 2) hsq.ne
  filter_upwards [ha] with x hx
  simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hx

/-- The ordinary real-valued representative; its value at infinite outputs
is irrelevant since the preceding theorem proves their nullity.-/
noncomputable def paperFixedHeightQuadraticMaximalReal
    (height : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  (paperFixedHeightQuadraticMaximal height f x).toReal

/--
@isnad1 id=measurab.1h2v.s6.405ce215bc9d from=translated src=- shape=beb7f001 vocab=53d12b78
-/
theorem measurable_paperFixedHeightQuadraticMaximalReal (height : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    Measurable (paperFixedHeightQuadraticMaximalReal height f) :=
  (measurable_paperFixedHeightQuadraticMaximal height hf).ennreal_toReal

/--
@isnad1 id=memlp.1h2v.s7.eba073624684 from=translated src=- shape=afe8df5b vocab=cb96df02
-/
theorem memLp_paperFixedHeightQuadraticMaximalReal (height : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    MemLp (paperFixedHeightQuadraticMaximalReal height f) 2 := by
  apply (memLp_paperFixedHeightQuadraticMaximal height hf).of_le_enorm
    (measurable_paperFixedHeightQuadraticMaximalReal height hf).aestronglyMeasurable
  filter_upwards [] with x
  simp only [paperFixedHeightQuadraticMaximalReal, enorm_eq_self, Real.enorm_eq_ofReal_abs,
    abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

/--
@isnad1 id=eq.1h2v.s7.2486d5ff29cd from=translated src=- shape=7914b725 vocab=2a18bdc3
-/
theorem paperFixedHeightQuadraticMaximalReal_eLpNorm_eq (height : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    eLpNorm (paperFixedHeightQuadraticMaximalReal height f) 2 =
      eLpNorm (paperFixedHeightQuadraticMaximal height f) 2 := by
  apply eLpNorm_congr_enorm_ae
  filter_upwards [ae_paperFixedHeightQuadraticMaximal_lt_top height hf] with x hx
  exact Real.enorm_toReal hx.ne

/-- The familiar pointwise difference bound holds on a common conull set;
no continuity is claimed across modulation-scale jumps.
@isnad1 id=eventual.2h3v.s7.b81e6cc7eafd from=translated src=- shape=d8d8bbb0 vocab=53266706
-/
theorem ae_abs_paperFixedHeightQuadraticMaximalReal_sub_le (height : ℕ)
    {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    ∀ᵐ x, |paperFixedHeightQuadraticMaximalReal height f x -
      paperFixedHeightQuadraticMaximalReal height g x| ≤
        paperFixedHeightQuadraticMaximalReal height (f - g) x := by
  filter_upwards [ae_paperFixedHeightQuadraticMaximal_lt_top height hf,
    ae_paperFixedHeightQuadraticMaximal_lt_top height hg,
    ae_paperFixedHeightQuadraticMaximal_lt_top height (hf.sub hg)] with x hfx hgx hd
  have h₁ := paperFixedHeightQuadraticMaximal_le_add_sub height hf hg x
  have h₂ := paperFixedHeightQuadraticMaximal_le_add_sub height hg hf x
  have hneg : paperFixedHeightQuadraticMaximal height (g - f) =
      paperFixedHeightQuadraticMaximal height (f - g) := by
    rw [← neg_sub f g, paperFixedHeightQuadraticMaximal_neg]
  rw [hneg] at h₂
  have ht₁ := (ENNReal.toReal_le_toReal hfx.ne (ENNReal.add_ne_top.mpr
    ⟨hgx.ne, hd.ne⟩)).mpr h₁
  have ht₂ := (ENNReal.toReal_le_toReal hgx.ne (ENNReal.add_ne_top.mpr
    ⟨hfx.ne, hd.ne⟩)).mpr h₂
  rw [ENNReal.toReal_add hgx.ne hd.ne] at ht₁
  rw [ENNReal.toReal_add hfx.ne hd.ne] at ht₂
  dsimp only [paperFixedHeightQuadraticMaximalReal]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- L² stability with exactly the proved fixed-height decay constant.
@isnad1 id=le.2h3v.s8.bd16788bb346 from=translated src=- shape=f975ec49 vocab=c1d2d6ab
-/
theorem paperFixedHeightQuadraticMaximalReal_sub_eLpNorm_decay (height : ℕ)
    {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    eLpNorm (paperFixedHeightQuadraticMaximalReal height f -
      paperFixedHeightQuadraticMaximalReal height g) 2 ≤
        ENNReal.ofReal (fixedHeightL2DecayConstant *
          (2 : ℝ) ^ (-(height : ℝ) / 10)) * eLpNorm (f - g) 2 := by
  have hbound := paperFixedHeightQuadraticMaximal_eLpNorm_decay height
    (f := f - g) (hf.sub hg)
  apply le_trans _ hbound
  apply eLpNorm_mono_enorm_ae
  filter_upwards [ae_abs_paperFixedHeightQuadraticMaximalReal_sub_le height hf hg]
    with x hx
  simp only [Pi.sub_apply, Real.enorm_eq_ofReal_abs, enorm_eq_self]
  exact (ENNReal.ofReal_le_ofReal hx).trans ENNReal.ofReal_toReal_le

/-- The actual maximal operator on equivalence classes of L² functions.-/
noncomputable def paperFixedHeightQuadraticMaximalLp (height : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℝ 2 (volume : Measure ℝ) :=
  (memLp_paperFixedHeightQuadraticMaximalReal height (Lp.memLp f)).toLp
    (paperFixedHeightQuadraticMaximalReal height f)

/-- This representative is the genuine real-modulation supremum almost
everywhere, rather than an abstract extension chosen from a dense domain.
@isnad1 id=eventual.0h2v.s9.e7974e45913b from=translated src=- shape=7d288413 vocab=59f7107d
-/
theorem paperFixedHeightQuadraticMaximalLp_coeFn (height : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (paperFixedHeightQuadraticMaximalLp height f : ℝ → ℝ) =ᵐ[volume]
      paperFixedHeightQuadraticMaximalReal height f :=
  MemLp.coeFn_toLp _

/-- The L² map agrees with the original formula for every L² input, including
inputs that are only almost everywhere strongly measurable.
@isnad1 id=eventual.1h2v.s8.b90c87ba0585 from=translated src=- shape=a55f603d vocab=5415a44a
-/
theorem paperFixedHeightQuadraticMaximalLp_toLp_coeFn (height : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2) :
    (paperFixedHeightQuadraticMaximalLp height (hf.toLp f) : ℝ → ℝ) =ᵐ[volume]
      paperFixedHeightQuadraticMaximalReal height f := by
  have h := paperFixedHeightQuadraticMaximal_congr_ae height hf.coeFn_toLp
  apply (paperFixedHeightQuadraticMaximalLp_coeFn height (hf.toLp f)).trans
  exact Filter.Eventually.of_forall fun x ↦ congrArg ENNReal.toReal (congrFun h x)

/--
@isnad1 id=le.0h2v.s12.91027fd245c5 from=translated src=- shape=009f5616 vocab=220fb618
-/
theorem paperFixedHeightQuadraticMaximalLp_enorm_decay (height : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖paperFixedHeightQuadraticMaximalLp height f‖ₑ ≤
      ENNReal.ofReal (fixedHeightL2DecayConstant *
        (2 : ℝ) ^ (-(height : ℝ) / 10)) * ‖f‖ₑ := by
  rw [paperFixedHeightQuadraticMaximalLp, Lp.enorm_toLp, Lp.enorm_def,
    paperFixedHeightQuadraticMaximalReal_eLpNorm_eq height (Lp.memLp f)]
  exact paperFixedHeightQuadraticMaximal_eLpNorm_decay height (Lp.memLp f)

/-- Quantitative Lipschitz continuity in L², retaining the c = 2 decay.
@isnad1 id=lipschit.0h1v.s10.3d703ae8da9a from=translated src=- shape=8423386b vocab=491aca93
-/
theorem lipschitzWith_paperFixedHeightQuadraticMaximalLp (height : ℕ) :
    LipschitzWith (Real.toNNReal (fixedHeightL2DecayConstant *
      (2 : ℝ) ^ (-(height : ℝ) / 10)))
        (paperFixedHeightQuadraticMaximalLp height) := by
  intro f g
  change edist ((memLp_paperFixedHeightQuadraticMaximalReal height (Lp.memLp f)).toLp _)
    ((memLp_paperFixedHeightQuadraticMaximalReal height (Lp.memLp g)).toLp _) ≤ _
  rw [Lp.edist_toLp_toLp, Lp.edist_def]
  exact paperFixedHeightQuadraticMaximalReal_sub_eLpNorm_decay height
    (f := (f : ℝ → ℂ)) (g := (g : ℝ → ℂ)) (Lp.memLp f) (Lp.memLp g)

/--
@isnad1 id=continuo.0h1v.s11.af562aef07d3 from=translated src=- shape=b163c43f vocab=853b750a
-/
theorem continuous_paperFixedHeightQuadraticMaximalLp (height : ℕ) :
    Continuous (paperFixedHeightQuadraticMaximalLp height) :=
  (lipschitzWith_paperFixedHeightQuadraticMaximalLp height).continuous

end QuadraticCarleson
