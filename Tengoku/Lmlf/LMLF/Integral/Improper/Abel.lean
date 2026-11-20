import Tengoku.Lmlf.LMLF.Integral.Improper.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Tengoku.Seed.MeasureTheory.Integral.Prod
import Tengoku.Seed.MeasureTheory.Integral.IntegralEqImproper

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter MeasureTheory Set
open scoped Interval

noncomputable section

namespace LMLF.Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem intervalIntegral_weighted_primitive_fubini
    [CompleteSpace E] {g : ℝ → E} {w : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : IntervalIntegrable g volume a b)
    (hw : ContinuousOn w (Icc a b)) :
    ∫ t in a..b, w t • (∫ v in a..t, g v) =
      ∫ v in a..b, (∫ t in v..b, w t) • g v := by
  let ν := volume.restrict (uIoc a b)
  let K : ℝ → ℝ → E :=
    fun t v => {v | v ≤ t}.indicator (fun v => w t • g v) v
  have hwi : Integrable w ν :=
    intervalIntegrable_iff.mp (hw.intervalIntegrable_of_Icc hab)
  have hgi : Integrable g ν := intervalIntegrable_iff.mp hg
  have hbase : Integrable (fun z : ℝ × ℝ => w z.1 • g z.2) (ν.prod ν) :=
    hwi.smul_prod hgi
  let tri : Set (ℝ × ℝ) := {z | z.2 ≤ z.1}
  have htri : MeasurableSet tri :=
    measurableSet_le measurable_snd measurable_fst
  have hK : Integrable (Function.uncurry K) (ν.prod ν) := by
    change Integrable
      (tri.indicator (fun z : ℝ × ℝ => w z.1 • g z.2)) (ν.prod ν)
    exact hbase.indicator htri
  have hleft (t : ℝ) (ht : t ∈ Icc a b) :
      ∫ v, K t v ∂ν = w t • ∫ v in a..t, g v := by
    dsimp [K, ν]
    simp only [uIoc_of_le hab]
    rw [← intervalIntegral.integral_of_le hab]
    rw [intervalIntegral.integral_indicator ht]
    exact intervalIntegral.integral_smul _ _
  have hright (v : ℝ) (hv : v ∈ Ioc a b) :
      ∫ t in a..b, K t v = (∫ t in v..b, w t) • g v := by
    dsimp [K]
    change (∫ t in a..b, (Ici v).indicator (fun t => w t • g v) t) = _
    rw [intervalIntegral.integral_of_le hab]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ici]
    have hset : Ioc a b ∩ Ici v = Icc v b := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, htb⟩, hvt⟩
        exact ⟨hvt, htb⟩
      · rintro ⟨hvt, htb⟩
        exact ⟨⟨hv.1.trans_le hvt, htb⟩, hvt⟩
    rw [hset]
    rw [MeasureTheory.setIntegral_congr_set
      (Ioc_ae_eq_Icc (a := v) (b := b)).symm]
    rw [← intervalIntegral.integral_of_le hv.2]
    exact intervalIntegral.integral_smul_const _ _
  have hswap :
      (∫ t in a..b, (∫ v, K t v ∂ν) ∂volume) =
        (∫ v, (∫ t in a..b, K t v ∂volume) ∂ν) :=
    MeasureTheory.intervalIntegral_integral_swap
      (a := a) (b := b) (μ := ν) hK
  calc
    ∫ t in a..b, w t • (∫ v in a..t, g v) =
        (∫ t in a..b, (∫ v, K t v ∂ν) ∂volume) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact (hleft t (by simpa [uIcc_of_le hab] using ht)).symm
    _ = (∫ v, (∫ t in a..b, K t v ∂volume) ∂ν) := hswap
    _ = ∫ v in a..b, ∫ t in a..b, K t v := by
      dsimp [ν]
      rw [uIoc_of_le hab]
      exact (intervalIntegral.integral_of_le hab).symm
    _ = ∫ v in a..b, (∫ t in v..b, w t) • g v := by
      apply intervalIntegral.integral_congr_ae
      refine Eventually.of_forall fun v hv => ?_
      rw [uIoc_of_le hab] at hv
      exact hright v hv

private theorem exp_mul_intervalIntegral (h : ℝ) {u v : ℝ} (huv : u ≤ v) :
    h * ∫ t in u..v, Real.exp (-h * t) =
      Real.exp (-h * u) - Real.exp (-h * v) := by
  let w : ℝ → ℝ := fun t => Real.exp (-h * t)
  have hwderiv (t : ℝ) : HasDerivAt w (-h * w t) t := by
    simpa only [w, id_eq, neg_mul, mul_one, mul_neg, mul_comm] using
      ((hasDerivAt_id t).const_mul (-h)).exp
  have hwcont : Continuous w :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hw'int : IntervalIntegrable (fun t => -h * w t) volume u v :=
    (continuous_const.mul hwcont).intervalIntegrable u v
  have hftc : ∫ t in u..v, -h * w t = w v - w u :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
      hwcont.continuousOn (fun t _ => hwderiv t) hw'int
  rw [intervalIntegral.integral_const_mul] at hftc
  dsimp [w] at hftc ⊢
  linarith

private theorem intervalIntegral_exp_smul_primitive
    [CompleteSpace E] {g F : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b)
    (hF : ContinuousOn F (Icc a b))
    (hinc : ∀ t ∈ Icc a b, F t - F a = ∫ v in a..t, g v)
    (h : ℝ) :
    ∫ t in a..b, Real.exp (-h * t) • g t =
      Real.exp (-h * b) • F b - Real.exp (-h * a) • F a +
        h • ∫ t in a..b, Real.exp (-h * t) • F t := by
  let w : ℝ → ℝ := fun t => Real.exp (-h * t)
  let G : ℝ → E := fun t => ∫ v in a..t, g v
  have hwcont : Continuous w :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hwg : IntervalIntegrable (fun t => w t • g t) volume a b :=
    hg.continuousOn_smul hwcont.continuousOn
  have hGInt : IntervalIntegrable G volume a b := by
    have hGcont : ContinuousOn G (Icc a b) := by
      simpa only [G, uIcc_of_le hab] using
        intervalIntegral.continuousOn_primitive_interval' hg
          (by simpa [uIcc_of_le hab] using
            (show a ∈ Icc a b from ⟨le_rfl, hab⟩))
    exact hGcont.intervalIntegrable_of_Icc hab
  have hwG : IntervalIntegrable (fun t => w t • G t) volume a b :=
    hGInt.continuousOn_smul hwcont.continuousOn
  have hwF : IntervalIntegrable (fun t => w t • F t) volume a b :=
    (hwcont.continuousOn.smul hF).intervalIntegrable_of_Icc hab
  have htri :
      ∫ t in a..b, w t • G t =
        ∫ v in a..b, (∫ t in v..b, w t) • g v := by
    exact intervalIntegral_weighted_primitive_fubini hab hg hwcont.continuousOn
  have hscaledG :
      h • ∫ t in a..b, w t • G t =
        ∫ v in a..b, (w v - w b) • g v := by
    calc
      h • ∫ t in a..b, w t • G t =
          h • ∫ v in a..b, (∫ t in v..b, w t) • g v :=
        congrArg (fun z : E => h • z) htri
      _ = ∫ v in a..b, h • ((∫ t in v..b, w t) • g v) := by
        rw [intervalIntegral.integral_smul]
      _ = ∫ v in a..b, (w v - w b) • g v := by
        apply intervalIntegral.integral_congr
        intro v hv
        change h • ((∫ t in v..b, w t) • g v) = (w v - w b) • g v
        have hvb : v ≤ b := (by simpa [uIcc_of_le hab] using hv : v ∈ Icc a b).2
        rw [smul_smul, exp_mul_intervalIntegral h hvb]
  have hscaledG' :
      h • ∫ t in a..b, w t • G t =
        (∫ v in a..b, w v • g v) - w b • (∫ v in a..b, g v) := by
    rw [hscaledG]
    have hwbg : IntervalIntegrable (fun v => w b • g v) volume a b := by
      change IntervalIntegrable (w b • g) volume a b
      exact hg.smul (w b)
    rw [show (fun v => (w v - w b) • g v) =
        (fun v => w v • g v - w b • g v) by
      funext v
      exact sub_smul (w v) (w b) (g v)]
    rw [intervalIntegral.integral_sub hwg hwbg]
    rw [intervalIntegral.integral_smul]
  have hconst :
      h • ∫ t in a..b, w t • F a = (w a - w b) • F a := by
    rw [intervalIntegral.integral_smul_const]
    rw [smul_smul, exp_mul_intervalIntegral h hab]
  have hdecomp :
      ∫ t in a..b, w t • F t =
        (∫ t in a..b, w t • F a) + ∫ t in a..b, w t • G t := by
    have hconstInt : IntervalIntegrable (fun t => w t • F a) volume a b :=
      (hwcont.smul continuous_const).intervalIntegrable a b
    rw [← intervalIntegral.integral_add hconstInt hwG]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc a b := by simpa [uIcc_of_le hab] using ht
    have hFt : F t = F a + G t := by
      dsimp [G]
      have := hinc t ht'
      rw [sub_eq_iff_eq_add] at this
      simpa only [add_comm] using this
    change w t • F t = w t • F a + w t • G t
    rw [hFt, smul_add]
  have hFb : ∫ t in a..b, g t = F b - F a := by
    simpa using (hinc b ⟨hab, le_rfl⟩).symm
  rw [hdecomp, smul_add, hconst, hscaledG', hFb]
  dsimp [w]
  module

private theorem transformedPrimitivePackage
    [CompleteSpace E] {g F : ℝ → E} {k : ℝ} {S : Finset ℝ}
    (hF : IsFiniteExceptionalPrimitive g k S F) (h : ℝ)
    (hInt : IntegrableOn (fun t => Real.exp (-h * t) • F t) (Ioi k))
    (hLim : Tendsto (fun R => Real.exp (-h * R) • F R)
      atTop (nhds 0)) :
    let G := fun t =>
      Real.exp (-h * t) • F t +
        h • ∫ u in k..t, Real.exp (-h * u) • F u
    IsFiniteExceptionalPrimitive
        (fun t => Real.exp (-h * t) • g t) k S G ∧
      Tendsto G atTop
        (nhds (h • ∫ u in Ioi k, Real.exp (-h * u) • F u)) := by
  dsimp only
  let w : ℝ → ℝ := fun t => Real.exp (-h * t)
  let q : ℝ → E := fun t => w t • F t
  let Q : ℝ → E := fun t => ∫ u in k..t, q u
  let G : ℝ → E := fun t => q t + h • Q t
  have hwcont : Continuous w :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hqcont : ContinuousOn q (Ici k) :=
    hwcont.continuousOn.smul hF.2.1
  have hQcont : ContinuousOn Q (Ici k) := by
    have htail := hInt.continuousOn_Ici_primitive_Ioi
    exact (continuousOn_const.sub htail).congr fun t ht =>
      (intervalIntegral.integral_Ioi_sub_Ioi hInt ht).symm
  have hGcont : ContinuousOn G (Ici k) :=
    hqcont.add (hQcont.const_smul h)
  have hGzero : G k = 0 := by
    simp [G, Q, q, w, hF.2.2.1]
  have hGprim : IsFiniteExceptionalPrimitive
      (fun t => Real.exp (-h * t) • g t) k S G := by
    refine ⟨hF.1, hGcont, hGzero, ?_⟩
    intro a b hka hab hdisj
    rcases hF.2.2.2 hka hab hdisj with ⟨hgInt, hFab⟩
    have hFcont : ContinuousOn F (Icc a b) :=
      hF.2.1.mono (fun t ht => hka.trans ht.1)
    have hinc : ∀ t ∈ Icc a b, F t - F a = ∫ v in a..t, g v := by
      intro t ht
      have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
      have hdisj' : Disjoint (Icc a t) (↑S : Set ℝ) :=
        hdisj.mono hsub Subset.rfl
      exact (hF.2.2.2 hka ht.1 hdisj').2
    have hAbel :=
      intervalIntegral_exp_smul_primitive hab hgInt hFcont hinc h
    have hweightedInt : IntervalIntegrable
        (fun t => Real.exp (-h * t) • g t) volume a b :=
      hgInt.continuousOn_smul hwcont.continuousOn
    have hkaOn : IntegrableOn q (Ioc k a) := by
      exact hInt.mono_set (fun x hx => hx.1)
    have habOn : IntegrableOn q (Ioc a b) := by
      exact hInt.mono_set (fun x hx => lt_of_le_of_lt hka hx.1)
    have hkaInt : IntervalIntegrable q volume k a :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hka).2 hkaOn
    have habInt : IntervalIntegrable q volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 habOn
    have hadd :=
      intervalIntegral.integral_add_adjacent_intervals hkaInt habInt
    refine ⟨hweightedInt, ?_⟩
    change (q b + h • Q b) - (q a + h • Q a) = _
    dsimp [Q]
    rw [← hadd]
    dsimp [q, w]
    rw [hAbel]
    module
  have hQLim : Tendsto Q atTop (nhds (∫ u in Ioi k, q u)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi k hInt tendsto_id
  have hGLim : Tendsto G atTop (nhds (h • ∫ u in Ioi k, q u)) := by
    simpa only [G, q, w, zero_add] using hLim.add (hQLim.const_smul h)
  exact ⟨hGprim, hGLim⟩

/-- IMP-001-T06.-/
theorem IsFiniteExceptionalPrimitive.hasImproperIntegralAtTopExcept_exp_smul
    [CompleteSpace E] {g F : ℝ → E} {k : ℝ} {S : Finset ℝ}
    (hF : IsFiniteExceptionalPrimitive g k S F) (h : ℝ)
    (hInt : IntegrableOn (fun t => Real.exp (-h * t) • F t) (Ioi k))
    (hLim : Tendsto (fun R => Real.exp (-h * R) • F R)
      atTop (nhds 0)) :
    HasImproperIntegralAtTopExcept
      (fun t => Real.exp (-h * t) • g t) k S
      (h • ∫ t in Ioi k, Real.exp (-h * t) • F t) := by
  apply hasImproperIntegralAtTopExcept_iff_exists_primitive.mpr
  exact ⟨_, transformedPrimitivePackage hF h hInt hLim⟩

end LMLF.Integral
