import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.Hecke.FiniteEulerFactors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.QuasiRiemann end Tengoku.QuasiRiemann open Tengoku.QuasiRiemann
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter

namespace CompactScaleBridge

open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics

noncomputable def realCompactOutsideSum
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (W : ℝ → ℂ) (D : ℝ) : ℂ :=
  ∑ I ∈ outsideIdealsUpTo S (2 * Nat.ceil D),
    baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)

structure FixedTestPrimeMSConstants
    {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (m : ℕ) (ε Cmean Ccount : ℝ) where
  H : ℕ
  selected : Finset O
  hp : ∀ p ∈ selected, p ≠ 0
  hprime : ∀ p ∈ selected, (Ideal.span {p} : Ideal O).IsMaximal
  hinj : Set.InjOn (fun p : O => (Ideal.span {p} : Ideal O)) (selected : Set O)
  hnormlower : ∀ p ∈ selected,
    ((2 * m : ℕ) : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ)
  hnormupper : ∀ p ∈ selected,
    (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤
      ((2 * m : ℕ) : ℝ) ^ (11 / 60 : ℝ)
  hH : Nat.floor (((2 * m : ℕ) : ℝ) ^ (11 / 10 : ℝ)) ≤ H
  hcount : Ccount * ((2 * m : ℕ) : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤
    (selected.card : ℝ)
  hmean :
    (∑ u ∈ rowNormDisk H,
      ‖idealRowSum (outsideIdealsUpTo S (2 * m))
          (outsideIdealsUpTo_ne_bot S (2 * m))
          (outsideIdealsUpTo_good S (2 * m) hSbad)
          χ (fixedTestWeight W m) u‖ ^ 2) ≤
      Cmean * ((2 * m : ℕ) : ℝ) ^ ((21 / 10 : ℝ) + ε)

noncomputable def FixedTestPrimeMSConstants.absorb
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (m : ℕ) (ε η Cmean Ccount : ℝ)
    (h : FixedTestPrimeMSConstants χ S hSbad W m ε Cmean Ccount)
    (hm : 0 < m) (hCmean : Cmean ≤ ((2 * m : ℕ) : ℝ) ^ η)
    (hCcount : 1 ≤ Ccount * ((2 * m : ℕ) : ℝ) ^ η) :
    FixedTestPrimeMS χ S hSbad W m (ε + η) := by
  let N : ℝ := (2 * m : ℕ)
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (by omega : 0 < 2 * m)
  have hcount' : N ^ ((11 / 60 : ℝ) - (ε + η)) ≤
      (h.selected.card : ℝ) := by
    calc
      N ^ ((11 / 60 : ℝ) - (ε + η)) =
          1 * N ^ ((11 / 60 : ℝ) - (ε + η)) := by ring
      _ ≤ (Ccount * N ^ η) * N ^ ((11 / 60 : ℝ) - (ε + η)) :=
        mul_le_mul_of_nonneg_right hCcount (Real.rpow_nonneg hNpos.le _)
      _ = Ccount * N ^ ((11 / 60 : ℝ) - ε) := by
        rw [mul_assoc, ← Real.rpow_add hNpos]
        congr 1
        ring_nf
      _ ≤ _ := h.hcount
  have hmean' :
      (∑ u ∈ rowNormDisk h.H,
        ‖idealRowSum (outsideIdealsUpTo S (2 * m))
            (outsideIdealsUpTo_ne_bot S (2 * m))
            (outsideIdealsUpTo_good S (2 * m) hSbad)
            χ (fixedTestWeight W m) u‖ ^ 2) ≤
        N ^ ((21 / 10 : ℝ) + (ε + η)) := by
    calc
      _ ≤ Cmean * N ^ ((21 / 10 : ℝ) + ε) := h.hmean
      _ ≤ N ^ η * N ^ ((21 / 10 : ℝ) + ε) :=
        mul_le_mul_of_nonneg_right hCmean (Real.rpow_nonneg hNpos.le _)
      _ = N ^ ((21 / 10 : ℝ) + (ε + η)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  exact {
    H := h.H
    selected := h.selected
    hp := h.hp
    hprime := h.hprime
    hinj := h.hinj
    hnormlower := h.hnormlower
    hnormupper := h.hnormupper
    hH := h.hH
    hcount := hcount'
    hmean := hmean'
  }

end CompactScaleBridge

open Filter Asymptotics MeasureTheory
open scoped Topology

namespace CompactMellinBridge

/--
@isnad1 id=mellinco.2h2v.s6.226989bb8f19 from=translated src=- shape=3906fce7 vocab=7ed0073e
-/
theorem compact_weight_mellin_convergent
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (s : ℂ) : MellinConvergent W s := by
  have hlocal : LocallyIntegrableOn W (Set.Ioi (0 : ℝ)) :=
    hW.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : W =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
    exact hsupp y (Or.inr hy)
  have hbotzero : W =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
    exact hsupp y (Or.inl hy.2.le)
  have htop : W =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : W =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)

/--
@isnad1 id=integrab.2h4v.s7.d9beade14d1b from=translated src=- shape=16c33419 vocab=a916251d
-/
theorem weighted_term_integrable
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W : ℝ → ℂ)
    (s : ℂ) (hW : MellinConvergent W s) (n : ℕ) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        (a n * W ((n : ℝ) * t)))
      (Set.Ioi 0) := by
  by_cases hn : n = 0
  · subst n
    simp [ha0]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hscale : MellinConvergent
        (fun t : ℝ => W ((n : ℝ) * t)) s :=
      (MellinConvergent.comp_mul_left hnpos).mpr hW
    have hscaled := hscale.const_smul (a n)
    simpa only [MellinConvergent, smul_eq_mul, mul_assoc] using hscaled

/--
@isnad1 id=continuo.3h3v.s7.b492d990657c from=translated src=- shape=83e55378 vocab=d1babc5f
-/
theorem weighted_sum_continuousOn_pos
    (a : ℕ → ℂ) (W F : ℝ → ℂ)
    (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t)) :
    ContinuousOn F (Set.Ioi (0 : ℝ)) := by
  intro t0 ht0
  have ht0pos : 0 < t0 := ht0
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / t0)
  have hNmul := mul_lt_mul_of_pos_right hN (by positivity : 0 < t0 / 2)
  have hNtwo : 2 < (N : ℝ) * (t0 / 2) := by
    have hdiv : (4 / t0) * (t0 / 2) = 2 := by
      field_simp
      ring
    rw [hdiv] at hNmul
    exact hNmul
  have hsumEq (u : ℝ) (hu : t0 / 2 ≤ u) :
      F u = ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u) := by
    have hupos : 0 < u := lt_of_lt_of_le (by positivity : 0 < t0 / 2) hu
    have htail (n : ℕ) (hn : n ∉ Finset.range N) :
        a n * W ((n : ℝ) * u) = 0 := by
      have hnNat : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
      have hnReal : (N : ℝ) ≤ n := by exact_mod_cast hnNat
      have hnu : 2 ≤ (n : ℝ) * u := by
        calc
          2 ≤ (N : ℝ) * (t0 / 2) := hNtwo.le
          _ ≤ (N : ℝ) * u :=
            mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α := ℝ) N)
          _ ≤ (n : ℝ) * u :=
            mul_le_mul_of_nonneg_right hnReal hupos.le
      simp [hsupp _ hnu]
    calc
      F u = ∑' n : ℕ, a n * W ((n : ℝ) * u) := (hF u hupos).tsum_eq.symm
      _ = ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u) :=
        tsum_eq_sum htail
  have hcontW : Continuous W := hW.continuous
  have hcontSum : Continuous
      (fun u : ℝ => ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u)) := by
    fun_prop
  have hevent : F =ᶠ[𝓝 t0]
      (fun u : ℝ => ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u)) := by
    filter_upwards [Ioi_mem_nhds (by linarith : t0 / 2 < t0)] with u hu
    exact hsumEq u hu.le
  exact (hcontSum.continuousAt.congr_of_eventuallyEq hevent).continuousWithinAt

/--
@isnad1 id=locallyi.3h3v.s7.38a1892018fe from=translated src=- shape=efee64cc vocab=e3f2c7de
-/
theorem weighted_sum_inv_locallyIntegrableOn_pos
    (a : ℕ → ℂ) (W F : ℝ → ℂ)
    (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t)) :
    LocallyIntegrableOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0) := by
    apply (weighted_sum_continuousOn_pos a W F hW hsupp hF).comp
      (continuousOn_inv₀.mono (by
        intro D hD
        exact ne_of_gt hD))
    intro D hD
    exact inv_pos.mpr (show 0 < D from hD)
  exact hcont.locallyIntegrableOn measurableSet_Ioi

private theorem weighted_norm_scale
    (a : ℂ) (W : ℝ → ℂ) (s : ℂ)
    (N t : ℝ) (hN : 0 < N) (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) * (a * W (N * t))‖ =
      (‖a‖ / N ^ (s.re - 1)) *
        ‖(N * t : ℂ) ^ (s - 1) * W (N * t)‖ := by
  have hNt : 0 < N * t := mul_pos hN ht
  have hNpow : 0 < N ^ (s.re - 1) := Real.rpow_pos_of_pos hN _
  rw [norm_mul, norm_mul, norm_mul]
  rw [← Complex.ofReal_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_cpow_eq_rpow_re_of_pos hNt]
  simp only [Complex.sub_re, Complex.one_re]
  rw [Real.mul_rpow hN.le ht.le]
  field_simp

private theorem weighted_norm_integral
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W : ℝ → ℂ)
    (s : ℂ) (n : ℕ) :
    (∫ t : ℝ in Set.Ioi 0,
      ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖) =
    ‖LSeries.term a s n‖ *
      (∫ u : ℝ in Set.Ioi 0,
        ‖(u : ℂ) ^ (s - 1) * W u‖) := by
  by_cases hn : n = 0
  · subst n
    simp [ha0, LSeries.term_zero]
  · have hN : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    let G : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (s - 1) * W u‖
    have hscale :
        (∫ t : ℝ in Set.Ioi 0,
          ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖) =
          (‖a n‖ / (n : ℝ) ^ (s.re - 1)) *
            (∫ t : ℝ in Set.Ioi 0, G ((n : ℝ) * t)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simpa only [G, Complex.ofReal_mul] using
        weighted_norm_scale (a n) W s n t hN ht
    rw [hscale, integral_comp_mul_left_Ioi G 0 hN]
    simp only [mul_zero, smul_eq_mul]
    have hpow : (n : ℝ) ^ (s.re - 1) * (n : ℝ) =
        (n : ℝ) ^ s.re := by
      calc
        (n : ℝ) ^ (s.re - 1) * (n : ℝ) =
            (n : ℝ) ^ (s.re - 1) * (n : ℝ) ^ (1 : ℝ) := by
              rw [Real.rpow_one]
        _ = (n : ℝ) ^ ((s.re - 1) + 1) :=
          (Real.rpow_add hN (s.re - 1) 1).symm
        _ = (n : ℝ) ^ s.re := by congr 1; ring
    rw [LSeries.norm_term_eq]
    simp only [ite_eq_right hn, G]
    have hinv : ((n : ℝ) ^ (s.re - 1))⁻¹ * (n : ℝ)⁻¹ =
        ((n : ℝ) ^ s.re)⁻¹ := by
      rw [← mul_inv_rev, mul_comm, hpow]
    simp only [div_eq_mul_inv]
    calc
      ‖a n‖ * ((n : ℝ) ^ (s.re - 1))⁻¹ *
          ((n : ℝ)⁻¹ *
            (∫ u : ℝ in Set.Ioi 0, ‖(u : ℂ) ^ (s - 1) * W u‖)) =
          (‖a n‖ * (((n : ℝ) ^ (s.re - 1))⁻¹ * (n : ℝ)⁻¹)) *
            (∫ u : ℝ in Set.Ioi 0, ‖(u : ℂ) ^ (s - 1) * W u‖) := by ring
      _ = (‖a n‖ * ((n : ℝ) ^ s.re)⁻¹) *
            (∫ u : ℝ in Set.Ioi 0, ‖(u : ℂ) ^ (s - 1) * W u‖) := by rw [hinv]

/--
@isnad1 id=summable.2h3v.s7.110b00da13f7 from=translated src=- shape=5bbdcab2 vocab=49b23dd4
-/
theorem weighted_terms_fubini
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W : ℝ → ℂ)
    (s : ℂ) (hlsum : LSeriesSummable a s) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖) := by
  let C : ℝ := ∫ u : ℝ in Set.Ioi 0,
    ‖(u : ℂ) ^ (s - 1) * W u‖
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term a s n‖) := hlsum.norm
  have hsum : Summable (fun n : ℕ => ‖LSeries.term a s n‖ * C) :=
    hnorm.mul_right C
  exact hsum.congr (fun n => (weighted_norm_integral a ha0 W s n).symm)

noncomputable def finiteEulerFactor
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ShortDraftHeckeBridge.O)) (s : ℂ) : ℂ :=
  ∏ P ∈ S,
    (1 - χ (Ideal.absNorm P) *
      ((Ideal.absNorm P : ℂ) ^ (-s)))

/--
@isnad1 id=analytic.1h4v.s7.1826cfd852aa from=translated src=- shape=b68afae7 vocab=73184c99
-/
theorem finiteEulerFactor_analytic
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ShortDraftHeckeBridge.O))
    (hprime : ∀ P ∈ S, Prime P) (σ : ℝ) :
    AnalyticOnNhd ℂ (finiteEulerFactor χ S)
      {s : ℂ | σ < s.re} := by
  have hE : Differentiable ℂ (finiteEulerFactor χ S) := by
    unfold finiteEulerFactor
    apply Differentiable.fun_finsetProd
    intro P hPS
    have hN : Ideal.absNorm P ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr (hprime P hPS).1
    have hNc : (Ideal.absNorm P : ℂ) ≠ 0 := by exact_mod_cast hN
    have hcpow : Differentiable ℂ
        (fun s : ℂ => ((Ideal.absNorm P : ℂ) ^ (-s))) :=
      (differentiable_id.neg).const_cpow (Or.inl hNc)
    exact (differentiable_const (1 : ℂ)).sub
      ((differentiable_const (χ (Ideal.absNorm P))).mul hcpow)
  exact (Complex.analyticOnNhd_iff_differentiableOn
    (Complex.isOpen_re_gt σ)).2 hE.differentiableOn

/--
@isnad1 id=ne.7h5v.s7.84056cba6b1a from=translated src=- shape=10147444 vocab=2b62810c
-/
theorem zero_free_of_analytic_identity_gt_two
    (σ : ℝ) (hσ : σ < 2) (G M W : ℂ → ℂ)
    (hG : AnalyticOnNhd ℂ G {s | σ < s.re})
    (hM : AnalyticOnNhd ℂ M {s | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s | σ < s.re})
    (heq : ∀ s : ℂ, 2 < s.re → G s * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : W ρ ≠ 0) : G ρ ≠ 0 := by
  have hthree : (3 : ℂ) ∈ {s : ℂ | σ < s.re} := by
    change σ < (3 : ℂ).re
    norm_num at *
    linarith
  have heventual : (fun s : ℂ => G s * M s) =ᶠ[𝓝 (3 : ℂ)] W := by
    filter_upwards [((Complex.isOpen_re_gt 2).mem_nhds
      (by norm_num : (3 : ℂ) ∈ {s : ℂ | 2 < s.re}))] with s hs
    exact heq s hs
  have hident : Set.EqOn (fun s : ℂ => G s * M s) W
      {s | σ < s.re} :=
    (hG.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
      ((convex_halfSpace_re_gt σ).isPreconnected) hthree heventual
  intro hGρ
  have heqρ := hident hρ
  change G ρ * M ρ = W ρ at heqρ
  rw [hGρ, zero_mul] at heqρ
  exact hWρ heqρ.symm

/--
@isnad1 id=ne.9h6v.s8.592f9712be04 from=translated src=- shape=4e5acd3a vocab=ac9de204
-/
theorem zero_free_of_regularized_identity_gt_two
    (σ : ℝ) (hσ : σ < 2) (G Lregular M W : ℂ → ℂ)
    (hLregular : AnalyticOnNhd ℂ Lregular {s | σ < s.re})
    (hM : AnalyticOnNhd ℂ M {s | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s | σ < s.re})
    (hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      Lregular s = (s - 1) * G s)
    (heq : ∀ s : ℂ, 2 < s.re →
      Lregular s * M s = (s - 1) * W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : W ρ ≠ 0) : G ρ ≠ 0 := by
  have hWregular : AnalyticOnNhd ℂ
      (fun s : ℂ => (s - 1) * W s) {s | σ < s.re} :=
    (analyticOnNhd_id.sub analyticOnNhd_const).mul hW
  have hWregularρ : (ρ - 1) * W ρ ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hρone) hWρ
  have hLregularρ := zero_free_of_analytic_identity_gt_two σ hσ
    Lregular M (fun s : ℂ => (s - 1) * W s)
    hLregular hM hWregular heq ρ hρ hWregularρ
  rw [hregular ρ hρ hρone] at hLregularρ
  exact (mul_ne_zero_iff.mp hLregularρ).2

/--
@isnad1 id=eq.0h3v.s5.4f6bbea1db85 from=translated src=- shape=8a74bb4f vocab=6b473500
-/
theorem outsideCoeff_baseChange_zero {q : ℕ}
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) :
    FiniteSFactor.outsideCoeff S
      (ShortDraftHeckeBridge.baseChangeWeight χ) 0 = 0 := by
  classical
  unfold FiniteSFactor.outsideCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = 0 := by
    simpa [FiniteSFactor.fiber] using hI
  have hbot : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp hnorm
  subst I
  unfold FiniteSFactor.outsideWeight
  split_ifs
  · have hz : UniqueFactorizationMonoid.moebius (⊥ : Ideal FiniteSFactor.O) = 0 := by
      simpa only [Ideal.zero_eq_bot] using
        (UniqueFactorizationMonoid.moebius_zero (α := Ideal FiniteSFactor.O))
    simp [ShortDraftHeckeBridge.baseChangeWeight, hz]
  · rfl

noncomputable def outsideCompactSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) (W : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ,
    FiniteSFactor.outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n *
      W ((n : ℝ) * t)

/--
@isnad1 id=hassum.2h5v.s7.20a50be4a3b1 from=translated src=- shape=75b38f22 vocab=bbdd09a8
-/
theorem outsideCompactSum_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) (W : ℝ → ℂ)
    (hsupp : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ =>
      FiniteSFactor.outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n *
        W ((n : ℝ) * t)) (outsideCompactSum χ S W t) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / t)
  have htail (n : ℕ) (hn : n ∉ Finset.range N) :
      FiniteSFactor.outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n *
        W ((n : ℝ) * t) = 0 := by
    have hnNat : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
    have hnReal : (N : ℝ) ≤ n := by exact_mod_cast hnNat
    have hNt : 2 ≤ (N : ℝ) * t := by
      have h := mul_lt_mul_of_pos_right hN ht
      have hcancel : (2 / t) * t = 2 := by
        field_simp
      rw [hcancel] at h
      exact h.le
    have hnt : 2 ≤ (n : ℝ) * t :=
      hNt.trans (mul_le_mul_of_nonneg_right hnReal ht.le)
    simp [hsupp _ hnt]
  exact (summable_of_ne_finset_zero htail).hasSum

/--
@isnad1 id=eq.4h5v.s8.22c06d3c551c from=translated src=- shape=9ad9bbf2 vocab=703df01c
-/
theorem outside_compact_euler_identity {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) (hS : ∀ P ∈ S, Prime P)
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (s : ℂ) (hs : 2 < s.re) :
    (χ.LFunction s * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
      (finiteEulerFactor χ S s *
        mellin (fun D : ℝ => (outsideCompactSum χ S W) D⁻¹) (-s)) =
      mellin W s := by
  let a : ℕ → ℂ := FiniteSFactor.outsideCoeff S
    (ShortDraftHeckeBridge.baseChangeWeight χ)
  have ha0 : a 0 = 0 := outsideCoeff_baseChange_zero χ S
  have hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t))
        (outsideCompactSum χ S W t) := by
    intro t ht
    exact outsideCompactSum_hasSum χ S W (fun y hy => hsupp y (Or.inr hy)) t ht
  have hlsum : LSeriesSummable a s :=
    FiniteSFactor.outsideCoeff_LSeriesSummable_baseChange χ S s hs
  have hM := mellin_weighted_sum a W (outsideCompactSum χ S W) s
    ha0 hF
    (weighted_term_integrable a ha0 W s
      (compact_weight_mellin_convergent W hW hsupp s))
    (weighted_terms_fubini a ha0 W s hlsum) hlsum
  have hnorm := FiniteSFactor.normFiberLSeries_finiteEuler_baseChange
    χ S hS s hs
  change LSeries (ShortDraftHeckeBridge.normFiberCoeff
    (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
    finiteEulerFactor χ S s * LSeries a s at hnorm
  have hcoeff := ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff χ
  have hpair := ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse
    χ (ShortDraftHeckeBridge.baseChangeChar χ)
    (ShortDraftHeckeBridge.baseChangeWeight χ) hcoeff s
  have hEuler := ShortDraftHeckeBridge.pair_inverse_euler_identity
    χ (ShortDraftHeckeBridge.baseChangeChar χ) s (by linarith : 1 < s.re)
  have hfinite :
      (χ.LFunction s * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
        (finiteEulerFactor χ S s * LSeries a s) = 1 := by
    rw [← hnorm, hpair]
    exact hEuler
  rw [hM]
  calc
    (χ.LFunction s * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
        (finiteEulerFactor χ S s * (mellin W s * LSeries a s)) =
      ((χ.LFunction s * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
        (finiteEulerFactor χ S s * LSeries a s)) * mellin W s := by ring
    _ = mellin W s := by rw [hfinite]; ring

/--
@isnad1 id=and.8h8v.s8.786c3f9d690d from=translated src=- shape=ef3f5f21 vocab=4eaf3514
-/
theorem pair_zero_free_of_identity_gt_two
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hnotboth : χ ≠ 1 ∨ ψ ≠ 1)
    (σ : ℝ) (hσ : σ < 1) (M W : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | σ < s.re})
    (heq : ∀ s : ℂ, 2 < s.re →
      (χ.LFunction s * ψ.LFunction s) * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hσtwo : σ < 2 := by linarith
  by_cases hχ : χ = 1
  · have hψ : ψ ≠ 1 := by
      intro hψ
      rcases hnotboth with h | h
      · exact h hχ
      · exact h hψ
    subst χ
    have hLregular₁ : AnalyticOnNhd ℂ
        (DirichletCharacter.LFunctionTrivChar₁ q) U :=
      (Complex.analyticOnNhd_iff_differentiableOn hopen).2
        (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn
    have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
      (Complex.analyticOnNhd_iff_differentiableOn hopen).2
        (ψ.differentiable_LFunction hψ).differentiableOn
    have hLregular : AnalyticOnNhd ℂ
        (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) U :=
      hLregular₁.mul hLψ
    have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
        DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s =
          (s - 1) * ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) := by
      intro s _ hs
      simp [DirichletCharacter.LFunctionTrivChar₁,
        DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
      ring
    have heqregular : ∀ s : ℂ, 2 < s.re →
        (DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) * M s =
          (s - 1) * W s := by
      intro s hs
      rw [hregular s (lt_trans hσ (by linarith : 1 < s.re)) (by
        intro h; subst s; norm_num at hs)]
      calc
        (s - 1) * ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s =
            (s - 1) * (((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s) := by ring
        _ = (s - 1) * W s := by rw [heq s hs]
    have hprod := zero_free_of_regularized_identity_gt_two σ hσtwo
      (fun s => (1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s)
      (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s)
      M W hLregular hM hW hregular heqregular ρ hρ hρone hWρ
    exact mul_ne_zero_iff.mp hprod
  · by_cases hψ : ψ = 1
    · subst ψ
      have hLregular₁ : AnalyticOnNhd ℂ
          (DirichletCharacter.LFunctionTrivChar₁ r) U :=
        (Complex.analyticOnNhd_iff_differentiableOn hopen).2
          (DirichletCharacter.differentiable_LFunctionTrivChar₁ r).differentiableOn
      have hLχ : AnalyticOnNhd ℂ χ.LFunction U :=
        (Complex.analyticOnNhd_iff_differentiableOn hopen).2
          (χ.differentiable_LFunction hχ).differentiableOn
      have hLregular : AnalyticOnNhd ℂ
          (fun s => χ.LFunction s * DirichletCharacter.LFunctionTrivChar₁ r s) U :=
        hLχ.mul hLregular₁
      have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
          χ.LFunction s * DirichletCharacter.LFunctionTrivChar₁ r s =
            (s - 1) * (χ.LFunction s *
              (1 : DirichletCharacter ℂ r).LFunction s) := by
        intro s _ hs
        simp [DirichletCharacter.LFunctionTrivChar₁,
          DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
        ring
      have heqregular : ∀ s : ℂ, 2 < s.re →
          (χ.LFunction s * DirichletCharacter.LFunctionTrivChar₁ r s) * M s =
            (s - 1) * W s := by
        intro s hs
        rw [hregular s (lt_trans hσ (by linarith : 1 < s.re)) (by
          intro h; subst s; norm_num at hs)]
        calc
          (s - 1) * (χ.LFunction s *
              (1 : DirichletCharacter ℂ r).LFunction s) * M s =
              (s - 1) * ((χ.LFunction s *
                (1 : DirichletCharacter ℂ r).LFunction s) * M s) := by ring
          _ = (s - 1) * W s := by rw [heq s hs]
      have hprod := zero_free_of_regularized_identity_gt_two σ hσtwo
        (fun s => χ.LFunction s *
          (1 : DirichletCharacter ℂ r).LFunction s)
        (fun s => χ.LFunction s * DirichletCharacter.LFunctionTrivChar₁ r s)
        M W hLregular hM hW hregular heqregular ρ hρ hρone hWρ
      exact mul_ne_zero_iff.mp hprod
    · have hLχ : AnalyticOnNhd ℂ χ.LFunction U :=
        (Complex.analyticOnNhd_iff_differentiableOn hopen).2
          (χ.differentiable_LFunction hχ).differentiableOn
      have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
        (Complex.analyticOnNhd_iff_differentiableOn hopen).2
          (ψ.differentiable_LFunction hψ).differentiableOn
      have hprod := zero_free_of_analytic_identity_gt_two σ hσtwo
        (fun s => χ.LFunction s * ψ.LFunction s) M W
        (hLχ.mul hLψ) hM hW heq ρ hρ hWρ
      exact mul_ne_zero_iff.mp hprod

/--
@isnad1 id=ne.7h6v.s8.03d3da8d3cfb from=translated src=- shape=a8ee457e vocab=cb5de93a
-/
theorem baseChange_outsideCompact_zero_free {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) (hS : ∀ P ∈ S, Prime P)
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (σ : ℝ)
    (htop : (fun D : ℝ => outsideCompactSum χ S W D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hσρ : σ < ρ.re) (hρone : ρ.re < 1)
    (hWρ : mellin W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  let a : ℕ → ℂ := FiniteSFactor.outsideCoeff S
    (ShortDraftHeckeBridge.baseChangeWeight χ)
  have ha0 : a 0 = 0 := outsideCoeff_baseChange_zero χ S
  have hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t))
        (outsideCompactSum χ S W t) := by
    intro t ht
    exact outsideCompactSum_hasSum χ S W (fun y hy => hsupp y (Or.inr hy)) t ht
  have hlocal : LocallyIntegrableOn
      (fun D : ℝ => outsideCompactSum χ S W D⁻¹) (Set.Ioi 0) :=
    weighted_sum_inv_locallyIntegrableOn_pos a W
      (outsideCompactSum χ S W) hW
      (fun y hy => hsupp y (Or.inr hy)) hF
  have hzero : (fun D : ℝ => outsideCompactSum χ S W D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ => 0) :=
    weighted_sum_zero_near_small_D a ha0 W
      (outsideCompactSum χ S W)
      (fun y hy => hsupp y (Or.inr hy)) hF
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin
        (fun D : ℝ => outsideCompactSum χ S W D⁻¹) (-s))
      {s : ℂ | σ < s.re} :=
    ShortDraftMellin.inverse_mellin_analytic _ σ hlocal htop hzero
  have hE : AnalyticOnNhd ℂ (finiteEulerFactor χ S)
      {s : ℂ | σ < s.re} :=
    finiteEulerFactor_analytic χ S hS σ
  have hWanalytic : AnalyticOnNhd ℂ (mellin W)
      {s : ℂ | σ < s.re} :=
    compact_weight_mellin_analytic W hW hsupp σ
  have hnotboth : χ ≠ 1 ∨ ShortDraftHeckeBridge.baseChangeChar χ ≠ 1 := by
    by_cases hχ : χ = 1
    · exact Or.inr (ShortDraftHeckeBridge.baseChangeChar_ne_one_of_one χ hχ)
    · exact Or.inl hχ
  have heq (s : ℂ) (hs : 2 < s.re) :
      (χ.LFunction s *
        (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
        (finiteEulerFactor χ S s *
          mellin (fun D : ℝ => outsideCompactSum χ S W D⁻¹) (-s)) =
        mellin W s :=
    outside_compact_euler_identity χ S hS W hW hsupp s hs
  have hρneq : ρ ≠ 1 := by
    intro h
    subst ρ
    norm_num at hρone
  exact (pair_zero_free_of_identity_gt_two
    χ (ShortDraftHeckeBridge.baseChangeChar χ) hnotboth
    σ (lt_trans hσρ hρone)
    (fun s => finiteEulerFactor χ S s *
      mellin (fun D : ℝ => outsideCompactSum χ S W D⁻¹) (-s))
    (mellin W) (hE.mul hM) hWanalytic heq
    ρ hσρ hρneq hWρ).1

structure BaseChangeOutsideCompactTest
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) where
  S : Finset (Ideal FiniteSFactor.O)
  S_prime : ∀ P ∈ S, Prime P
  W : ℝ → ℂ
  sigma : ℝ
  sigma_lt : sigma < ρ.re
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W
  support : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0
  power_bound :
    (fun D : ℝ => outsideCompactSum χ S W D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ sigma)
  mellin_nonzero : mellin W ρ ≠ 0

/--
@isnad1 id=dirichle.0h1v.s6.882e875aece2 from=translated src=- shape=25d84d4b vocab=b63f0b5f
-/
theorem dirichletTarget_of_compact_outside_tests
    (hTest : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        BaseChangeOutsideCompactTest χ ρ) :
    ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρ : ρ.re < 1
  · let T := hTest q χ ρ h23 hρ
    exact baseChange_outsideCompact_zero_free χ T.S T.S_prime
      T.W T.smooth T.support T.sigma T.power_bound
      ρ T.sigma_lt hρ T.mellin_nonzero
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρ) hprincipal

end CompactMellinBridge

end

end OAI
-- Tengoku: root names of this library moved to Tengoku.QuasiRiemann so they do not collide with other libraries (generated)
