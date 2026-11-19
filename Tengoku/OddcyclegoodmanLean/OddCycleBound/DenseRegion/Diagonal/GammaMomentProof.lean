import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.GammaMoment
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.LogRatioBound
import Tengoku.Seed.Analysis.Analytic.IsolatedZeros
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.Analysis.Complex.ExponentialBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace OddCycleBound.DenseRegion

noncomputable def Mb (r : ℕ) (b : ℝ) (k : ℕ) : ℝ := gExp r (fun y => (y - b) ^ k)

private lemma pow_exp_pow_int_b (r a d : ℕ) (_ha : r - 1 ≤ a) (b : ℝ) :
    IntegrableOn (fun y => y ^ a * Real.exp (-y) * (y - b) ^ d) (Set.Ioi (0 : ℝ)) := by
  refine IntegrableOn.congr_fun (gExp_affinePow_integrableOn (a + 1) d 1 (-b))
    (fun y _ => ?_) measurableSet_Ioi
  rw [show a + 1 - 1 = a from by omega, show (1 : ℝ) * y + -b = y - b from by ring]

/--
@isnad1 id=eq.0h3v.s6.62622b76b556 from=translated src=- shape=ad9c395a vocab=3ca51481
-/
lemma Mb_explicit (r : ℕ) (b : ℝ) (k : ℕ) :
    Mb r b k = ∑ i ∈ Finset.range (k + 1),
      (Nat.choose k i : ℝ) * (-b) ^ (k - i) * (Nat.factorial (r - 1 + i) : ℝ) := by
  unfold Mb
  have hrw : (fun y : ℝ => (y - b) ^ k)
      = fun y => ∑ i ∈ Finset.range (k + 1), ((Nat.choose k i : ℝ) * (-b) ^ (k - i)) * y ^ i := by
    funext y
    rw [show y - b = y + -b from by ring, add_pow]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  rw [hrw, gExp_finset_sum r _ _ (fun i _ =>
    IntegrableOn.congr_fun ((gExp_integrableOn r i).const_mul ((Nat.choose k i : ℝ) * (-b) ^ (k - i)))
      (fun y _ => by ring) measurableSet_Ioi)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [gExp_const_mul r _ (fun y => y ^ i), gExp_monomial r i]

private lemma gExp_y_mul_b (r : ℕ) (hr : 1 ≤ r) (b : ℝ) (k : ℕ) :
    (∫ y in Set.Ioi (0 : ℝ), y ^ r * Real.exp (-y) * (y - b) ^ k)
      = Mb r b (k + 1) + b * Mb r b k := by
  have hrw : (fun y : ℝ => y ^ r * Real.exp (-y) * (y - b) ^ k)
      = fun y => y ^ (r - 1) * Real.exp (-y) * ((y - b) ^ (k + 1) + b * (y - b) ^ k) := by
    funext y
    have h1 : y ^ r = y ^ (r - 1) * y := by rw [← pow_succ]; congr 1; omega
    have h2 : (y - b) ^ (k + 1) + b * (y - b) ^ k = y * (y - b) ^ k := by rw [pow_succ]; ring
    rw [h1, h2]; ring
  rw [hrw]
  show gExp r (fun y => (y - b) ^ (k + 1) + b * (y - b) ^ k) = _
  rw [gExp_add r (fun y => (y - b) ^ (k + 1)) (fun y => b * (y - b) ^ k)
      (pow_exp_pow_int_b r (r - 1) (k + 1) (le_refl _) b)
      (IntegrableOn.congr_fun ((pow_exp_pow_int_b r (r - 1) k (le_refl _) b).const_mul b)
        (fun y _ => by ring) measurableSet_Ioi),
    gExp_const_mul r b (fun y => (y - b) ^ k)]
  rfl

/--
@isnad1 id=eq.1h3v.s6.d3561bab4f5e from=translated src=- shape=106a1c2d vocab=a9d420ac
-/
lemma Mb_recurrence (r : ℕ) (hr : 1 ≤ r) (b : ℝ) (k : ℕ) :
    Mb r b (k + 1) = ((r : ℝ) + k - b) * Mb r b k + (k : ℝ) * b * Mb r b (k - 1) := by
  set g : ℝ → ℝ := fun y => y ^ r * Real.exp (-y) * (y - b) ^ k with hg
  set g' : ℝ → ℝ := fun y =>
      (r : ℝ) * (y ^ (r - 1) * Real.exp (-y) * (y - b) ^ k)
      - y ^ r * Real.exp (-y) * (y - b) ^ k
      + (k : ℝ) * (y ^ r * Real.exp (-y) * (y - b) ^ (k - 1)) with hg'
  have hderiv : ∀ y : ℝ, HasDerivAt g (g' y) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => y ^ r) ((r : ℝ) * y ^ (r - 1)) y := hasDerivAt_pow r y
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
      simpa using (((hasDerivAt_id y).neg).exp)
    have hbd : HasDerivAt (fun y : ℝ => y - b) 1 y := by simpa using (hasDerivAt_id y).sub_const b
    have hp := (h1.mul h2).mul (hbd.pow k)
    have heq : g' y = ((r : ℝ) * y ^ (r - 1) * Real.exp (-y) + y ^ r * -Real.exp (-y))
        * (y - b) ^ k
        + y ^ r * Real.exp (-y) * ((k : ℝ) * (y - b) ^ (k - 1) * 1) := by
      simp only [hg']; ring
    rw [heq]; exact hp
  have hg0 : g 0 = 0 := by simp only [hg]; rw [zero_pow (show r ≠ 0 by omega)]; ring
  have htend : Tendsto g atTop (𝓝 0) := by
    have hsum : g = fun y => ∑ i ∈ Finset.range (k + 1),
        (Nat.choose k i : ℝ) * (-b) ^ (k - i) * (y ^ (r + i) * Real.exp (-y)) := by
      funext y; simp only [hg]
      rw [show y - b = y + -b from by ring, add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [pow_add]; ring
    rw [hsum, show (0 : ℝ) = ∑ _i ∈ Finset.range (k + 1), (0 : ℝ) from by simp]
    refine tendsto_finsetSum _ (fun i _ => ?_)
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (r + i)).const_mul
      ((Nat.choose k i : ℝ) * (-b) ^ (k - i))
  have hg'int : IntegrableOn g' (Set.Ioi (0 : ℝ)) := by
    rw [hg']
    exact (((pow_exp_pow_int_b r (r - 1) k (le_refl _) b).const_mul (r : ℝ)).sub
      (pow_exp_pow_int_b r r k (by omega) b)).add
      ((pow_exp_pow_int_b r r (k - 1) (by omega) b).const_mul (k : ℝ))
  have hFTC : (∫ y in Set.Ioi (0 : ℝ), g' y) = 0 := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hderiv x) hg'int htend, hg0, sub_zero]
  have hsplit : (∫ y in Set.Ioi (0 : ℝ), g' y)
      = (r : ℝ) * (∫ y in Set.Ioi (0 : ℝ), y ^ (r - 1) * Real.exp (-y) * (y - b) ^ k)
        - (∫ y in Set.Ioi (0 : ℝ), y ^ r * Real.exp (-y) * (y - b) ^ k)
        + (k : ℝ) * (∫ y in Set.Ioi (0 : ℝ), y ^ r * Real.exp (-y) * (y - b) ^ (k - 1)) := by
    simp only [hg']
    rw [MeasureTheory.integral_add
          (f := fun y => (r : ℝ) * (y ^ (r - 1) * Real.exp (-y) * (y - b) ^ k)
            - y ^ r * Real.exp (-y) * (y - b) ^ k)
          (g := fun y => (k : ℝ) * (y ^ r * Real.exp (-y) * (y - b) ^ (k - 1)))
          (((pow_exp_pow_int_b r (r - 1) k (le_refl _) b).const_mul (r : ℝ)).sub
            (pow_exp_pow_int_b r r k (by omega) b))
          ((pow_exp_pow_int_b r r (k - 1) (by omega) b).const_mul (k : ℝ)),
        MeasureTheory.integral_sub
          (f := fun y => (r : ℝ) * (y ^ (r - 1) * Real.exp (-y) * (y - b) ^ k))
          (g := fun y => y ^ r * Real.exp (-y) * (y - b) ^ k)
          ((pow_exp_pow_int_b r (r - 1) k (le_refl _) b).const_mul (r : ℝ))
          (pow_exp_pow_int_b r r k (by omega) b),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hFTC,
    show (∫ y in Set.Ioi (0 : ℝ), y ^ (r - 1) * Real.exp (-y) * (y - b) ^ k) = Mb r b k from rfl,
    gExp_y_mul_b r hr b k, gExp_y_mul_b r hr b (k - 1)] at hsplit
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0; simp only [Mb, Nat.zero_sub, Nat.cast_zero, zero_mul, add_zero] at hsplit ⊢
    linear_combination hsplit
  · rw [show k - 1 + 1 = k from by omega] at hsplit
    linear_combination hsplit

/--
@isnad1 id=hasderiv.0h3v.s6.625235b1d2b6 from=translated src=- shape=cc570188 vocab=7bcabeba
-/
lemma Mb_hasDeriv (r : ℕ) (b : ℝ) (k : ℕ) :
    HasDerivAt (fun b => Mb r b k) (-(k : ℝ) * Mb r b (k - 1)) b := by

  have hpoly : (fun b : ℝ => Mb r b k)
      = fun b => ∑ i ∈ Finset.range (k + 1),
          (Nat.choose k i : ℝ) * (-b) ^ (k - i) * (Nat.factorial (r - 1 + i) : ℝ) :=
    funext (fun b => Mb_explicit r b k)

  have hterm : ∀ i ∈ Finset.range (k + 1),
      HasDerivAt (fun b : ℝ =>
          (Nat.choose k i : ℝ) * (-b) ^ (k - i) * (Nat.factorial (r - 1 + i) : ℝ))
        ((Nat.choose k i : ℝ) * (((k - i : ℕ) : ℝ) * (-b) ^ (k - i - 1) * (-1))
          * (Nat.factorial (r - 1 + i) : ℝ)) b := by
    intro i _
    have hb : HasDerivAt (fun b : ℝ => -b) (-1 : ℝ) b := hasDerivAt_neg' b
    have hp : HasDerivAt (fun b : ℝ => (-b) ^ (k - i))
        (((k - i : ℕ) : ℝ) * (-b) ^ (k - i - 1) * (-1)) b := hb.pow (k - i)
    exact (hp.const_mul (Nat.choose k i : ℝ)).mul_const (Nat.factorial (r - 1 + i) : ℝ)

  have hval : -(k : ℝ) * Mb r b (k - 1)
      = ∑ i ∈ Finset.range (k + 1),
          (Nat.choose k i : ℝ) * (((k - i : ℕ) : ℝ) * (-b) ^ (k - i - 1) * (-1))
            * (Nat.factorial (r - 1 + i) : ℝ) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · subst hk0; simp
    · rw [Mb_explicit r b (k - 1), Finset.mul_sum, show k - 1 + 1 = k from by omega,
        Finset.sum_range_succ, show k - k = 0 from by omega]
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      have hidx : k - i - 1 = k - 1 - i := by omega
      have hchoose : (Nat.choose k i : ℝ) * ((k - i : ℕ) : ℝ)
          = (k : ℝ) * (Nat.choose (k - 1) i : ℝ) := by
        have h0 := Nat.choose_mul_succ_eq (k - 1) i
        rw [show (k - 1) + 1 = k from by omega] at h0
        calc (Nat.choose k i : ℝ) * ((k - i : ℕ) : ℝ)
            = ((Nat.choose k i * (k - i) : ℕ) : ℝ) := by push_cast; ring
          _ = ((Nat.choose (k - 1) i * k : ℕ) : ℝ) := by rw [h0.symm]
          _ = (k : ℝ) * (Nat.choose (k - 1) i : ℝ) := by push_cast; ring
      rw [hidx]
      linear_combination ((-b) ^ (k - 1 - i) * (Nat.factorial (r - 1 + i) : ℝ)) * hchoose
  rw [hpoly, hval]
  exact HasDerivAt.fun_sum hterm

noncomputable def Hb (r j : ℕ) (b : ℝ) : ℝ :=
  ((r : ℝ) + j) * Mb r b (2 * j) - 3 * (j : ℝ) * b * Mb r b (2 * j - 1)

noncomputable def Hb' (r j : ℕ) (b : ℝ) : ℝ :=
  3 * (j : ℝ) * Mb r b (2 * j) + (j : ℝ) * (3 * b - 5 * (r : ℝ) - 8 * (j : ℝ)) * Mb r b (2 * j - 1)

/--
@isnad1 id=hasderiv.2h3v.s6.bff1d27a89ff from=translated src=- shape=5d5e2f6d vocab=69aab7a3
-/
lemma Hb_hasDeriv (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (b : ℝ) :
    HasDerivAt (fun b => Hb r j b) (Hb' r j b) b := by
  have hfun : (fun b => Hb r j b)
      = fun b => ((r : ℝ) + j) * Mb r b (2 * j) - 3 * (j : ℝ) * (b * Mb r b (2 * j - 1)) := by
    funext b; unfold Hb; ring
  rw [hfun]
  have hM1 := Mb_hasDeriv r b (2 * j - 1)
  have hraw := ((Mb_hasDeriv r b (2 * j)).const_mul ((r : ℝ) + j)).sub
    (((hasDerivAt_id b).mul hM1).const_mul (3 * (j : ℝ)))
  have hrec := Mb_recurrence r hr b (2 * j - 1)
  rw [show 2 * j - 1 + 1 = 2 * j from by omega] at hrec
  have e2j1 : ((2 * j - 1 : ℕ) : ℝ) = 2 * (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * j)]; push_cast; ring
  rw [e2j1] at hrec
  have hdeq : Hb' r j b
      = ((r : ℝ) + j) * (-(((2 * j : ℕ) : ℝ)) * Mb r b (2 * j - 1))
        - 3 * (j : ℝ) * (1 * Mb r b (2 * j - 1)
            + b * (-(((2 * j - 1 : ℕ) : ℝ)) * Mb r b (2 * j - 1 - 1))) := by
    unfold Hb'
    rw [show ((2 * j : ℕ) : ℝ) = 2 * (j : ℝ) from by push_cast; ring, e2j1]
    linear_combination (3 * (j : ℝ)) * hrec
  rw [hdeq]
  exact hraw

/--
@isnad1 id=eq.1h3v.s7.af151d06005e from=translated src=- shape=102d7e50 vocab=279990a2
-/
lemma Hb_cross (r j : ℕ) (β : ℝ) (hz : Hb r j β = 0) :
    3 * β * Hb' r j β
      = Mb r β (2 * j)
        * (3 * ((r : ℝ) + 4 * (j : ℝ)) * β - ((r : ℝ) + (j : ℝ)) * (5 * (r : ℝ) + 8 * (j : ℝ))) := by
  unfold Hb at hz
  unfold Hb'
  linear_combination (5 * (r : ℝ) + 8 * (j : ℝ) - 3 * β) * hz

/--
@isnad1 id=lt.1h3v.s5.4f19ed7d13cc from=translated src=- shape=961b2fe6 vocab=4047c1b3
-/
lemma Mb_pos_even (r j : ℕ) (_hr : 1 ≤ r) (b : ℝ) : 0 < Mb r b (2 * j) := by
  have hMb : Mb r b (2 * j)
      = ∫ y in Set.Ioi (0 : ℝ), y ^ (r - 1) * Real.exp (-y) * (y - b) ^ (2 * j) := rfl
  have hnn : ∀ y ∈ Set.Ioi (0 : ℝ), 0 ≤ y ^ (r - 1) * Real.exp (-y) * (y - b) ^ (2 * j) := by
    intro y hy; rw [Set.mem_Ioi] at hy
    have : (y - b) ^ (2 * j) = ((y - b) ^ 2) ^ j := by rw [← pow_mul, Nat.mul_comm]
    rw [this]; positivity
  have haenn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      fun y => y ^ (r - 1) * Real.exp (-y) * (y - b) ^ (2 * j) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hnn)
  have hint : MeasureTheory.IntegrableOn
      (fun y => y ^ (r - 1) * Real.exp (-y) * (y - b) ^ (2 * j)) (Set.Ioi (0 : ℝ)) :=
    pow_exp_pow_int_b r (r - 1) (2 * j) (le_refl _) b
  rw [hMb, MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae haenn hint]

  have hsub : Set.Ioo (|b| + 1) (|b| + 2)
      ⊆ Function.support (fun y => y ^ (r - 1) * Real.exp (-y) * (y - b) ^ (2 * j))
        ∩ Set.Ioi (0 : ℝ) := by
    intro y hy
    rw [Set.mem_Ioo] at hy
    have hy0 : 0 < y := by have := abs_nonneg b; linarith [hy.1]
    have hyb : y - b ≠ 0 := by
      have hbb : b ≤ |b| := le_abs_self b
      have : 0 < y - b := by linarith [hy.1]
      exact ne_of_gt this
    refine ⟨?_, Set.mem_Ioi.mpr hy0⟩
    rw [Function.mem_support]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (ne_of_gt hy0)) (Real.exp_ne_zero _))
      (pow_ne_zero _ hyb)
  have hpos : (0 : ENNReal) < MeasureTheory.volume (Set.Ioo (|b| + 1) (|b| + 2)) := by
    rw [Real.volume_Ioo]; simp
  exact lt_of_lt_of_le hpos (MeasureTheory.measure_mono hsub)

noncomputable def bstar (r j : ℕ) : ℝ :=
  ((r : ℝ) + j) * (5 * (r : ℝ) + 8 * (j : ℝ)) / (3 * ((r : ℝ) + 4 * (j : ℝ)))

/--
@isnad1 id=lt.1h2v.s4.ee09f561ca28 from=translated src=- shape=e3349857 vocab=2c2890a3
-/
lemma bstar_pos (r j : ℕ) (hr : 1 ≤ r) : 0 < bstar r j := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hjnn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  unfold bstar; positivity

/--
@isnad1 id=eq.1h3v.s7.8f335b2b6b19 from=translated src=- shape=faedd7e6 vocab=d7abc8e9
-/
lemma cross_bracket (r j : ℕ) (hr : 1 ≤ r) (β : ℝ) :
    3 * ((r : ℝ) + 4 * (j : ℝ)) * β - ((r : ℝ) + (j : ℝ)) * (5 * (r : ℝ) + 8 * (j : ℝ))
      = 3 * ((r : ℝ) + 4 * (j : ℝ)) * (β - bstar r j) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hjnn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hden : (3 : ℝ) * ((r : ℝ) + 4 * (j : ℝ)) ≠ 0 := by positivity
  unfold bstar; field_simp

private lemma slope_neg_right {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (hf' : f' < 0) :
    ∀ᶠ y in nhdsWithin x (Set.Ioi x), f y < f x := by
  have h0 := hasDerivAt_iff_tendsto_slope.mp hf
  have hs : Filter.Tendsto (slope f x) (nhdsWithin x (Set.Ioi x)) (nhds f') :=
    h0.mono_left (nhdsWithin_mono x (fun y hy => hy.ne'))
  have hev : ∀ᶠ y in nhdsWithin x (Set.Ioi x), slope f x y < 0 :=
    hs.eventually (Filter.eventually_of_mem (Iio_mem_nhds hf') (fun z hz => hz))
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hymem
  have hyx : x < y := hymem
  rw [slope_def_field] at hy
  rcases div_neg_iff.mp hy with ⟨h1, h2⟩ | ⟨h1, _⟩
  · linarith
  · linarith

private lemma slope_pos_left {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (hf' : 0 < f') :
    ∀ᶠ y in nhdsWithin x (Set.Iio x), f y < f x := by
  have h0 := hasDerivAt_iff_tendsto_slope.mp hf
  have hs : Filter.Tendsto (slope f x) (nhdsWithin x (Set.Iio x)) (nhds f') :=
    h0.mono_left (nhdsWithin_mono x (fun y hy => hy.ne))
  have hev : ∀ᶠ y in nhdsWithin x (Set.Iio x), 0 < slope f x y :=
    hs.eventually (Filter.eventually_of_mem (Ioi_mem_nhds hf') (fun z hz => hz))
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hymem
  have hyx : y < x := hymem
  rw [slope_def_field] at hy
  rcases div_pos_iff.mp hy with ⟨h1, h2⟩ | ⟨h1, _⟩
  · linarith
  · linarith

/--
@isnad1 id=le.4h3v.s6.f983a52fc47d from=translated src=- shape=96931de4 vocab=f0026d98
-/
lemma Hb_nonneg (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j)
    (hbstar : 0 < Hb r j (bstar r j)) (b : ℝ) (hb : 0 < b) : 0 ≤ Hb r j b := by
  by_contra hcon
  push Not at hcon
  set bs := bstar r j with hbs
  have hbspos : 0 < bs := bstar_pos r j hr
  have hcont : Continuous (fun x => Hb r j x) :=
    continuous_iff_continuousAt.mpr (fun x => (Hb_hasDeriv r j hr hj x).continuousAt)
  have h34 : (0 : ℝ) < 3 * ((r : ℝ) + 4 * (j : ℝ)) := by
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    positivity
  have hpne : b ≠ bs := fun h => by rw [h] at hcon; linarith
  rcases lt_or_gt_of_ne hpne with hlt | hgt
  ·
    set S := Set.Icc b bs ∩ (fun x => Hb r j x) ⁻¹' {0} with hSdef
    have hScl : IsClosed S := isClosed_Icc.inter (isClosed_singleton.preimage hcont)
    have hSbdd : BddAbove S := bddAbove_Icc.mono Set.inter_subset_left
    obtain ⟨c, hcIcc, hc0⟩ := intermediate_value_Icc (le_of_lt hlt) hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (Hb r j b) (Hb r j bs) from ⟨le_of_lt hcon, le_of_lt hbstar⟩)
    have hSne : S.Nonempty := ⟨c, hcIcc, hc0⟩
    set β := sSup S with hβdef
    have hβS : β ∈ S := hScl.csSup_mem hSne hSbdd
    have hβ0 : Hb r j β = 0 := hβS.2
    have hβbs : β < bs := lt_of_le_of_ne hβS.1.2 (fun h => by rw [h] at hβ0; linarith)
    have hβpos : 0 < β := lt_of_lt_of_le hb hβS.1.1

    have hpos_right : ∀ x, β < x → x ≤ bs → 0 < Hb r j x := by
      intro x hx1 hx2
      by_contra hxle; push Not at hxle
      have hxne : Hb r j x ≠ 0 := fun h =>
        absurd (le_csSup hSbdd (⟨⟨le_trans hβS.1.1 (le_of_lt hx1), hx2⟩, h⟩ : x ∈ S))
          (not_le.mpr hx1)
      have hxlt : Hb r j x < 0 := lt_of_le_of_ne hxle hxne
      obtain ⟨d, hdIcc, hd0⟩ := intermediate_value_Icc hx2 hcont.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (Hb r j x) (Hb r j bs) from ⟨le_of_lt hxlt, le_of_lt hbstar⟩)
      exact absurd (le_csSup hSbdd
        (⟨⟨le_trans (le_trans hβS.1.1 (le_of_lt hx1)) hdIcc.1, hdIcc.2⟩, hd0⟩ : d ∈ S))
        (not_le.mpr (lt_of_lt_of_le hx1 hdIcc.1))

    have hHderiv_neg : Hb' r j β < 0 := by
      have hcross := Hb_cross r j β hβ0
      have hKneg : 3 * ((r : ℝ) + 4 * (j : ℝ)) * β
          - ((r : ℝ) + (j : ℝ)) * (5 * (r : ℝ) + 8 * (j : ℝ)) < 0 := by
        rw [cross_bracket r j hr β]
        exact mul_neg_of_pos_of_neg h34 (by rw [← hbs]; linarith)
      have hprod : 3 * β * Hb' r j β < 0 := by
        rw [hcross]; exact mul_neg_of_pos_of_neg (Mb_pos_even r j hr β) hKneg
      by_contra h; push Not at h
      exact absurd hprod (not_lt.mpr (mul_nonneg (by linarith) h))
    have hlt_right : ∀ᶠ y in nhdsWithin β (Set.Ioi β), Hb r j y < Hb r j β :=
      slope_neg_right (Hb_hasDeriv r j hr hj β) hHderiv_neg
    rw [hβ0] at hlt_right
    have hgt_right : ∀ᶠ y in nhdsWithin β (Set.Ioi β), 0 < Hb r j y := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hβbs)]
        with y hy1 hy2
      exact hpos_right y hy1 (le_of_lt hy2)
    obtain ⟨y, hya, hyb⟩ := (hlt_right.and hgt_right).exists
    linarith
  ·
    set S := Set.Icc bs b ∩ (fun x => Hb r j x) ⁻¹' {0} with hSdef
    have hScl : IsClosed S := isClosed_Icc.inter (isClosed_singleton.preimage hcont)
    have hSbdd : BddBelow S := bddBelow_Icc.mono Set.inter_subset_left
    obtain ⟨c, hcIcc, hc0⟩ := intermediate_value_Icc' (le_of_lt hgt) hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (Hb r j b) (Hb r j bs) from ⟨le_of_lt hcon, le_of_lt hbstar⟩)
    have hSne : S.Nonempty := ⟨c, hcIcc, hc0⟩
    set β := sInf S with hβdef
    have hβS : β ∈ S := hScl.csInf_mem hSne hSbdd
    have hβ0 : Hb r j β = 0 := hβS.2
    have hβbs : bs < β := lt_of_le_of_ne hβS.1.1 (fun h => by rw [← h] at hβ0; linarith)
    have hβpos : 0 < β := lt_of_lt_of_le hbspos (le_of_lt hβbs)

    have hpos_left : ∀ x, bs ≤ x → x < β → 0 < Hb r j x := by
      intro x hx1 hx2
      by_contra hxle; push Not at hxle
      have hxne : Hb r j x ≠ 0 := fun h =>
        absurd (csInf_le hSbdd (⟨⟨hx1, le_trans (le_of_lt hx2) hβS.1.2⟩, h⟩ : x ∈ S))
          (not_le.mpr hx2)
      have hxlt : Hb r j x < 0 := lt_of_le_of_ne hxle hxne
      obtain ⟨d, hdIcc, hd0⟩ := intermediate_value_Icc' hx1 hcont.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (Hb r j x) (Hb r j bs) from ⟨le_of_lt hxlt, le_of_lt hbstar⟩)
      exact absurd (csInf_le hSbdd
        (⟨⟨hdIcc.1, le_trans (le_trans hdIcc.2 (le_of_lt hx2)) hβS.1.2⟩, hd0⟩ : d ∈ S))
        (not_le.mpr (lt_of_le_of_lt hdIcc.2 hx2))

    have hHderiv_pos : 0 < Hb' r j β := by
      have hcross := Hb_cross r j β hβ0
      have hKpos : 0 < 3 * ((r : ℝ) + 4 * (j : ℝ)) * β
          - ((r : ℝ) + (j : ℝ)) * (5 * (r : ℝ) + 8 * (j : ℝ)) := by
        rw [cross_bracket r j hr β]
        exact mul_pos h34 (by rw [← hbs]; linarith)
      have hprod : 0 < 3 * β * Hb' r j β := by
        rw [hcross]; exact mul_pos (Mb_pos_even r j hr β) hKpos
      by_contra h; push Not at h
      exact absurd hprod (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (by linarith) h))
    have hlt_left : ∀ᶠ y in nhdsWithin β (Set.Iio β), Hb r j y < Hb r j β :=
      slope_pos_left (Hb_hasDeriv r j hr hj β) hHderiv_pos
    rw [hβ0] at hlt_left
    have hgt_left : ∀ᶠ y in nhdsWithin β (Set.Iio β), 0 < Hb r j y := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hβbs)]
        with y hy1 hy2
      exact hpos_left y (le_of_lt hy2) hy1
    obtain ⟨y, hya, hyb⟩ := (hlt_left.and hgt_left).exists
    linarith

/--
@isnad1 id=le.4h3v.s7.ca6d7e4d88b4 from=translated src=- shape=781d9d56 vocab=52ba7b4a
-/
theorem gamma_moment_bound (r : ℕ) (hr : 1 ≤ r)
    (hbstar_hyp : ∀ j : ℕ, 1 ≤ j → 0 < Hb r j (bstar r j)) :
    ∀ (j : ℕ), 1 ≤ j → ∀ z : ℝ, 0 ≤ z →
      3 * (j : ℝ) * gExp r (fun y => (z * y - 1) ^ (2 * j - 1))
        ≤ ((r : ℝ) + j) * gExp r (fun y => (z * y - 1) ^ (2 * j)) := by
  have hfac : (0 : ℝ) < (Nat.factorial (r - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  intro j hj z hz
  rcases eq_or_lt_of_le hz with rfl | hzpos
  ·
    have hz0eval : ∀ k : ℕ,
        gExp r (fun y => ((0 : ℝ) * y - 1) ^ k) = (-1) ^ k * (Nat.factorial (r - 1) : ℝ) := by
      intro k
      rw [show (fun y : ℝ => ((0 : ℝ) * y - 1) ^ k) = fun y => (-1) ^ k * y ^ 0 from by
            funext y; simp,
          gExp_const_mul, gExp_monomial, Nat.add_zero]
    rw [hz0eval (2 * j - 1), hz0eval (2 * j),
        show (-1 : ℝ) ^ (2 * j - 1) = -1 from Odd.neg_one_pow ⟨j - 1, by omega⟩,
        show (-1 : ℝ) ^ (2 * j) = 1 from Even.neg_one_pow ⟨j, by omega⟩]
    nlinarith [hfac, (by positivity : (0 : ℝ) ≤ (j : ℝ)), (by positivity : (0 : ℝ) ≤ (r : ℝ)),
      mul_nonneg (show (0 : ℝ) ≤ (r : ℝ) + 4 * (j : ℝ) by positivity) hfac.le]
  ·
    set b := z⁻¹ with hbdef
    have hbpos : 0 < b := by rw [hbdef]; positivity
    have hconv : ∀ k : ℕ, gExp r (fun y => (z * y - 1) ^ k) = z ^ k * Mb r b k := by
      intro k
      have hpt : (fun y : ℝ => (z * y - 1) ^ k) = fun y => z ^ k * (y - b) ^ k := by
        funext y
        have : z * y - 1 = z * (y - b) := by
          rw [hbdef, mul_sub, mul_inv_cancel₀ (ne_of_gt hzpos)]
        rw [this, mul_pow]
      unfold Mb
      rw [hpt, gExp_const_mul]
    have hHb : 0 ≤ Hb r j b := Hb_nonneg r j hr hj (hbstar_hyp j hj) b hbpos
    have hHb' : 3 * (j : ℝ) * b * Mb r b (2 * j - 1) ≤ ((r : ℝ) + j) * Mb r b (2 * j) := by
      unfold Hb at hHb; linarith
    have hkey : z ^ (2 * j - 1) * z = z ^ (2 * j) := by rw [← pow_succ]; congr 1; omega
    have hbz : b * z ^ (2 * j) = z ^ (2 * j - 1) := by
      rw [hbdef, ← hkey, mul_comm (z ^ (2 * j - 1)) z, ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt hzpos), one_mul]
    rw [hconv (2 * j - 1), hconv (2 * j)]
    calc 3 * (j : ℝ) * (z ^ (2 * j - 1) * Mb r b (2 * j - 1))
        = 3 * (j : ℝ) * b * Mb r b (2 * j - 1) * z ^ (2 * j) := by rw [← hbz]; ring
      _ ≤ ((r : ℝ) + j) * Mb r b (2 * j) * z ^ (2 * j) :=
          mul_le_mul_of_nonneg_right hHb' (by positivity)
      _ = ((r : ℝ) + j) * (z ^ (2 * j) * Mb r b (2 * j)) := by ring

noncomputable def cc (r j : ℕ) : ℝ := 3 * (j : ℝ) * bstar r j / ((r : ℝ) + j)

noncomputable def dd (r j : ℕ) : ℝ := 2 * ((r : ℝ) + j) / 3

noncomputable def Gg (r j : ℕ) (x : ℝ) : ℝ := x ^ (2 * j) * (x + bstar r j) ^ r * Real.exp (-x)

private lemma cast_add_pos (r j : ℕ) (hr : 1 ≤ r) : (0 : ℝ) < (r : ℝ) + j := by
  have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h2 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  linarith
private lemma cast_add4_pos (r j : ℕ) (hr : 1 ≤ r) : (0 : ℝ) < (r : ℝ) + 4 * (j : ℝ) := by
  have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h2 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  linarith

/--
@isnad1 id=eq.1h2v.s5.417ae9031147 from=translated src=- shape=ec5d8fc1 vocab=b06e1ae7
-/
lemma cd_mul (r j : ℕ) (hr : 1 ≤ r) : cc r j * dd r j = 2 * (j : ℝ) * bstar r j := by
  have h := (cast_add_pos r j hr).ne'
  unfold cc dd; field_simp

/--
@isnad1 id=eq.1h2v.s6.12201ee3e779 from=translated src=- shape=7c7c6cb6 vocab=9052caec
-/
lemma bstar_sub_dd (r j : ℕ) (hr : 1 ≤ r) :
    bstar r j - dd r j = (r : ℝ) * ((r : ℝ) + j) / ((r : ℝ) + 4 * (j : ℝ)) := by
  have h := (cast_add4_pos r j hr).ne'
  unfold bstar dd; field_simp; ring

/--
@isnad1 id=eq.1h2v.s6.b8eea827abbd from=translated src=- shape=b79e4f57 vocab=b7b39322
-/
lemma cc_sub_dd (r j : ℕ) (hr : 1 ≤ r) : cc r j - dd r j = (r : ℝ) + 2 * (j : ℝ) - bstar r j := by
  have h := (cast_add_pos r j hr).ne'
  have h4 := (cast_add4_pos r j hr).ne'
  unfold cc dd bstar; field_simp; ring

/--
@isnad1 id=hasderiv.2h3v.s7.b88f0db20402 from=translated src=- shape=8da30b41 vocab=d7d7a431
-/
lemma Gg_hasDeriv (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (x : ℝ) :
    HasDerivAt (Gg r j)
      (x ^ (2 * j - 1) * (x + bstar r j) ^ (r - 1) * Real.exp (-x)
        * (cc r j - x) * (x + dd r j)) x := by
  have hu : HasDerivAt (fun x : ℝ => x ^ (2 * j)) (((2 * j : ℕ) : ℝ) * x ^ (2 * j - 1)) x :=
    hasDerivAt_pow (2 * j) x
  have hb : HasDerivAt (fun x : ℝ => x + bstar r j) 1 x := by
    simpa using (hasDerivAt_id x).add_const (bstar r j)
  have hv : HasDerivAt (fun x : ℝ => (x + bstar r j) ^ r)
      (((r : ℕ) : ℝ) * (x + bstar r j) ^ (r - 1) * 1) x := hb.pow r
  have hw : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-(Real.exp (-x))) x := by
    simpa using (hasDerivAt_neg' x).exp
  have hraw := (hu.mul hv).mul hw
  have htgt : x ^ (2 * j - 1) * (x + bstar r j) ^ (r - 1) * Real.exp (-x)
        * (cc r j - x) * (x + dd r j)
      = ((((2 * j : ℕ) : ℝ) * x ^ (2 * j - 1)) * (x + bstar r j) ^ r
            + x ^ (2 * j) * (((r : ℕ) : ℝ) * (x + bstar r j) ^ (r - 1) * 1)) * Real.exp (-x)
          + x ^ (2 * j) * (x + bstar r j) ^ r * -Real.exp (-x) := by
    have hx2j : x ^ (2 * j) = x * x ^ (2 * j - 1) := by rw [← pow_succ']; congr 1; omega
    have hxbr : (x + bstar r j) ^ r = (x + bstar r j) * (x + bstar r j) ^ (r - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hx2j, hxbr]; push_cast
    linear_combination
      (x ^ (2 * j - 1) * (x + bstar r j) ^ (r - 1) * Real.exp (-x) * x) * cc_sub_dd r j hr
      + (x ^ (2 * j - 1) * (x + bstar r j) ^ (r - 1) * Real.exp (-x)) * cd_mul r j hr
  rw [show Gg r j = fun x => x ^ (2 * j) * (x + bstar r j) ^ r * Real.exp (-x) from rfl, htgt]
  exact hraw

/--
@isnad1 id=eq.2h3v.s7.ca2be05534a8 from=translated src=- shape=31b75b62 vocab=7177b14e
-/
lemma Hb_integral_form (r j : ℕ) (_hr : 1 ≤ r) (hj : 1 ≤ j) (b : ℝ) :
    Hb r j b = ∫ y in Set.Ioi (0 : ℝ),
      y ^ (r - 1) * Real.exp (-y)
        * ((y - b) ^ (2 * j - 1) * (((r : ℝ) + j) * (y - b) - 3 * (j : ℝ) * b)) := by
  have hf : MeasureTheory.IntegrableOn
      (fun y => ((r : ℝ) + j) * (y ^ (r - 1) * Real.exp (-y) * (y - b) ^ (2 * j)))
      (Set.Ioi (0 : ℝ)) :=
    (pow_exp_pow_int_b r (r - 1) (2 * j) (le_refl _) b).const_mul ((r : ℝ) + j)
  have hg : MeasureTheory.IntegrableOn
      (fun y => 3 * (j : ℝ) * b * (y ^ (r - 1) * Real.exp (-y) * (y - b) ^ (2 * j - 1)))
      (Set.Ioi (0 : ℝ)) :=
    (pow_exp_pow_int_b r (r - 1) (2 * j - 1) (le_refl _) b).const_mul (3 * (j : ℝ) * b)
  unfold Hb Mb gExp
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_sub hf hg]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  have hpow : (y - b) ^ (2 * j) = (y - b) ^ (2 * j - 1) * (y - b) := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow]; ring

/--
@isnad1 id=lt.1h2v.s4.cb994ff89e48 from=translated src=- shape=678da05f vocab=c19cedc3
-/
lemma dd_lt_bstar (r j : ℕ) (hr : 1 ≤ r) : dd r j < bstar r j := by
  have h := bstar_sub_dd r j hr
  have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h2 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have h4 := cast_add4_pos r j hr
  have hnum : 0 < (r : ℝ) * ((r : ℝ) + j) / ((r : ℝ) + 4 * (j : ℝ)) := by positivity
  linarith

/--
@isnad1 id=eq.1h2v.s4.22c6f58d5f2d from=translated src=- shape=c36f83eb vocab=2f258922
-/
lemma Gg_neg_bstar (r j : ℕ) (hr : 1 ≤ r) : Gg r j (-(bstar r j)) = 0 := by
  unfold Gg
  rw [show -(bstar r j) + bstar r j = 0 from by ring, zero_pow (show r ≠ 0 by omega)]
  ring

/--
@isnad1 id=tendsto.0h2v.s4.9dda16baea72 from=translated src=- shape=6ce139b3 vocab=38e0303b
-/
lemma Gg_tendsto (r j : ℕ) : Filter.Tendsto (Gg r j) Filter.atTop (nhds 0) := by
  have hsum : Gg r j = fun x => ∑ i ∈ Finset.range (r + 1),
      (Nat.choose r i : ℝ) * (bstar r j) ^ (r - i) * (x ^ (2 * j + i) * Real.exp (-x)) := by
    funext x; unfold Gg
    rw [add_pow, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pow_add]; ring
  rw [hsum, show (0 : ℝ) = ∑ _i ∈ Finset.range (r + 1), (0 : ℝ) from by simp]
  refine tendsto_finsetSum _ (fun i _ => ?_)
  simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (2 * j + i)).const_mul
    ((Nat.choose r i : ℝ) * (bstar r j) ^ (r - i))

/--
@isnad1 id=analytic.0h3v.s5.2325f4664822 from=translated src=- shape=6e3afc3f vocab=07e1ea69
-/
lemma Gg_analyticAt (r j : ℕ) (x : ℝ) : AnalyticAt ℝ (Gg r j) x := by
  unfold Gg; fun_prop

/--
@isnad1 id=analytic.0h2v.s6.3e1af7e40ef4 from=translated src=- shape=d1714f0e vocab=506e75cb
-/
lemma dslope_Gg_analyticAt (r j : ℕ) :
    AnalyticAt ℝ (dslope (Gg r j) (-(dd r j))) (-(dd r j)) := by
  obtain ⟨p, hp⟩ := Gg_analyticAt r j (-(dd r j))
  exact hp.has_fpower_series_dslope_fslope.analyticAt

/--
@isnad1 id=differen.0h2v.s6.d9dc61cc1ef8 from=translated src=- shape=d1714f0e vocab=66d480a7
-/
lemma dslope_Gg_differentiableAt (r j : ℕ) :
    DifferentiableAt ℝ (dslope (Gg r j) (-(dd r j))) (-(dd r j)) :=
  (dslope_Gg_analyticAt r j).differentiableAt

/--
@isnad1 id=tendsto.0h2v.s5.e9daf6e4323c from=translated src=- shape=7c2d3c3d vocab=27bbbfce
-/
lemma dslope_Gg_tendsto (r j : ℕ) :
    Tendsto (dslope (Gg r j) (-(dd r j))) atTop (𝓝 0) := by
  have hev : dslope (Gg r j) (-(dd r j)) =ᶠ[atTop]
      fun x => (Gg r j x - Gg r j (-(dd r j))) / (x + dd r j) := by
    filter_upwards [eventually_gt_atTop (-(dd r j))] with x hx
    rw [dslope_of_ne _ hx.ne', slope_def_field, show x - -(dd r j) = x + dd r j from by ring]
  rw [tendsto_congr' hev]
  have hnum : Tendsto (fun x => Gg r j x - Gg r j (-(dd r j))) atTop
      (𝓝 (0 - Gg r j (-(dd r j)))) := (Gg_tendsto r j).sub_const _
  have hden : Tendsto (fun x : ℝ => x + dd r j) atTop atTop :=
    tendsto_atTop_add_const_right atTop (dd r j) tendsto_id
  exact hnum.div_atTop hden

/--
@isnad1 id=eq.1h2v.s6.2afc77b68941 from=translated src=- shape=5537d4d9 vocab=4fd7634e
-/
lemma dslope_Gg_neg_b (r j : ℕ) (hr : 1 ≤ r) :
    dslope (Gg r j) (-(dd r j)) (-(bstar r j))
      = Gg r j (-(dd r j)) / (bstar r j - dd r j) := by
  have hne : -(bstar r j) ≠ -(dd r j) := by
    have := dd_lt_bstar r j hr; intro h; exact absurd (neg_injective h) (by linarith)
  rw [dslope_of_ne _ hne, slope_def_field, Gg_neg_bstar r j hr,
      show -(bstar r j) - -(dd r j) = -(bstar r j - dd r j) from by ring, zero_sub, neg_div_neg_eq]

/--
@isnad1 id=hasderiv.3h3v.s8.764806bbe14a from=translated src=- shape=33f40b6b vocab=3cdce33b
-/
lemma dslope_Gg_hasDerivAt_ne (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) {x : ℝ}
    (hx : x ≠ -(dd r j)) :
    HasDerivAt (dslope (Gg r j) (-(dd r j)))
      ((x ^ (2 * j - 1) * (x + bstar r j) ^ (r - 1) * Real.exp (-x) * (cc r j - x) * (x + dd r j)
          * (x + dd r j) - (Gg r j x - Gg r j (-(dd r j))) * 1) / (x + dd r j) ^ 2) x := by
  have hxd : x + dd r j ≠ 0 := by intro h; apply hx; linarith
  have hden : HasDerivAt (fun y : ℝ => y + dd r j) 1 x := by
    simpa using (hasDerivAt_id x).add_const (dd r j)
  have hquot := ((Gg_hasDeriv r j hr hj x).sub_const (Gg r j (-(dd r j)))).div hden hxd
  refine hquot.congr_of_eventuallyEq ?_
  filter_upwards [dslope_eventuallyEq_slope_of_ne (Gg r j) hx] with y hy
  rw [hy, slope_def_field, show y - -(dd r j) = y + dd r j from by ring, Pi.div_apply]

/--
@isnad1 id=eq.3h3v.s8.dd89b34d9fa1 from=translated src=- shape=19b52dcd vocab=d5ff464e
-/
lemma deriv_dslope_Gg_eq (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) {x : ℝ} (hx : x ≠ -(dd r j)) :
    deriv (dslope (Gg r j) (-(dd r j))) x
      = (x ^ (2 * j - 1) * (x + bstar r j) ^ (r - 1) * Real.exp (-x) * (cc r j - x) * (x + dd r j)
          * (x + dd r j) - (Gg r j x - Gg r j (-(dd r j))) * 1) / (x + dd r j) ^ 2 :=
  (dslope_Gg_hasDerivAt_ne r j hr hj hx).deriv

/--
@isnad1 id=continuo.0h2v.s6.2284ee022fcc from=translated src=- shape=8af630c9 vocab=d4a58b4d
-/
lemma deriv_dslope_Gg_continuousAt_neg_dd (r j : ℕ) :
    ContinuousAt (deriv (dslope (Gg r j) (-(dd r j)))) (-(dd r j)) :=
  (dslope_Gg_analyticAt r j).deriv.continuousAt

/--
@isnad1 id=integrab.0h2v.s5.44c5cb0f5136 from=translated src=- shape=08c8c4b9 vocab=29884973
-/
lemma Gg_integrableOn_Ioi0 (r j : ℕ) : MeasureTheory.IntegrableOn (Gg r j) (Set.Ioi (0 : ℝ)) := by
  refine MeasureTheory.IntegrableOn.congr_fun
    (gExp_affinePow_integrableOn (2 * j + 1) r 1 (bstar r j)) (fun y _ => ?_) measurableSet_Ioi
  unfold Gg
  rw [show 2 * j + 1 - 1 = 2 * j from by omega]; ring

/--
@isnad1 id=integrab.1h2v.s7.82c5399ce023 from=translated src=- shape=3888712a vocab=5708afad
-/
lemma GgExpr0_integrableOn_Ioi0 (r j : ℕ) (hj : 1 ≤ j) :
    MeasureTheory.IntegrableOn
      (fun x => x ^ (2 * j - 1) * (x + bstar r j) ^ (r - 1) * Real.exp (-x) * (cc r j - x))
      (Set.Ioi (0 : ℝ)) := by
  have h1 := (gExp_affinePow_integrableOn (2 * j) (r - 1) 1 (bstar r j)).const_mul (cc r j)
  have h2 := gExp_affinePow_integrableOn (2 * j + 1) (r - 1) 1 (bstar r j)
  refine MeasureTheory.IntegrableOn.congr_fun (h1.sub h2) (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, show 2 * j + 1 - 1 = 2 * j from by omega]
  rw [show x ^ (2 * j) = x ^ (2 * j - 1) * x from by rw [← pow_succ]; congr 1; omega]
  ring

/--
@isnad1 id=integrab.1h2v.s6.817b52d50d99 from=translated src=- shape=504f79c7 vocab=265a9919
-/
lemma inv_sq_shift_integrableOn (r j : ℕ) (hr : 1 ≤ r) :
    MeasureTheory.IntegrableOn (fun x : ℝ => (x + dd r j)⁻¹ ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hdd : (0 : ℝ) < dd r j := by unfold dd; positivity
  have hcont : ContinuousOn (fun x : ℝ => (x + dd r j)⁻¹ ^ 2) (Set.Ici (0 : ℝ)) := by
    refine ContinuousOn.pow (ContinuousOn.inv₀ (by fun_prop) ?_) 2
    intro x hx; rw [Set.mem_Ici] at hx
    exact (by linarith : (0 : ℝ) < x + dd r j).ne'
  have hbigO : (fun x : ℝ => (x + dd r j)⁻¹ ^ 2) =O[atTop] (fun x : ℝ => x ^ (-2 : ℝ)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
        abs_of_nonneg (by positivity), abs_of_nonneg (Real.rpow_nonneg hx.le _),
        show (-2 : ℝ) = -(2 : ℕ) from by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast,
        inv_pow]
    exact inv_anti₀ (by positivity) (by nlinarith [hdd.le])
  have hgint : MeasureTheory.IntegrableAtFilter (fun x : ℝ => x ^ (-2 : ℝ)) atTop :=
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos⟩
  exact ((hcont.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop hbigO
    hgint).mono_set Set.Ioi_subset_Ici_self

/--
@isnad1 id=continuo.2h3v.s6.8ba006454c92 from=translated src=- shape=2148e4cc vocab=69f968f7
-/
lemma deriv_dslope_Gg_continuousOn (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (a : ℝ) :
    ContinuousOn (deriv (dslope (Gg r j) (-(dd r j)))) (Set.Ici a) := by
  have hGgc : Continuous (Gg r j) := by unfold Gg; fun_prop
  intro x _
  by_cases hxd : x = -(dd r j)
  · subst hxd; exact (deriv_dslope_Gg_continuousAt_neg_dd r j).continuousWithinAt
  · have hxd' : x + dd r j ≠ 0 := fun h => hxd (by linarith)
    have hcont_expl : ContinuousAt (fun y =>
        (y ^ (2 * j - 1) * (y + bstar r j) ^ (r - 1) * Real.exp (-y) * (cc r j - y)
            * (y + dd r j) * (y + dd r j) - (Gg r j y - Gg r j (-(dd r j))) * 1)
          / (y + dd r j) ^ 2) x := by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · exact pow_ne_zero 2 hxd'
    refine (hcont_expl.congr ?_).continuousWithinAt
    filter_upwards [compl_singleton_mem_nhds hxd] with y hy
    exact (deriv_dslope_Gg_eq r j hr hj hy).symm

/--
@isnad1 id=integrab.2h2v.s6.f7885c68fbac from=translated src=- shape=19adf3c0 vocab=6219cd95
-/
lemma deriv_dslope_Gg_integrableOn_Ioi0 (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    MeasureTheory.IntegrableOn (deriv (dslope (Gg r j) (-(dd r j)))) (Set.Ioi (0 : ℝ)) := by
  have hdd : (0 : ℝ) < dd r j := by
    unfold dd; have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have : (0 : ℝ) ≤ (j : ℝ) := by positivity
    positivity
  have hinv_meas : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => (x + dd r j)⁻¹ ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (inv_sq_shift_integrableOn r j hr).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ‖(x + dd r j)⁻¹ ^ 2‖ ≤ (dd r j)⁻¹ ^ 2 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    rw [Set.mem_Ioi] at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    linarith
  have hGgmul : MeasureTheory.IntegrableOn
      (fun x => Gg r j x * (x + dd r j)⁻¹ ^ 2) (Set.Ioi (0 : ℝ)) :=
    (Gg_integrableOn_Ioi0 r j).mul_bdd hinv_meas hbound
  have hG0mul : MeasureTheory.IntegrableOn
      (fun x => Gg r j (-(dd r j)) * (x + dd r j)⁻¹ ^ 2) (Set.Ioi (0 : ℝ)) :=
    (inv_sq_shift_integrableOn r j hr).const_mul _
  have hdecomp := (GgExpr0_integrableOn_Ioi0 r j hj).sub (hGgmul.sub hG0mul)
  refine MeasureTheory.IntegrableOn.congr_fun hdecomp (fun x hx => ?_) measurableSet_Ioi
  rw [Set.mem_Ioi] at hx
  have hxne : x ≠ -(dd r j) := fun h => by rw [h] at hx; linarith
  have hxd : x + dd r j ≠ 0 := fun h => hxne (by linarith)
  simp only [Pi.sub_apply]
  rw [deriv_dslope_Gg_eq r j hr hj hxne]
  unfold Gg
  field_simp

/--
@isnad1 id=differen.0h3v.s6.7dcaf63c1422 from=translated src=- shape=e0aa8e9d vocab=66d480a7
-/
lemma dslope_Gg_differentiableAt_all (r j : ℕ) (x : ℝ) :
    DifferentiableAt ℝ (dslope (Gg r j) (-(dd r j))) x := by
  by_cases hxd : x = -(dd r j)
  · subst hxd; exact dslope_Gg_differentiableAt r j
  · exact (differentiableAt_dslope_of_ne hxd).mpr (Gg_analyticAt r j x).differentiableAt

/--
@isnad1 id=integrab.2h2v.s6.26114b821a13 from=translated src=- shape=3490a4c7 vocab=e961594e
-/
lemma deriv_dslope_Gg_integrableOn (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    MeasureTheory.IntegrableOn (deriv (dslope (Gg r j) (-(dd r j)))) (Set.Ioi (-(bstar r j))) := by
  have hb : -(bstar r j) ≤ 0 := by have := bstar_pos r j hr; linarith
  rw [show Set.Ioi (-(bstar r j)) = Set.Ioc (-(bstar r j)) 0 ∪ Set.Ioi 0 from
      (Set.Ioc_union_Ioi_eq_Ioi hb).symm, MeasureTheory.integrableOn_union]
  refine ⟨?_, deriv_dslope_Gg_integrableOn_Ioi0 r j hr hj⟩
  exact (((deriv_dslope_Gg_continuousOn r j hr hj (-(bstar r j))).mono
    Set.Icc_subset_Ici_self).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self

/--
@isnad1 id=eq.2h2v.s7.eb8fded0c2f5 from=translated src=- shape=a54f1f89 vocab=fdf57779
-/
lemma dslope_Gg_ftc (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    ∫ x in Set.Ioi (-(bstar r j)), deriv (dslope (Gg r j) (-(dd r j))) x
      = -(Gg r j (-(dd r j)) / (bstar r j - dd r j)) := by
  have hbne : -(bstar r j) ≠ -(dd r j) := by
    have := dd_lt_bstar r j hr; exact fun h => absurd (neg_injective h) (by linarith)
  have hcont : ContinuousWithinAt (dslope (Gg r j) (-(dd r j))) (Set.Ici (-(bstar r j)))
      (-(bstar r j)) :=
    (((continuousAt_dslope_of_ne hbne).mpr
      (by unfold Gg; fun_prop : Continuous (Gg r j)).continuousAt)).continuousWithinAt
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont
      (fun x _ => (dslope_Gg_differentiableAt_all r j x).hasDerivAt)
      (deriv_dslope_Gg_integrableOn r j hr hj) (dslope_Gg_tendsto r j),
    dslope_Gg_neg_b r j hr, zero_sub]

/--
@isnad1 id=integrab.2h2v.s7.0d62bc78a217 from=translated src=- shape=7e264958 vocab=5708afad
-/
lemma GgExpr0_integrableOn (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    MeasureTheory.IntegrableOn
      (fun x => x ^ (2 * j - 1) * (x + bstar r j) ^ (r - 1) * Real.exp (-x) * (cc r j - x))
      (Set.Ioi (-(bstar r j))) := by
  have hb : -(bstar r j) ≤ 0 := by have := bstar_pos r j hr; linarith
  rw [show Set.Ioi (-(bstar r j)) = Set.Ioc (-(bstar r j)) 0 ∪ Set.Ioi 0 from
      (Set.Ioc_union_Ioi_eq_Ioi hb).symm, MeasureTheory.integrableOn_union]
  refine ⟨?_, GgExpr0_integrableOn_Ioi0 r j hj⟩
  have hcont : ContinuousOn
      (fun x => x ^ (2 * j - 1) * (x + bstar r j) ^ (r - 1) * Real.exp (-x) * (cc r j - x))
      (Set.Icc (-(bstar r j)) 0) := by fun_prop
  exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

/--
@isnad1 id=eq.2h2v.s7.cd466458a34e from=translated src=- shape=0f07378a vocab=daf4b6b9
-/
lemma Hb_bstar_eq (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    Hb r j (bstar r j)
      = -(Real.exp (-(bstar r j)) * ((r : ℝ) + j))
        * ∫ x in Set.Ioi (-(bstar r j)),
            x ^ (2 * j - 1) * (x + bstar r j) ^ (r - 1) * Real.exp (-x) * (cc r j - x) := by
  set b := bstar r j with hbdef
  have hmp : MeasureTheory.MeasurePreserving (fun x => x + b) MeasureTheory.volume
      MeasureTheory.volume :=
    ⟨(continuous_add_const b).measurable, MeasureTheory.map_add_right_eq_self MeasureTheory.volume b⟩
  have hme : MeasurableEmbedding (fun x => x + b) :=
    (Homeomorph.addRight b).isClosedEmbedding.measurableEmbedding
  have hcc : ((r : ℝ) + j) * cc r j = 3 * (j : ℝ) * b := by rw [hbdef]; unfold cc; field_simp
  rw [Hb_integral_form r j hr hj b, ← hmp.setIntegral_preimage_emb hme _ (Set.Ioi 0),
    show (fun x => x + b) ⁻¹' Set.Ioi (0 : ℝ) = Set.Ioi (-b) from by
      rw [preimage_add_const_Ioi]; norm_num,
    ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  simp only [add_sub_cancel_right]
  rw [show -(x + b) = -x + -b from by ring, Real.exp_add]
  linear_combination
    ((x + b) ^ (r - 1) * Real.exp (-x) * Real.exp (-b) * x ^ (2 * j - 1)) * hcc

/--
@isnad1 id=eq.3h3v.s8.1a86cda8ae50 from=translated src=- shape=1f1e905e vocab=d5ff464e
-/
lemma deriv_dslope_Gg_eq_add (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) {x : ℝ} (hx : x ≠ -(dd r j)) :
    deriv (dslope (Gg r j) (-(dd r j))) x
      = x ^ (2 * j - 1) * (x + bstar r j) ^ (r - 1) * Real.exp (-x) * (cc r j - x)
        + (Gg r j (-(dd r j)) - Gg r j x) / (x + dd r j) ^ 2 := by
  rw [deriv_dslope_Gg_eq r j hr hj hx]
  have hxd : x + dd r j ≠ 0 := fun h => hx (by linarith)
  unfold Gg; field_simp; ring

/--
@isnad1 id=lt.3h2v.s6.49c9b219217a from=translated src=- shape=446a3424 vocab=8a47d20c
-/
lemma Hb_bstar_pos_of_max (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j)
    (hmax : ∀ x ∈ Set.Ioi (-(bstar r j)), Gg r j x ≤ Gg r j (-(dd r j))) :
    0 < Hb r j (bstar r j) := by
  set b := bstar r j with hbdef
  set E : ℝ → ℝ := fun x => x ^ (2 * j - 1) * (x + b) ^ (r - 1) * Real.exp (-x) * (cc r j - x)
    with hEdef
  set J : ℝ → ℝ := fun x => (Gg r j (-(dd r j)) - Gg r j x) / (x + dd r j) ^ 2 with hJdef
  have hEint : MeasureTheory.IntegrableOn E (Set.Ioi (-b)) := GgExpr0_integrableOn r j hr hj
  have hDint : MeasureTheory.IntegrableOn (deriv (dslope (Gg r j) (-(dd r j)))) (Set.Ioi (-b)) :=
    deriv_dslope_Gg_integrableOn r j hr hj

  have hne_ae : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioi (-b))), x ≠ -(dd r j) := by
    apply MeasureTheory.ae_restrict_of_ae
    rw [MeasureTheory.ae_iff]; simp
  have hDae : deriv (dslope (Gg r j) (-(dd r j))) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (-b))]
      fun x => E x + J x := by
    filter_upwards [hne_ae] with x hx using deriv_dslope_Gg_eq_add r j hr hj hx
  have hJint : MeasureTheory.IntegrableOn J (Set.Ioi (-b)) :=
    (hDint.sub hEint).congr (by
      filter_upwards [hDae] with x hx; simp only [Pi.sub_apply]; rw [hx]; ring)

  have hsplit : (∫ x in Set.Ioi (-b), E x) + ∫ x in Set.Ioi (-b), J x
      = -(Gg r j (-(dd r j)) / (b - dd r j)) := by
    rw [← MeasureTheory.integral_add hEint hJint,
      ← MeasureTheory.integral_congr_ae hDae, dslope_Gg_ftc r j hr hj]

  have hJnn : 0 ≤ ∫ x in Set.Ioi (-b), J x := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun x hx => ?_)
    rw [hJdef]
    exact div_nonneg (by linarith [hmax x hx]) (by positivity)

  have hd : (0 : ℝ) < dd r j := by
    unfold dd; have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have h2 : (0 : ℝ) ≤ (j : ℝ) := by positivity
    positivity
  have hddlt : dd r j < b := by rw [hbdef]; exact dd_lt_bstar r j hr
  have hbdd : 0 < b - dd r j := by linarith
  have hG0 : 0 < Gg r j (-(dd r j)) := by
    unfold Gg
    rw [Even.neg_pow (even_two.mul_right j), show -(dd r j) + b = b - dd r j from by ring]
    have hp1 : (0 : ℝ) < (dd r j) ^ (2 * j) := by positivity
    have hp2 : (0 : ℝ) < (b - dd r j) ^ r := by positivity
    positivity
  have hEval : (∫ x in Set.Ioi (-b), E x) = -(Gg r j (-(dd r j)) / (b - dd r j)) - ∫ x in Set.Ioi (-b), J x := by
    linarith [hsplit]
  rw [Hb_bstar_eq r j hr hj, ← hbdef, hEval]
  have hexp : 0 < Real.exp (-b) * ((r : ℝ) + j) := by
    have : (0 : ℝ) < (r : ℝ) + j := by
      have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      have : (0 : ℝ) ≤ (j : ℝ) := by positivity
      linarith
    positivity
  have hg0d : 0 < Gg r j (-(dd r j)) / (b - dd r j) := by positivity
  nlinarith [mul_pos hexp hg0d, mul_nonneg hexp.le hJnn]

/--
@isnad1 id=lt.2h2v.s5.fd63aa8f796d from=translated src=- shape=603a042a vocab=3cfe5dfa
-/
lemma cc_pos (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) : 0 < cc r j := by
  unfold cc
  have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h2 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hb := bstar_pos r j hr
  positivity

/--
@isnad1 id=differen.0h2v.s5.aff098937cf9 from=translated src=- shape=feb27325 vocab=651fb2b6
-/
lemma Gg_differentiable (r j : ℕ) : Differentiable ℝ (Gg r j) :=
  fun x => (Gg_analyticAt r j x).differentiableAt

/--
@isnad1 id=eq.2h3v.s7.f7382163e528 from=translated src=- shape=e3ea2f79 vocab=e241cb5f
-/
lemma deriv_Gg_eq (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) (x : ℝ) :
    deriv (Gg r j) x
      = x ^ (2 * j - 1) * (x + bstar r j) ^ (r - 1) * Real.exp (-x) * (cc r j - x) * (x + dd r j) :=
  (Gg_hasDeriv r j hr hj x).deriv

/--
@isnad1 id=le.4h3v.s6.c1340b793719 from=translated src=- shape=7a3be14e vocab=89527fc4
-/
lemma Gg_le_neg_dd_of_cc_le (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j)
    (hcc : Gg r j (cc r j) ≤ Gg r j (-(dd r j))) :
    ∀ x ∈ Set.Ioi (-(bstar r j)), Gg r j x ≤ Gg r j (-(dd r j)) := by
  have hd : (0 : ℝ) < dd r j := by
    unfold dd; have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have : (0 : ℝ) ≤ (j : ℝ) := by positivity
    positivity
  have hc : (0 : ℝ) < cc r j := cc_pos r j hr hj
  have hddb : dd r j < bstar r j := dd_lt_bstar r j hr
  have hbpos : (0 : ℝ) < bstar r j := bstar_pos r j hr
  have hGgcont : Continuous (Gg r j) := by unfold Gg; fun_prop
  have hfac : ∀ x : ℝ, deriv (Gg r j) x
      = (x ^ (2 * j - 1) * (cc r j - x) * (x + dd r j)) * ((x + bstar r j) ^ (r - 1) * Real.exp (-x)) :=
    fun x => by rw [deriv_Gg_eq r j hr hj]; ring
  have hodd_np : ∀ y : ℝ, y ≤ 0 → y ^ (2 * j - 1) ≤ 0 := fun y hy => by
    rw [show 2 * j - 1 = 2 * (j - 1) + 1 from by omega, pow_succ, pow_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hy
  have hodd_nn : ∀ y : ℝ, 0 ≤ y → 0 ≤ y ^ (2 * j - 1) := fun y hy => pow_nonneg hy _
  have hposf : ∀ x : ℝ, -(bstar r j) < x → 0 < (x + bstar r j) ^ (r - 1) * Real.exp (-x) :=
    fun x hx => mul_pos (pow_pos (by linarith) _) (Real.exp_pos _)

  have hmono1 : MonotoneOn (Gg r j) (Set.Icc (-(bstar r j)) (-(dd r j))) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hGgcont.continuousOn
      (Gg_differentiable r j).differentiableOn (fun x hx => ?_)
    rw [interior_Icc, Set.mem_Ioo] at hx; obtain ⟨hxl, hxr⟩ := hx
    rw [hfac]
    exact mul_nonneg (mul_nonneg_iff.mpr (Or.inr
      ⟨mul_nonpos_iff.mpr (Or.inr ⟨hodd_np x (by linarith), by linarith⟩), by linarith⟩))
      (hposf x hxl).le
  have hanti1 : AntitoneOn (Gg r j) (Set.Icc (-(dd r j)) 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hGgcont.continuousOn
      (Gg_differentiable r j).differentiableOn (fun x hx => ?_)
    rw [interior_Icc, Set.mem_Ioo] at hx; obtain ⟨hxl, hxr⟩ := hx
    rw [hfac]
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_iff.mpr (Or.inr
      ⟨mul_nonpos_iff.mpr (Or.inr ⟨hodd_np x (by linarith), by linarith⟩), by linarith⟩))
      (hposf x (by linarith)).le
  have hmono2 : MonotoneOn (Gg r j) (Set.Icc 0 (cc r j)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hGgcont.continuousOn
      (Gg_differentiable r j).differentiableOn (fun x hx => ?_)
    rw [interior_Icc, Set.mem_Ioo] at hx; obtain ⟨hxl, hxr⟩ := hx
    rw [hfac]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hodd_nn x (le_of_lt hxl)) (by linarith [hxr]))
      (by linarith [hxl, hd])) (hposf x (by linarith [hxl, hbpos])).le
  have hanti2 : AntitoneOn (Gg r j) (Set.Ici (cc r j)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici _) hGgcont.continuousOn
      (Gg_differentiable r j).differentiableOn (fun x hx => ?_)
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [hfac]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (hodd_nn x (by linarith)) (by linarith))
        (by linarith))
      (hposf x (by linarith)).le

  intro x hx; rw [Set.mem_Ioi] at hx
  have hnegdd_mem1 : -(dd r j) ∈ Set.Icc (-(bstar r j)) (-(dd r j)) := ⟨by linarith, le_refl _⟩
  rcases le_total x (-(dd r j)) with h1 | h1
  · exact hmono1 ⟨le_of_lt hx, h1⟩ hnegdd_mem1 h1
  · rcases le_total x 0 with h0 | h0
    · exact hanti1 ⟨le_refl _, by linarith⟩ ⟨h1, h0⟩ h1
    · rcases le_total x (cc r j) with hc' | hc'
      · exact le_trans (hmono2 ⟨h0, hc'⟩ ⟨le_of_lt hc, le_refl _⟩ hc') hcc
      · exact le_trans (hanti2 Set.self_mem_Ici hc' hc') hcc

/--
@isnad1 id=lt.3h2v.s5.7daf35277dc8 from=translated src=- shape=ced3b347 vocab=f8d180f2
-/
lemma Hb_bstar_pos_of_cc_le (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j)
    (hcc : Gg r j (cc r j) ≤ Gg r j (-(dd r j))) : 0 < Hb r j (bstar r j) :=
  Hb_bstar_pos_of_max r j hr hj (Gg_le_neg_dd_of_cc_le r j hr hj hcc)

/--
@isnad1 id=le.3h2v.s7.7283e00aa03f from=translated src=- shape=0b984a77 vocab=03504b8a
-/
lemma Gg_cc_le_neg_dd (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j)
    (hL : 2 * (j : ℝ) * Real.log (cc r j) + (r : ℝ) * Real.log (cc r j + bstar r j) - cc r j
        ≤ 2 * (j : ℝ) * Real.log (dd r j) + (r : ℝ) * Real.log (bstar r j - dd r j) + dd r j) :
    Gg r j (cc r j) ≤ Gg r j (-(dd r j)) := by
  have hcc : 0 < cc r j := cc_pos r j hr hj
  have hd : 0 < dd r j := by
    unfold dd; have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have : (0 : ℝ) ≤ (j : ℝ) := by positivity
    positivity
  have hbpos : 0 < bstar r j := bstar_pos r j hr
  have hbd : 0 < bstar r j - dd r j := by have := dd_lt_bstar r j hr; linarith
  have hccb : 0 < cc r j + bstar r j := by linarith
  have hGcc : 0 < Gg r j (cc r j) := by unfold Gg; positivity
  have hGdd : 0 < Gg r j (-(dd r j)) := by
    unfold Gg
    rw [Even.neg_pow (even_two.mul_right j),
        show -(dd r j) + bstar r j = bstar r j - dd r j from by ring]
    positivity
  rw [← Real.log_le_log_iff hGcc hGdd]
  have hlogcc : Real.log (Gg r j (cc r j))
      = 2 * (j : ℝ) * Real.log (cc r j) + (r : ℝ) * Real.log (cc r j + bstar r j) - cc r j := by
    unfold Gg
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_exp]
    push_cast; ring
  have hlogdd : Real.log (Gg r j (-(dd r j)))
      = 2 * (j : ℝ) * Real.log (dd r j) + (r : ℝ) * Real.log (bstar r j - dd r j) + dd r j := by
    unfold Gg
    rw [Even.neg_pow (even_two.mul_right j),
        show -(dd r j) + bstar r j = bstar r j - dd r j from by ring,
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_exp]
    push_cast; ring
  rw [hlogcc, hlogdd]; exact hL

/--
@isnad1 id=le.2h2v.s7.799201fc3b82 from=translated src=- shape=35bbd0e0 vocab=0fc24e15
-/
lemma hL_of_Lexpr (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) :
    2 * (j : ℝ) * Real.log (cc r j) + (r : ℝ) * Real.log (cc r j + bstar r j) - cc r j
      ≤ 2 * (j : ℝ) * Real.log (dd r j) + (r : ℝ) * Real.log (bstar r j - dd r j) + dd r j := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hrj : (0 : ℝ) < (r : ℝ) + j := by linarith
  have hr4j : (0 : ℝ) < (r : ℝ) + 4 * j := by linarith
  have hcc : 0 < cc r j := cc_pos r j hr hj
  have hdd : 0 < dd r j := by unfold dd; positivity
  have hbstar : 0 < bstar r j := bstar_pos r j hr
  have hbd : 0 < bstar r j - dd r j := by have := dd_lt_bstar r j hr; linarith
  have hccb : 0 < cc r j + bstar r j := by linarith
  have ht : (0 : ℝ) < (j : ℝ) / r := div_pos hj0 hr0
  have hLneg := Lexpr_neg ht
  have hA : Aexpr ((j : ℝ) / r) = cc r j / dd r j := by
    unfold Aexpr cc dd bstar
    field_simp
  have hB : Bexpr ((j : ℝ) / r) = (cc r j + bstar r j) / (bstar r j - dd r j) := by
    rw [eq_div_iff (ne_of_gt hbd)]
    unfold Bexpr cc dd bstar
    field_simp
    ring
  have hC : Cexpr ((j : ℝ) / r) = (cc r j + dd r j) / r := by
    unfold Cexpr cc dd bstar
    field_simp
    ring
  have hlogA : Real.log (Aexpr ((j : ℝ) / r)) = Real.log (cc r j) - Real.log (dd r j) := by
    rw [hA, Real.log_div (ne_of_gt hcc) (ne_of_gt hdd)]
  have hlogB : Real.log (Bexpr ((j : ℝ) / r))
      = Real.log (cc r j + bstar r j) - Real.log (bstar r j - dd r j) := by
    rw [hB, Real.log_div (ne_of_gt hccb) (ne_of_gt hbd)]
  unfold Lexpr at hLneg
  rw [hlogA, hlogB, hC] at hLneg
  have hmul : 2 * (j : ℝ) * (Real.log (cc r j) - Real.log (dd r j))
        + (r : ℝ) * (Real.log (cc r j + bstar r j) - Real.log (bstar r j - dd r j))
        - (cc r j + dd r j)
      = r * (2 * ((j : ℝ) / r) * (Real.log (cc r j) - Real.log (dd r j))
        + (Real.log (cc r j + bstar r j) - Real.log (bstar r j - dd r j))
        - (cc r j + dd r j) / r) := by
    field_simp
  have hneg := mul_neg_of_pos_of_neg hr0 hLneg
  rw [← hmul] at hneg
  linarith

/--
@isnad1 id=lt.2h2v.s5.60b3fa6dce3d from=translated src=- shape=e6bbf401 vocab=f0026d98
-/
lemma Hb_bstar_pos (r j : ℕ) (hr : 1 ≤ r) (hj : 1 ≤ j) : 0 < Hb r j (bstar r j) :=
  Hb_bstar_pos_of_cc_le r j hr hj (Gg_cc_le_neg_dd r j hr hj (hL_of_Lexpr r j hr hj))

/--
@isnad1 id=le.3h3v.s7.32ef59736cf6 from=translated src=- shape=1245bd9a vocab=fd9cab6b
-/
theorem gamma_moment_inequality (r : ℕ) (hr : 1 ≤ r) :
    ∀ (j : ℕ), 1 ≤ j → ∀ z : ℝ, 0 ≤ z →
      3 * (j : ℝ) * gExp r (fun y => (z * y - 1) ^ (2 * j - 1))
        ≤ ((r : ℝ) + j) * gExp r (fun y => (z * y - 1) ^ (2 * j)) :=
  gamma_moment_bound r hr (fun j hj => Hb_bstar_pos r j hr hj)

end OddCycleBound.DenseRegion
