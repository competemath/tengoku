import Tengoku.Twinprime.TwinPrime.Analytic.BilinearGcdReduction
import Tengoku.Seed.NumberTheory.Harmonic.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Removing inputs with a large prime square factor

The absolute mass is taken over the actual signed bilinear factor summands.
If the left Möbius coefficient is nonzero, a prime square in the product
lies either wholly in the right factor or across both factors.
-/

noncomputable section

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius Topology

namespace TwinPrime.Analytic

def positiveHyperbolaPairs (T : ℕ) : Finset (ℕ × ℕ) :=
  ((Ioc 0 T).product (Ioc 0 T)).filter (fun ab => ab.1 * ab.2 ≤ T)

/--
@isnad1 id=iff.0h2v.s6.ae65a4540fd6 from=translated src=- shape=abb6fa61 vocab=fecddfd7
-/
theorem mem_positiveHyperbolaPairs_iff (T : ℕ) (ab : ℕ × ℕ) :
    ab ∈ positiveHyperbolaPairs T ↔ 0 < ab.1 ∧ 0 < ab.2 ∧ ab.1 * ab.2 ≤ T := by
  simp only [positiveHyperbolaPairs, mem_filter, Finset.product_eq_sprod, mem_product, mem_Ioc]
  constructor
  · rintro ⟨⟨⟨ha, _⟩, ⟨hb, _⟩⟩, hp⟩
    exact ⟨ha, hb, hp⟩
  · rintro ⟨ha, hb, hp⟩
    exact ⟨⟨⟨ha, (Nat.le_mul_of_pos_right _ hb).trans hp⟩,
      ⟨hb, (Nat.le_mul_of_pos_left _ ha).trans hp⟩⟩, hp⟩

/--
@isnad1 id=eq.0h1v.s5.ea422ab72f57 from=translated src=- shape=bb5f4c8a vocab=2c9adcb2
-/
theorem positiveHyperbolaPairs_card (T : ℕ) :
    (positiveHyperbolaPairs T).card = ∑ d ∈ Ioc 0 T, T / d := by
  simp only [positiveHyperbolaPairs, card_eq_sum_ones, sum_filter,
    Finset.product_eq_sprod, sum_product]
  apply sum_congr rfl
  intro d hd
  have hd0 := (mem_Ioc.mp hd).1
  have hset : (Ioc 0 T).filter (fun r => d * r ≤ T) = Ioc 0 (T / d) := by
    ext r
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hr, _⟩, hprod⟩
      exact ⟨hr, (Nat.le_div_iff_mul_le hd0).mpr (by simpa [mul_comm] using hprod)⟩
    · rintro ⟨hr, hdiv⟩
      exact ⟨⟨hr, hdiv.trans (Nat.div_le_self T d)⟩,
        by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd0).mp hdiv⟩
  have hc := congrArg Finset.card hset
  rw [Nat.card_Ioc, Nat.sub_zero] at hc
  simpa only [card_eq_sum_ones, sum_filter] using hc

/--
@isnad1 id=le.0h1v.s5.0540a8242aae from=translated src=- shape=16417a38 vocab=38fb7966
-/
theorem positiveHyperbolaPairs_card_le (T : ℕ) :
    ((positiveHyperbolaPairs T).card : ℝ) ≤ T * (1 + Real.log T) := by
  rw [positiveHyperbolaPairs_card, Nat.cast_sum]
  calc
    _ ≤ ∑ d ∈ Ioc 0 T, (T : ℝ) / d := sum_le_sum fun d _ => Nat.cast_div_le
    _ = (T : ℝ) * (harmonic T : ℝ) := by
      have hI : Ioc 0 T = Icc 1 T := by ext n; simp; omega
      rw [hI]
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      rw [div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log T) (Nat.cast_nonneg T)

/-- A prime square in a product with squarefree left factor has two possible
allocations. Both cases may hold, which is harmless in the counting cover.
@isnad1 id=or.3h3v.s6.a41e7796c6bf from=translated src=- shape=0ca4721e vocab=23087afa
-/
theorem prime_sq_dvd_mul_of_squarefree_left {p d r : ℕ}
    (hp : p.Prime) (hd : Squarefree d) (hprod : p ^ 2 ∣ d * r) :
    p ^ 2 ∣ r ∨ p ∣ d ∧ p ∣ r := by
  by_cases hpd : p ∣ d
  · right
    refine ⟨hpd, ?_⟩
    obtain ⟨a, rfl⟩ := hpd
    have hpa : ¬p ∣ a := by
      intro h
      exact (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hd)) h
    have hpr : p ∣ a * r := by
      apply (Nat.dvd_of_mul_dvd_mul_left hp.pos)
      simpa only [pow_two, mul_assoc] using hprod
    exact (hp.dvd_mul.mp hpr).resolve_left hpa
  · left
    exact (hp.coprime_iff_not_dvd.mpr hpd).pow_left 2 |>.dvd_of_dvd_mul_left hprod

def largePrimeSquareInput (H n : ℕ) : Prop :=
  ∃ p, p.Prime ∧ H < p ∧ p ^ 2 ∣ n

def largePrimeSquarePairs (T H : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (positiveHyperbolaPairs T).filter
    (fun dr => Squarefree dr.1 ∧ largePrimeSquareInput H (dr.1 * dr.2))

/--
@isnad1 id=le.1h2v.s6.caa4db202faa from=translated src=- shape=13fbe2e9 vocab=0c0590dc
-/
theorem largePrimeSquarePairs_card_le (T H : ℕ) (hH : 1 ≤ H) :
    ((largePrimeSquarePairs T H).card : ℝ) ≤ 2 * T * (1 + Real.log T) / H := by
  classical
  let R : ℕ → Finset (ℕ × ℕ) := fun p =>
    (positiveHyperbolaPairs (T / p ^ 2)).image (fun ab => (ab.1, p ^ 2 * ab.2))
  let C : ℕ → Finset (ℕ × ℕ) := fun p =>
    (positiveHyperbolaPairs (T / p ^ 2)).image (fun ab => (p * ab.1, p * ab.2))
  have hcover : largePrimeSquarePairs T H ⊆ (Ioc H T).biUnion (fun p => R p ∪ C p) := by
    intro dr hdr
    rcases mem_filter.mp hdr with ⟨hdr, hsq, p, hp, hHp, hpp⟩
    rcases (mem_positiveHyperbolaPairs_iff T dr).mp hdr with ⟨hd0, hr0, hprod⟩
    have hpT : p ≤ T := (Nat.le_of_dvd (Nat.mul_pos hd0 hr0)
      ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hpp)).trans hprod
    apply mem_biUnion.mpr
    refine ⟨p, mem_Ioc.mpr ⟨hHp, hpT⟩, ?_⟩
    rcases prime_sq_dvd_mul_of_squarefree_left hp hsq hpp with hpr | ⟨hpd, hpr⟩
    · obtain ⟨b, hb⟩ := hpr
      apply mem_union_left
      apply mem_image.mpr
      refine ⟨(dr.1, b), ?_, ?_⟩
      · apply (mem_positiveHyperbolaPairs_iff _ _).mpr
        refine ⟨hd0, ?_, (Nat.le_div_iff_mul_le (pow_pos hp.pos 2)).mpr ?_⟩
        · by_contra h
          have : b = 0 := by omega
          simp [this] at hb
          omega
        · dsimp only
          rw [hb] at hprod
          nlinarith only [hprod]
      · exact Prod.ext rfl hb.symm
    · obtain ⟨a, ha⟩ := hpd
      obtain ⟨b, hb⟩ := hpr
      apply mem_union_right
      apply mem_image.mpr
      refine ⟨(a, b), ?_, ?_⟩
      · apply (mem_positiveHyperbolaPairs_iff _ _).mpr
        refine ⟨?_, ?_, (Nat.le_div_iff_mul_le (pow_pos hp.pos 2)).mpr ?_⟩
        · by_contra h
          have : a = 0 := by omega
          simp [this] at ha
          omega
        · by_contra h
          have : b = 0 := by omega
          simp [this] at hb
          omega
        · dsimp only
          rw [ha, hb] at hprod
          nlinarith only [hprod]
      · exact Prod.ext ha.symm hb.symm
  have hcount (p : ℕ) (hp : p ∈ Ioc H T) :
      ((positiveHyperbolaPairs (T / p ^ 2)).card : ℝ) ≤
        ((T : ℝ) * (1 + Real.log T)) * ((p : ℝ) ^ 2)⁻¹ := by
    by_cases hz : T / p ^ 2 = 0
    · simpa [hz, positiveHyperbolaPairs] using
        (show (0 : ℝ) ≤ ((T : ℝ) * (1 + Real.log T)) * ((p : ℝ) ^ 2)⁻¹ by positivity)
    have hz0 : (0 : ℝ) < (T / p ^ 2 : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
    have hzT : ((T / p ^ 2 : ℕ) : ℝ) ≤ T := by exact_mod_cast Nat.div_le_self T (p ^ 2)
    calc
      _ ≤ ((T / p ^ 2 : ℕ) : ℝ) * (1 + Real.log (T / p ^ 2 : ℕ)) :=
        positiveHyperbolaPairs_card_le _
      _ ≤ ((T / p ^ 2 : ℕ) : ℝ) * (1 + Real.log T) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (Real.log_le_log hz0 hzT)) (by positivity)
      _ ≤ ((T : ℝ) / (p ^ 2 : ℕ)) * (1 + Real.log T) :=
        mul_le_mul_of_nonneg_right Nat.cast_div_le (by linarith [Real.log_natCast_nonneg T])
      _ = _ := by push_cast; ring
  calc
    _ ≤ ∑ p ∈ Ioc H T, ((R p ∪ C p).card : ℝ) := by
      exact_mod_cast (card_le_card hcover).trans card_biUnion_le
    _ ≤ ∑ p ∈ Ioc H T, 2 * ((positiveHyperbolaPairs (T / p ^ 2)).card : ℝ) := by
      apply sum_le_sum
      intro p _
      have h := (card_union_le (R p) (C p)).trans
        (Nat.add_le_add (card_image_le) (card_image_le))
      have h' : ((R p ∪ C p).card : ℝ) ≤
          (positiveHyperbolaPairs (T / p ^ 2)).card +
            (positiveHyperbolaPairs (T / p ^ 2)).card := by exact_mod_cast h
      simpa only [two_mul] using h'
    _ ≤ ∑ p ∈ Ioc H T,
        2 * (((T : ℝ) * (1 + Real.log T)) * ((p : ℝ) ^ 2)⁻¹) :=
      sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hcount p hp) (by norm_num)
    _ = (2 * T * (1 + Real.log T)) * ∑ p ∈ Ioc H T, ((p : ℝ) ^ 2)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ (2 * T * (1 + Real.log T)) * (H : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_inv H T hH)
        (by positivity)
    _ = _ := by rw [div_eq_mul_inv]

def bilinearLargePrimeSquareAbsMass (U V X H : ℕ) : ℝ := by
  classical
  exact ∑ dr ∈ (bilinearPairs U V X).filter (fun dr => largePrimeSquareInput H (dr.1 * dr.2)),
    |(μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2)|

def bilinearLargePrimeSquare (U V X H : ℕ) : ℝ := by
  classical
  exact ∑ dr ∈ (bilinearPairs U V X).filter (fun dr => largePrimeSquareInput H (dr.1 * dr.2)),
    (μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2)

/--
@isnad1 id=le.0h4v.s4.563fef10aaf8 from=translated src=- shape=f0c23793 vocab=e9c4b241
-/
theorem bilinearLargePrimeSquareAbsMass_nonneg (U V X H : ℕ) :
    0 ≤ bilinearLargePrimeSquareAbsMass U V X H :=
  sum_nonneg fun _ _ => abs_nonneg _

/--
@isnad1 id=le.2h4v.s6.ede94d60f91d from=translated src=- shape=2b71e873 vocab=cbe0a5b3
-/
theorem bilinearLargePrimeSquareAbsMass_le (U V X H : ℕ) (hX : 1 ≤ X) (hH : 1 ≤ H) :
    bilinearLargePrimeSquareAbsMass U V X H ≤
      8 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 3 / H := by
  classical
  let L := Real.log (4 * (X : ℝ) + 4)
  let s := (bilinearPairs U V X).filter (fun dr => largePrimeSquareInput H (dr.1 * dr.2))
  let t := s.filter (fun dr => Squarefree dr.1)
  have hL : 1 ≤ L := one_le_dispersion_log X
  have heq : bilinearLargePrimeSquareAbsMass U V X H =
      ∑ dr ∈ t, |(μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2)| := by
    unfold bilinearLargePrimeSquareAbsMass
    change (∑ dr ∈ s, |(μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2)|) =
      ∑ dr ∈ s.filter (fun dr => Squarefree dr.1),
        |(μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2)|
    conv_rhs => rw [sum_filter]
    apply sum_congr rfl
    intro dr _
    by_cases h : Squarefree dr.1
    · simp [h]
    · simp [h]
  have hsub : t ⊆ largePrimeSquarePairs (2 * X) H := by
    intro dr hdr
    rcases mem_filter.mp hdr with ⟨hdr, hsq⟩
    rcases mem_filter.mp hdr with ⟨hdr, hp⟩
    rcases mem_filter.mp hdr with ⟨hdr, _, _, _, hprod⟩
    rcases mem_product.mp hdr with ⟨hd, hr⟩
    exact mem_filter.mpr ⟨(mem_positiveHyperbolaPairs_iff _ _).mpr
      ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hr).1, hprod⟩, hsq, hp⟩
  have hw (dr : ℕ × ℕ) (hdr : dr ∈ t) :
      |(μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2)| ≤ L ^ 2 := by
    have hpair := (mem_filter.mp (mem_filter.mp hdr).1).1
    rcases mem_filter.mp hpair with ⟨hpair, _, _, _, hprod⟩
    have hr := mem_Icc.mp (mem_product.mp hpair).2
    have hbeta : vaughanBeta V dr.2 ≤ L :=
      (vaughanBeta_le_log V dr.2).trans (Real.log_le_log
        (by exact_mod_cast hr.1) (by exact_mod_cast (by omega : dr.2 ≤ 4 * X + 4)))
    have hvm : vonMangoldt (dr.1 * dr.2 + 2) ≤ L :=
      vonMangoldt_le_log.trans (Real.log_le_log (by positivity)
        (by exact_mod_cast (by omega : dr.1 * dr.2 + 2 ≤ 4 * X + 4)))
    have hm : |(μ dr.1 : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := dr.1)
    rw [abs_mul, abs_mul, abs_of_nonneg (vaughanBeta_nonneg V dr.2),
      abs_of_nonneg vonMangoldt_nonneg, pow_two]
    calc
      _ ≤ 1 * L * L := by
        apply mul_le_mul _ hvm (by positivity) (by linarith)
        exact mul_le_mul hm hbeta (vaughanBeta_nonneg V dr.2) (by norm_num)
      _ = _ := by ring
  have hlog : 1 + Real.log ((2 * X : ℕ) : ℝ) ≤ 2 * L := by
    have hh : Real.log ((2 * X : ℕ) : ℝ) ≤ L :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < 2 * X))
        (by exact_mod_cast (by omega : 2 * X ≤ 4 * X + 4))
    linarith
  calc
    _ = ∑ dr ∈ t, |(μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2)| := heq
    _ ≤ ∑ _dr ∈ t, L ^ 2 := sum_le_sum hw
    _ = (t.card : ℝ) * L ^ 2 := by simp
    _ ≤ ((largePrimeSquarePairs (2 * X) H).card : ℝ) * L ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card hsub) (sq_nonneg L)
    _ ≤ (2 * (2 * X : ℕ) * (1 + Real.log ((2 * X : ℕ) : ℝ)) / H) * L ^ 2 :=
      mul_le_mul_of_nonneg_right (largePrimeSquarePairs_card_le (2 * X) H hH) (sq_nonneg L)
    _ ≤ (2 * (2 * X : ℕ) * (2 * L) / H) * L ^ 2 := by gcongr
    _ = _ := by change _ = 8 * (X : ℝ) * L ^ 3 / H; push_cast; ring

/--
@isnad1 id=le.2h4v.s7.6e8e62984c28 from=translated src=- shape=8a44973c vocab=cb6655e2
-/
theorem abs_bilinearLargePrimeSquare_le (U V X H : ℕ) (hX : 1 ≤ X) (hH : 1 ≤ H) :
    |bilinearLargePrimeSquare U V X H| ≤
      8 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 3 / H :=
  (abs_sum_le_sum_abs _ _).trans (bilinearLargePrimeSquareAbsMass_le U V X H hX hH)

def bilinearNoLargePrimeSquare (U V X H : ℕ) : ℝ := by
  classical
  exact ∑ dr ∈ (bilinearPairs U V X).filter (fun dr => ¬largePrimeSquareInput H (dr.1 * dr.2)),
    (μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2)

/--
@isnad1 id=eq.0h4v.s4.babac8327a75 from=translated src=- shape=a54507de vocab=886bf859
-/
theorem bilinearTerm_eq_noLargePrimeSquare_add_largePrimeSquare (U V X H : ℕ) :
    bilinearTerm U V X =
      bilinearNoLargePrimeSquare U V X H + bilinearLargePrimeSquare U V X H := by
  classical
  rw [bilinearTerm_eq_pair_sum]
  simp only [bilinearNoLargePrimeSquare, bilinearLargePrimeSquare, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro dr _
  by_cases h : largePrimeSquareInput H (dr.1 * dr.2) <;> simp [h]

/--
@isnad1 id=le.1h3v.s6.62c9da591f07 from=translated src=- shape=df733a38 vocab=beff5fc2
-/
theorem bilinearLargePrimeSquareAbsMass_div_le_log (U V X : ℕ) (hX : 1 ≤ X) :
    bilinearLargePrimeSquareAbsMass U V X (dispersionGcdCutoff X) / X ≤
      8 / (Real.log (4 * (X : ℝ) + 4)) ^ 7 := by
  let L := Real.log (4 * (X : ℝ) + 4)
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (one_le_dispersion_log X)
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hG : (0 : ℝ) < dispersionGcdCutoff X := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_dispersionGcdCutoff X))
  calc
    _ ≤ (8 * (X : ℝ) * L ^ 3 / dispersionGcdCutoff X) / X :=
      div_le_div_of_nonneg_right (bilinearLargePrimeSquareAbsMass_le U V X _
        hX (one_le_dispersionGcdCutoff X)) hx.le
    _ = 8 * L ^ 3 / dispersionGcdCutoff X := by field_simp
    _ ≤ 8 / L ^ 7 := by
      apply (div_le_iff₀ hG).mpr
      have h := mul_le_mul_of_nonneg_left (log_pow_le_dispersionGcdCutoff X)
        (show 0 ≤ 8 / L ^ 7 by positivity)
      have he : (8 / L ^ 7) * L ^ 10 = 8 * L ^ 3 := by field_simp
      exact he.symm.trans_le h

/--
@isnad1 id=tendsto.0h2v.s5.734810667698 from=translated src=- shape=56beeab1 vocab=c922c5ec
-/
theorem tendsto_bilinearLargePrimeSquareAbsMass_div (U V : ℕ → ℕ) :
    Tendsto (fun X : ℕ => bilinearLargePrimeSquareAbsMass (U X) (V X) X
      (dispersionGcdCutoff X) / X) atTop (𝓝 0) := by
  have harg : Tendsto (fun X : ℕ => 4 * (X : ℝ) + 4) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    filter_upwards with X
    have := Nat.cast_nonneg (α := ℝ) X
    linarith
  have hinv := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp harg)
  have hu : Tendsto (fun X : ℕ => 8 / (Real.log (4 * (X : ℝ) + 4)) ^ 7) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, inv_pow, zero_pow (by decide : 7 ≠ 0),
      mul_zero] using (hinv.pow 7).const_mul 8
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards with X
    exact div_nonneg (bilinearLargePrimeSquareAbsMass_nonneg _ _ _ _) (Nat.cast_nonneg X)
  · filter_upwards [eventually_ge_atTop 1] with X hX
    exact bilinearLargePrimeSquareAbsMass_div_le_log _ _ X hX

/--
@isnad1 id=tendsto.0h2v.s5.bd943a420114 from=translated src=- shape=56beeab1 vocab=1dacfcda
-/
theorem tendsto_bilinearLargePrimeSquare_div (U V : ℕ → ℕ) :
    Tendsto (fun X : ℕ => bilinearLargePrimeSquare (U X) (V X) X
      (dispersionGcdCutoff X) / X) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (tendsto_bilinearLargePrimeSquareAbsMass_div U V)
  · filter_upwards with X
    exact abs_nonneg _
  · filter_upwards with X
    dsimp only [Function.comp_def]
    rw [abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg X)

/-- Removing the whole input range containing a prime square above the
logarithmic threshold changes the normalized signed sum by o(1).
@isnad1 id=tendsto.0h2v.s6.df8fbf625b22 from=translated src=- shape=8e3a156b vocab=cce6885a
-/
theorem tendsto_bilinearTerm_sub_noLargePrimeSquare_div (U V : ℕ → ℕ) :
    Tendsto (fun X : ℕ => (bilinearTerm (U X) (V X) X -
      bilinearNoLargePrimeSquare (U X) (V X) X (dispersionGcdCutoff X)) / X)
      atTop (𝓝 0) := by
  apply (tendsto_bilinearLargePrimeSquare_div U V).congr'
  filter_upwards with X
  rw [bilinearTerm_eq_noLargePrimeSquare_add_largePrimeSquare
    (U X) (V X) X (dispersionGcdCutoff X), add_sub_cancel_left]

end TwinPrime.Analytic
