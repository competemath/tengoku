import Tengoku.Twinprime.TwinPrime.Analytic.DispersionGcdGlobal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The three-level band of nonzero dispersion boxes

The exact product cutoff implies `X < 4MN` and `MN < 2X` for every
nonzero entry in a right-closed box. Thus the possible dyadic product
exponents lie in three consecutive levels. This is a support reduction,
not an estimate for the signed correlations within the surviving boxes.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

def dispersionActiveBoxIndices (U V X : ℕ) : Finset (ℕ × ℕ) :=
  (dispersionBoxIndices U V X).filter
    (fun ij => X < 4 * (2 ^ ij.1 * 2 ^ ij.2) ∧ 2 ^ ij.1 * 2 ^ ij.2 < 2 * X)

/--
@isnad1 id=le.0h3v.s5.3014dc1caab3 from=translated src=- shape=59e90078 vocab=8f412081
-/
theorem dispersionActiveBoxIndices_subset (U V X : ℕ) :
    dispersionActiveBoxIndices U V X ⊆ dispersionBoxIndices U V X :=
  filter_subset _ _

/--
@isnad1 id=iff.0h4v.s7.1adafa4ebd42 from=translated src=- shape=46ef27b2 vocab=f77afb24
-/
theorem mem_dispersionActiveBoxIndices_iff (U V X : ℕ) (ij : ℕ × ℕ) :
    ij ∈ dispersionActiveBoxIndices U V X ↔
      ij ∈ dispersionBoxIndices U V X ∧
        X < 4 * (2 ^ ij.1 * 2 ^ ij.2) ∧ 2 ^ ij.1 * 2 ^ ij.2 < 2 * X :=
  mem_filter

/-- Any two exponents in the product band differ by at most two.
@isnad1 id=le.2h3v.s6.54a535fbaa93 from=translated src=- shape=2906e262 vocab=3f16b8dd
-/
theorem dyadic_product_band_exponent_le {X k l : ℕ}
    (hk : X < 4 * 2 ^ k) (hl : 2 ^ l < 2 * X) : l ≤ k + 2 := by
  by_contra h
  have hkl : k + 3 ≤ l := by omega
  have hp : 2 ^ (k + 3) ≤ 2 ^ l := pow_le_pow_right' (by norm_num) hkl
  rw [pow_add] at hp
  norm_num at hp
  omega

/-- The full support family has at most three boxes for each left exponent,
including all boundary and empty cases.
@isnad1 id=le.0h3v.s5.658f9a32e1d0 from=translated src=- shape=f4a43410 vocab=31dde327
-/
theorem dispersionActiveBoxIndices_card_le (U V X : ℕ) :
    (dispersionActiveBoxIndices U V X).card ≤ 3 * dyadicNatDepth (2 * X) := by
  classical
  let s := dispersionActiveBoxIndices U V X
  by_cases hs : s.Nonempty
  · let e : ℕ × ℕ → ℕ := fun ij => ij.1 + ij.2
    have he : (s.image e).Nonempty := hs.image e
    let m := (s.image e).min' he
    have hm : m ∈ s.image e := min'_mem _ _
    obtain ⟨kl, hkl, hkm⟩ := mem_image.mp hm
    have hkband := (mem_dispersionActiveBoxIndices_iff U V X kl).mp hkl
    have hmlo : X < 4 * 2 ^ m := by
      rw [← hkm]
      simpa only [e, pow_add] using hkband.2.1
    have hmap : Set.MapsTo (fun ij : ℕ × ℕ => (ij.1, e ij)) s
        ((range (dyadicNatDepth (2 * X))).product (Icc m (m + 2))) := by
      intro ij hij
      have hi := (mem_dispersionActiveBoxIndices_iff U V X ij).mp hij
      apply mem_product.mpr
      refine ⟨mem_range.mpr ((mem_dispersionBoxIndices_iff U V X ij).mp hi.1).1, ?_⟩
      apply mem_Icc.mpr
      refine ⟨min'_le _ _ (mem_image.mpr ⟨ij, hij, rfl⟩), ?_⟩
      apply dyadic_product_band_exponent_le hmlo
      simpa only [e, pow_add] using hi.2.2
    have hinj : Set.InjOn (fun ij : ℕ × ℕ => (ij.1, e ij)) s := by
      intro ij hij kl hkl heq
      have hi := congrArg Prod.fst heq
      have hj := congrArg Prod.snd heq
      dsimp only [e] at hi hj
      exact Prod.ext hi (by omega)
    calc
      _ ≤ ((range (dyadicNatDepth (2 * X))).product (Icc m (m + 2))).card :=
        card_le_card_of_injOn _ hmap hinj
      _ = _ := by
        simp only [product_eq_sprod, card_product, card_range, Nat.card_Icc]
        rw [show m + 2 + 1 - m = 3 by omega, Nat.mul_comm]
  · have hz : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    change s.card ≤ _
    simp only [hz, card_empty, Nat.zero_le]

/-- Outside the strict product band, every entry in the box vanishes.
@isnad1 id=eq.3h5v.s7.9aa2885e0b71 from=translated src=- shape=49dea22f vocab=f7073779
-/
theorem dispersionEntry_eq_zero_of_not_band {X M N d r : ℕ}
    (hd : d ∈ Ioc M (2 * M)) (hr : r ∈ Ioc N (2 * N))
    (hband : ¬ (X < 4 * (M * N) ∧ M * N < 2 * X)) :
    dispersionEntry X d r = 0 := by
  apply ite_eq_right
  intro hprod
  have hdI := mem_Ioc.mp hd
  have hrI := mem_Ioc.mp hr
  have hupper : d * r ≤ 4 * (M * N) := by
    have h := Nat.mul_le_mul hdI.2 hrI.2
    nlinarith
  have hlower : M * N < d * r := by
    have h1 := Nat.mul_le_mul_left M (Nat.le_of_lt hrI.1)
    have h2 := Nat.mul_lt_mul_of_pos_right hdI.1 (show 0 < r by omega)
    exact lt_of_le_of_lt h1 h2
  exact hband ⟨lt_of_lt_of_le hprod.1 hupper, lt_of_lt_of_le hlower hprod.2⟩

/--
@isnad1 id=eq.1h5v.s6.f305d5a61d1b from=translated src=- shape=268025b1 vocab=853a971d
-/
theorem bilinearBox_eq_zero_of_not_band (U V X M N : ℕ)
    (hband : ¬ (X < 4 * (M * N) ∧ M * N < 2 * X)) :
    bilinearBox U V X M N = 0 := by
  unfold bilinearBox
  apply sum_eq_zero
  intro r hr
  have hsum : (∑ d ∈ dispersionLeft U M, dispersionEntry X d r) = 0 := by
    apply sum_eq_zero
    intro d hd
    exact dispersionEntry_eq_zero_of_not_band (mem_filter.mp hd).1 (mem_filter.mp hr).1 hband
  rw [hsum, mul_zero]

/--
@isnad1 id=eq.1h5v.s6.cf06f6ed3f81 from=translated src=- shape=268025b1 vocab=23413230
-/
theorem dispersionDiagonal_eq_zero_of_not_band (U V X M N : ℕ)
    (hband : ¬ (X < 4 * (M * N) ∧ M * N < 2 * X)) :
    dispersionDiagonal U V X M N = 0 := by
  unfold dispersionDiagonal
  apply sum_eq_zero
  intro r hr
  have hsum : (∑ d ∈ dispersionLeft U M, dispersionEntry X d r ^ 2) = 0 := by
    apply sum_eq_zero
    intro d hd
    rw [dispersionEntry_eq_zero_of_not_band (mem_filter.mp hd).1
      (mem_filter.mp hr).1 hband, zero_pow (by decide : 2 ≠ 0)]
  rw [hsum, mul_zero]

/--
@isnad1 id=eq.1h5v.s6.f75f34ef8816 from=translated src=- shape=268025b1 vocab=9f39d39d
-/
theorem dispersionOffDiagonal_eq_zero_of_not_band (U V X M N : ℕ)
    (hband : ¬ (X < 4 * (M * N) ∧ M * N < 2 * X)) :
    dispersionOffDiagonal U V X M N = 0 := by
  unfold dispersionOffDiagonal
  apply sum_eq_zero
  intro r hr
  have hsum : (∑ d ∈ dispersionLeft U M, ∑ e ∈ (dispersionLeft U M).erase d,
      dispersionEntry X d r * dispersionEntry X e r) = 0 := by
    apply sum_eq_zero
    intro d hd
    simp only [dispersionEntry_eq_zero_of_not_band (mem_filter.mp hd).1
      (mem_filter.mp hr).1 hband, zero_mul, sum_const_zero]
  rw [hsum, mul_zero]

/--
@isnad1 id=eq.1h6v.s6.cc1feb0eac29 from=translated src=- shape=fd532551 vocab=aab77134
-/
theorem dispersionOffDiagonalLargeGcd_eq_zero_of_not_band (U V X M N G : ℕ)
    (hband : ¬ (X < 4 * (M * N) ∧ M * N < 2 * X)) :
    dispersionOffDiagonalLargeGcd U V X M N G = 0 := by
  unfold dispersionOffDiagonalLargeGcd
  apply sum_eq_zero
  intro r hr
  have hsum : (∑ de ∈ dispersionLargeGcdPairs U M G,
      dispersionEntry X de.1 r * dispersionEntry X de.2 r) = 0 := by
    apply sum_eq_zero
    intro de hde
    have hd := (mem_product.mp (mem_filter.mp hde).1).1
    rw [dispersionEntry_eq_zero_of_not_band (mem_filter.mp hd).1
      (mem_filter.mp hr).1 hband, zero_mul]
  rw [hsum, mul_zero]

/--
@isnad1 id=eq.1h6v.s6.478c36e6c16d from=translated src=- shape=fd532551 vocab=aba4cbf6
-/
theorem dispersionOffDiagonalSmallGcd_eq_zero_of_not_band (U V X M N G : ℕ)
    (hband : ¬ (X < 4 * (M * N) ∧ M * N < 2 * X)) :
    dispersionOffDiagonalSmallGcd U V X M N G = 0 := by
  unfold dispersionOffDiagonalSmallGcd
  apply sum_eq_zero
  intro r hr
  have hsum : (∑ de ∈ dispersionSmallGcdPairs U M G,
      dispersionEntry X de.1 r * dispersionEntry X de.2 r) = 0 := by
    apply sum_eq_zero
    intro de hde
    have hd := (mem_product.mp (mem_filter.mp hde).1).1
    rw [dispersionEntry_eq_zero_of_not_band (mem_filter.mp hd).1
      (mem_filter.mp hr).1 hband, zero_mul]
  rw [hsum, mul_zero]

/-- Generic exact transport, also valid for externally weighted box sums.
@isnad1 id=eq.1h5v.s7.311aa3c28852 from=translated src=- shape=8695efba vocab=00f065f9
-/
theorem sum_dispersionBoxIndices_eq_active {A : Type*} [AddCommMonoid A]
    (U V X : ℕ) (f : ℕ × ℕ → A)
    (hzero : ∀ ij ∈ dispersionBoxIndices U V X,
      ¬ (X < 4 * (2 ^ ij.1 * 2 ^ ij.2) ∧ 2 ^ ij.1 * 2 ^ ij.2 < 2 * X) → f ij = 0) :
    (∑ ij ∈ dispersionBoxIndices U V X, f ij) =
      ∑ ij ∈ dispersionActiveBoxIndices U V X, f ij := by
  classical
  simp only [dispersionActiveBoxIndices, sum_filter]
  apply sum_congr rfl
  intro ij hij
  by_cases hband : X < 4 * (2 ^ ij.1 * 2 ^ ij.2) ∧ 2 ^ ij.1 * 2 ^ ij.2 < 2 * X
  · simp only [ite_eq_left hband]
  · rw [ite_eq_right hband, hzero ij hij hband]

/--
@isnad1 id=eq.2h3v.s6.9ccd1a9526f0 from=translated src=- shape=f5305edb vocab=17c7c6a1
-/
theorem bilinearTerm_eq_sum_dispersionActiveBoxes (U V X : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    bilinearTerm U V X = ∑ ij ∈ dispersionActiveBoxIndices U V X,
      bilinearBox U V X (2 ^ ij.1) (2 ^ ij.2) := by
  rw [bilinearTerm_eq_sum_dispersionBoxes U V X hU hV]
  apply sum_dispersionBoxIndices_eq_active
  intro ij _ hband
  exact bilinearBox_eq_zero_of_not_band U V X _ _ hband

/--
@isnad1 id=eq.0h3v.s4.badc215e978c from=translated src=- shape=eb5d5ec4 vocab=e93c7b62
-/
theorem dispersionDiagonalSum_eq_active (U V X : ℕ) :
    dispersionDiagonalSum U V X (dispersionBoxIndices U V X) =
      dispersionDiagonalSum U V X (dispersionActiveBoxIndices U V X) := by
  unfold dispersionDiagonalSum
  apply sum_dispersionBoxIndices_eq_active
  intro ij _ hband
  simp only [dispersionDiagonal_eq_zero_of_not_band U V X _ _ hband, mul_zero, Real.sqrt_zero]

/--
@isnad1 id=eq.0h3v.s4.0a6f7ece2240 from=translated src=- shape=eb5d5ec4 vocab=b1012597
-/
theorem dispersionOffDiagonalSum_eq_active (U V X : ℕ) :
    dispersionOffDiagonalSum U V X (dispersionBoxIndices U V X) =
      dispersionOffDiagonalSum U V X (dispersionActiveBoxIndices U V X) := by
  unfold dispersionOffDiagonalSum
  apply sum_dispersionBoxIndices_eq_active
  intro ij _ hband
  simp only [dispersionOffDiagonal_eq_zero_of_not_band U V X _ _ hband,
    mul_zero, max_self, Real.sqrt_zero]

/--
@isnad1 id=eq.0h4v.s4.035de383d545 from=translated src=- shape=3941b868 vocab=871d9f8b
-/
theorem dispersionLargeGcdSum_eq_active (U V X G : ℕ) :
    dispersionLargeGcdSum U V X G (dispersionBoxIndices U V X) =
      dispersionLargeGcdSum U V X G (dispersionActiveBoxIndices U V X) := by
  unfold dispersionLargeGcdSum
  apply sum_dispersionBoxIndices_eq_active
  intro ij _ hband
  simp only [dispersionOffDiagonalLargeGcd_eq_zero_of_not_band U V X _ _ G hband,
    abs_zero, mul_zero, Real.sqrt_zero]

/--
@isnad1 id=eq.0h4v.s4.a08930d38096 from=translated src=- shape=3941b868 vocab=1b240bcc
-/
theorem dispersionSmallGcdSum_eq_active (U V X G : ℕ) :
    dispersionSmallGcdSum U V X G (dispersionBoxIndices U V X) =
      dispersionSmallGcdSum U V X G (dispersionActiveBoxIndices U V X) := by
  unfold dispersionSmallGcdSum
  apply sum_dispersionBoxIndices_eq_active
  intro ij _ hband
  simp only [dispersionOffDiagonalSmallGcd_eq_zero_of_not_band U V X _ _ G hband,
    mul_zero, max_self, Real.sqrt_zero]

end TwinPrime.Analytic
