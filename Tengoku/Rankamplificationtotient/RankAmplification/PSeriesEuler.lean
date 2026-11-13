import Tengoku.Rankamplificationtotient.RankAmplification.MertensProduct
import Tengoku.Seed.Analysis.PSeries
import Tengoku.Seed.Analysis.SpecialFunctions.ImproperIntegrals
import Tengoku.Seed.Analysis.SumIntegralComparisons

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # A softened Euler product and an explicit p-series bound This is the convergent comparison half of the elementary proof of the quantitative part of Lemma 2.2. -/

namespace RankAmplification

open Set MeasureTheory
open scoped Nat.Prime BigOperators

noncomputable section

/-- The completely multiplicative function `n ↦ n ^ (-s)`.-/
def reciprocalRpowMonoidHom (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

/--
@isnad1 id=eq.0h2v.s5.7bd7f3b08300 from=translated src=- shape=7d8b3926 vocab=82d1522d
-/
@[simp]
theorem reciprocalRpowMonoidHom_apply (s : ℝ) (n : ℕ) :
    reciprocalRpowMonoidHom s n = (n : ℝ) ^ (-s) := rfl

/-- The finite Euler product at the convergent exponent `s`.-/
def softenedMertensProduct (R : ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesLE R, (1 - (p : ℝ) ^ (-s))⁻¹

/-- The corresponding sum over the positive `R`-smooth integers.-/
def smoothRpowTsum (R : ℕ) (s : ℝ) : ℝ :=
  ∑' n : (R + 1).smoothNumbers, (n.1 : ℝ) ^ (-s)

/--
@isnad1 id=lt.2h2v.s6.21d92abd975a from=translated src=- shape=9ca54363 vocab=c2d862bb
-/
theorem norm_reciprocalRpowMonoidHom_prime_lt_one {s : ℝ} (hs : 0 < s)
    {p : ℕ} (hp : p.Prime) :
    ‖reciprocalRpowMonoidHom s p‖ < 1 := by
  rw [reciprocalRpowMonoidHom_apply, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hs)

/-- Exact finite Euler-product expansion at a convergent exponent.
@isnad1 id=eq.1h2v.s4.c37bf4d2b375 from=translated src=- shape=0eb5832c vocab=c9e55512
-/
theorem smoothRpowTsum_eq_softenedMertensProduct (R : ℕ) {s : ℝ} (hs : 0 < s) :
    smoothRpowTsum R s = softenedMertensProduct R s := by
  have h := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := reciprocalRpowMonoidHom s)
    (fun {_p} hp ↦ norm_reciprocalRpowMonoidHom_prime_lt_one hs hp)
    (R + 1)
  exact h.2.tsum_eq.trans (by
    simp only [softenedMertensProduct, Nat.primesLE,
      reciprocalRpowMonoidHom_apply])

/-- The full p-series in the normalization convenient for the Euler product.-/
def naturalPSeries (s : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-s)

/--
@isnad1 id=summable.1h1v.s5.603c6040cd2f from=translated src=- shape=4ef34d07 vocab=e51fd383
-/
theorem summable_naturalPSeries {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s)) := by
  exact Real.summable_nat_rpow.mpr (by linarith)

/-- Restricting the p-series to smooth positive integers only decreases it.
@isnad1 id=le.1h2v.s4.228b41cdd199 from=translated src=- shape=ef85f838 vocab=03c9fdcd
-/
theorem smoothRpowTsum_le_naturalPSeries (R : ℕ) {s : ℝ} (hs : 1 < s) :
    smoothRpowTsum R s ≤ naturalPSeries s := by
  unfold smoothRpowTsum naturalPSeries
  exact Summable.tsum_subtype_le
    (fun n : ℕ ↦ (n : ℝ) ^ (-s))
    ((R + 1).smoothNumbers)
    (fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (summable_naturalPSeries hs)

/-- The integral-test tail bound beginning at the integer `2`.
@isnad1 id=le.1h1v.s6.32f01f419889 from=translated src=- shape=700665ab vocab=576683b8
-/
theorem naturalPSeries_tail_le {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-s)) ≤ 1 / (s - 1) := by
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ (-s)) (Ici (1 : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
      (fun _ hx ↦ by simpa only [mem_Ioi] using zero_lt_one.trans_le hx)
  have hint : IntegrableOn (fun x : ℝ ↦ x ^ (-s)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hnonneg : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ x ^ (-s) :=
    fun x _ ↦ Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ‹1 < x›)) _
  have h := AntitoneOn.tsum_comp_add_le_integral
    (f := fun x : ℝ ↦ x ^ (-s)) 1
    (by simpa only [Nat.cast_one] using hanti)
    (by simpa only [Nat.cast_one] using hint)
    (by simpa only [Nat.cast_one] using hnonneg)
  have h' : (∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-s)) ≤
      ∫ x in Ioi (1 : ℝ), x ^ (-s) := by
    convert h using 1
    all_goals norm_num
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one] at h'
  convert h' using 1
  all_goals norm_num
  have hsne : s - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hs)
  have hneg : -s + 1 ≠ 0 := by linarith
  field_simp [hsne, hneg]
  ring

/-- Elementary explicit bound `ζ(s) ≤ 1 + 1/(s-1)` for real `s > 1`.
@isnad1 id=le.1h1v.s5.26fd0a9bf2f0 from=translated src=- shape=b0e2616d vocab=f2cc610c
-/
theorem naturalPSeries_le (s : ℝ) (hs : 1 < s) :
    naturalPSeries s ≤ 1 + 1 / (s - 1) := by
  have hsum := summable_naturalPSeries hs
  have hshift : Summable (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (-s)) :=
    hsum.comp_injective Nat.succ_injective
  have hzero : (0 : ℝ) ^ (-s) = 0 := by
    rw [Real.zero_rpow]
    linarith
  have hone : (1 : ℝ) ^ (-s) = 1 := by simp
  calc
    naturalPSeries s = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-s) := by
      rw [naturalPSeries, hsum.tsum_eq_zero_add]
      simp only [Nat.cast_zero, hzero, zero_add]
    _ = 1 + ∑' n : ℕ, ((n + 2 : ℕ) : ℝ) ^ (-s) := by
      rw [hshift.tsum_eq_zero_add]
      simp only [Nat.zero_add, Nat.cast_one, hone]
    _ ≤ 1 + 1 / (s - 1) := add_le_add le_rfl (naturalPSeries_tail_le hs)

/-- The softened finite Euler product has the same explicit p-series majorant.
@isnad1 id=le.1h2v.s5.fbdbe27b5d89 from=translated src=- shape=8e6544d7 vocab=804e78a8
-/
theorem softenedMertensProduct_le (R : ℕ) (s : ℝ) (hs : 1 < s) :
    softenedMertensProduct R s ≤ 1 + 1 / (s - 1) := by
  rw [← smoothRpowTsum_eq_softenedMertensProduct R (lt_trans zero_lt_one hs)]
  exact (smoothRpowTsum_le_naturalPSeries R hs).trans (naturalPSeries_le s hs)

end

end RankAmplification
