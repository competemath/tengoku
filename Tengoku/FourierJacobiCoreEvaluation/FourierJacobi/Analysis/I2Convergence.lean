import Tengoku.FourierJacobiCoreEvaluation.FourierJacobi.Analysis.MasterSeries
import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Product-family analysis used in the independent I2 valuation sums. -/

noncomputable section

namespace FourierJacobi.Analysis

/--
@isnad1 id=ne.1h1v.s5.66695d3f34f3 from=translated src=- shape=e0aee735 vocab=0fcc4b44
-/
theorem i2_geometric_denominator_ne (z : ℂ) (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have hz1 : z = 1 := (sub_eq_zero.mp h).symm
  rw [hz1, norm_one] at hz
  exact (lt_irrefl (1 : ℝ)) hz

/--
@isnad1 id=summable.2h3v.s6.f5a80e32dff0 from=translated src=- shape=77f9d5cc vocab=668390a1
-/
theorem i2_summable_norm_two_geometric (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    Summable (fun n : ℕ × ℕ => ‖C * a ^ n.1 * b ^ n.2‖) := by
  have h := (geometric_norm_summable a ha).mul_norm (geometric_norm_summable b hb)
  simpa only [norm_mul, mul_assoc] using h.mul_left ‖C‖

/--
@isnad1 id=hassum.2h3v.s7.77ddf91f3fa8 from=translated src=- shape=f97860bc vocab=916ef642
-/
theorem i2_hasSum_two_geometric (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    HasSum (fun n : ℕ × ℕ => C * a ^ n.1 * b ^ n.2)
      (C * (1 - a)⁻¹ * (1 - b)⁻¹) := by
  have hs := (i2_summable_norm_two_geometric C a b ha hb).of_norm
  have hA := (hasSum_geometric_of_norm_lt_one ha).tsum_eq
  have hB := (hasSum_geometric_of_norm_lt_one hb).tsum_eq
  have he : (∑' n : ℕ × ℕ, C * a ^ n.1 * b ^ n.2) =
      C * (1 - a)⁻¹ * (1 - b)⁻¹ := by
    rw [hs.tsum_prod]
    simp only [tsum_mul_left, hB, tsum_mul_right, hA]
  exact he ▸ hs.hasSum

/--
@isnad1 id=summable.1h2v.s5.93e364479b55 from=translated src=- shape=61e051d3 vocab=86b45335
-/
theorem i2_summable_norm_one_geometric (C a : ℂ) (ha : ‖a‖ < 1) :
    Summable (fun n : ℕ => ‖C * a ^ n‖) := by
  simpa only [norm_mul] using (geometric_norm_summable a ha).mul_left ‖C‖

/--
@isnad1 id=hassum.1h2v.s6.4ecb6b9bc6bb from=translated src=- shape=fc3fbd34 vocab=e95fbb1c
-/
theorem i2_hasSum_one_geometric (C a : ℂ) (ha : ‖a‖ < 1) :
    HasSum (fun n : ℕ => C * a ^ n) (C * (1 - a)⁻¹) :=
  (hasSum_geometric_of_norm_lt_one ha).mul_left C

/--
@isnad1 id=summable.3h5v.s8.0811d51a445c from=translated src=- shape=27d0d1fc vocab=c5475684
-/
theorem i2_summable_norm_parity_geometric (C z a b c : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) :
    Summable (fun n : Fin 2 × ℕ × ℕ × ℕ =>
      ‖C * z ^ n.1.val * a ^ n.2.1 * b ^ n.2.2.1 * c ^ n.2.2.2‖) := by
  have hz : Summable (fun e : Fin 2 => ‖z ^ e.val‖) := (hasSum_fintype _).summable
  have h := hz.mul_norm (summable_norm_three_geometric C a b c ha hb hc)
  convert h using 1
  funext n
  congr 1
  ring

/--
@isnad1 id=hassum.3h5v.s8.860df67be70c from=translated src=- shape=90df6735 vocab=52bf15c2
-/
theorem i2_hasSum_parity_geometric (C z a b c : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) :
    HasSum (fun n : Fin 2 × ℕ × ℕ × ℕ =>
      C * z ^ n.1.val * a ^ n.2.1 * b ^ n.2.2.1 * c ^ n.2.2.2)
      (C * (1 + z) * (1 - a)⁻¹ * (1 - b)⁻¹ * (1 - c)⁻¹) := by
  have hs := (i2_summable_norm_parity_geometric C z a b c ha hb hc).of_norm
  have hinner (e : Fin 2) :=
    (hasSum_three_geometric (C * z ^ e.val) a b c ha hb hc).tsum_eq
  have he : (∑' n : Fin 2 × ℕ × ℕ × ℕ,
      C * z ^ n.1.val * a ^ n.2.1 * b ^ n.2.2.1 * c ^ n.2.2.2) =
      C * (1 + z) * (1 - a)⁻¹ * (1 - b)⁻¹ * (1 - c)⁻¹ := by
    rw [hs.tsum_prod]
    simp only [hinner, tsum_fintype, Fin.sum_univ_two, Fin.val_zero,
      Fin.val_one, pow_zero, pow_one]
    ring
  exact he ▸ hs.hasSum

end FourierJacobi.Analysis
