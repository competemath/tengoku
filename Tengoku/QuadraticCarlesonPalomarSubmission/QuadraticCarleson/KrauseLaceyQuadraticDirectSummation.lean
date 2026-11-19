import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyScaleSummation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Numerical closure for the direct quadratic one-node proof

The author's direct proof produces the exact offset decay
`2 ^ (-(p - 1) / 2)` for `1 < p ≤ 2`.  This file records that decay,
the two threshold identities used in the pairing argument, and the final
geometric summation by comparison with the already verified project-wide
scale ratio.
-/

open scoped BigOperators

namespace QuadraticCarleson

set_option autoImplicit false

noncomputable section

/-- The exact decay ratio `2^{-(p-1)/2}` from the direct quadratic proof.-/
def directQuadraticDecayRatio (p : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(p - 1) / 2)

/-- The proof's scale parameter `δ = 2^{-s/2}`.-/
def directQuadraticDelta (s : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(s : ℝ) / 2)

/-- The low/high cutoff `A = δ^{-2}`.-/
def directQuadraticLowThreshold (s : ℕ) : ℝ :=
  directQuadraticDelta s ^ (-2 : ℝ)

/-- The exceptional-average cutoff `Λ = δ^{-(p-1)}`.-/
def directQuadraticExceptionalThreshold (p : ℝ) (s : ℕ) : ℝ :=
  directQuadraticDelta s ^ (-(p - 1))

/--
@isnad1 id=lt.0h1v.s3.96ee325c59dd from=translated src=- shape=b9369acb vocab=fc2c747e
-/
theorem directQuadraticDelta_pos (s : ℕ) :
    0 < directQuadraticDelta s := by
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- The low-part balance `δ A^{1-p/2} = δ^{p-1}`.
@isnad1 id=eq.0h2v.s6.3490914c6e17 from=translated src=- shape=007ae44f vocab=4fa44e15
-/
theorem directQuadratic_low_threshold_identity (p : ℝ) (s : ℕ) :
    directQuadraticDelta s *
        directQuadraticLowThreshold s ^ (1 - p / 2) =
      directQuadraticDelta s ^ (p - 1) := by
  have hδ := directQuadraticDelta_pos s
  rw [directQuadraticLowThreshold, ← Real.rpow_mul hδ.le]
  calc
    directQuadraticDelta s *
          directQuadraticDelta s ^ (-2 * (1 - p / 2)) =
        directQuadraticDelta s ^ (1 : ℝ) *
          directQuadraticDelta s ^ (-2 * (1 - p / 2)) := by
            rw [Real.rpow_one]
    _ = directQuadraticDelta s ^ (1 + (-2 * (1 - p / 2))) := by
      rw [Real.rpow_add hδ]
    _ = directQuadraticDelta s ^ (p - 1) := by
      congr 1
      ring

/-- The high-part balance `A^{1-p} Λ = δ^{p-1}`.
@isnad1 id=eq.0h2v.s6.d4f44ca871bf from=translated src=- shape=5799b0b6 vocab=a19a5925
-/
theorem directQuadratic_high_threshold_identity (p : ℝ) (s : ℕ) :
    directQuadraticLowThreshold s ^ (1 - p) *
        directQuadraticExceptionalThreshold p s =
      directQuadraticDelta s ^ (p - 1) := by
  have hδ := directQuadraticDelta_pos s
  rw [directQuadraticLowThreshold, directQuadraticExceptionalThreshold,
    ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
  congr 1
  ring

/-- The exceptional packing factor is exactly the desired offset decay.
@isnad1 id=eq.0h2v.s5.db6aadd42f3a from=translated src=- shape=562c5c72 vocab=ca1c8d0a
-/
theorem directQuadratic_exceptional_threshold_inv (p : ℝ) (s : ℕ) :
    (directQuadraticExceptionalThreshold p s)⁻¹ =
      directQuadraticDelta s ^ (p - 1) := by
  have hδ := directQuadraticDelta_pos s
  rw [directQuadraticExceptionalThreshold, ← Real.rpow_neg hδ.le]
  congr 1
  ring

/-- The per-offset factor produced by the pairing split is exactly the
`s`-th power of the geometric ratio used in the final sum.
@isnad1 id=eq.0h2v.s5.973519eb0d6c from=translated src=- shape=ca44c5d1 vocab=6fd16e51
-/
theorem directQuadraticDelta_rpow_eq_decayRatio_pow
    (p : ℝ) (s : ℕ) :
    directQuadraticDelta s ^ (p - 1) =
      directQuadraticDecayRatio p ^ s := by
  unfold directQuadraticDelta directQuadraticDecayRatio
  calc
    ((2 : ℝ) ^ (-(s : ℝ) / 2)) ^ (p - 1) =
        (2 : ℝ) ^ ((-(s : ℝ) / 2) * (p - 1)) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
    _ = (2 : ℝ) ^ ((-(p - 1) / 2) * (s : ℝ)) := by
      congr 1
      ring
    _ = ((2 : ℝ) ^ (-(p - 1) / 2)) ^ s :=
      Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) _ _

/--
@isnad1 id=le.0h1v.s3.ed8d67f4b039 from=translated src=- shape=8a62b088 vocab=572a935b
-/
theorem directQuadraticDecayRatio_nonneg (p : ℝ) :
    0 ≤ directQuadraticDecayRatio p := by
  exact Real.rpow_nonneg (by norm_num) _

/--
@isnad1 id=lt.1h1v.s4.1830b0a05f82 from=translated src=- shape=3965f485 vocab=5fcf51f6
-/
theorem directQuadraticDecayRatio_lt_one {p : ℝ} (hp : 1 < p) :
    directQuadraticDecayRatio p < 1 := by
  unfold directQuadraticDecayRatio
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · norm_num
  · linarith

/-- The direct decay is stronger than the slower project-wide ratio used by
the existing geometric summation theorem.
@isnad1 id=le.1h1v.s4.f4734d929867 from=translated src=- shape=83738c8f vocab=29e30c00
-/
theorem directQuadraticDecayRatio_le_scaleDecayRatio {p : ℝ}
    (hp : 1 < p) :
    directQuadraticDecayRatio p ≤ scaleDecayRatio (holderConjugate p) := by
  unfold directQuadraticDecayRatio scaleDecayRatio holderConjugate
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  have hpm1 : 0 < p - 1 := sub_pos.mpr hp
  have heq : (1 : ℝ) / (5 * (p / (p - 1))) = (p - 1) / (5 * p) := by
    field_simp
  have heqneg : (-1 : ℝ) / (5 * (p / (p - 1))) = -(p - 1) / (5 * p) := by
    calc
      (-1 : ℝ) / (5 * (p / (p - 1))) =
          -(1 / (5 * (p / (p - 1)))) := by ring
      _ = -((p - 1) / (5 * p)) := by rw [heq]
      _ = -(p - 1) / (5 * p) := by ring
  rw [heqneg, neg_div, neg_div, neg_le_neg_iff]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 5 * p)
    (by norm_num : (0 : ℝ) < 2)).2
  nlinarith

/-- Exact infinite offset summation used after the low/high pairing split.
@isnad1 id=le.2h1v.s6.40b446047a21 from=translated src=- shape=00c703e5 vocab=06f06bf0
-/
theorem directQuadraticDecayRatio_sum_le_twenty_mul_holderConjugate
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    (∑' s : ℕ, (directQuadraticDecayRatio p) ^ s) ≤
      20 * holderConjugate p := by
  have hq : 2 ≤ holderConjugate p := holderConjugate_ge_two hp hp2
  have hq0 : 0 < holderConjugate p := lt_of_lt_of_le (by norm_num) hq
  have hcomp := directQuadraticDecayRatio_le_scaleDecayRatio hp
  apply scale_decay_sum_le_twenty_mul_q hq
  · exact directQuadraticDecayRatio_nonneg p
  · exact directQuadraticDecayRatio_lt_one hp
  · have hgap := scaleDecayRatio_gap hq
    linarith

/-- Finite form of the exact direct decay summation.
@isnad1 id=le.2h2v.s6.6a2b625e75c1 from=translated src=- shape=a71af09f vocab=eefe6c5c
-/
theorem finite_directQuadraticDecayRatio_sum_le_twenty_mul_holderConjugate
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (N : ℕ) :
    (∑ s ∈ Finset.range N, (directQuadraticDecayRatio p) ^ s) ≤
      20 * holderConjugate p := by
  have hq : 2 ≤ holderConjugate p := holderConjugate_ge_two hp hp2
  have hcomp := directQuadraticDecayRatio_le_scaleDecayRatio hp
  apply finite_scale_decay_sum_le_twenty_mul_q hq
  · exact directQuadraticDecayRatio_nonneg p
  · exact directQuadraticDecayRatio_lt_one hp
  · have hgap := scaleDecayRatio_gap hq
    linarith

/-- The exact direct decay summed over an arbitrary finite set of
nonnegative integer offsets.  This is the form produced by the finite
selected-interval reconstruction: its offsets need not fill an initial
segment of `ℕ`.
@isnad1 id=le.3h2v.s6.80a15bbf9759 from=translated src=- shape=786bcc22 vocab=5be2f8bf
-/
theorem finite_int_directQuadraticDecayRatio_sum_le_twenty_mul_holderConjugate
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (S : Finset ℤ)
    (hS : ∀ s ∈ S, 0 ≤ s) :
    (∑ s ∈ S, directQuadraticDecayRatio p ^ s.toNat) ≤
      20 * holderConjugate p := by
  let r := directQuadraticDecayRatio p
  have hr0 : 0 ≤ r := directQuadraticDecayRatio_nonneg p
  have hr1 : r < 1 := directQuadraticDecayRatio_lt_one hp
  have hinj : Set.InjOn Int.toNat (↑S : Set ℤ) := by
    intro a ha b hb hab
    have ha0 := hS a (by simpa using ha)
    have hb0 := hS b (by simpa using hb)
    have haeq : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
    have hbeq : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
    exact haeq.symm.trans ((congrArg (fun n : ℕ ↦ (n : ℤ)) hab).trans hbeq)
  calc
    (∑ s ∈ S, directQuadraticDecayRatio p ^ s.toNat) =
        ∑ n ∈ S.image Int.toNat, r ^ n := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑' n : ℕ, r ^ n := by
      exact (summable_geometric_of_norm_lt_one
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)).sum_le_tsum
          (S.image Int.toNat) (fun n hn ↦ pow_nonneg hr0 n)
    _ ≤ 20 * holderConjugate p := by
      simpa only [r] using
        directQuadraticDecayRatio_sum_le_twenty_mul_holderConjugate hp hp2

end
end QuadraticCarleson
