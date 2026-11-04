import Tengoku.GeneralStochToDet.stoch_to_det.Constants
import Tengoku.Seed.NumberTheory.Harmonic.GammaDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact constants for the improved `1771` theorem

The definitions in this file are symbolic.  In particular,
`logExpAbsMoment` is an actual Lebesgue integral and `infoFloor1771` contains
an actual logarithm.  Numerical-looking inequalities are proved separately;
none of these definitions uses floating-point evaluation.
-/

namespace stoch_to_det

open MeasureTheory

/-! ### Rational threshold data -/

/-- The exact rational secant threshold `527 / 2000`.-/
def eta1771Q : ℚ := 527 / 2000

/-- The exact rational Hellinger threshold `eta1771Q ^ 3`.-/
def delta1771Q : ℚ := eta1771Q ^ 3

/-- The exact rational HGR threshold `1/2 - eta1771Q^2`.-/
def rho1771Q : ℚ := 1 / 2 - eta1771Q ^ 2

/-- The exact rational Hellinger-to-information parameter.-/
def chi1771Q : ℚ := rho1771Q ^ 6 / (1 + rho1771Q ^ 2) ^ 2

/-- `eta_* = 527/2000`.-/
noncomputable def eta1771 : ℝ := eta1771Q

/-- `Delta_* = eta_*^3`, the squared-Hellinger near threshold.-/
noncomputable def delta1771 : ℝ := delta1771Q

/-- `rho_* = 1/2 - eta_*^2`.-/
noncomputable def rho1771 : ℝ := rho1771Q

/-- `chi_* = rho_*^6/(1+rho_*^2)^2`.-/
noncomputable def chi1771 : ℝ := chi1771Q

/-- The exact HGR information floor, in bits.-/
noncomputable def infoFloor1771 : ℝ :=
  -2 * lg (1 - chi1771 / 2)

/-! ### Scalar-channel constants -/

/-- The exponential integral at `1`,
`E₁(1) = ∫_1^∞ exp(-t) / t dt`.-/
noncomputable def E1one : ℝ :=
  ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t

/-- The exact absolute first moment of `log T`, for `T ~ Exp(1)`.-/
noncomputable def logExpAbsMoment : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), |Real.log t| * Real.exp (-t)

/-- `alpha = 2/e + E|log T|`.-/
noncomputable def alpha1771 : ℝ :=
  2 / Real.exp 1 + logExpAbsMoment

/-- The exact additive off-diagonal charge, in nats.-/
noncomputable def cOff1771 : ℝ :=
  Real.log (2 * alpha1771) - Real.eulerMascheroniConstant

/-- The scalar mismatch coefficient, in bits.-/
noncomputable def kappa1771 : ℝ :=
  (1 + cOff1771) / Real.log 2

/-- The scalar-plus-cone mismatch coefficient, in bits.-/
noncomputable def beta1771 : ℝ :=
  (2 + cOff1771) / Real.log 2

/-! ### Closing ledger -/

noncomputable def KM1771 : ℝ :=
  beta1771 / infoFloor1771

noncomputable def KS1771 : ℝ :=
  2 + 2 * beta1771 * Real.log 2 / delta1771

noncomputable def KD1771 : ℝ :=
  max (3 * KM1771) (6 * KS1771 + 2)

/-- The exact constant `C^ddagger = K_D + 1`.-/
noncomputable def Cdagger1771 : ℝ :=
  KD1771 + 1

/-! ### Exact threshold identities and elementary positivity -/

/--
@isnad1 id=eq.0h0v.s4.ca93fe658cd4 from=translated src=- shape=0efb1284 vocab=7638bf94
-/
lemma eta1771_eq : eta1771 = (527 : ℝ) / 2000 := by
  norm_num [eta1771, eta1771Q]

/--
@isnad1 id=eq.0h0v.s4.d6ba1ca29e57 from=translated src=- shape=9a2ead57 vocab=17892708
-/
lemma delta1771_eq : delta1771 = eta1771 ^ 3 := by
  norm_num [delta1771, delta1771Q, eta1771, eta1771Q]

/--
@isnad1 id=eq.0h0v.s5.e41a041224b8 from=translated src=- shape=f2920ecc vocab=f799af26
-/
lemma rho1771_eq : rho1771 = 1 / 2 - eta1771 ^ 2 := by
  norm_num [rho1771, rho1771Q, eta1771, eta1771Q]

/--
@isnad1 id=eq.0h0v.s6.c915078bb32a from=translated src=- shape=5114b5f5 vocab=feb359e8
-/
lemma chi1771_eq : chi1771 = rho1771 ^ 6 / (1 + rho1771 ^ 2) ^ 2 := by
  norm_num [chi1771, chi1771Q, rho1771, rho1771Q]

/--
@isnad1 id=lt.0h0v.s3.6bf6358d1a68 from=translated src=- shape=ff3a10fc vocab=d99c1fab
-/
lemma eta1771_pos : 0 < eta1771 := by
  norm_num [eta1771, eta1771Q]

/--
@isnad1 id=lt.0h0v.s3.5758d770f015 from=translated src=- shape=ff3a10fc vocab=f6585041
-/
lemma delta1771_pos : 0 < delta1771 := by
  norm_num [delta1771, delta1771Q, eta1771Q]

/--
@isnad1 id=lt.0h0v.s3.8ad744b276ed from=translated src=- shape=ff3a10fc vocab=25267af0
-/
lemma rho1771_pos : 0 < rho1771 := by
  norm_num [rho1771, rho1771Q, eta1771Q]

/--
@isnad1 id=lt.0h0v.s3.9341587d4e19 from=translated src=- shape=ffdda526 vocab=25267af0
-/
lemma rho1771_lt_one : rho1771 < 1 := by
  norm_num [rho1771, rho1771Q, eta1771Q]

/--
@isnad1 id=lt.0h0v.s3.7692799acf31 from=translated src=- shape=ff3a10fc vocab=ceb41379
-/
lemma chi1771_pos : 0 < chi1771 := by
  norm_num [chi1771, chi1771Q, rho1771Q, eta1771Q]

/--
@isnad1 id=lt.0h0v.s3.446f55ae7988 from=translated src=- shape=ffdda526 vocab=1340ca7a
-/
lemma chi1771_lt_two : chi1771 < 2 := by
  norm_num [chi1771, chi1771Q, rho1771Q, eta1771Q]

/--
@isnad1 id=lt.0h0v.s5.27bf1ea144b8 from=translated src=- shape=5c5055bc vocab=256f1a27
-/
lemma one_sub_chi1771_half_pos : 0 < 1 - chi1771 / 2 := by
  linarith [chi1771_lt_two]

/--
@isnad1 id=lt.0h0v.s5.8256f9fea1c4 from=translated src=- shape=22e1ca55 vocab=256f1a27
-/
lemma one_sub_chi1771_half_lt_one : 1 - chi1771 / 2 < 1 := by
  linarith [chi1771_pos]

/--
@isnad1 id=lt.0h0v.s3.ad1f175f37b9 from=translated src=- shape=ff3a10fc vocab=f3b38dfa
-/
lemma infoFloor1771_pos : 0 < infoFloor1771 := by
  have harg := one_sub_chi1771_half_pos
  have hlog : lg (1 - chi1771 / 2) < 0 := by
    rw [lg_eq_log_div]
    exact div_neg_of_neg_of_pos
      (Real.log_neg harg one_sub_chi1771_half_lt_one)
      (Real.log_pos one_lt_two)
  unfold infoFloor1771
  linarith

end stoch_to_det
