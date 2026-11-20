/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.Lift
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.MomentBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def lorentzProjectedGenerator (x : V) (c : IntegralGramLattice G x)
    (B : SecondSubconstituent G x) : ratGramSpace G x :=
  lorentzHeightZeroPart G x c (toRatSpace G x (integralGramGenerator G x B))

/--
@isnad1 id=eq.3h6v.s11.a83bf3344b55 from=translated src=- shape=ff5b2291 vocab=cf39eb39
-/
theorem lorentzProjectedGenerator_pair (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (y : ratGramSpace G x) (hy : centroidHeight G x c y = 0)
    (B : SecondSubconstituent G x) :
    lorentzGramForm G x c y (lorentzProjectedGenerator G x c B) =
      lorentzGramForm G x c y (toRatSpace G x (integralGramGenerator G x B)) := by
  simp only [lorentzProjectedGenerator, lorentzHeightZeroPart, map_sub, map_smul,
    smul_eq_mul]
  rw [(lorentzGramForm_isSymm G x c).eq y (lorentzWeylVector G x c),
    lorentzWeylVector_pair G hG x c hc y, hy]
  ring

/--
@isnad1 id=eq.2h4v.s8.734b4675d380 from=translated src=- shape=2844d122 vocab=70110489
-/
theorem lorentzProjectedGenerator_sum (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    ∑ B, lorentzProjectedGenerator G x c B = 0 := by
  have hsum : (∑ B, toRatSpace G x (integralGramGenerator G x B)) =
      (11 : ℚ) • toRatSpace G x c := by
    have h := congrArg (toRatSpace G x) hc
    simp only [map_zsmul, integralGramGeneratorSum, map_sum,
      ← Int.cast_smul_eq_zsmul ℚ] at h
    exact h.symm
  simp only [lorentzProjectedGenerator, lorentzHeightZeroPart,
    centroidHeight_generator G hG x c hc]
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ,
    secondSubconstituent_card G hG x]
  simp only [lorentzWeylVector]
  module

/--
@isnad1 id=eq.3h5v.s11.729402713253 from=translated src=- shape=2796b212 vocab=d637238a
-/
theorem lorentzProjectedGenerator_secondMoment (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (y : ratGramSpace G x) (hy : centroidHeight G x c y = 0) :
    ∑ B, (lorentzGramForm G x c y (lorentzProjectedGenerator G x c B)) ^ 2 =
      45 * lorentzGramForm G x c y y := by
  have hf := congrArg (fun z => lorentzGramForm G x c y z)
    (lorentz_rat_frame_identity G hG x c hc y)
  simp only [hy, mul_zero, zero_smul, sub_zero, map_sum, map_smul, smul_eq_mul] at hf
  calc
    _ = ∑ B, lorentzGramForm G x c y (toRatSpace G x (integralGramGenerator G x B)) *
        lorentzGramForm G x c y (toRatSpace G x (integralGramGenerator G x B)) := by
      apply Finset.sum_congr rfl
      intro B _
      rw [lorentzProjectedGenerator_pair G hG x c hc y hy B]
      ring
    _ = _ := hf

/--
@isnad1 id=ex.4h5v.s12.5db645d653ef from=translated src=- shape=280ff045 vocab=88c84975
-/
theorem lorentzProjectedGenerator_exists_small_score (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (y : ratGramSpace G x) (hy : centroidHeight G x c y = 0)
    (hypos : 0 < lorentzGramForm G x c y y) :
    ∃ B : SecondSubconstituent G x,
      (lorentzGramForm G x c y (lorentzProjectedGenerator G x c B)) ^ 2 <
        lorentzGramForm G x c y y / 4 := by
  by_contra hn
  push Not at hn
  apply MomentBounds.no_gap_of_moment_upper Finset.univ
    (by simpa using secondSubconstituent_card G hG x)
    (fun B => lorentzGramForm G x c y (lorentzProjectedGenerator G x c B))
    (lorentzGramForm G x c y y) hypos
  · intro B _
    exact hn B
  · exact le_of_eq (lorentzProjectedGenerator_secondMoment G hG x c hc y hy)

end SRG266
