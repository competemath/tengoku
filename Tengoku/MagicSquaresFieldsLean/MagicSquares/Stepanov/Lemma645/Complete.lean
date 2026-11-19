import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma645.PowerFibers
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma645.Abstract

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The field partition and complete numerical output of Lemma 6.45
-/

omit [DecidableEq F] in
/--
@isnad1 id=ne.1h2v.s5.7c2c81698c9f from=translated src=- shape=4c1b84ad vocab=a4ac2485
-/
theorem cast_divisor_card_sub_one_ne_zero {m : ℕ}
    (hmq : m ∣ Fintype.card F - 1) : (m : F) ≠ 0 := by
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have hcast : (m : F) * (((Fintype.card F - 1) / m : ℕ) : F) = -1 := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hmq, Nat.cast_sub hq]
    simp [Nat.cast_card_eq_zero]
  intro hz
  simp [hz] at hcast

omit [DecidableEq F] in
/--
@isnad1 id=eq.2h4v.s6.3dbbed87c02c from=translated src=- shape=2f3eec30 vocab=6b7eccc6
-/
theorem eval_stepanovG_of_eval_eq_zero {m : ℕ}
    (hmq : m ∣ Fintype.card F - 1) (f : Polynomial F) (c : F)
    (hc : eval c f = 0) : eval c (stepanovG m f) = 0 := by
  simp [stepanovG, stepanovPowerExponent, hc, (stepanovPowerExponent_pos hmq).ne']

omit [DecidableEq F] in
/--
@isnad1 id=eq.2h4v.s6.c9531b286a31 from=translated src=- shape=74c11eee vocab=cb1dc9cd
-/
theorem eval_stepanovG_pow {m : ℕ}
    (hmq : m ∣ Fintype.card F - 1) (f : Polynomial F) (c : F)
    (hc : eval c f ≠ 0) : (eval c (stepanovG m f)) ^ m = 1 := by
  simp only [stepanovG, stepanovPowerExponent, Polynomial.eval_pow,
    ← pow_mul, Nat.div_mul_cancel hmq]
  exact FiniteField.pow_card_sub_one_eq_one _ hc

omit [Fintype F] [DecidableEq F] in
/--
@isnad1 id=eq.1h2v.s6.427dcb9a13ff from=translated src=- shape=8a2c9c21 vocab=96eacde8
-/
theorem eval_geometricPolynomial_zero {m : ℕ} (hm : 0 < m) :
    eval (0 : F) (geometricPolynomial (F := F) m) = 1 := by
  simp [geometricPolynomial, hm.ne']

omit [Fintype F] [DecidableEq F] in
/--
@isnad1 id=eq.0h2v.s5.8c9a07ba33f7 from=translated src=- shape=f2133912 vocab=c7845fd3
-/
theorem eval_geometricPolynomial_one (m : ℕ) :
    eval (1 : F) (geometricPolynomial (F := F) m) = (m : F) := by
  simp [geometricPolynomial]

omit [Fintype F] [DecidableEq F] in
/--
@isnad1 id=eq.2h3v.s6.26245b104ab7 from=translated src=- shape=b727239e vocab=9d4ed2bb
-/
theorem eval_geometricPolynomial_eq_zero {m : ℕ} {a : F}
    (ha : a ^ m = 1) (ha1 : a ≠ 1) :
    eval a (geometricPolynomial (F := F) m) = 0 := by
  have h := geom_sum_mul a m
  rw [ha, sub_self, mul_eq_zero] at h
  simpa [geometricPolynomial] using h.resolve_right (sub_ne_zero.mpr ha1)

/--
@isnad1 id=disjoint.1h3v.s5.8c08c2029b17 from=translated src=- shape=46cb573c vocab=bff557d0
-/
theorem stepanovT0_disjoint_T1 {m : ℕ}
    (hmq : m ∣ Fintype.card F - 1) (f : Polynomial F) :
    Disjoint (stepanovT0 f) (stepanovT1 m f) := by
  apply Finset.disjoint_left.mpr
  intro c hc0 hc1
  have hz := eval_stepanovG_of_eval_eq_zero hmq f c ((mem_stepanovT0 f c).mp hc0)
  have hone := (mem_stepanovT1 m f c).mp hc1
  exact zero_ne_one (hz.symm.trans hone)

/--
@isnad1 id=disjoint.2h3v.s6.db6d221b8101 from=translated src=- shape=4ff4613d vocab=024ff5bc
-/
theorem stepanovT0_disjoint_T2 {m : ℕ} (hm : 0 < m)
    (hmq : m ∣ Fintype.card F - 1) (f : Polynomial F) :
    Disjoint (stepanovT0 f) (stepanovT2 m f) := by
  apply Finset.disjoint_left.mpr
  intro c hc0 hc2
  have hz := eval_stepanovG_of_eval_eq_zero hmq f c ((mem_stepanovT0 f c).mp hc0)
  have hgeo := (mem_stepanovT2 m f c).mp hc2
  rw [hz, eval_geometricPolynomial_zero hm] at hgeo
  exact one_ne_zero hgeo

/--
@isnad1 id=disjoint.1h3v.s6.6bcbdd95ffe3 from=translated src=- shape=835f2bec vocab=db900c62
-/
theorem stepanovT1_disjoint_T2 {m : ℕ}
    (hmq : m ∣ Fintype.card F - 1) (f : Polynomial F) :
    Disjoint (stepanovT1 m f) (stepanovT2 m f) := by
  apply Finset.disjoint_left.mpr
  intro c hc1 hc2
  have hone := (mem_stepanovT1 m f c).mp hc1
  have hgeo := (mem_stepanovT2 m f c).mp hc2
  rw [hone, eval_geometricPolynomial_one] at hgeo
  exact cast_divisor_card_sub_one_ne_zero hmq hgeo

/--
@isnad1 id=eq.1h3v.s6.972cc1a27010 from=translated src=- shape=a3925aed vocab=714b05fc
-/
theorem stepanovT_union {m : ℕ}
    (hmq : m ∣ Fintype.card F - 1) (f : Polynomial F) :
    (stepanovT0 f ∪ stepanovT1 m f) ∪ stepanovT2 m f = Finset.univ := by
  ext c
  simp only [Finset.mem_union, mem_stepanovT0, mem_stepanovT1, mem_stepanovT2,
    Finset.mem_univ, iff_true]
  by_cases hc0 : eval c f = 0
  · exact Or.inl (Or.inl hc0)
  by_cases hc1 : eval c (stepanovG m f) = 1
  · exact Or.inl (Or.inr hc1)
  exact Or.inr (eval_geometricPolynomial_eq_zero (eval_stepanovG_pow hmq f c hc0) hc1)

/-- The partition identity in Lemma 6.45.
@isnad1 id=eq.2h3v.s6.c1825248de3d from=translated src=- shape=d8cc9040 vocab=acd2891a
-/
theorem ln97_6_45_partition {m : ℕ} (hm : 0 < m)
    (hmq : m ∣ Fintype.card F - 1) (f : Polynomial F) :
    (stepanovT0 f).card + (stepanovT1 m f).card + (stepanovT2 m f).card =
      Fintype.card F := by
  have h := congrArg Finset.card (stepanovT_union hmq f)
  rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨stepanovT0_disjoint_T2 hm hmq f,
        stepanovT1_disjoint_T2 hmq f⟩),
    Finset.card_union_of_disjoint (stepanovT0_disjoint_T1 hmq f),
    Finset.card_univ] at h
  exact h

/-- All numerical data for 6.53, now derived from the actual finite field.-/
noncomputable def lemma645CountsOfField {m : ℕ} (hm : 0 < m)
    (hmq : m ∣ Fintype.card F - 1) (f : Polynomial F) : Lemma645Counts :=
  concrete645Counts m (stepanovSolutionCount m f) f
    (ln97_6_45_solutions hm hmq f) (ln97_6_45_partition hm hmq f)

end LN97
end MagicSquares
