/-
Uniform counting of one residue in a translated integer interval.
New proof source: not compiled in the assistant environment.
Every integer translation and representative is allowed; X=0 and d=1 are included.
-/
import Tengoku.Erdos647.Erdos647Sieve.Specification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve

/-- Actual number of integers in (A,A+X] congruent to r modulo d.-/
def progressionCount (A : ℤ) (X d : ℕ) (r : ℤ) : ℕ := by
  classical
  exact ((Finset.Icc (A + 1) (A + (X : ℤ))).filter
    (fun n : ℤ => (d : ℤ) ∣ n - r)).card

/-- A quotient threshold, proved from the Euclidean remainder inequalities.
@isnad1 id=iff.1h3v.s5.b98a9c8d918a from=translated src=- shape=10d3fd50 vocab=921eb918
-/
theorem mul_le_iff_le_euclideanQuotient (u d q : ℤ) (hd : 0 < d) :
    d * q ≤ u ↔ q ≤ u / d := by
  constructor
  · intro h
    by_contra hn
    have hq : u / d + 1 ≤ q := by omega
    have hm := mul_le_mul_of_nonneg_left hq hd.le
    have hu := Int.lt_mul_ediv_self_add (x := u) hd
    nlinarith
  · intro h
    exact (mul_le_mul_of_nonneg_left h hd.le).trans
      (Int.mul_ediv_self_le (x := u) hd.ne')

/-- The exact integer-division formula, with no sign restriction on A or r.
@isnad1 id=eq.1h4v.s6.dfa9e3f44b08 from=translated src=- shape=4940213a vocab=937f2cb4
-/
theorem progressionCount_eq_quotient_difference
    (A : ℤ) (X d : ℕ) (r : ℤ) (hd : 0 < d) :
    (progressionCount A X d r : ℤ) =
      (A + (X : ℤ) - r) / (d : ℤ) - (A - r) / (d : ℤ) := by
  classical
  have hdz : 0 < (d : ℤ) := by exact_mod_cast hd
  let lo : ℤ := (A - r) / (d : ℤ)
  let hi : ℤ := (A + (X : ℤ) - r) / (d : ℤ)
  have hmono : lo ≤ hi := by
    apply (mul_le_iff_le_euclideanQuotient
      (A + (X : ℤ) - r) (d : ℤ) lo hdz).mp
    have hl := Int.mul_ediv_self_le (x := A - r) hdz.ne'
    change (d : ℤ) * lo ≤ A - r at hl
    have hx : (0 : ℤ) ≤ X := by positivity
    linarith
  have hcard : (Finset.Icc (lo + 1) hi).card = progressionCount A X d r := by
    unfold progressionCount
    apply Finset.card_bij (fun q _ => (d : ℤ) * q + r)
    · intro q hq
      obtain ⟨hqlo, hqhi⟩ := Finset.mem_Icc.mp hq
      have hupper : (d : ℤ) * q ≤ A + (X : ℤ) - r :=
        (mul_le_iff_le_euclideanQuotient
          (A + (X : ℤ) - r) (d : ℤ) q hdz).mpr hqhi
      have hlower : A - r < (d : ℤ) * q := by
        by_contra hn
        have hqle := (mul_le_iff_le_euclideanQuotient
          (A - r) (d : ℤ) q hdz).mp (le_of_not_gt hn)
        change q ≤ lo at hqle
        omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      exact ⟨q, by ring⟩
    · intro q hq v hv heq
      have hm : (d : ℤ) * q = (d : ℤ) * v := by linarith
      exact mul_left_cancel₀ hdz.ne' hm
    · intro n hn
      obtain ⟨hnI, hdiv⟩ := Finset.mem_filter.mp hn
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hnI
      obtain ⟨q, hq⟩ := hdiv
      have hqhi : q ≤ hi := by
        apply (mul_le_iff_le_euclideanQuotient
          (A + (X : ℤ) - r) (d : ℤ) q hdz).mp
        linarith
      have hqlo : lo + 1 ≤ q := by
        by_contra hnq
        have hqle : q ≤ lo := by omega
        have hm := (mul_le_iff_le_euclideanQuotient
          (A - r) (d : ℤ) q hdz).mpr hqle
        linarith
      exact ⟨q, Finset.mem_Icc.mpr ⟨hqlo, hqhi⟩, by linarith⟩
  have hnonneg : 0 ≤ hi + 1 - (lo + 1) := by omega
  have hinterval : ((Finset.Icc (lo + 1) hi).card : ℤ) = hi - lo := by
    simp only [Int.card_Icc]
    omega
  rw [← hcard]
  exact hinterval

/-- Euclidean division differs from real division by a number in [0,1).
@isnad1 id=and.1h2v.s6.86beb4240a5e from=translated src=- shape=046df4cb vocab=df8f398b
-/
theorem euclideanQuotient_real_bounds (u : ℤ) (d : ℕ) (hd : 0 < d) :
    ((u / (d : ℤ) : ℤ) : ℝ) ≤ (u : ℝ) / (d : ℝ) ∧
      (u : ℝ) / (d : ℝ) < ((u / (d : ℤ) : ℤ) : ℝ) + 1 := by
  have hdz : 0 < (d : ℤ) := by exact_mod_cast hd
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  have hl := Int.mul_ediv_self_le (x := u) hdz.ne'
  have hu := Int.lt_mul_ediv_self_add (x := u) hdz
  have hlr : (d : ℝ) * ((u / (d : ℤ) : ℤ) : ℝ) ≤ (u : ℝ) := by exact_mod_cast hl
  have hur : (u : ℝ) <
      (d : ℝ) * ((u / (d : ℤ) : ℤ) : ℝ) + (d : ℝ) := by exact_mod_cast hu
  constructor
  · apply (le_div_iff₀ hdr).mpr
    nlinarith
  · apply (div_lt_iff₀ hdr).mpr
    nlinarith

/-- Uniform discrepancy at most one, including negative translations and X=0.
@isnad1 id=le.1h4v.s5.208661e6eac5 from=translated src=- shape=4fce3663 vocab=ad77599a
-/
theorem progressionCount_error_le_one
    (A : ℤ) (X d : ℕ) (r : ℤ) (hd : 0 < d) :
    |(progressionCount A X d r : ℝ) - (X : ℝ) / (d : ℝ)| ≤ 1 := by
  have heq : (progressionCount A X d r : ℝ) =
      (((A + (X : ℤ) - r) / (d : ℤ) : ℤ) : ℝ) -
        (((A - r) / (d : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast progressionCount_eq_quotient_difference A X d r hd
  have hb := euclideanQuotient_real_bounds (A + (X : ℤ) - r) d hd
  have ha := euclideanQuotient_real_bounds (A - r) d hd
  have hdiff : ((A + (X : ℤ) - r : ℤ) : ℝ) / (d : ℝ) -
      ((A - r : ℤ) : ℝ) / (d : ℝ) = (X : ℝ) / (d : ℝ) := by
    push_cast
    ring
  rw [heq, abs_le]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- The same actual interval count, indexed by an element of ZMod.-/
def residueClassCount (A : ℤ) (X d : ℕ) (r : ZMod d) : ℕ := by
  classical
  exact ((Finset.Icc (A + 1) (A + (X : ℤ))).filter
    (fun n : ℤ => (n : ZMod d) = r)).card

/--
@isnad1 id=eq.1h4v.s5.1b49e44e4054 from=translated src=- shape=4c867ca4 vocab=7d6cfb83
-/
theorem residueClassCount_eq_progressionCount
    (A : ℤ) (X d : ℕ) (r : ZMod d) (hd : 0 < d) :
    residueClassCount A X d r = progressionCount A X d (r.val : ℤ) := by
  classical
  letI : NeZero d := ⟨hd.ne'⟩
  unfold residueClassCount progressionCount
  apply congrArg Finset.card
  apply Finset.ext
  intro n
  have hiff : (d : ℤ) ∣ n - (r.val : ℤ) ↔ (n : ZMod d) = r := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast,
      ZMod.natCast_zmod_val, sub_eq_zero]
  simp only [Finset.mem_filter, hiff]

/--
@isnad1 id=le.1h4v.s6.57d9b8c0a6e7 from=translated src=- shape=b3dd6b38 vocab=a1a72b1e
-/
theorem residueClassCount_error_le_one
    (A : ℤ) (X d : ℕ) (r : ZMod d) (hd : 0 < d) :
    |(residueClassCount A X d r : ℝ) - (X : ℝ) / (d : ℝ)| ≤ 1 := by
  rw [residueClassCount_eq_progressionCount A X d r hd]
  exact progressionCount_error_le_one A X d (r.val : ℤ) hd

/-- Counting an arbitrary finite set of residue classes, with one error per class.
@isnad1 id=le.1h4v.s7.d19f810ba7fe from=translated src=- shape=30cc616a vocab=fd4cfdeb
-/
theorem residueSetCount_error_le_card
    (A : ℤ) (X d : ℕ) (R : Finset (ZMod d)) (hd : 0 < d) :
    |(((Finset.Icc (A + 1) (A + (X : ℤ))).filter
        (fun n : ℤ => (n : ZMod d) ∈ R)).card : ℝ) -
      (X : ℝ) * ((R.card : ℝ) / (d : ℝ))| ≤ (R.card : ℝ) := by
  classical
  let I : Finset ℤ := Finset.Icc (A + 1) (A + (X : ℤ))
  have hcount : (I.filter (fun n : ℤ => (n : ZMod d) ∈ R)).card =
      ∑ r ∈ R, residueClassCount A X d r := by
    simpa only [residueClassCount, I] using
      (Finset.sum_card_fiberwise_eq_card_filter I R (fun n : ℤ => (n : ZMod d))).symm
  have heq : ((I.filter (fun n : ℤ => (n : ZMod d) ∈ R)).card : ℝ) -
        (X : ℝ) * ((R.card : ℝ) / (d : ℝ)) =
      ∑ r ∈ R, ((residueClassCount A X d r : ℝ) - (X : ℝ) / (d : ℝ)) := by
    rw [hcount]
    simp only [Nat.cast_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  change |((I.filter (fun n : ℤ => (n : ZMod d) ∈ R)).card : ℝ) -
    (X : ℝ) * ((R.card : ℝ) / (d : ℝ))| ≤ (R.card : ℝ)
  rw [heq]
  calc
    _ ≤ ∑ r ∈ R, |(residueClassCount A X d r : ℝ) - (X : ℝ) / (d : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ R, (1 : ℝ) := Finset.sum_le_sum
      (fun r _hr => residueClassCount_error_le_one A X d r hd)
    _ = (R.card : ℝ) := by simp

end Erdos647Sieve
end
