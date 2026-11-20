import Tengoku.GnmLean.GNM.Lift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The counts are constant along each family

Above the threshold the lift and the truncation are mutually inverse, so the good partitions at a
fixed offset from two different powers of three are in bijection and the counts agree. Every value
of the two exceptional sets lies on such a family, which is how twenty exact counts at small values
decide the count at every member.
-/

namespace GNM

open GN

noncomputable section

/-- The count at a negative offset is the same at every admissible power.
@isnad1 id=eq.4h3v.s7.50c2f77144ae from=translated src=- shape=ca046f5e vocab=810e83d3
-/
theorem count_sub_eq {r t t' : ℕ} (hr : 1 ≤ r) (hthr : r * (r - 1) < 3 ^ t) (h2 : 2 * r < 3 ^ t)
    (htt' : t ≤ t') : count (3 ^ t - r) = count (3 ^ t' - r) := by
  have hpow : (3 : ℕ) ^ t ≤ 3 ^ t' := Nat.pow_le_pow_right (by norm_num) htt'
  refine le_antisymm (count_sub_le_count_sub hr h2 htt') ?_
  refine count_le_of_leftInverse
    (fun bs => truncBlocks ((3 ^ t : ℕ) : ℤ) ((3 ^ t' : ℕ) : ℤ) bs)
    (fun bs => liftBlocks ((3 ^ t : ℕ) : ℤ) ((3 ^ t' : ℕ) : ℤ) bs) ?_ ?_
  · intro bs hbs
    rw [isGoodPartition_iff] at hbs ⊢
    exact (liftBlocks_truncBlocks_sub (Q := 3 ^ t) (Q' := 3 ^ t') (r := r) (t := t) (t' := t')
      rfl rfl hpow hr h2 hthr hbs).2
  · intro bs hbs
    rw [isGoodPartition_iff] at hbs
    exact (liftBlocks_truncBlocks_sub (Q := 3 ^ t) (Q' := 3 ^ t') (r := r) (t := t) (t' := t')
      rfl rfl hpow hr h2 hthr hbs).1

/-- The count at a positive offset is the same at every admissible power.
@isnad1 id=eq.2h3v.s6.520db1b96bbf from=translated src=- shape=89eda202 vocab=66698a0f
-/
theorem count_add_eq {r t t' : ℕ} (hthr : r * (r + 1) < 3 ^ t) (htt' : t ≤ t') :
    count (3 ^ t + r) = count (3 ^ t' + r) := by
  have hpow : (3 : ℕ) ^ t ≤ 3 ^ t' := Nat.pow_le_pow_right (by norm_num) htt'
  refine le_antisymm ?_ ?_
  · refine count_le_of_leftInverse
      (fun bs => liftBlocks ((3 ^ t : ℕ) : ℤ) ((3 ^ t' : ℕ) : ℤ) bs)
      (fun bs => truncBlocks ((3 ^ t : ℕ) : ℤ) ((3 ^ t' : ℕ) : ℤ) bs) ?_ ?_
    · intro bs hbs
      rw [isGoodPartition_iff] at hbs ⊢
      exact liftBlocks_goodOn_add (P := 3 ^ t) (P' := 3 ^ t') (r := r) (t := t) (t' := t')
        rfl rfl hpow hthr hbs
    · intro bs hbs
      rw [isGoodPartition_iff] at hbs
      exact truncBlocks_liftBlocks_add (P := 3 ^ t) (P' := 3 ^ t') (r := r) (t := t) (t' := t')
        rfl rfl hpow hthr hbs
  · refine count_le_of_leftInverse
      (fun bs => truncBlocks ((3 ^ t : ℕ) : ℤ) ((3 ^ t' : ℕ) : ℤ) bs)
      (fun bs => liftBlocks ((3 ^ t : ℕ) : ℤ) ((3 ^ t' : ℕ) : ℤ) bs) ?_ ?_
    · intro bs hbs
      rw [isGoodPartition_iff] at hbs ⊢
      exact (liftBlocks_truncBlocks_add (P := 3 ^ t) (P' := 3 ^ t') (r := r) (t := t) (t' := t')
        rfl rfl hpow hthr hbs).2
    · intro bs hbs
      rw [isGoodPartition_iff] at hbs
      exact (liftBlocks_truncBlocks_add (P := 3 ^ t) (P' := 3 ^ t') (r := r) (t := t) (t' := t')
        rfl rfl hpow hthr hbs).1

end

end GNM
