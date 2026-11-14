import Tengoku.Seed.Data.Rat.Floor
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Algebra.Order.BigOperators.Group.LocallyFinite
import Tengoku.Seed.Order.Interval.Finset.Nat
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

def _root_.Tengoku.FltAnthropic.dedekindSaw (x : ℚ) : ℚ :=
  if Int.fract x = 0 then 0 else Int.fract x - 1 / 2

/--
@isnad1 id=eq.1h1v.s4.efa7ac4fae48 from=translated src=- shape=42fd2044 vocab=9bd8677c
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSaw_of_fract_eq_zero {x : ℚ} (h : Int.fract x = 0) : dedekindSaw x = 0 :=
  ite_eq_left h

/--
@isnad1 id=eq.1h1v.s5.dbf44976e1a2 from=translated src=- shape=56451591 vocab=99980bdc
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSaw_of_fract_ne_zero {x : ℚ} (h : Int.fract x ≠ 0) :
    dedekindSaw x = Int.fract x - 1 / 2 :=
  ite_eq_right h

/--
@isnad1 id=eq.0h1v.s3.75d24c9afd39 from=translated src=- shape=8723f6b7 vocab=7b57826b
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSaw_intCast (n : ℤ) : dedekindSaw (n : ℚ) = 0 :=
  dedekindSaw_of_fract_eq_zero (Int.fract_intCast n)

/--
@isnad1 id=eq.0h1v.s3.dad5f70247a5 from=translated src=- shape=8723f6b7 vocab=26633e55
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSaw_natCast (n : ℕ) : dedekindSaw (n : ℚ) = 0 := by
  rw [← Int.cast_natCast]; exact dedekindSaw_intCast (n : ℤ)

/--
@isnad1 id=eq.0h0v.s3.b27459cad60b from=translated src=- shape=3c26ae4f vocab=7a7fc2fa
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSaw_zero : dedekindSaw 0 = 0 := by
  rw [← Int.cast_zero]; exact dedekindSaw_intCast 0

/--
@isnad1 id=eq.0h0v.s3.611df57d02f2 from=translated src=- shape=3c26ae4f vocab=7a7fc2fa
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSaw_one : dedekindSaw 1 = 0 := by
  rw [← Int.cast_one]; exact dedekindSaw_intCast 1

/--
@isnad1 id=eq.0h2v.s4.9df300a8f09a from=translated src=- shape=1dc88c11 vocab=e6495c9c
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSaw_add_intCast (x : ℚ) (n : ℤ) : dedekindSaw (x + n) = dedekindSaw x := by
  unfold dedekindSaw
  rw [Int.fract_add_intCast]

/--
@isnad1 id=eq.0h2v.s4.0429cef79a82 from=translated src=- shape=236bda07 vocab=e6495c9c
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSaw_intCast_add (n : ℤ) (x : ℚ) : dedekindSaw ((n : ℚ) + x) = dedekindSaw x := by
  rw [add_comm, dedekindSaw_add_intCast]

/--
@isnad1 id=eq.0h2v.s4.d52ded83b5d3 from=translated src=- shape=1dc88c11 vocab=8b93143b
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSaw_add_natCast (x : ℚ) (n : ℕ) : dedekindSaw (x + n) = dedekindSaw x := by
  rw [← Int.cast_natCast]; exact dedekindSaw_add_intCast x (n : ℤ)

/--
@isnad1 id=eq.0h1v.s3.78a7c3760c8f from=translated src=- shape=c7188113 vocab=777dbd62
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSaw_neg (x : ℚ) : dedekindSaw (-x) = -dedekindSaw x := by
  unfold dedekindSaw
  by_cases h : Int.fract x = 0
  · rw [ite_eq_left h, ite_eq_left (Int.fract_neg_eq_zero.2 h), neg_zero]
  · rw [ite_eq_right h, ite_eq_right fun h' => h (Int.fract_neg_eq_zero.1 h'), Int.fract_neg h]
    ring

/--
@isnad1 id=lt.0h1v.s4.b030ff7265d9 from=translated src=- shape=e2474f27 vocab=57fa84e9
-/
theorem _root_.Tengoku.FltAnthropic.abs_dedekindSaw_lt_half (x : ℚ) : |dedekindSaw x| < 1 / 2 := by
  unfold dedekindSaw
  by_cases h : Int.fract x = 0
  · rw [ite_eq_left h, abs_zero]
    exact one_half_pos
  · have h0 : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm h)
    have h1 : Int.fract x < 1 := Int.fract_lt_one x
    rw [ite_eq_right h, abs_lt]
    constructor <;> linarith

/--
@isnad1 id=eq.0h0v.s4.629c886e0f5e from=translated src=- shape=7ed1bc26 vocab=8d978f90
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSaw_half : dedekindSaw (1 / 2) = 0 := by
  have hfr : Int.fract (1 / 2 : ℚ) = 1 / 2 :=
    Int.fract_eq_self.2 ⟨one_half_pos.le, one_half_lt_one⟩
  rw [dedekindSaw_of_fract_ne_zero (by rw [hfr]; exact one_half_pos.ne'), hfr, sub_self]

/--
@isnad1 id=eq.2h2v.s6.5672e2f96150 from=translated src=- shape=0d93e6f7 vocab=d1a2b5fa
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSaw_natCast_div {r k : ℕ} (h0 : 0 < r) (hrk : r < k) :
    dedekindSaw ((r : ℚ) / k) = (r : ℚ) / k - 1 / 2 := by
  have hk : (0 : ℚ) < k := by exact_mod_cast h0.trans hrk
  have hpos : (0 : ℚ) < (r : ℚ) / k := div_pos (by exact_mod_cast h0) hk
  have hlt : (r : ℚ) / k < 1 := (div_lt_one hk).2 (by exact_mod_cast hrk)
  have hfr : Int.fract ((r : ℚ) / k) = (r : ℚ) / k := Int.fract_eq_self.2 ⟨hpos.le, hlt⟩
  rw [dedekindSaw_of_fract_ne_zero (by rw [hfr]; exact hpos.ne'), hfr]

def _root_.Tengoku.FltAnthropic.dedekindSum (h : ℤ) (k : ℕ) : ℚ :=
  ∑ r ∈ Finset.range k, dedekindSaw ((r : ℚ) / k) * dedekindSaw ((h : ℚ) * r / k)

/--
@isnad1 id=eq.0h1v.s4.b21dc6878cde from=translated src=- shape=59ae2d96 vocab=a4737ee7
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSum_zero_right (h : ℤ) : dedekindSum h 0 = 0 := by
  simp [dedekindSum]

/--
@isnad1 id=eq.0h1v.s4.be0d57d50f5c from=translated src=- shape=59ae2d96 vocab=a4737ee7
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSum_one_right (h : ℤ) : dedekindSum h 1 = 0 := by
  simp [dedekindSum, dedekindSaw_zero]

/--
@isnad1 id=eq.0h1v.s4.3d7f9504ed61 from=translated src=- shape=fcc0db09 vocab=a4737ee7
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSum_zero_left (k : ℕ) : dedekindSum 0 k = 0 := by
  simp [dedekindSum, dedekindSaw_zero]

/--
@isnad1 id=eq.0h2v.s4.0dd51959e0fa from=translated src=- shape=23fa6e79 vocab=2401e37a
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSum_neg (h : ℤ) (k : ℕ) : dedekindSum (-h) k = -dedekindSum h k := by
  unfold dedekindSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Int.cast_neg, neg_mul, neg_div, dedekindSaw_neg]
  ring

/--
@isnad1 id=eq.0h3v.s5.dd1345b8efea from=translated src=- shape=b86f82f9 vocab=84c38aa4
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSum_add_mul (h m : ℤ) (k : ℕ) : dedekindSum (h + m * k) k = dedekindSum h k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [dedekindSum_zero_right, dedekindSum_zero_right]
  unfold dedekindSum
  refine Finset.sum_congr rfl fun r _ => ?_
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have key : ((h + m * k : ℤ) : ℚ) * r / k = (h : ℚ) * r / k + ((m * r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [key, dedekindSaw_add_intCast]

/--
@isnad1 id=eq.0h2v.s6.3d3844794f52 from=translated src=- shape=b3ed63af vocab=b43ba3b4
-/
theorem _root_.Tengoku.FltAnthropic.dedekindSum_eq_sum_Ico (h : ℤ) (k : ℕ) :
    dedekindSum h k =
      ∑ r ∈ Finset.Ico 1 k, ((r : ℚ) / k - 1 / 2) * dedekindSaw ((h : ℚ) * r / k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [dedekindSum_zero_right]
    simp
  unfold dedekindSum
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk, zero_add]
  simp only [Nat.cast_zero, zero_div, dedekindSaw_zero, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hr
  rw [dedekindSaw_natCast_div h1 h2]
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
