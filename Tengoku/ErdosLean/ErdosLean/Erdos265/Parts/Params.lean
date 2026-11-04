import Tengoku.ErdosLean.ErdosLean.Erdos265.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős #265 — Part L3: the parameter sequence `m_k`, `N_k = 4^{m_k}`, `M_k = 2^{m_k}`

`m_0 = 40`, `m_{k+1} = m_k + ⌊m_k/10⌋ + 1`.
* `M_k² = N_k`, `m_k ≥ 40`, `N_k ≥ 64`, `2 M_k < N_k`;
* the nesting condition (cf. KT v4 (7.17), with `D = 16`, `ε = 1/16`):
  `16/N_k² ≤ M_{k+1}/(16 N_{k+1}²)` ⇔ `8 + 3 m_{k+1} ≤ 4 m_k`, and
  `16/N_k³ ≤ M_{k+1}/(16 N_{k+1}³)` ⇔ `8 + 5 m_{k+1} ≤ 6 m_k` (true as `m_k ≥ 40`);
* consecutive blocks are separated: `2N_k + M_k + M_{k+1} < N_{k+1}`;
* radii are positive and tend to `0`;
* growth: `m_k ≥ 40 · (21/20)^k`.
-/

open Filter Topology

namespace Erdos265

/--
@isnad1 id=eq.0h1v.s5.bbe7a896f613 from=translated src=- shape=13804d8c vocab=b2aa1641
-/
theorem NN_eq_two_pow (k : ℕ) : NN k = 2 ^ (2 * mSeq k) := by
  unfold NN; rw [pow_mul]; norm_num

/--
@isnad1 id=eq.0h1v.s4.9ec85eb526dd from=translated src=- shape=e90133e3 vocab=81ad7bb1
-/
theorem MM_sq (k : ℕ) : MM k ^ 2 = NN k := by
  rw [NN_eq_two_pow]; unfold MM; rw [← pow_mul, mul_comm]

/--
@isnad1 id=le.0h1v.s4.b3e153eaffc4 from=translated src=- shape=9a470a5e vocab=c46bfd59
-/
theorem mSeq_ge_add (k : ℕ) : k + 40 ≤ mSeq k := by
  induction k with
  | zero => simp [mSeq]
  | succ k ih => simp only [mSeq]; omega

/--
@isnad1 id=le.0h1v.s3.b99cd2834f19 from=translated src=- shape=8a62b088 vocab=059792d4
-/
theorem mSeq_ge (k : ℕ) : 40 ≤ mSeq k := by
  have := mSeq_ge_add k; omega

/--
@isnad1 id=le.0h1v.s3.4d1117b08b82 from=translated src=- shape=8a62b088 vocab=b603700a
-/
theorem NN_ge (k : ℕ) : 64 ≤ NN k := by
  unfold NN
  calc (64 : ℕ) = 4 ^ 3 := by norm_num
    _ ≤ 4 ^ mSeq k := Nat.pow_le_pow_right (by norm_num) (by have := mSeq_ge k; omega)

/--
@isnad1 id=le.0h1v.s3.d3ef2ede72fb from=translated src=- shape=8a62b088 vocab=8c33479d
-/
theorem MM_ge (k : ℕ) : 4 ≤ MM k := by
  unfold MM
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ mSeq k := Nat.pow_le_pow_right (by norm_num) (by have := mSeq_ge k; omega)

/--
@isnad1 id=lt.0h1v.s4.43b0b508c6fd from=translated src=- shape=66759b31 vocab=00dac181
-/
theorem two_MM_lt (k : ℕ) : 2 * MM k < NN k := by
  rw [← MM_sq, sq]
  have := MM_ge k
  nlinarith

/--
@isnad1 id=lt.0h1v.s5.47dafeec5555 from=translated src=- shape=5798a8ae vocab=be2515b7
-/
theorem block_gap (k : ℕ) : 2 * NN k + MM k + MM (k + 1) < NN (k + 1) := by
  have hm := mSeq_ge k
  have hs : mSeq (k + 1) = mSeq k + mSeq k / 10 + 1 := rfl
  rw [NN_eq_two_pow, NN_eq_two_pow]
  unfold MM
  have h1 : 2 ^ mSeq k ≤ 2 ^ (2 * mSeq k) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ mSeq (k + 1) ≤ 2 ^ (2 * mSeq (k + 1) - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (2 * mSeq k) * 2 ^ 3 ≤ 2 ^ (2 * mSeq (k + 1) - 1) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (2 * mSeq (k + 1)) = 2 ^ (2 * mSeq (k + 1) - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have h5 : 0 < 2 ^ (2 * mSeq k) := by positivity
  omega

/--
@isnad1 id=lt.0h1v.s3.029f64a0f38f from=translated src=- shape=b9369acb vocab=31ee7446
-/
theorem rad1_pos (k : ℕ) : 0 < rad1 k := by
  unfold rad1
  have : (0 : ℝ) < MM k := by exact_mod_cast (show 0 < MM k by have := MM_ge k; omega)
  have : (0 : ℝ) < NN k := by exact_mod_cast (show 0 < NN k by have := NN_ge k; omega)
  positivity

/--
@isnad1 id=lt.0h1v.s3.f31c10b0ce76 from=translated src=- shape=b9369acb vocab=76c0fb99
-/
theorem rad2_pos (k : ℕ) : 0 < rad2 k := by
  unfold rad2
  have : (0 : ℝ) < MM k := by exact_mod_cast (show 0 < MM k by have := MM_ge k; omega)
  have : (0 : ℝ) < NN k := by exact_mod_cast (show 0 < NN k by have := NN_ge k; omega)
  positivity

/--
@isnad1 id=le.0h1v.s6.2a180668c6e3 from=translated src=- shape=9d334864 vocab=a0844e3c
-/
theorem step_rad1_nat (k : ℕ) : 256 * NN (k + 1) ^ 2 ≤ MM (k + 1) * NN k ^ 2 := by
  have hm := mSeq_ge k
  have hs : mSeq (k + 1) = mSeq k + mSeq k / 10 + 1 := rfl
  rw [NN_eq_two_pow, NN_eq_two_pow]; unfold MM
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/--
@isnad1 id=le.0h1v.s6.d8ef59b71f45 from=translated src=- shape=9d334864 vocab=a0844e3c
-/
theorem step_rad2_nat (k : ℕ) : 256 * NN (k + 1) ^ 3 ≤ MM (k + 1) * NN k ^ 3 := by
  have hm := mSeq_ge k
  have hs : mSeq (k + 1) = mSeq k + mSeq k / 10 + 1 := rfl
  rw [NN_eq_two_pow, NN_eq_two_pow]; unfold MM
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/--
@isnad1 id=le.0h1v.s5.c58c81cb35e8 from=translated src=- shape=2ceaf890 vocab=528a676e
-/
theorem step_rad1 (k : ℕ) : 16 / (NN k : ℝ) ^ 2 ≤ rad1 (k + 1) := by
  unfold rad1
  have h : ((256 * NN (k + 1) ^ 2 : ℕ) : ℝ) ≤ ((MM (k + 1) * NN k ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast step_rad1_nat k
  push_cast at h
  have a : (0 : ℝ) < NN k := by exact_mod_cast (show 0 < NN k by have := NN_ge k; omega)
  have b : (0 : ℝ) < NN (k + 1) := by
    exact_mod_cast (show 0 < NN (k + 1) by have := NN_ge (k + 1); omega)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/--
@isnad1 id=le.0h1v.s5.fd70e909894c from=translated src=- shape=2ceaf890 vocab=bd6eacfb
-/
theorem step_rad2 (k : ℕ) : 16 / (NN k : ℝ) ^ 3 ≤ rad2 (k + 1) := by
  unfold rad2
  have h : ((256 * NN (k + 1) ^ 3 : ℕ) : ℝ) ≤ ((MM (k + 1) * NN k ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast step_rad2_nat k
  push_cast at h
  have a : (0 : ℝ) < NN k := by exact_mod_cast (show 0 < NN k by have := NN_ge k; omega)
  have b : (0 : ℝ) < NN (k + 1) := by
    exact_mod_cast (show 0 < NN (k + 1) by have := NN_ge (k + 1); omega)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/--
@isnad1 id=le.0h1v.s4.a07579587717 from=translated src=- shape=9a470a5e vocab=17d35469
-/
theorem NN_ge_succ (k : ℕ) : k + 1 ≤ NN k := by
  have h := mSeq_ge_add k
  have : mSeq k < 2 ^ mSeq k := Nat.lt_two_pow_self
  have : 2 ^ mSeq k ≤ NN k := by
    rw [NN_eq_two_pow]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/--
@isnad1 id=le.0h1v.s3.a77dc7dfe231 from=translated src=- shape=0fc427d2 vocab=474e61df
-/
theorem MM_le_NN (k : ℕ) : MM k ≤ NN k := by
  rw [← MM_sq, sq]; exact Nat.le_mul_of_pos_left _ (by have := MM_ge k; omega)

/--
@isnad1 id=le.0h1v.s5.bfa6da3c7511 from=translated src=- shape=3db9ef6f vocab=99d94b48
-/
theorem rad1_le (k : ℕ) : rad1 k ≤ 1 / ((k : ℝ) + 1) := by
  unfold rad1
  have h1 : ((k + 1 : ℕ) : ℝ) ≤ (NN k : ℝ) := by exact_mod_cast NN_ge_succ k
  have h2 : (MM k : ℝ) ≤ (NN k : ℝ) := by exact_mod_cast MM_le_NN k
  have a : (0 : ℝ) < NN k := by exact_mod_cast (show 0 < NN k by have := NN_ge k; omega)
  have hM : (0 : ℝ) ≤ MM k := by positivity
  push_cast at h1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul h2 h1 (by positivity) a.le]

/--
@isnad1 id=le.0h1v.s5.b625d0863869 from=translated src=- shape=3db9ef6f vocab=4fc9c3f5
-/
theorem rad2_le (k : ℕ) : rad2 k ≤ 1 / ((k : ℝ) + 1) := by
  have a : (1 : ℝ) ≤ NN k := by exact_mod_cast (show 1 ≤ NN k by have := NN_ge k; omega)
  have : rad2 k ≤ rad1 k := by
    unfold rad1 rad2
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    rw [pow_succ]; nlinarith [pow_pos (show (0:ℝ) < NN k by linarith) 2]
  exact this.trans (rad1_le k)

/--
@isnad1 id=tendsto.0h0v.s5.ba475f5e97c5 from=translated src=- shape=92a488d6 vocab=1663a2e8
-/
theorem tendsto_one_div_succ' : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/--
@isnad1 id=tendsto.0h0v.s4.df3624af18ed from=translated src=- shape=8e2810f0 vocab=c50eca34
-/
theorem rad1_tendsto : Tendsto rad1 atTop (𝓝 0) :=
  squeeze_zero (fun k => (rad1_pos k).le) rad1_le tendsto_one_div_succ'

/--
@isnad1 id=tendsto.0h0v.s4.784f74fb80dd from=translated src=- shape=8e2810f0 vocab=73782f55
-/
theorem rad2_tendsto : Tendsto rad2 atTop (𝓝 0) :=
  squeeze_zero (fun k => (rad2_pos k).le) rad2_le tendsto_one_div_succ'

/--
@isnad1 id=le.0h1v.s5.44a6eca221c6 from=translated src=- shape=7197f5e2 vocab=3fc1c7f2
-/
theorem mSeq_growth (k : ℕ) : (40 : ℝ) * (21 / 20 : ℝ) ^ k ≤ (mSeq k : ℝ) := by
  induction k with
  | zero => simp [mSeq]
  | succ k ih =>
    have hn : 20 * mSeq (k + 1) ≥ 21 * mSeq k := by
      simp only [mSeq]; omega
    have hr : (20 : ℝ) * (mSeq (k + 1) : ℝ) ≥ 21 * (mSeq k : ℝ) := by exact_mod_cast hn
    rw [pow_succ]
    nlinarith
end Erdos265
