import Tengoku.FourierJacobiCoreEvaluation.FourierJacobi.Analysis.MasterSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/abhisaha-git/fourier-jacobi-core-evaluation@fb2b788d6271, `FourierJacobi/Analysis/I1Complete.lean`: removed 3 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!+# Infinite I1 valuation rows

The monomial below is the independent entry/minor valuation monomial, with
the actual I1 coefficient incorporated using q*t^2=1.  It is not defined by
any finite region fraction. Each lattice cone is parameterized explicitly;
both inverse laws and every infinite geometric evaluation are kernel checked.
The parity refinements of rows 3a and 8a are kept visible.
-/

noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations

set_option maxHeartbeats 2000000

def i1Raw (t d U V T : ℂ) (p : ℤ × ℤ × ℤ) (c : ℕ) : ℂ :=
  let ell := (cartanIndices 1 p.1 p.2.1 p.2.2 c).1
  let b := (cartanIndices 1 p.1 p.2.1 p.2.2 c).2
  (1 - t ^ 2) ^ 3 * d ^ p.1 *
    t ^ (3 * p.1 + 2 * p.2.1 + 2 * p.2.2 + 3 * ell + 4 * b - 2) *
    (T * U) ^ (ell / 2) * (T * V) ^ b

/--
@isnad1 id=eq.2h8v.s6.b6270619a3aa from=translated src=- shape=030491b6 vocab=7be53a0e
-/
theorem i1Raw_eq_shell (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q * t ^ 2 = 1) (p : ℤ × ℤ × ℤ) (c : ℕ) :
    i1Raw t d U V T p c = shellCoeff q 1 * shellMonomial t d U V T 1 p c := by
  have hq : q = (t ^ 2)⁻¹ := by
    calc
      q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
      _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hqt, one_mul]
  have hi : q⁻¹ = t ^ 2 := by rw [hq, inv_inv]
  unfold i1Raw shellMonomial shellCoeff
  simp only [one_ne_zero, ↓reduceIte]
  rw [zpow_sub₀ ht, hi, hq]
  simp only [zpow_ofNat, div_eq_mul_inv]
  ring

/--
@isnad1 id=summable.2h3v.s6.f5a80e32dff0 from=translated src=- shape=77f9d5cc vocab=668390a1
-/
theorem i1_summable_norm_two_geometric (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    Summable (fun n : ℕ × ℕ => ‖C * a ^ n.1 * b ^ n.2‖) := by
  have h := (geometric_norm_summable a ha).mul_norm (geometric_norm_summable b hb)
  simpa only [norm_mul, mul_assoc] using h.mul_left ‖C‖

/--
@isnad1 id=hassum.2h3v.s7.77ddf91f3fa8 from=translated src=- shape=f97860bc vocab=916ef642
-/
theorem i1_hasSum_two_geometric (C a b : ℂ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    HasSum (fun n : ℕ × ℕ => C * a ^ n.1 * b ^ n.2)
      (C * (1 - a)⁻¹ * (1 - b)⁻¹) := by
  have hA := (hasSum_geometric_of_norm_lt_one ha).tsum_eq
  have hB := (hasSum_geometric_of_norm_lt_one hb).tsum_eq
  have hs := (i1_summable_norm_two_geometric C a b ha hb).of_norm
  have he : (∑' n : ℕ × ℕ, C * a ^ n.1 * b ^ n.2) =
      C * (1 - a)⁻¹ * (1 - b)⁻¹ := by
    rw [hs.tsum_prod]
    simp only [tsum_mul_left, hB, tsum_mul_right, hA]
  exact he ▸ hs.hasSum

/-- Source I1 row 1, with integer valuation inequalities.-/
abbrev I1R1Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ -2 * k ≤ j ∧ -k ≤ h}

def i1r1Equiv : (ℕ × ℕ × ℕ) ≃ I1R1Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ) + 1, (b : ℤ) - 2 * (a : ℤ) - 2, (c : ℤ) - (a : ℤ) - 1)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k - 1).toNat, ( j + 2 * k).toNat, ( h + k).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h3v.s7.2b7fdab878b6 from=translated src=- shape=3b5c04d2 vocab=128cca37
-/
@[simp] theorem i1r1Equiv_val (a b c : ℕ) :
    (i1r1Equiv (a,b,c)).val = ((a : ℤ) + 1, (b : ℤ) - 2 * (a : ℤ) - 2, (c : ℤ) - (a : ℤ) - 1) := rfl

/--
@isnad1 id=eq.0h2v.s8.8a09d2947632 from=translated src=- shape=ddd75715 vocab=b5f1f6b1
-/
theorem i1r1_cartan (p : I1R1Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2, p.val.1 - 1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=eq.0h7v.s8.142f32b27ad9 from=translated src=- shape=f9a2a7ef vocab=d0805bb0
-/
theorem i1r1_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r1Equiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U) * t) * (d * T * V * t) ^ n.1 * (t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r1_cartan]
  
  simp only [i1r1Equiv_val]
  have he : 3 * ((a : ℤ) + 1) + 2 * ( (b : ℤ) - 2 * (a : ℤ) - 2) + 2 * ( (c : ℤ) - (a : ℤ) - 1) +
      3 * (2) + 4 * ( ((a : ℤ) + 1) - 1) - 2 = ((a + 2*b + 2*c + 1 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ) + 1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb :  ((a : ℤ) + 1) - 1 = ((a : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.3h6v.s8.ffca03025557 from=translated src=- shape=74a422ca vocab=2b054d98
-/
theorem hasSum_i1r1_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R1Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * t) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r1Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * t) (d * T * V * t) (t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r1_reindexed t d U V T depth n

/--
@isnad1 id=summable.3h6v.s7.b6e52c92ba5d from=translated src=- shape=3b74a337 vocab=0ab1a48a
-/
theorem summable_norm_i1r1_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R1Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r1Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * t) (d * T * V * t) (t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r1_reindexed t d U V T depth n)

/-- Source I1 row 2, with integer valuation inequalities.-/
abbrev I1R2Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ -2 * k ≤ j ∧ h < -k}

def i1r2Equiv : (ℕ × ℕ × ℕ) ≃ I1R2Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ) + 1, (b : ℤ) - 2 * (a : ℤ) - 2, -(a : ℤ) - (c : ℤ) - 2)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k - 1).toNat, ( j + 2 * k).toNat, ( -h - k - 1).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h3v.s7.11d8dba73f9f from=translated src=- shape=e929302f vocab=5c54a08b
-/
@[simp] theorem i1r2Equiv_val (a b c : ℕ) :
    (i1r2Equiv (a,b,c)).val = ((a : ℤ) + 1, (b : ℤ) - 2 * (a : ℤ) - 2, -(a : ℤ) - (c : ℤ) - 2) := rfl

/--
@isnad1 id=eq.0h2v.s9.7d49480d0cca from=translated src=- shape=a5444dbb vocab=9e2e883a
-/
theorem i1r2_cartan (p : I1R2Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (-2*p.val.1-2*p.val.2.2, p.val.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=eq.0h7v.s8.e46ad6327239 from=translated src=- shape=e0238e66 vocab=a67d8772
-/
theorem i1r2_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r2Equiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) * (d * T * V * t) ^ n.1 * (t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r2_cartan]
  
  simp only [i1r2Equiv_val]
  have he : 3 * ((a : ℤ) + 1) + 2 * ( (b : ℤ) - 2 * (a : ℤ) - 2) + 2 * ( -(a : ℤ) - (c : ℤ) - 2) +
      3 * (-2*((a : ℤ) + 1)-2*( -(a : ℤ) - (c : ℤ) - 2)) + 4 * ( ((a : ℤ) + 1)) - 2 = ((a + 2*b + 4*c + 3 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ) + 1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb :  ((a : ℤ) + 1) = ((a+1 : ℕ) : ℤ) := by omega
  have hl : (-2*((a : ℤ) + 1)-2*( -(a : ℤ) - (c : ℤ) - 2)) / 2 = ((c+1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.3h6v.s8.2eb438627d1b from=translated src=- shape=5b0acfde vocab=ae3acb08
-/
theorem hasSum_i1r2_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I1R2Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  apply i1r2Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) (d * T * V * t) (t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => i1r2_reindexed t d U V T depth n

/--
@isnad1 id=summable.3h6v.s7.3233300f8805 from=translated src=- shape=5e4a8909 vocab=ee9c7a04
-/
theorem summable_norm_i1r2_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I1R2Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r2Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) (d * T * V * t) (t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r2_reindexed t d U V T depth n)

/-- Source I1 row 3ae, with integer valuation inequalities.-/
abbrev I1R3AERow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 0}

def i1r3aeEquiv : (ℕ × ℕ × ℕ) ≃ I1R3AERow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-4,-(a : ℤ)-(b : ℤ)-2+(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, ((-j-2*k-2)/2).toNat, (h-j/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h3v.s8.eb41221cc214 from=translated src=- shape=4f080406 vocab=be0d2bc8
-/
@[simp] theorem i1r3aeEquiv_val (a b c : ℕ) :
    (i1r3aeEquiv (a,b,c)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-4,-(a : ℤ)-(b : ℤ)-2+(c : ℤ)) := rfl

/--
@isnad1 id=eq.0h2v.s9.03fd4ec4bfa1 from=translated src=- shape=76a85e15 vocab=22a4e85f
-/
theorem i1r3ae_cartan (p : I1R3AERow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  have hp0 : 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  clear hp
  rw [tableOne, ite_eq_left hp0.1, ite_eq_right (by omega : ¬ -2*k ≤ j),
    ite_eq_right (by omega : ¬ h < k+j)]
  rw [collisionRows, ite_eq_left (by omega : j-1+1 ≤ 2*h)]
  norm_num

/--
@isnad1 id=eq.0h7v.s9.1844d9da7966 from=translated src=- shape=f9c936ed vocab=00fe6362
-/
theorem i1r3ae_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r3aeEquiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r3ae_cartan]
  
  simp only [i1r3aeEquiv_val]
  have he : 3 * ((a : ℤ)+1) + 2 * (-2*(a : ℤ)-2*(b : ℤ)-4) + 2 * (-(a : ℤ)-(b : ℤ)-2+(c : ℤ)) +
      3 * (2) + 4 * (-((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-4)-1) - 2 = ((a+2*b+2*c+3 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ)+1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb : -((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-4)-1 = ((a+2*b+2 : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.3h6v.s9.b821ece49dda from=translated src=- shape=adbca8de vocab=b45e8459
-/
theorem hasSum_i1r3ae_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R3AERow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r3aeEquiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r3ae_reindexed t d U V T depth n

/--
@isnad1 id=summable.3h6v.s8.c4f33f4def49 from=translated src=- shape=60d5abea vocab=676a34ef
-/
theorem summable_norm_i1r3ae_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R3AERow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r3aeEquiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r3ae_reindexed t d U V T depth n)

/-- Source I1 row 3ao, with integer valuation inequalities.-/
abbrev I1R3AORow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 1}

def i1r3aoEquiv : (ℕ × ℕ × ℕ) ≃ I1R3AORow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-1+(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, ((-j-2*k-1)/2).toNat, (h-(j+1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h3v.s8.ba1aeebd7854 from=translated src=- shape=4f080406 vocab=d4875a6c
-/
@[simp] theorem i1r3aoEquiv_val (a b c : ℕ) :
    (i1r3aoEquiv (a,b,c)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-1+(c : ℤ)) := rfl

/--
@isnad1 id=eq.0h2v.s9.bb6f2a64bed7 from=translated src=- shape=76a85e15 vocab=30ab9c46
-/
theorem i1r3ao_cartan (p : I1R3AORow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  have hp0 : 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  clear hp
  rw [tableOne, ite_eq_left hp0.1, ite_eq_right (by omega : ¬ -2*k ≤ j),
    ite_eq_right (by omega : ¬ h < k+j)]
  rw [collisionRows, ite_eq_left (by omega : j-1+1 ≤ 2*h)]
  norm_num

/--
@isnad1 id=eq.0h7v.s8.a98fff87e39b from=translated src=- shape=9dc45b26 vocab=37729b72
-/
theorem i1r3ao_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r3aoEquiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r3ao_cartan]
  
  simp only [i1r3aoEquiv_val]
  have he : 3 * ((a : ℤ)+1) + 2 * (-2*(a : ℤ)-2*(b : ℤ)-3) + 2 * (-(a : ℤ)-(b : ℤ)-1+(c : ℤ)) +
      3 * (2) + 4 * (-((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-3)-1) - 2 = ((a+2*b+2*c+3 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ)+1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb : -((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-3)-1 = ((a+2*b+1 : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.3h6v.s9.4d63989645dd from=translated src=- shape=4a7a1092 vocab=c0f8ca02
-/
theorem hasSum_i1r3ao_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R3AORow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r3aoEquiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r3ao_reindexed t d U V T depth n

/--
@isnad1 id=summable.3h6v.s8.f31ef518fd52 from=translated src=- shape=60d5abea vocab=a0145937
-/
theorem summable_norm_i1r3ao_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R3AORow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r3aoEquiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r3ao_reindexed t d U V T depth n)

/-- Source I1 row 3b, with integer valuation inequalities.-/
abbrev I1R3BRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-1}

def i1r3bEquiv : (ℕ × ℕ) ≃ I1R3BRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-2)), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, ((-j-2*k-1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h2v.s8.6dcb5c5f0b9a from=translated src=- shape=32dd8ccb vocab=6eaa85d1
-/
@[simp] theorem i1r3bEquiv_val (a b : ℕ) :
    (i1r3bEquiv (a,b)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-2) := rfl

/--
@isnad1 id=eq.0h1v.s9.49e07b249a86 from=translated src=- shape=e2b8ce3c vocab=6bc63b47
-/
theorem i1r3b_cartan (p : I1R3BRow)  :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 0 = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=eq.0h6v.s8.d5ffe5dddb33 from=translated src=- shape=07f86665 vocab=81ac61fc
-/
theorem i1r3b_reindexed (t d U V T : ℂ)  
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r3bEquiv n).val 0 = ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  rcases n with ⟨a, b⟩
  unfold i1Raw
  simp only [Nat.cast_zero]
  rw [i1r3b_cartan]
  
  simp only [i1r3bEquiv_val]
  have he : 3 * ((a : ℤ)+1) + 2 * (-2*(a : ℤ)-2*(b : ℤ)-3) + 2 * (-(a : ℤ)-(b : ℤ)-2) +
      3 * (2) + 4 * (-((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-3)-1) - 2 = ((a+2*b+1 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ)+1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb : -((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-3)-1 = ((a+2*b+1 : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.2h5v.s8.9726b23c8e5e from=translated src=- shape=ff66ad03 vocab=4eea8a3c
-/
theorem hasSum_i1r3b_raw (t d U V T : ℂ)  
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I1R3BRow => i1Raw t d U V T p.val 0)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹) := by
  apply i1r3bEquiv.hasSum_iff.mp
  convert i1_hasSum_two_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) (d * T * V * t) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => i1r3b_reindexed t d U V T n

/--
@isnad1 id=summable.2h5v.s8.0f329e12294f from=translated src=- shape=b864f64e vocab=e4167c7d
-/
theorem summable_norm_i1r3b_raw (t d U V T : ℂ)  
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I1R3BRow => ‖i1Raw t d U V T p.val 0‖) := by
  apply i1r3bEquiv.summable_iff.mp
  convert i1_summable_norm_two_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) (d * T * V * t) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => congrArg norm
    (i1r3b_reindexed t d U V T n)

/-- Source I1 row 3c, with integer valuation inequalities.-/
abbrev I1R3CRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-1}

def i1r3cEquiv : (ℕ × ℕ) ≃ I1R3CRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-2)), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, ((-j-2*k-1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h2v.s8.ee65e4180d50 from=translated src=- shape=32dd8ccb vocab=e2e43a4d
-/
@[simp] theorem i1r3cEquiv_val (a b : ℕ) :
    (i1r3cEquiv (a,b)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-2) := rfl

/--
@isnad1 id=eq.1h2v.s9.70ae4b9b8e80 from=translated src=- shape=30b55519 vocab=cbcba1e0
-/
theorem i1r3c_cartan (p : I1R3CRow) (depth : ℕ) (hdepth : 1 ≤ depth) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (0,-p.val.1-p.val.2.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=eq.2h7v.s8.2840760086f9 from=translated src=- shape=056ccb04 vocab=ab40e4a8
-/
theorem i1r3c_reindexed (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r3cEquiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  rcases n with ⟨a, b⟩
  unfold i1Raw
  
  rw [i1r3c_cartan]
  all_goals try omega
  simp only [i1r3cEquiv_val]
  have he : 3 * ((a : ℤ)+1) + 2 * (-2*(a : ℤ)-2*(b : ℤ)-3) + 2 * (-(a : ℤ)-(b : ℤ)-2) +
      3 * (0) + 4 * (-((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-3)) - 2 = ((a+2*b : ℕ) : ℤ) - 1 := by omega
  have hk : (a : ℤ)+1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb : -((a : ℤ)+1)-(-2*(a : ℤ)-2*(b : ℤ)-3) = ((a+2*b+2 : ℕ) : ℤ) := by omega
  have hl : (0) / 2 = ((0 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  rw [zpow_sub₀ ht]
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.4h6v.s9.c5d2fcf64225 from=translated src=- shape=885607c2 vocab=4b47533f
-/
theorem hasSum_i1r3c_raw (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I1R3CRow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹) := by
  apply i1r3cEquiv.hasSum_iff.mp
  convert i1_hasSum_two_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) (d * T * V * t) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => i1r3c_reindexed t d U V T ht depth hdepth n

/--
@isnad1 id=summable.4h6v.s8.82fb322e96c3 from=translated src=- shape=c2902b20 vocab=4b6f0d7c
-/
theorem summable_norm_i1r3c_raw (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I1R3CRow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r3cEquiv.summable_iff.mp
  convert i1_summable_norm_two_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) (d * T * V * t) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => congrArg norm
    (i1r3c_reindexed t d U V T ht depth hdepth n)

/-- Source I1 row 4, with integer valuation inequalities.-/
abbrev I1R4Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h ≤ j-2}

def i1r4Equiv : (ℕ × ℕ × ℕ) ≃ I1R4Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4,-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, (h-k-j).toNat, (j-2*h-2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h3v.s8.a2c25fcf71fd from=translated src=- shape=dc1ffd96 vocab=9b1cd8b2
-/
@[simp] theorem i1r4Equiv_val (a b c : ℕ) :
    (i1r4Equiv (a,b,c)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4,-(a : ℤ)-(b : ℤ)-(c : ℤ)-3) := rfl

/--
@isnad1 id=eq.0h2v.s10.c206b07f19b4 from=translated src=- shape=5b6988d5 vocab=7a8a6739
-/
theorem i1r4_cartan (p : I1R4Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2*p.val.2.1-4*p.val.2.2,2*p.val.2.2-2*p.val.2.1-p.val.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=eq.0h7v.s9.145534579749 from=translated src=- shape=c57d27f5 vocab=c16d1372
-/
theorem i1r4_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r4Equiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (T * U * t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r4_cartan]
  
  simp only [i1r4Equiv_val]
  have he : 3 * ((a : ℤ)+1) + 2 * (-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4) + 2 * (-(a : ℤ)-(b : ℤ)-(c : ℤ)-3) +
      3 * (2*(-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4)-4*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)) + 4 * (2*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)-2*(-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4)-((a : ℤ)+1)) - 2 = ((a+2*b+2*c+3 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ)+1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb : 2*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)-2*(-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4)-((a : ℤ)+1) = ((a+2*b+1 : ℕ) : ℤ) := by omega
  have hl : (2*(-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4)-4*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)) / 2 = ((c+2 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.3h6v.s9.bc01d43490fd from=translated src=- shape=666b6c5d vocab=7ad2543f
-/
theorem hasSum_i1r4_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 2‖ < 1) :
    HasSum (fun p : I1R4Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) := by
  apply i1r4Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r4_reindexed t d U V T depth n

/--
@isnad1 id=summable.3h6v.s8.50c6916a40ee from=translated src=- shape=f4b55b1e vocab=d43b0507
-/
theorem summable_norm_i1r4_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 2‖ < 1) :
    Summable (fun p : I1R4Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r4Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) (d * T * V * t) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r4_reindexed t d U V T depth n)

/-- Source I1 row 5, with integer valuation inequalities.-/
abbrev I1R5Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ h < k+j}

def i1r5Equiv : (ℕ × ℕ × ℕ) ≃ I1R5Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, (-j-2*k-1).toNat, (k+j-h-1).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h3v.s8.1087a1985bca from=translated src=- shape=a455d63f vocab=934f07fa
-/
@[simp] theorem i1r5Equiv_val (a b c : ℕ) :
    (i1r5Equiv (a,b,c)).val = ((a : ℤ)+1,-2*(a : ℤ)-(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-(c : ℤ)-3) := rfl

/--
@isnad1 id=eq.0h2v.s9.e533b195bc8f from=translated src=- shape=1e0acbbb vocab=4d06bd57
-/
theorem i1r5_cartan (p : I1R5Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (-2*p.val.1-2*p.val.2.2,p.val.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=eq.0h7v.s8.094434d38c8c from=translated src=- shape=bed4d7a0 vocab=83d1e52e
-/
theorem i1r5_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r5Equiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) * (d * T * V * t) ^ n.1 * (T * U * t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r5_cartan]
  
  simp only [i1r5Equiv_val]
  have he : 3 * ((a : ℤ)+1) + 2 * (-2*(a : ℤ)-(b : ℤ)-3) + 2 * (-(a : ℤ)-(b : ℤ)-(c : ℤ)-3) +
      3 * (-2*((a : ℤ)+1)-2*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)) + 4 * (((a : ℤ)+1)) - 2 = ((a+2*b+4*c+5 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ)+1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb : ((a : ℤ)+1) = ((a+1 : ℕ) : ℤ) := by omega
  have hl : (-2*((a : ℤ)+1)-2*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)) / 2 = ((b+c+2 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.3h6v.s9.7d5763073e98 from=translated src=- shape=58cde2a7 vocab=4bb226e8
-/
theorem hasSum_i1r5_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖T * U * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I1R5Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) * (1 - d * T * V * t)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  apply i1r5Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) (d * T * V * t) (T * U * t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => i1r5_reindexed t d U V T depth n

/--
@isnad1 id=summable.3h6v.s8.f20b502a0975 from=translated src=- shape=1a63e914 vocab=7ae5e387
-/
theorem summable_norm_i1r5_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖d * T * V * t‖ < 1)
    (h1 : ‖T * U * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I1R5Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r5Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) (d * T * V * t) (T * U * t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r5_reindexed t d U V T depth n)

/-- Source I1 row 6a, with integer valuation inequalities.-/
abbrev I1R6ARow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k = 0 ∧ 0 ≤ j ∧ 0 ≤ h}

def i1r6aEquiv : (ℕ × ℕ) ≃ I1R6ARow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact (0,(a : ℤ),(b : ℤ))), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((j).toNat, (h).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h2v.s7.27ad391554bb from=translated src=- shape=ac49e12b vocab=5988923d
-/
@[simp] theorem i1r6aEquiv_val (a b : ℕ) :
    (i1r6aEquiv (a,b)).val = (0,(a : ℤ),(b : ℤ)) := rfl

/--
@isnad1 id=eq.0h2v.s8.ed594dc85f82 from=translated src=- shape=d63fed27 vocab=2e9c4b9d
-/
theorem i1r6a_cartan (p : I1R6ARow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (0,1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=eq.0h7v.s8.0e41593fda09 from=translated src=- shape=0c157ead vocab=8c01262d
-/
theorem i1r6a_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r6aEquiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (t ^ 2) ^ n.1 * (t ^ 2) ^ n.2 := by
  rcases n with ⟨a, b⟩
  unfold i1Raw
  
  rw [i1r6a_cartan]
  
  simp only [i1r6aEquiv_val]
  have he : 3 * (0) + 2 * ((a : ℤ)) + 2 * ((b : ℤ)) +
      3 * (0) + 4 * (1) - 2 = ((2*a+2*b+2 : ℕ) : ℤ) := by omega
  have hk : 0 = ((0 : ℕ) : ℤ) := by omega
  have hb : 1 = ((1 : ℕ) : ℤ) := by omega
  have hl : (0) / 2 = ((0 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.2h6v.s8.f06da3f8f6d5 from=translated src=- shape=90a6947b vocab=54481eaa
-/
theorem hasSum_i1r6a_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖t ^ 2‖ < 1)
    (h1 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R6ARow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r6aEquiv.hasSum_iff.mp
  convert i1_hasSum_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * V) * t^2) (t ^ 2) (t ^ 2)
    h0 h1 using 1
  exact funext fun n => i1r6a_reindexed t d U V T depth n

/--
@isnad1 id=summable.2h6v.s7.a372bbceef30 from=translated src=- shape=fb2be240 vocab=3ffc9936
-/
theorem summable_norm_i1r6a_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖t ^ 2‖ < 1)
    (h1 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R6ARow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r6aEquiv.summable_iff.mp
  convert i1_summable_norm_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * V) * t^2) (t ^ 2) (t ^ 2)
    h0 h1 using 1
  exact funext fun n => congrArg norm
    (i1r6a_reindexed t d U V T depth n)

/-- Source I1 row 6b, with integer valuation inequalities.-/
abbrev I1R6BRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ -1 ∧ 0 ≤ j ∧ 0 ≤ h}

def i1r6bEquiv : (ℕ × ℕ × ℕ) ≃ I1R6BRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ)-1,(b : ℤ),(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k-1).toNat, (j).toNat, (h).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h3v.s7.c9eeb46153b6 from=translated src=- shape=c87a23e4 vocab=aac36f3f
-/
@[simp] theorem i1r6bEquiv_val (a b c : ℕ) :
    (i1r6bEquiv (a,b,c)).val = (-(a : ℤ)-1,(b : ℤ),(c : ℤ)) := rfl

/--
@isnad1 id=eq.0h2v.s8.f19d0ec307ad from=translated src=- shape=bac0f9c0 vocab=1fb85a50
-/
theorem i1r6b_cartan (p : I1R6BRow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2,-p.val.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=eq.0h7v.s8.3ca1f67d738c from=translated src=- shape=9f5681e8 vocab=3a76ba70
-/
theorem i1r6b_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r6bEquiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U) * t / d) * (T * V * t / d) ^ n.1 * (t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r6b_cartan]
  
  simp only [i1r6bEquiv_val]
  have he : 3 * (-(a : ℤ)-1) + 2 * ((b : ℤ)) + 2 * ((c : ℤ)) +
      3 * (2) + 4 * (-(-(a : ℤ)-1)-1) - 2 = ((a+2*b+2*c+1 : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ)-1 = -(((a+1) : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ)-1)-1 = ((a : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.3h6v.s8.bed49e6cdf43 from=translated src=- shape=ee3a5d47 vocab=699f9169
-/
theorem hasSum_i1r6b_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R6BRow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * U) * t / d) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r6bEquiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * t / d) (T * V * t / d) (t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r6b_reindexed t d U V T depth n

/--
@isnad1 id=summable.3h6v.s7.55707082a2f3 from=translated src=- shape=aab1a972 vocab=91ccecc6
-/
theorem summable_norm_i1r6b_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R6BRow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r6bEquiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * t / d) (T * V * t / d) (t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r6b_reindexed t d U V T depth n)

/-- Source I1 row 7, with integer valuation inequalities.-/
abbrev I1R7Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ 0 ≤ j ∧ h < 0}

def i1r7Equiv : (ℕ × ℕ × ℕ) ≃ I1R7Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),(b : ℤ),-(c : ℤ)-1)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, (j).toNat, (-h-1).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h3v.s7.13361de34a44 from=translated src=- shape=f96d2d62 vocab=79b56df7
-/
@[simp] theorem i1r7Equiv_val (a b c : ℕ) :
    (i1r7Equiv (a,b,c)).val = (-(a : ℤ),(b : ℤ),-(c : ℤ)-1) := rfl

/--
@isnad1 id=eq.0h2v.s8.3b522db21afa from=translated src=- shape=791d7e5d vocab=32ed21fb
-/
theorem i1r7_cartan (p : I1R7Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (-2*p.val.2.2,-p.val.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=eq.0h7v.s8.850e06eae019 from=translated src=- shape=ca729312 vocab=f259bc39
-/
theorem i1r7_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r7Equiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (T * V * t / d) ^ n.1 * (t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r7_cartan]
  
  simp only [i1r7Equiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * ((b : ℤ)) + 2 * (-(c : ℤ)-1) +
      3 * (-2*(-(c : ℤ)-1)) + 4 * (-(-(a : ℤ))) - 2 = ((a+2*b+4*c+2 : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ)) = ((a : ℕ) : ℤ) := by omega
  have hl : (-2*(-(c : ℤ)-1)) / 2 = ((c+1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.3h6v.s8.1c6816eb3e92 from=translated src=- shape=5031da92 vocab=ae663190
-/
theorem hasSum_i1r7_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I1R7Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  apply i1r7Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) (T * V * t / d) (t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => i1r7_reindexed t d U V T depth n

/--
@isnad1 id=summable.3h6v.s7.871ba7e06038 from=translated src=- shape=3565cb86 vocab=fe0b6c8b
-/
theorem summable_norm_i1r7_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I1R7Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r7Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) (T * V * t / d) (t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r7_reindexed t d U V T depth n)

/-- Source I1 row 8ae, with integer valuation inequalities.-/
abbrev I1R8AERow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 0}

def i1r8aeEquiv : (ℕ × ℕ × ℕ) ≃ I1R8AERow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),-2*(b : ℤ)-2,-(b : ℤ)-1+(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, ((-j-2)/2).toNat, (h-j/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h3v.s7.316a838b84b6 from=translated src=- shape=d4db272d vocab=0c8108f2
-/
@[simp] theorem i1r8aeEquiv_val (a b c : ℕ) :
    (i1r8aeEquiv (a,b,c)).val = (-(a : ℤ),-2*(b : ℤ)-2,-(b : ℤ)-1+(c : ℤ)) := rfl

/--
@isnad1 id=eq.0h2v.s9.53aac48b9342 from=translated src=- shape=b1054096 vocab=ce77f826
-/
theorem i1r8ae_cartan (p : I1R8AERow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  have hp0 : k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  clear hp
  rw [tableOne, ite_eq_right (by omega : ¬ 1 ≤ k), ite_eq_right (by omega : ¬ 0 ≤ j),
    ite_eq_right (by omega : ¬ h < j)]
  rw [collisionRows, ite_eq_left (by omega : j-1+1 ≤ 2*h)]
  norm_num

/--
@isnad1 id=eq.0h7v.s8.de8a396f0fa8 from=translated src=- shape=6bea0793 vocab=146c468f
-/
theorem i1r8ae_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r8aeEquiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r8ae_cartan]
  
  simp only [i1r8aeEquiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * (-2*(b : ℤ)-2) + 2 * (-(b : ℤ)-1+(c : ℤ)) +
      3 * (2) + 4 * (-(-(a : ℤ))-(-2*(b : ℤ)-2)-1) - 2 = ((a+2*b+2*c+2 : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ))-(-2*(b : ℤ)-2)-1 = ((a+2*b+1 : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.3h6v.s9.901b297b1ebe from=translated src=- shape=9c8bc332 vocab=f137c7ac
-/
theorem hasSum_i1r8ae_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R8AERow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r8aeEquiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r8ae_reindexed t d U V T depth n

/--
@isnad1 id=summable.3h6v.s8.66b4237e544a from=translated src=- shape=78f3b0af vocab=b8cf2d0f
-/
theorem summable_norm_i1r8ae_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R8AERow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r8aeEquiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r8ae_reindexed t d U V T depth n)

/-- Source I1 row 8ao, with integer valuation inequalities.-/
abbrev I1R8AORow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 1}

def i1r8aoEquiv : (ℕ × ℕ × ℕ) ≃ I1R8AORow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)+(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, ((-j-1)/2).toNat, (h-(j+1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h3v.s7.b27266dfe3a2 from=translated src=- shape=14dabb47 vocab=15982f1b
-/
@[simp] theorem i1r8aoEquiv_val (a b c : ℕ) :
    (i1r8aoEquiv (a,b,c)).val = (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)+(c : ℤ)) := rfl

/--
@isnad1 id=eq.0h2v.s9.d5fa58bd5bd0 from=translated src=- shape=b1054096 vocab=50896b8b
-/
theorem i1r8ao_cartan (p : I1R8AORow) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  have hp0 : k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h := ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  clear hp
  rw [tableOne, ite_eq_right (by omega : ¬ 1 ≤ k), ite_eq_right (by omega : ¬ 0 ≤ j),
    ite_eq_right (by omega : ¬ h < j)]
  rw [collisionRows, ite_eq_left (by omega : j-1+1 ≤ 2*h)]
  norm_num

/--
@isnad1 id=eq.0h7v.s8.49ecfcff5185 from=translated src=- shape=0c5a8a8c vocab=910f62a9
-/
theorem i1r8ao_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r8aoEquiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r8ao_cartan]
  
  simp only [i1r8aoEquiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * (-2*(b : ℤ)-1) + 2 * (-(b : ℤ)+(c : ℤ)) +
      3 * (2) + 4 * (-(-(a : ℤ))-(-2*(b : ℤ)-1)-1) - 2 = ((a+2*b+2*c+2 : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ))-(-2*(b : ℤ)-1)-1 = ((a+2*b : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.3h6v.s9.995d90d31e73 from=translated src=- shape=7335ce84 vocab=038ff878
-/
theorem hasSum_i1r8ao_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    HasSum (fun p : I1R8AORow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  apply i1r8aoEquiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r8ao_reindexed t d U V T depth n

/--
@isnad1 id=summable.3h6v.s8.0039e541adad from=translated src=- shape=78f3b0af vocab=b2ae00d9
-/
theorem summable_norm_i1r8ao_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖t ^ 2‖ < 1) :
    Summable (fun p : I1R8AORow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r8aoEquiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r8ao_reindexed t d U V T depth n)

/-- Source I1 row 8b, with integer valuation inequalities.-/
abbrev I1R8BRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h = j-1}

def i1r8bEquiv : (ℕ × ℕ) ≃ I1R8BRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)-1)), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, ((-j-1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h2v.s7.839c7faccce5 from=translated src=- shape=c84c483c vocab=f11e13e0
-/
@[simp] theorem i1r8bEquiv_val (a b : ℕ) :
    (i1r8bEquiv (a,b)).val = (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)-1) := rfl

/--
@isnad1 id=eq.0h1v.s9.04d68e051d04 from=translated src=- shape=148bb98d vocab=7a98b54a
-/
theorem i1r8b_cartan (p : I1R8BRow)  :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 0 = (2,-p.val.1-p.val.2.1-1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=eq.0h6v.s8.b05313c4583a from=translated src=- shape=2fb5214f vocab=bfd70667
-/
theorem i1r8b_reindexed (t d U V T : ℂ)  
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r8bEquiv n).val 0 = ((1 - t ^ 2) ^ 3 * (T * U)) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  rcases n with ⟨a, b⟩
  unfold i1Raw
  simp only [Nat.cast_zero]
  rw [i1r8b_cartan]
  
  simp only [i1r8bEquiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * (-2*(b : ℤ)-1) + 2 * (-(b : ℤ)-1) +
      3 * (2) + 4 * (-(-(a : ℤ))-(-2*(b : ℤ)-1)-1) - 2 = ((a+2*b : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ))-(-2*(b : ℤ)-1)-1 = ((a+2*b : ℕ) : ℤ) := by omega
  have hl : (2) / 2 = ((1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.2h5v.s8.e6531a763816 from=translated src=- shape=1cac08b8 vocab=12e48d05
-/
theorem hasSum_i1r8b_raw (t d U V T : ℂ)  
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I1R8BRow => i1Raw t d U V T p.val 0)
      (((1 - t ^ 2) ^ 3 * (T * U)) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹) := by
  apply i1r8bEquiv.hasSum_iff.mp
  convert i1_hasSum_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)) (T * V * t / d) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => i1r8b_reindexed t d U V T n

/--
@isnad1 id=summable.2h5v.s7.947de45006e6 from=translated src=- shape=0acdbeb4 vocab=a0408e2a
-/
theorem summable_norm_i1r8b_raw (t d U V T : ℂ)  
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I1R8BRow => ‖i1Raw t d U V T p.val 0‖) := by
  apply i1r8bEquiv.summable_iff.mp
  convert i1_summable_norm_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)) (T * V * t / d) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => congrArg norm
    (i1r8b_reindexed t d U V T n)

/-- Source I1 row 8c, with integer valuation inequalities.-/
abbrev I1R8CRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h = j-1}

def i1r8cEquiv : (ℕ × ℕ) ≃ I1R8CRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)-1)), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, ((-j-1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h2v.s7.090169fe93ad from=translated src=- shape=c84c483c vocab=0b504f84
-/
@[simp] theorem i1r8cEquiv_val (a b : ℕ) :
    (i1r8cEquiv (a,b)).val = (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)-1) := rfl

/--
@isnad1 id=eq.1h2v.s9.ba0e6373bdf1 from=translated src=- shape=69e32d88 vocab=0f7b4317
-/
theorem i1r8c_cartan (p : I1R8CRow) (depth : ℕ) (hdepth : 1 ≤ depth) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (0,-p.val.1-p.val.2.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=eq.2h7v.s8.6dd4d42d712d from=translated src=- shape=477fea33 vocab=e86fa4df
-/
theorem i1r8c_reindexed (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r8cEquiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * V) / t^2) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2 := by
  rcases n with ⟨a, b⟩
  unfold i1Raw
  
  rw [i1r8c_cartan]
  all_goals try omega
  simp only [i1r8cEquiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * (-2*(b : ℤ)-1) + 2 * (-(b : ℤ)-1) +
      3 * (0) + 4 * (-(-(a : ℤ))-(-2*(b : ℤ)-1)) - 2 = ((a+2*b : ℕ) : ℤ) - 2 := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ))-(-2*(b : ℤ)-1) = ((a+2*b+1 : ℕ) : ℤ) := by omega
  have hl : (0) / 2 = ((0 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  rw [zpow_sub₀ ht]
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.4h6v.s8.436dab5394ea from=translated src=- shape=1d383918 vocab=44973a5e
-/
theorem hasSum_i1r8c_raw (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    HasSum (fun p : I1R8CRow => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * V) / t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹) := by
  apply i1r8cEquiv.hasSum_iff.mp
  convert i1_hasSum_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * V) / t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => i1r8c_reindexed t d U V T ht depth hdepth n

/--
@isnad1 id=summable.4h6v.s8.d8f785bbf28e from=translated src=- shape=217926bc vocab=ca7b6db0
-/
theorem summable_norm_i1r8c_raw (t d U V T : ℂ) (ht : t ≠ 0) (depth : ℕ) (hdepth : 1 ≤ depth)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun p : I1R8CRow => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r8cEquiv.summable_iff.mp
  convert i1_summable_norm_two_geometric
    ((1 - t ^ 2) ^ 3 * (T * V) / t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2)
    h0 h1 using 1
  exact funext fun n => congrArg norm
    (i1r8c_reindexed t d U V T ht depth hdepth n)

/-- Source I1 row 9, with integer valuation inequalities.-/
abbrev I1R9Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h ≤ j-2}

def i1r9Equiv : (ℕ × ℕ × ℕ) ≃ I1R9Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),-2*(b : ℤ)-(c : ℤ)-2,-(b : ℤ)-(c : ℤ)-2)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, (h-j).toNat, (j-2*h-2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h3v.s7.eaee011983ee from=translated src=- shape=d53cf102 vocab=557590d5
-/
@[simp] theorem i1r9Equiv_val (a b c : ℕ) :
    (i1r9Equiv (a,b,c)).val = (-(a : ℤ),-2*(b : ℤ)-(c : ℤ)-2,-(b : ℤ)-(c : ℤ)-2) := rfl

/--
@isnad1 id=eq.0h2v.s9.c3efa136eabe from=translated src=- shape=cd645e0d vocab=f242c483
-/
theorem i1r9_cartan (p : I1R9Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (2*p.val.2.1-4*p.val.2.2,2*p.val.2.2-2*p.val.2.1-p.val.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=eq.0h7v.s8.226948704fa6 from=translated src=- shape=b3823ebb vocab=c88b1c38
-/
theorem i1r9_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r9Equiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) * (T * V * t / d) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (T * U * t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r9_cartan]
  
  simp only [i1r9Equiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * (-2*(b : ℤ)-(c : ℤ)-2) + 2 * (-(b : ℤ)-(c : ℤ)-2) +
      3 * (2*(-2*(b : ℤ)-(c : ℤ)-2)-4*(-(b : ℤ)-(c : ℤ)-2)) + 4 * (2*(-(b : ℤ)-(c : ℤ)-2)-2*(-2*(b : ℤ)-(c : ℤ)-2)-(-(a : ℤ))) - 2 = ((a+2*b+2*c+2 : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : 2*(-(b : ℤ)-(c : ℤ)-2)-2*(-2*(b : ℤ)-(c : ℤ)-2)-(-(a : ℤ)) = ((a+2*b : ℕ) : ℤ) := by omega
  have hl : (2*(-2*(b : ℤ)-(c : ℤ)-2)-4*(-(b : ℤ)-(c : ℤ)-2)) / 2 = ((c+2 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.3h6v.s9.76da1d40fb46 from=translated src=- shape=6a67de95 vocab=c5dd9f0b
-/
theorem hasSum_i1r9_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 2‖ < 1) :
    HasSum (fun p : I1R9Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) := by
  apply i1r9Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => i1r9_reindexed t d U V T depth n

/--
@isnad1 id=summable.3h6v.s8.8ff7f50b11df from=translated src=- shape=77e9f670 vocab=f484cd01
-/
theorem summable_norm_i1r9_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 2‖ < 1) :
    Summable (fun p : I1R9Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r9Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) (T * V * t / d) ((T * V) ^ 2 * t ^ 2) (T * U * t ^ 2)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r9_reindexed t d U V T depth n)

/-- Source I1 row 10, with integer valuation inequalities.-/
abbrev I1R10Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ h < j}

def i1r10Equiv : (ℕ × ℕ × ℕ) ≃ I1R10Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),-(b : ℤ)-1,-(b : ℤ)-(c : ℤ)-2)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, (-j-1).toNat, (j-h-1).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega

/--
@isnad1 id=eq.0h3v.s7.05618ca3cfce from=translated src=- shape=03d1b52f vocab=5bc76683
-/
@[simp] theorem i1r10Equiv_val (a b c : ℕ) :
    (i1r10Equiv (a,b,c)).val = (-(a : ℤ),-(b : ℤ)-1,-(b : ℤ)-(c : ℤ)-2) := rfl

/--
@isnad1 id=eq.0h2v.s8.4b18442bd633 from=translated src=- shape=033f5fc5 vocab=66c0eecf
-/
theorem i1r10_cartan (p : I1R10Row) (depth : ℕ) :
    cartanIndices 1 p.val.1 p.val.2.1 p.val.2.2 depth = (-2*p.val.2.2,-p.val.1) := by
  rw [← tableOne_correct _ _ _ _ (by omega)]
  rcases p with ⟨⟨k,j,h⟩,hp⟩
  dsimp at hp ⊢
  
  unfold tableOne collisionRows
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=eq.0h7v.s8.e1d3e67c9da5 from=translated src=- shape=efdcca21 vocab=a3da2fd2
-/
theorem i1r10_reindexed (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r10Equiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) * (T * V * t / d) ^ n.1 * (T * U * t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r10_cartan]
  
  simp only [i1r10Equiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * (-(b : ℤ)-1) + 2 * (-(b : ℤ)-(c : ℤ)-2) +
      3 * (-2*(-(b : ℤ)-(c : ℤ)-2)) + 4 * (-(-(a : ℤ))) - 2 = ((a+2*b+4*c+4 : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ)) = ((a : ℕ) : ℤ) := by omega
  have hl : (-2*(-(b : ℤ)-(c : ℤ)-2)) / 2 = ((b+c+2 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring

/--
@isnad1 id=hassum.3h6v.s9.cf8e46994f6f from=translated src=- shape=62b27904 vocab=2df25820
-/
theorem hasSum_i1r10_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖T * U * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    HasSum (fun p : I1R10Row => i1Raw t d U V T p.val depth)
      (((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) * (1 - T * V * t / d)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  apply i1r10Equiv.hasSum_iff.mp
  convert hasSum_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) (T * V * t / d) (T * U * t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => i1r10_reindexed t d U V T depth n

/--
@isnad1 id=summable.3h6v.s7.1ff74d5041d5 from=translated src=- shape=f888ed16 vocab=2a62a981
-/
theorem summable_norm_i1r10_raw (t d U V T : ℂ)  (depth : ℕ)
    (h0 : ‖T * V * t / d‖ < 1)
    (h1 : ‖T * U * t ^ 2‖ < 1)
    (h2 : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : I1R10Row => ‖i1Raw t d U V T p.val depth‖) := by
  apply i1r10Equiv.summable_iff.mp
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) (T * V * t / d) (T * U * t ^ 2) (T * U * t ^ 4)
    h0 h1 h2 using 1
  exact funext fun n => congrArg norm
    (i1r10_reindexed t d U V T depth n)

end FourierJacobi.Analysis
