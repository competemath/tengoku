import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Nat_MacaulayPow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add

set_option autoImplicit false

namespace GreenNum

def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)

def rem (d a : ℕ) : ℕ := a - (top d a).choose (d + 1)

/--
@isnad1 id=eq.0h1v.s4.4c1971dcb6e5 from=translated src=- shape=fe2c2146 vocab=9e4fbcdb
-/
theorem macaulayPow_zero (a : ℕ) : Nat.macaulayPow 0 a = 0 := by simp [Nat.macaulayPow]

/--
@isnad1 id=eq.0h2v.s5.48e9cd68fe59 from=translated src=- shape=030f4f4e vocab=c31588db
-/
theorem macaulayPow_succ (d a : ℕ) :
    Nat.macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) + Nat.macaulayPow d (rem d a) := by
  rw [Nat.macaulayPow]; rfl

/--
@isnad1 id=le.0h2v.s4.07ec6f5cf2c6 from=translated src=- shape=d2ff0e15 vocab=2297b6f3
-/
theorem sub_le_choose (d : ℕ) : ∀ k : ℕ, k - d ≤ k.choose (d + 1)
  | 0 => by simp
  | k + 1 => by
      rw [Nat.choose_succ_succ']
      have ih := sub_le_choose d k
      rcases lt_or_ge k d with h | h
      · have : k + 1 - d = 0 := by omega
        omega
      · have hpos : 1 ≤ k.choose d := Nat.choose_pos h
        omega

/--
@isnad1 id=le.0h2v.s4.194c8f5da9ae from=translated src=- shape=d5c96991 vocab=a2356f2e
-/
theorem choose_top_le (d a : ℕ) : (top d a).choose (d + 1) ≤ a :=
  Nat.findGreatest_spec (P := fun k => k.choose (d + 1) ≤ a) (Nat.zero_le _) (by simp)

/--
@isnad1 id=lt.1h3v.s5.76ef89ec4362 from=translated src=- shape=daa6bc3d vocab=74d8bfdd
-/
theorem lt_choose_of_top_lt (d a : ℕ) {k : ℕ} (hk : top d a < k) : a < k.choose (d + 1) := by
  rcases le_or_gt k (a + d + 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun k => k.choose (d + 1) ≤ a) hk h
    simpa using this
  · have := sub_le_choose d k
    omega

/--
@isnad1 id=lt.0h2v.s5.71bcf58981a5 from=translated src=- shape=cb038863 vocab=74d8bfdd
-/
theorem lt_choose_top_succ (d a : ℕ) : a < (top d a + 1).choose (d + 1) :=
  lt_choose_of_top_lt d a (Nat.lt_succ_self _)

/--
@isnad1 id=eq.2h3v.s6.5bd9b3c35462 from=translated src=- shape=6c07a21a vocab=0d26edaa
-/
theorem top_eq_of (d a k : ℕ) (h₁ : k.choose (d + 1) ≤ a) (h₂ : a < (k + 1).choose (d + 1)) :
    top d a = k := by
  apply le_antisymm
  · by_contra h
    push Not at h
    have : (k + 1).choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h
    have := choose_top_le d a
    omega
  · by_contra h
    push Not at h
    have := lt_choose_of_top_lt d a h
    omega

/--
@isnad1 id=le.1h3v.s5.9d7ad144796b from=translated src=- shape=9e65ee99 vocab=a2356f2e
-/
theorem le_top_of_choose_le (d a k : ℕ) (h : k.choose (d + 1) ≤ a) : k ≤ top d a := by
  by_contra h'
  push Not at h'
  have := lt_choose_of_top_lt d a h'
  omega

/--
@isnad1 id=lt.1h3v.s5.1877fa5dd548 from=translated src=- shape=f3b3f3dd vocab=74d8bfdd
-/
theorem top_lt_of_lt_choose (d a k : ℕ) (h : a < k.choose (d + 1)) : top d a < k := by
  by_contra h'
  push Not at h'
  have : k.choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h'
  have := choose_top_le d a
  omega

/--
@isnad1 id=le.0h2v.s3.fc3621fe56f3 from=translated src=- shape=70252ff3 vocab=4734f7e5
-/
theorem d_le_top (d a : ℕ) : d ≤ top d a := le_top_of_choose_le d a d (by simp)

/--
@isnad1 id=eq.0h1v.s3.21ed13b1210b from=translated src=- shape=1fa26838 vocab=09da956a
-/
theorem top_zero_right (d : ℕ) : top d 0 = d := top_eq_of d 0 d (by simp) (by simp)

/--
@isnad1 id=lt.1h2v.s4.5611d24fbefc from=translated src=- shape=9030f010 vocab=cf4cc731
-/
theorem d_lt_top_of_pos (d a : ℕ) (ha : 0 < a) : d < top d a := by
  have := le_top_of_choose_le d a (d + 1) (by simp; omega)
  omega

/--
@isnad1 id=eq.0h1v.s3.ed805f6fa0d7 from=translated src=- shape=a60e91e3 vocab=09da956a
-/
theorem top_zero_left (a : ℕ) : top 0 a = a := top_eq_of 0 a a (by simp) (by simp)

/--
@isnad1 id=eq.0h1v.s4.b50fa3aed1ea from=translated src=- shape=fe2c2146 vocab=d7c67e9d
-/
theorem rem_zero_left (a : ℕ) : rem 0 a = 0 := by simp [rem, top_zero_left]

/--
@isnad1 id=eq.0h1v.s4.ff755bcdd8e8 from=translated src=- shape=1d838610 vocab=d7c67e9d
-/
theorem rem_zero_right (d : ℕ) : rem d 0 = 0 := by simp [rem]

/--
@isnad1 id=eq.0h2v.s5.9581dfca6000 from=translated src=- shape=98a64286 vocab=2e58dbc6
-/
theorem rem_add_choose (d a : ℕ) : rem d a + (top d a).choose (d + 1) = a := by
  unfold rem; have := choose_top_le d a; omega

/--
@isnad1 id=lt.0h2v.s3.59a732d9fcd6 from=translated src=- shape=167e73b6 vocab=1a909845
-/
theorem rem_lt (d a : ℕ) : rem d a < (top d a).choose d := by
  have h := lt_choose_top_succ d a
  rw [Nat.choose_succ_succ'] at h
  unfold rem; have := choose_top_le d a; omega

/--
@isnad1 id=lt.1h3v.s5.cc4e447355a4 from=translated src=- shape=c053cf03 vocab=bf0e55b6
-/
theorem macaulayPow_lt_choose : ∀ (d m r : ℕ), r < m.choose d →
    Nat.macaulayPow d r < (m + 1).choose (d + 1)
  | 0, m, r, _ => by simp [macaulayPow_zero]
  | d + 1, m, r, h => by
      rw [macaulayPow_succ]
      show _ < (m + 1).choose (d + 2)
      have hK : top d r < m := top_lt_of_lt_choose d r m h
      have hrem : Nat.macaulayPow d (rem d r) < (top d r + 1).choose (d + 1) :=
        macaulayPow_lt_choose d (top d r) (rem d r) (rem_lt d r)
      have h1 : (top d r + 1).choose (d + 2) + (top d r + 1).choose (d + 1) =
          (top d r + 2).choose (d + 2) := by
        rw [Nat.choose_succ_succ' (top d r + 1) (d + 1), add_comm]
      have h2 : (top d r + 2).choose (d + 2) ≤ (m + 1).choose (d + 2) :=
        Nat.choose_le_choose _ (by omega)
      omega

/--
@isnad1 id=le.1h3v.s4.d9750b577910 from=translated src=- shape=32f89d1d vocab=87c0a6ba
-/
theorem macaulayPow_mono : ∀ (d : ℕ) {a b : ℕ}, a ≤ b → Nat.macaulayPow d a ≤ Nat.macaulayPow d b
  | 0, a, b, _ => by simp [macaulayPow_zero]
  | d + 1, a, b, h => by
      have ht : top d a ≤ top d b := le_top_of_choose_le d b _ ((choose_top_le d a).trans h)
      rcases ht.eq_or_lt with ht | ht
      · rw [macaulayPow_succ, macaulayPow_succ, ht]
        have hr : rem d a ≤ rem d b := by
          have ha := rem_add_choose d a; have hb := rem_add_choose d b; rw [ht] at ha; omega
        have := macaulayPow_mono d hr
        omega
      · have h1 : Nat.macaulayPow (d + 1) a < (top d a + 1 + 1).choose (d + 1 + 1) :=
          macaulayPow_lt_choose (d + 1) (top d a + 1) a (lt_choose_top_succ d a)
        have h2 : (top d a + 1 + 1).choose (d + 1 + 1) ≤ (top d b + 1).choose (d + 1 + 1) :=
          Nat.choose_le_choose _ (by omega)
        have h3 : (top d b + 1).choose (d + 1 + 1) ≤ Nat.macaulayPow (d + 1) b := by
          rw [macaulayPow_succ]; exact Nat.le_add_right _ _
        omega

/--
@isnad1 id=eq.0h1v.s4.53cd8a5c100c from=translated src=- shape=c3982312 vocab=aa789aff
-/
theorem macaulayPow_one (a : ℕ) : Nat.macaulayPow 1 a = (a + 1).choose 2 := by
  rw [macaulayPow_succ, top_zero_left, rem_zero_left, macaulayPow_zero]; rfl

/--
@isnad1 id=eq.0h1v.s4.1e3b0bba89c7 from=translated src=- shape=1d838610 vocab=9e4fbcdb
-/
theorem macaulayPow_zero_right : ∀ d : ℕ, Nat.macaulayPow d 0 = 0
  | 0 => macaulayPow_zero 0
  | d + 1 => by
      rw [macaulayPow_succ, top_zero_right, rem_zero_right, macaulayPow_zero_right d,
        Nat.choose_eq_zero_of_lt (by omega)]

/--
@isnad1 id=eq.2h2v.s5.2db5ef92d297 from=translated src=- shape=c6d857a0 vocab=fc45cdd3
-/
theorem top_succ_of_le (d a : ℕ) (ha : 1 ≤ a) (h : a ≤ d + 2) : top (d + 1) a = d + 2 :=
  top_eq_of (d + 1) a (d + 2) (by rw [Nat.choose_self]; exact ha)
    (by have : (d + 2 + 1).choose (d + 1 + 1) = d + 2 + 1 := Nat.choose_succ_self_right (d + 2); omega)

/--
@isnad1 id=eq.1h2v.s5.87eeef13462c from=translated src=- shape=eb19043f vocab=644d85f7
-/
theorem macaulayPow_eq_self : ∀ (d a : ℕ), a ≤ d + 1 → Nat.macaulayPow (d + 1) a = a
  | d, 0, _ => macaulayPow_zero_right (d + 1)
  | 0, a + 1, h => by
      obtain rfl : a = 0 := by omega
      rw [macaulayPow_one]; rfl
  | d + 1, a + 1, h => by
      have ht : top (d + 1) (a + 1) = d + 2 := top_succ_of_le d (a + 1) (by omega) (by omega)
      have hr : rem (d + 1) (a + 1) = a := by simp [rem, ht]
      rw [macaulayPow_succ, ht, hr, macaulayPow_eq_self d a (by omega)]
      have : (d + 2 + 1).choose (d + 1 + 2) = 1 := by
        rw [show d + 1 + 2 = d + 2 + 1 by omega, Nat.choose_self]
      omega

def low : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, a => (top d a - 1).choose (d + 1) + low d (rem d a)

/--
@isnad1 id=eq.0h1v.s4.2fdbf3173d76 from=translated src=- shape=fe2c2146 vocab=16231192
-/
theorem low_zero (a : ℕ) : low 0 a = 0 := rfl

/--
@isnad1 id=eq.0h2v.s5.0f0cb441be8d from=translated src=- shape=b617f051 vocab=b13a4907
-/
theorem low_succ (d a : ℕ) : low (d + 1) a = (top d a - 1).choose (d + 1) + low d (rem d a) := rfl

/--
@isnad1 id=eq.0h1v.s4.ab67f12a0665 from=translated src=- shape=1d838610 vocab=16231192
-/
theorem low_zero_right : ∀ d : ℕ, low d 0 = 0
  | 0 => rfl
  | d + 1 => by
      rw [low_succ, top_zero_right, rem_zero_right, low_zero_right d, Nat.choose_eq_zero_of_lt (by omega)]

/--
@isnad1 id=eq.1h2v.s5.848f12030075 from=translated src=- shape=b7870e07 vocab=063d191b
-/
theorem low_eq_zero : ∀ (d a : ℕ), a ≤ d + 1 → low (d + 1) a = 0
  | d, 0, _ => low_zero_right _
  | 0, a + 1, h => by
      obtain rfl : a = 0 := by omega
      rw [low_succ, top_zero_left, low_zero]; rfl
  | d + 1, a + 1, h => by
      have ht : top (d + 1) (a + 1) = d + 2 := top_succ_of_le d (a + 1) (by omega) (by omega)
      have hr : rem (d + 1) (a + 1) = a := by simp [rem, ht]
      rw [low_succ, ht, hr, low_eq_zero d a (by omega), Nat.choose_eq_zero_of_lt (by omega)]

/--
@isnad1 id=lt.2h3v.s6.a8a95c7be5fd from=translated src=- shape=b6c1ccae vocab=4a484b05
-/
theorem low_lt_choose : ∀ (d m r : ℕ), r < (m + 1).choose (d + 1) → d + 1 ≤ m →
    low (d + 1) r < m.choose (d + 1)
  | 0, m, r, h, hm => by
      rw [low_succ, top_zero_left, low_zero]
      simp only [zero_add, Nat.choose_one_right, add_zero] at h ⊢
      omega
  | d + 1, m, r, h, hm => by
      rw [low_succ]
      show (top (d + 1) r - 1).choose (d + 2) + low (d + 1) (rem (d + 1) r) < m.choose (d + 2)
      have hT : top (d + 1) r ≤ m := Nat.lt_succ_iff.1 (top_lt_of_lt_choose (d + 1) r (m + 1) h)
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        rw [top_zero_right, rem_zero_right, low_zero_right, Nat.choose_eq_zero_of_lt (by omega),
          zero_add]
        exact Nat.choose_pos (by omega)
      · have hT' : d + 1 < top (d + 1) r := d_lt_top_of_pos _ _ hr
        have hRlt : rem (d + 1) r < (top (d + 1) r - 1 + 1).choose (d + 1) := by
          rw [Nat.sub_add_cancel (by omega)]; exact rem_lt (d + 1) r
        have ih := low_lt_choose d (top (d + 1) r - 1) (rem (d + 1) r) hRlt (by omega)
        have h1 : (top (d + 1) r - 1).choose (d + 2) + (top (d + 1) r - 1).choose (d + 1) =
            (top (d + 1) r).choose (d + 2) := by
          have := Nat.choose_succ_succ' (top (d + 1) r - 1) (d + 1)
          rw [Nat.sub_add_cancel (show 1 ≤ top (d + 1) r by omega)] at this
          rw [add_comm]; exact this.symm
        have h2 : (top (d + 1) r).choose (d + 2) ≤ m.choose (d + 2) := Nat.choose_le_choose _ hT
        omega

/--
@isnad1 id=eq.0h2v.s5.d684635d44fe from=translated src=- shape=237f4b52 vocab=bb91b3e8
-/
theorem macaulayPow_low_add : ∀ (d a : ℕ),
    Nat.macaulayPow (d + 1) (low (d + 1) a) + a = Nat.macaulayPow (d + 1) a
  | 0, a => by
      rw [low_succ, top_zero_left, low_zero, add_zero, macaulayPow_one, macaulayPow_one,
        Nat.choose_one_right]
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rfl
      · have h2 : (a + 1).choose 2 = a + a.choose 2 := by
          have := Nat.choose_succ_succ' a 1; rw [Nat.choose_one_right] at this; exact this
        rw [Nat.sub_add_cancel ha]; omega
  | d + 1, a => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [low_zero_right, add_zero]
      · set T := top (d + 1) a with hT
        set R := rem (d + 1) a with hR
        have hTd : d + 1 < T := d_lt_top_of_pos _ _ ha
        have hRa : R + T.choose (d + 2) = a := rem_add_choose (d + 1) a
        have hRlt : R < T.choose (d + 1) := rem_lt (d + 1) a
        have ih := macaulayPow_low_add d R
        rw [low_succ, macaulayPow_succ (d + 1) a]
        show Nat.macaulayPow (d + 2) ((T - 1).choose (d + 2) + low (d + 1) R) + a =
          (T + 1).choose (d + 3) + Nat.macaulayPow (d + 1) R
        rcases (show T = d + 2 ∨ d + 3 ≤ T by omega) with hT2 | hT3
        ·
          have hC : (d + 2).choose (d + 1) = d + 2 := Nat.choose_succ_self_right (d + 1)
          have hR1 : R ≤ d + 1 := by rw [hT2] at hRlt; omega
          rw [hT2, show d + 2 - 1 = d + 1 from rfl, Nat.choose_succ_self, zero_add, low_eq_zero d R hR1,
            macaulayPow_zero_right, macaulayPow_eq_self d R hR1, Nat.choose_self]
          rw [hT2, Nat.choose_self] at hRa
          omega
        ·
          have hlow : low (d + 1) R < (T - 1).choose (d + 1) :=
            low_lt_choose d (T - 1) R (by rw [Nat.sub_add_cancel (by omega)]; exact hRlt) (by omega)
          have hpasc : (T - 1).choose (d + 2) + (T - 1).choose (d + 1) = T.choose (d + 2) := by
            have := Nat.choose_succ_succ' (T - 1) (d + 1)
            rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
            rw [add_comm]; exact this.symm
          have hpasc' : T.choose (d + 3) + T.choose (d + 2) = (T + 1).choose (d + 3) := by
            rw [Nat.choose_succ_succ' T (d + 2), add_comm]
          have htop : top (d + 1) ((T - 1).choose (d + 2) + low (d + 1) R) = T - 1 :=
            top_eq_of (d + 1) _ (T - 1) (Nat.le_add_right _ _)
              (by rw [Nat.sub_add_cancel (show 1 ≤ T by omega)]; show _ < T.choose (d + 2); omega)
          have hrem : rem (d + 1) ((T - 1).choose (d + 2) + low (d + 1) R) = low (d + 1) R := by
            simp [rem, htop]
          rw [macaulayPow_succ, htop, hrem, Nat.sub_add_cancel (show 1 ≤ T by omega)]
          show T.choose (d + 3) + Nat.macaulayPow (d + 1) (low (d + 1) R) + a = _
          omega

/--
@isnad1 id=le.1h3v.s6.e586afbc6277 from=translated src=- shape=37fd55b6 vocab=4a484b05
-/
theorem le_choose_add_low : ∀ (d m r : ℕ), r < (m + 1).choose (d + 1) → r ≤ m.choose d + low (d + 1) r
  | 0, m, r, _ => by
      rw [low_succ, top_zero_left, low_zero, Nat.choose_zero_right, Nat.choose_one_right]; omega
  | d + 1, m, r, h => by
      rw [low_succ]
      show r ≤ m.choose (d + 1) + ((top (d + 1) r - 1).choose (d + 2) + low (d + 1) (rem (d + 1) r))
      have hT : top (d + 1) r ≤ m := Nat.lt_succ_iff.1 (top_lt_of_lt_choose (d + 1) r (m + 1) h)
      have hT1 : 1 ≤ top (d + 1) r := by have := d_le_top (d + 1) r; omega
      have hRa : rem (d + 1) r + (top (d + 1) r).choose (d + 2) = r := rem_add_choose (d + 1) r
      have hRlt : rem (d + 1) r < (top (d + 1) r - 1 + 1).choose (d + 1) := by
        rw [Nat.sub_add_cancel hT1]; exact rem_lt (d + 1) r
      have ih := le_choose_add_low d (top (d + 1) r - 1) (rem (d + 1) r) hRlt
      have h1 : (top (d + 1) r - 1).choose (d + 2) + (top (d + 1) r - 1).choose (d + 1) =
          (top (d + 1) r).choose (d + 2) := by
        have := Nat.choose_succ_succ' (top (d + 1) r - 1) (d + 1)
        rw [Nat.sub_add_cancel hT1] at this
        rw [add_comm]; exact this.symm
      have h2 : (top (d + 1) r - 1).choose (d + 1) + (top (d + 1) r - 1).choose d =
          (top (d + 1) r).choose (d + 1) := by
        have := Nat.choose_succ_succ' (top (d + 1) r - 1) d
        rw [Nat.sub_add_cancel hT1] at this
        rw [add_comm]; exact this.symm
      have h3 : (top (d + 1) r).choose (d + 1) ≤ m.choose (d + 1) := Nat.choose_le_choose _ hT
      omega

/--
@isnad1 id=le.1h3v.s5.f8ec57c08186 from=translated src=- shape=955c0b24 vocab=3be1ff91
-/
theorem le_add_low : ∀ (d a s : ℕ), a ≤ Nat.macaulayPow d s → a ≤ s + low (d + 1) a
  | 0, a, s, h => by rw [macaulayPow_zero] at h; omega
  | d + 1, a, s, h => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · exact Nat.zero_le _
      set T := top (d + 1) a with hT
      set R := rem (d + 1) a with hR
      have hTd : d + 1 < T := d_lt_top_of_pos _ _ ha
      have hRa : R + T.choose (d + 2) = a := rem_add_choose (d + 1) a
      have hRlt : R < T.choose (d + 1) := rem_lt (d + 1) a
      set T' := top d s with hT'
      have hs : rem d s + T'.choose (d + 1) = s := rem_add_choose d s

      have hlt : Nat.macaulayPow (d + 1) s < (T' + 1 + 1).choose (d + 1 + 1) :=
        macaulayPow_lt_choose (d + 1) (T' + 1) s (lt_choose_top_succ d s)
      have hTT' : T ≤ T' + 1 := by
        have := top_lt_of_lt_choose (d + 1) a (T' + 1 + 1) (h.trans_lt hlt); omega
      rw [low_succ]
      show a ≤ s + ((T - 1).choose (d + 2) + low (d + 1) R)
      have hpasc : (T - 1).choose (d + 2) + (T - 1).choose (d + 1) = T.choose (d + 2) := by
        have := Nat.choose_succ_succ' (T - 1) (d + 1)
        rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
        rw [add_comm]; exact this.symm
      rcases (show T ≤ T' ∨ T = T' + 1 by omega) with hle | heq
      ·
        have h1 : T.choose (d + 1) ≤ T'.choose (d + 1) := Nat.choose_le_choose _ hle
        have h2 : R ≤ (T - 1).choose d + low (d + 1) R :=
          le_choose_add_low d (T - 1) R (by rw [Nat.sub_add_cancel (by omega)]; exact hRlt)
        have h3 : (T - 1).choose (d + 1) + (T - 1).choose d = T.choose (d + 1) := by
          have := Nat.choose_succ_succ' (T - 1) d
          rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
          rw [add_comm]; exact this.symm
        omega
      ·
        have hμ : Nat.macaulayPow (d + 1) s = (T' + 1).choose (d + 2) + Nat.macaulayPow d (rem d s) :=
          macaulayPow_succ d s
        rw [← heq] at hμ
        rw [show T' = T - 1 by omega] at hs
        have hR' : R ≤ Nat.macaulayPow d (rem d s) := by omega
        have ih := le_add_low d R (rem d s) hR'
        omega

/--
@isnad1 id=le.0h2v.s3.bd52661d1087 from=translated src=- shape=bf83e09e vocab=e77e85fb
-/
theorem low_le : ∀ (d a : ℕ), low d a ≤ a
  | 0, _ => Nat.zero_le _
  | d + 1, a => by
      rw [low_succ]
      have h1 : (top d a - 1).choose (d + 1) ≤ (top d a).choose (d + 1) :=
        Nat.choose_le_choose _ (Nat.sub_le _ _)
      have h2 := low_le d (rem d a)
      have h3 := rem_add_choose d a
      omega

/--
@isnad1 id=lt.0h2v.s5.40cf03dd2b98 from=translated src=- shape=6b796bb6 vocab=36f96e1e
-/
theorem macaulayPow_lt_succ : ∀ (d a : ℕ), Nat.macaulayPow (d + 1) a < Nat.macaulayPow (d + 1) (a + 1)
  | 0, a => by
      rw [macaulayPow_one, macaulayPow_one]
      have h2 : (a + 1 + 1).choose 2 = (a + 1) + (a + 1).choose 2 := by
        have h := Nat.choose_succ_succ' (a + 1) 1
        rw [Nat.choose_one_right] at h
        exact h
      omega
  | d + 1, a => by
      have hT : top (d + 1) a ≤ top (d + 1) (a + 1) :=
        le_top_of_choose_le _ _ _ ((choose_top_le (d + 1) a).trans (Nat.le_succ a))
      rcases hT.eq_or_lt with hT | hT
      · rw [macaulayPow_succ (d + 1) a, macaulayPow_succ (d + 1) (a + 1), hT]
        have hr : rem (d + 1) (a + 1) = rem (d + 1) a + 1 := by
          have h1 := rem_add_choose (d + 1) a
          have h2 := rem_add_choose (d + 1) (a + 1)
          rw [hT] at h1
          omega
        rw [hr]
        have := macaulayPow_lt_succ d (rem (d + 1) a)
        omega
      · have h1 : Nat.macaulayPow (d + 1 + 1) a < (top (d + 1) a + 1 + 1).choose (d + 1 + 1 + 1) :=
          macaulayPow_lt_choose (d + 1 + 1) (top (d + 1) a + 1) a (lt_choose_top_succ (d + 1) a)
        have h2 : (top (d + 1) a + 1 + 1).choose (d + 1 + 1 + 1) ≤
            (top (d + 1) (a + 1) + 1).choose (d + 1 + 1 + 1) := Nat.choose_le_choose _ (by omega)
        have h3 : (top (d + 1) (a + 1) + 1).choose (d + 1 + 1 + 1) ≤ Nat.macaulayPow (d + 1 + 1) (a + 1) := by
          rw [macaulayPow_succ]; exact Nat.le_add_right _ _
        omega

/--
@isnad1 id=strictmo.0h1v.s4.bea4fd00c3b0 from=translated src=- shape=8d7f2f9c vocab=ebf7de3b
-/
theorem macaulayPow_strictMono (d : ℕ) : StrictMono (Nat.macaulayPow (d + 1)) :=
  strictMono_nat_of_lt_succ fun a => macaulayPow_lt_succ d a

/--
@isnad1 id=le.1h3v.s5.113ab0932c3c from=translated src=- shape=974639cc vocab=644d85f7
-/
theorem le_of_macaulayPow_le (d : ℕ) {a b : ℕ} (h : Nat.macaulayPow (d + 1) a ≤ Nat.macaulayPow (d + 1) b) :
    a ≤ b :=
  (macaulayPow_strictMono d).le_iff_le.mp h

/--
@isnad1 id=le.0h2v.s5.eb5888f28dba from=translated src=- shape=b0709bb8 vocab=7bbfc20e
-/
theorem le_macaulayPow_sub_low : ∀ (d a : ℕ), a ≤ Nat.macaulayPow (d + 1) (a - low (d + 2) a)
  | d, a => by
      set T := top (d + 1) a with hT
      set R := rem (d + 1) a with hR
      have hTd : d + 1 ≤ T := d_le_top (d + 1) a
      have hRa : R + T.choose (d + 2) = a := rem_add_choose (d + 1) a
      have hRlt : R < T.choose (d + 1) := rem_lt (d + 1) a
      have hlowR : low (d + 1) R ≤ R := low_le (d + 1) R
      have hpasc : (T - 1).choose (d + 2) + (T - 1).choose (d + 1) = T.choose (d + 2) := by
        have := Nat.choose_succ_succ' (T - 1) (d + 1)
        rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
        rw [add_comm]; exact this.symm
      have hpasc' : (T - 1).choose (d + 1) + (T - 1).choose d = T.choose (d + 1) := by
        have := Nat.choose_succ_succ' (T - 1) d
        rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
        rw [add_comm]; exact this.symm
      have hle1 : (T - 1).choose (d + 2) ≤ T.choose (d + 2) := Nat.choose_le_choose _ (Nat.sub_le _ _)
      have hτ : a - low (d + 2) a = (T - 1).choose (d + 1) + (R - low (d + 1) R) := by
        rw [low_succ (d + 1) a]
        show a - ((T - 1).choose (d + 1 + 1) + low (d + 1) R) = _
        show a - ((T - 1).choose (d + 2) + low (d + 1) R) = _
        omega
      rw [hτ]
      set z := (T - 1).choose (d + 1) + (R - low (d + 1) R) with hz
      rcases lt_or_ge (R - low (d + 1) R) ((T - 1).choose d) with hsmall | hbig
      ·
        have hz1 : (T - 1).choose (d + 1) ≤ z := Nat.le_add_right _ _
        have hz2 : z < (T - 1 + 1).choose (d + 1) := by
          rw [Nat.sub_add_cancel (show 1 ≤ T by omega)]; omega
        have htop : top d z = T - 1 := top_eq_of d z (T - 1) hz1 hz2
        have hrem : rem d z = R - low (d + 1) R := by
          have := rem_add_choose d z; rw [htop] at this; omega
        rw [macaulayPow_succ, htop, hrem, Nat.sub_add_cancel (show 1 ≤ T by omega)]

        have hkey : R ≤ Nat.macaulayPow d (R - low (d + 1) R) := by
          cases d with
          | zero =>
              have hl : low 1 R = R - 1 := by
                rw [low_succ, top_zero_left, low_zero, Nat.choose_one_right, Nat.add_zero]
              have h0 : (T - 1).choose 0 = 1 := Nat.choose_zero_right _
              rw [h0, hl] at hsmall
              have : R = 0 := by omega
              rw [this]; exact Nat.zero_le _
          | succ d => exact le_macaulayPow_sub_low d R
        omega
      ·
        have hz1 : T.choose (d + 1) ≤ z := by omega
        have h1 : T ≤ top d z := le_top_of_choose_le d z T hz1
        have h2 : (T + 1).choose (d + 2) ≤ (top d z + 1).choose (d + 2) := Nat.choose_le_choose _ (by omega)
        have h3 : (top d z + 1).choose (d + 2) ≤ Nat.macaulayPow (d + 1) z := by
          rw [macaulayPow_succ]; exact Nat.le_add_right _ _
        have h4 : a < (T + 1).choose (d + 2) := lt_choose_top_succ (d + 1) a
        omega

end GreenNum

open GreenNum in

/--
@isnad1 id=le.4h5v.s7.1caa5c66295b from=translated src=- shape=0c853a95 vocab=644d85f7
-/
theorem solution (d x y u v : ℕ) (hd : 1 ≤ d) (hx : x ≤ u + v)
    (hu : Nat.macaulayPow d u + y ≤ Nat.macaulayPow d y)
    (hv : Nat.macaulayPow (d + 1) v + x ≤ Nat.macaulayPow (d + 1) x) :
    Nat.macaulayPow (d + 1) x + (x + y) ≤ Nat.macaulayPow (d + 1) (x + y) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩

  have h1 : v ≤ low (e + 1 + 1) x := by
    have hg := macaulayPow_low_add (e + 1) x
    exact le_of_macaulayPow_le (e + 1) (by omega)
  have h2 : u ≤ low (e + 1) y := by
    have hg := macaulayPow_low_add e y
    exact le_of_macaulayPow_le e (by omega)

  have h3 : x - low (e + 1 + 1) x ≤ low (e + 1) y := by omega
  have h4 : x ≤ Nat.macaulayPow (e + 1) (low (e + 1) y) :=
    (le_macaulayPow_sub_low e x).trans (macaulayPow_mono _ h3)
  have h5 : x + y ≤ Nat.macaulayPow (e + 1) y := by
    have := macaulayPow_low_add e y; omega

  have h6 : x ≤ low (e + 1 + 1) (x + y) := by
    have := le_add_low (e + 1) (x + y) y h5; omega
  have h7 := macaulayPow_mono (e + 1 + 1) h6
  have h8 := macaulayPow_low_add (e + 1) (x + y)
  omega
