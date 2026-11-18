import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Nat_MacaulayPow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Nat_macaulayPow_lt_macaulayPow_of_lt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Nat_macaulayPow_lt_macaulayPow_of_lt

set_option autoImplicit false

namespace MacMono

open Nat

def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)

/--
@isnad1 id=eq.0h2v.s6.335e0679b9ba from=translated src=- shape=14dadc76 vocab=8c003907
-/
theorem macaulayPow_succ (d a : ℕ) :
    macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) + macaulayPow d (a - (top d a).choose (d + 1)) := by
  rw [macaulayPow, top]

/--
@isnad1 id=le.0h2v.s5.819cf1ccc044 from=translated src=- shape=8728c15b vocab=8264a478
-/
theorem succ_le_choose (d j : ℕ) : j + 1 ≤ (j + d + 1).choose (d + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (j + 1 + d + 1).choose (d + 1) = (j + d + 1).choose d + (j + d + 1).choose (d + 1) := by
      rw [show j + 1 + d + 1 = (j + d + 1) + 1 by ring, Nat.choose_succ_succ]
    have h2 : 1 ≤ (j + d + 1).choose d := Nat.choose_pos (by omega)
    omega

/--
@isnad1 id=le.1h3v.s5.022cc6dab85e from=translated src=- shape=8437f83e vocab=8264a478
-/
theorem le_bound {d a k : ℕ} (h : k.choose (d + 1) ≤ a) : k ≤ a + d + 1 := by
  by_cases hk : k ≤ d
  · omega
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + d + 1 := ⟨k - (d + 1), by omega⟩
    have := succ_le_choose d j
    omega

/--
@isnad1 id=iff.0h3v.s5.f5bbb99c64c7 from=translated src=- shape=c427fa43 vocab=26ef5675
-/
theorem choose_le_iff (d a k : ℕ) : k.choose (d + 1) ≤ a ↔ k ≤ top d a := by
  constructor
  · intro h
    exact Nat.le_findGreatest (le_bound h) h
  · intro h
    have hspec : (top d a).choose (d + 1) ≤ a :=
      Nat.findGreatest_spec (P := fun k => k.choose (d + 1) ≤ a) (m := 0) (Nat.zero_le _) (by simp)
    exact (Nat.choose_le_choose (d + 1) h).trans hspec

/--
@isnad1 id=le.0h2v.s4.e46c904eebdc from=translated src=- shape=d5c96991 vocab=26ef5675
-/
theorem top_choose_le (d a : ℕ) : (top d a).choose (d + 1) ≤ a := (choose_le_iff d a _).2 le_rfl

/--
@isnad1 id=lt.0h2v.s5.4c43af66d1fe from=translated src=- shape=cb038863 vocab=3fd49d52
-/
theorem lt_succ_top_choose (d a : ℕ) : a < (top d a + 1).choose (d + 1) := by
  by_contra h
  have := (choose_le_iff d a (top d a + 1)).1 (not_lt.1 h)
  omega

/--
@isnad1 id=eq.2h3v.s6.8326770147e0 from=translated src=- shape=6c07a21a vocab=f0c4653f
-/
theorem top_eq {d a k : ℕ} (h₁ : k.choose (d + 1) ≤ a) (h₂ : a < (k + 1).choose (d + 1)) : top d a = k := by
  have hk : k ≤ top d a := (choose_le_iff d a k).1 h₁
  rcases hk.lt_or_eq with hlt | heq
  · exact absurd ((choose_le_iff d a (k + 1)).2 (by omega)) (not_le.2 h₂)
  · exact heq.symm

/--
@isnad1 id=le.1h3v.s4.f63c67db8f28 from=translated src=- shape=32f89d1d vocab=2b131b46
-/
theorem top_mono (d : ℕ) {a b : ℕ} (h : a ≤ b) : top d a ≤ top d b :=
  (choose_le_iff d b _).1 ((top_choose_le d a).trans h)

/--
@isnad1 id=eq.0h1v.s4.1e3b0bba89c7 from=translated src=- shape=1d838610 vocab=9e4fbcdb
-/
theorem macaulayPow_zero_right (d : ℕ) : macaulayPow d 0 = 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have ht : top d 0 = d := top_eq (by simp [Nat.choose_succ_self]) (by simp)
    rw [macaulayPow_succ, ht, Nat.choose_succ_self, Nat.choose_succ_self, Nat.sub_zero, ih]

/--
@isnad1 id=eq.1h2v.s6.884d9056c3ea from=translated src=- shape=d97e8333 vocab=26fca95d
-/
theorem macaulayPow_succ_choose (d K : ℕ) (hK : d ≤ K) :
    macaulayPow (d + 1) (K.choose (d + 1)) = (K + 1).choose (d + 2) := by
  have ht : top d (K.choose (d + 1)) = K := by
    refine top_eq le_rfl ?_
    rw [Nat.choose_succ_succ']
    have : 0 < K.choose d := Nat.choose_pos hK
    omega
  rw [macaulayPow_succ, ht, Nat.sub_self, macaulayPow_zero_right, Nat.add_zero]

/--
@isnad1 id=eq.0h1v.s4.53cd8a5c100c from=translated src=- shape=c3982312 vocab=aa789aff
-/
theorem macaulayPow_one (a : ℕ) : macaulayPow 1 a = (a + 1).choose 2 := by
  have ht : top 0 a = a := top_eq (by simp) (by simp)
  rw [macaulayPow_succ, ht]
  simp [macaulayPow]

/--
@isnad1 id=lt.1h3v.s5.6145147f876f from=translated src=- shape=0dd5ea2a vocab=36f96e1e
-/
theorem strictMono_succ (d : ℕ) : ∀ a b : ℕ, a < b → macaulayPow (d + 1) a < macaulayPow (d + 1) b := by
  induction d with
  | zero =>
    intro a b hab
    rw [macaulayPow_one, macaulayPow_one]
    have h1 : (a + 1).choose 2 < (a + 2).choose 2 := by
      rw [show a + 2 = (a + 1) + 1 by ring, Nat.choose_succ_succ (a + 1) 1]
      simp
    exact h1.trans_le (Nat.choose_le_choose 2 (by omega))
  | succ d ih =>
    intro a b hab
    rw [macaulayPow_succ (d + 1) a, macaulayPow_succ (d + 1) b]
    have e1 : d + 1 + 1 = d + 2 := rfl
    have e2 : d + 1 + 2 = d + 3 := rfl
    simp only [e1, e2]
    have hka := top_choose_le (d + 1) a
    have hkb := top_choose_le (d + 1) b
    simp only [e1] at hka hkb
    have hmono : top (d + 1) a ≤ top (d + 1) b := top_mono (d + 1) hab.le
    rcases hmono.lt_or_eq with hlt | heq
    ·
      have hra : a - (top (d + 1) a).choose (d + 2) < (top (d + 1) a).choose (d + 1) := by
        have h2 := lt_succ_top_choose (d + 1) a
        rw [e1, Nat.choose_succ_succ'] at h2
        simp only [e1] at h2
        omega

      have hK : d + 1 ≤ top (d + 1) a := by
        by_contra hK
        rw [Nat.choose_eq_zero_of_lt (show top (d + 1) a < d + 1 by omega)] at hra
        omega
      have hrem : macaulayPow (d + 1) (a - (top (d + 1) a).choose (d + 2)) <
          (top (d + 1) a + 1).choose (d + 2) := by
        have := ih _ _ hra
        rwa [macaulayPow_succ_choose d (top (d + 1) a) (by omega)] at this

      have hpascal : (top (d + 1) a + 1 + 1).choose (d + 2 + 1) =
          (top (d + 1) a + 1).choose (d + 2) + (top (d + 1) a + 1).choose (d + 2 + 1) :=
        Nat.choose_succ_succ' _ _
      have e3 : d + 2 + 1 = d + 3 := rfl
      simp only [e3] at hpascal
      have hle : (top (d + 1) a + 1 + 1).choose (d + 3) ≤ (top (d + 1) b + 1).choose (d + 3) :=
        Nat.choose_le_choose _ (by omega)
      omega
    ·
      have hr : a - (top (d + 1) a).choose (d + 2) < b - (top (d + 1) b).choose (d + 2) := by
        rw [← heq]; omega
      have := ih _ _ hr
      rw [heq] at this ⊢
      omega

/--
@isnad1 id=lt.2h3v.s4.fd7c94b92438 from=translated src=- shape=aad03d02 vocab=958acc08
-/
theorem macaulayPow_strictMono {d : ℕ} (hd : 1 ≤ d) {a b : ℕ} (h : a < b) :
    macaulayPow d a < macaulayPow d b := by
  obtain ⟨d, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  exact strictMono_succ d a b h

end MacMono

/--
@isnad1 id=lt.2h3v.s4.fd7c94b92438 from=translated src=- shape=aad03d02 vocab=958acc08
-/
theorem solution {d : ℕ} (hd : 1 ≤ d) {a b : ℕ} (h : a < b) :
    Nat.macaulayPow d a < Nat.macaulayPow d b :=
  MacMono.macaulayPow_strictMono hd h
