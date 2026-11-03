/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_7
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proposition 1.8

The last nonzero entry of the signed remainder sequence of $P$ and $Q$
is a greatest common divisor of $P$ and $Q$.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

open Classical in
/--
@isnad1 id=eq.1h4v.s7.243ad82e1cb4 from=translated src=- shape=dad01e50 vocab=e7d659c0
-/
lemma SRemS_ss (P Q : K[X]) (n : ℕ) (hne : SRemS P Q (n + 1) ≠ 0) :
    SRemS P Q (n + 2) = -(SRemS P Q n % SRemS P Q (n + 1)) := by
  simp [SRemS, hne]

open Classical in
/--
@isnad1 id=eq.2h5v.s7.551afbf3d06c from=translated src=- shape=3b928cec vocab=f8fb7683
-/
lemma SRemS_zero_ge (P Q : K[X]) (n : ℕ) (h : SRemS P Q (n + 1) = 0)
    (m : ℕ) (hm : m ≥ n + 1) : SRemS P Q m = 0 := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm' : m + 1 ≤ n + 1
    · rw [show m + 1 = n + 1 from by omega]; exact h
    · have ihm : SRemS P Q m = 0 := ih (by omega)
      cases m with
      | zero => omega
      | succ p => simp [SRemS, ihm]

open Classical in
/-- Forward induction: any common divisor of P and Q divides every entry
    of the signed remainder sequence.
@isnad1 id=dvd.2h5v.s8.a1c629b824b2 from=translated src=- shape=0ddd0c27 vocab=84f4b9f2
-/
theorem dvd_SRemS (P Q D : K[X]) (hP : D ∣ P) (hQ : D ∣ Q) (n : ℕ) :
    D ∣ SRemS P Q n := by
  match n with
  | 0 => exact hP
  | 1 => exact hQ
  | n + 2 =>
    by_cases hne : SRemS P Q (n + 1) = 0
    · simp [SRemS, hne]
    · rw [SRemS_ss P Q n hne]
      exact dvd_neg.mpr ((EuclideanDomain.dvd_mod_iff
        (dvd_SRemS P Q D hP hQ (n + 1))).mpr (dvd_SRemS P Q D hP hQ n))
termination_by n

open Classical in
/-- Backward step: if G divides SRemS(n+1) and SRemS(n+2), it divides SRemS(n).-/
private lemma SRemS_back (P Q G : K[X]) (n : ℕ) (hne : SRemS P Q (n + 1) ≠ 0)
    (h1 : G ∣ SRemS P Q (n + 1)) (h2 : G ∣ SRemS P Q (n + 2)) :
    G ∣ SRemS P Q n := by
  rw [SRemS_ss P Q n hne] at h2
  exact (EuclideanDomain.dvd_mod_iff h1).mp (dvd_neg.mp h2)

open Classical in
/-- Backward induction: when SRemS(k+1) = 0, SRemS_k divides all earlier entries.-/
private theorem SRemS_last_dvd (P Q : K[X]) (k : ℕ)
    (hk : SRemS P Q (k + 1) = 0) (hk_ne : SRemS P Q k ≠ 0)
    (m : ℕ) (hm : m ≤ k) : SRemS P Q k ∣ SRemS P Q m := by
  by_cases hm' : m = k
  · subst hm'; exact dvd_refl _
  · have hm1 : m + 1 ≤ k := by omega
    have hne : SRemS P Q (m + 1) ≠ 0 := by
      intro heq
      cases m with
      | zero => exact hk_ne (SRemS_zero_ge P Q 0 heq k (by omega))
      | succ p => exact hk_ne (SRemS_zero_ge P Q (p + 1) heq k (by omega))
    have ih1 := SRemS_last_dvd P Q k hk hk_ne (m + 1) hm1
    have ih2 : SRemS P Q k ∣ SRemS P Q (m + 2) := by
      by_cases hm2 : m + 2 ≤ k
      · exact SRemS_last_dvd P Q k hk hk_ne (m + 2) hm2
      · rw [SRemS_zero_ge P Q k hk (m + 2) (by omega)]; exact dvd_zero _
    exact SRemS_back P Q (SRemS P Q k) m hne ih1 ih2
termination_by k - m

open Classical in
/-- BPR Proposition 1.8: The last nonzero element of the signed remainder sequence
    is a greatest common divisor of P and Q.
@isnad1 id=isgcd.2h4v.s7.dce36bc288ab from=translated src=- shape=743f6389 vocab=81b3f265
-/
theorem prop_1_8 {P Q : K[X]} {k : ℕ}
    (hk : SRemS P Q (k + 1) = 0) (hk_ne : SRemS P Q k ≠ 0) :
    IsGCD (SRemS P Q k) P Q := by
  refine ⟨SRemS_last_dvd P Q k hk hk_ne 0 (Nat.zero_le _), ?_,
    fun D hDP hDQ => dvd_SRemS P Q D hDP hDQ k⟩
  cases k with
  | zero => simp [SRemS] at hk; rw [hk]; exact dvd_zero _
  | succ k' => exact SRemS_last_dvd P Q (k' + 1) hk hk_ne 1 (by omega)

open Classical in
/-- The signed remainder sequence of P and 0 has SRemS(0) = P.
@isnad1 id=eq.0h2v.s6.bec7db674950 from=translated src=- shape=31ddcac1 vocab=a8b8db07
-/
@[simp] theorem SRemS_zero_left (P : K[X]) : SRemS P 0 0 = P := rfl

open Classical in
/-- The signed remainder sequence of P and 0 stabilizes at 0 from index 1 onward.
@isnad1 id=eq.1h3v.s6.a3b7be8f4841 from=translated src=- shape=199cf038 vocab=d492c869
-/
theorem SRemS_zero_right (P : K[X]) (n : ℕ) (hn : n ≥ 1) :
    SRemS P 0 n = 0 :=
  SRemS_zero_ge P 0 0 rfl n hn

open Classical in
/-- The signed remainder sequence of 0 and Q has SRemS(0) = 0.
@isnad1 id=eq.0h2v.s6.b9b6418476f5 from=translated src=- shape=ff3d7b45 vocab=a8b8db07
-/
@[simp] theorem SRemS_zero_fst (Q : K[X]) : SRemS 0 Q 0 = 0 := rfl

open Classical in
/-- The signed remainder sequence of 0 and Q has SRemS(1) = Q.
@isnad1 id=eq.0h2v.s6.a55251ffcb26 from=translated src=- shape=c0aedce3 vocab=a8b8db07
-/
@[simp] theorem SRemS_zero_snd (Q : K[X]) : SRemS 0 Q 1 = Q := rfl

open Classical in
/-- When Q ≠ 0, the signed remainder sequence of 0 and Q stabilizes at 0
    from index 2 onward: SRemS(0, Q) = [0, Q, 0, 0, …].
@isnad1 id=eq.2h3v.s7.56b368884fcf from=translated src=- shape=88dc72d5 vocab=d492c869
-/
theorem SRemS_zero_left_stabilizes (Q : K[X]) (hQ : Q ≠ 0) (n : ℕ) (hn : n ≥ 2) :
    SRemS 0 Q n = 0 := by
  apply SRemS_zero_ge 0 Q 1 _ n (by omega)
  simp [SRemS, hQ]

end Azurite.BPR
