/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Data.Fin.Basic
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Tactic.DeriveFintype
import Tengoku.Seed.Tactic.IntervalCases
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

def signedUnit : Bool → ℤ
  | false => -1
  | true => 1

structure DRoot (m : ℕ) where
  i : Fin m
  j : Fin m
  lt : i < j
  si : Bool
  sj : Bool
  deriving DecidableEq, Fintype

def DRoot.vector {m : ℕ} (r : DRoot m) : Fin m → ℤ := fun k =>
  if k = r.i then signedUnit r.si else if k = r.j then signedUnit r.sj else 0

def intDot {m : ℕ} (x y : Fin m → ℤ) : ℤ :=
  ∑ i, x i * y i

/--
@isnad1 id=le.0h2v.s4.7ea44b97e7b7 from=translated src=- shape=9ff44887 vocab=50b56c4d
-/
theorem intDot_self_nonneg {m : ℕ} (x : Fin m → ℤ) :
    0 ≤ intDot x x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/--
@isnad1 id=iff.0h2v.s5.bb0c106741ea from=translated src=- shape=11d5b95f vocab=d602ac24
-/
theorem intDot_self_eq_zero_iff {m : ℕ} (x : Fin m → ℤ) :
    intDot x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have hi : x i * x i ≤ intDot x x :=
      Finset.single_le_sum (fun j _ => mul_self_nonneg (x j))
        (Finset.mem_univ i)
    rw [h] at hi
    have hs := mul_self_nonneg (x i)
    exact mul_self_eq_zero.mp (le_antisymm hi hs)
  · rintro rfl
    simp [intDot]

def DRoot.test {m : ℕ} (hm : 2 ≤ m) : DRoot m where
  i := ⟨0, by omega⟩
  j := ⟨1, hm⟩
  lt := by simp
  si := true
  sj := true

/--
@isnad1 id=eq.0h1v.s4.bfcb672d0529 from=translated src=- shape=7bab346c vocab=a3171321
-/
@[simp]
theorem signedUnit_sq (s : Bool) : signedUnit s * signedUnit s = 1 := by
  cases s <;> decide

/--
@isnad1 id=eq.0h2v.s4.a1e837e62173 from=translated src=- shape=18d72d6d vocab=2aa63144
-/
theorem DRoot.intDot_self {m : ℕ} (r : DRoot m) :
    intDot r.vector r.vector = 2 := by
  classical
  rw [show intDot r.vector r.vector =
      ∑ k, ((if k = r.i then 1 else 0) + if k = r.j then 1 else 0) by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hi : k = r.i
    · subst k
      simp [DRoot.vector, signedUnit_sq, ne_of_lt r.lt]
    · by_cases hj : k = r.j
      · subst k
        simp [DRoot.vector, hi, signedUnit_sq]
      · simp [DRoot.vector, hi, hj]]
  simp [Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h2v.s5.88031cb7de6a from=translated src=- shape=1258f27c vocab=24eb1dc7
-/
theorem DRoot.sum_vector {m : ℕ} (r : DRoot m) :
    (∑ i, r.vector i) = signedUnit r.si + signedUnit r.sj := by
  classical
  rw [show (∑ i, r.vector i) =
      ∑ i, ((if i = r.i then signedUnit r.si else 0) +
        (if i = r.j then signedUnit r.sj else 0)) by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = r.i
    · subst i
      simp [DRoot.vector, ne_of_lt r.lt]
    · by_cases hj : i = r.j
      · subst i
        simp [DRoot.vector, ne_of_gt r.lt]
      · simp [DRoot.vector, hi, hj]]
  rw [Finset.sum_add_distrib]
  simp

/--
@isnad1 id=ex.0h2v.s5.efa9c9f19249 from=translated src=- shape=33ec9acb vocab=f68b755f
-/
theorem DRoot.sum_vector_even {m : ℕ} (r : DRoot m) :
    ∃ a : ℤ, (∑ i, r.vector i) = 2 * a := by
  rw [r.sum_vector]
  cases r.si <;> cases r.sj
  · exact ⟨-1, by norm_num [signedUnit]⟩
  · exact ⟨0, by norm_num [signedUnit]⟩
  · exact ⟨0, by norm_num [signedUnit]⟩
  · exact ⟨1, by norm_num [signedUnit]⟩

/--
@isnad1 id=ne.0h1v.s3.6d734f91f3a3 from=translated src=- shape=a311c14d vocab=88e8f261
-/
@[simp]
theorem signedUnit_ne_zero (s : Bool) : signedUnit s ≠ 0 := by
  cases s <;> decide

/--
@isnad1 id=injectiv.0h0v.s2.92e0762ca498 from=translated src=- shape=54c8eceb vocab=ec34412a
-/
theorem signedUnit_injective : Function.Injective signedUnit := by
  intro s t h
  cases s <;> cases t <;> simp_all [signedUnit]

/--
@isnad1 id=eq.0h2v.s4.48363525132f from=translated src=- shape=268bd18e vocab=c1779917
-/
@[simp]
theorem DRoot.vector_i {m : ℕ} (r : DRoot m) :
    r.vector r.i = signedUnit r.si := by
  simp [DRoot.vector]

/--
@isnad1 id=eq.0h2v.s4.c9c10c5384de from=translated src=- shape=268bd18e vocab=c5955abb
-/
@[simp]
theorem DRoot.vector_j {m : ℕ} (r : DRoot m) :
    r.vector r.j = signedUnit r.sj := by
  simp [DRoot.vector, ne_of_gt r.lt]

/--
@isnad1 id=iff.0h3v.s5.8e80a022aa4d from=translated src=- shape=726ee3a4 vocab=74a969c4
-/
theorem DRoot.vector_ne_zero_iff {m : ℕ} (r : DRoot m) (k : Fin m) :
    r.vector k ≠ 0 ↔ k = r.i ∨ k = r.j := by
  by_cases hi : k = r.i
  · simp [hi]
  · by_cases hj : k = r.j
    · subst k
      simp [DRoot.vector, ne_of_gt r.lt]
    · simp [DRoot.vector, hi, hj]

/--
@isnad1 id=injectiv.0h1v.s3.8495f6a100c3 from=translated src=- shape=0cd72c43 vocab=5d058f6a
-/
theorem DRoot.vector_injective {m : ℕ} :
    Function.Injective (@DRoot.vector m) := by
  intro r s hrs
  have hi : r.i = s.i ∨ r.i = s.j :=
    (s.vector_ne_zero_iff r.i).mp (by
      rw [← hrs]
      show r.vector r.i ≠ 0
      rw [r.vector_i]
      exact signedUnit_ne_zero r.si)
  have hj : r.j = s.i ∨ r.j = s.j :=
    (s.vector_ne_zero_iff r.j).mp (by
      rw [← hrs]
      show r.vector r.j ≠ 0
      rw [r.vector_j]
      exact signedUnit_ne_zero r.sj)
  have hii : r.i = s.i := by
    rcases hi with hi | hi
    · exact hi
    · rcases hj with hj | hj
      · exfalso
        have hsr : s.i < r.i := by simpa [hi] using s.lt
        have hrs' : r.i < s.i := by simpa [hj] using r.lt
        exact lt_asymm hsr hrs'
      · exact absurd (hi.trans hj.symm) (ne_of_lt r.lt)
  have hjj : r.j = s.j := by
    rcases hj with hj | hj
    · exact absurd (hii.trans hj.symm) (ne_of_lt r.lt)
    · exact hj
  have hsi : r.si = s.si := by
    apply signedUnit_injective
    calc
      signedUnit r.si = r.vector r.i := r.vector_i.symm
      _ = s.vector r.i := congrFun hrs r.i
      _ = s.vector s.i := congrArg s.vector hii
      _ = signedUnit s.si := s.vector_i
  have hsj : r.sj = s.sj := by
    apply signedUnit_injective
    calc
      signedUnit r.sj = r.vector r.j := r.vector_j.symm
      _ = s.vector r.j := congrFun hrs r.j
      _ = s.vector s.j := congrArg s.vector hjj
      _ = signedUnit s.sj := s.vector_j
  cases r
  cases s
  simp_all

/--
@isnad1 id=or.1h1v.s5.637fa593f47b from=translated src=- shape=02d88960 vocab=415b9514
-/
theorem int_eq_zero_or_signedUnit_of_sq_le_two (z : ℤ) (hz : z * z ≤ 2) :
    z = 0 ∨ ∃ s : Bool, signedUnit s = z := by
  have hlo : -1 ≤ z := by
    by_contra h
    have : z ≤ -2 := by omega
    nlinarith
  have hhi : z ≤ 1 := by
    by_contra h
    have : 2 ≤ z := by omega
    nlinarith
  interval_cases z
  · exact Or.inr ⟨false, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨true, rfl⟩

/--
@isnad1 id=ex.1h2v.s5.332da9bac9af from=translated src=- shape=728b8592 vocab=3bc89ed2
-/
theorem DRoot.exists_vector_eq_of_intDot_self_eq_two {m : ℕ}
    (z : Fin m → ℤ) (hz : intDot z z = 2) :
    ∃ r : DRoot m, r.vector = z := by
  classical
  let support : Finset (Fin m) := Finset.univ.filter fun i => z i ≠ 0
  have hle : ∀ i, z i * z i ≤ 2 := by
    intro i
    calc
      z i * z i ≤ ∑ j, z j * z j :=
        Finset.single_le_sum (fun j _ => mul_self_nonneg (z j))
          (Finset.mem_univ i)
      _ = 2 := hz
  have hunit : ∀ i, z i = 0 ∨ ∃ s : Bool, signedUnit s = z i := fun i =>
    int_eq_zero_or_signedUnit_of_sq_le_two (z i) (hle i)
  have hsumCard : (support.card : ℤ) = 2 := by
    calc
      (support.card : ℤ) = (∑ i ∈ support, (1 : ℤ)) := by simp
      _ = ∑ i, z i * z i := by
        calc
          (∑ i ∈ support, (1 : ℤ)) =
              ∑ i, if z i ≠ 0 then (1 : ℤ) else 0 := by
            dsimp only [support]
            exact Finset.sum_filter (s := Finset.univ)
              (fun i => z i ≠ 0) (fun _ => (1 : ℤ))
          _ = ∑ i, z i * z i := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : z i = 0
            · simp [hi]
            · obtain ⟨s, hs⟩ := (hunit i).resolve_left hi
              simp [← hs, signedUnit_sq]
      _ = 2 := hz
  have hcard : support.card = 2 := by omega
  obtain ⟨i, j, hij, hsupp⟩ := Finset.card_eq_two.mp hcard
  have hi : z i ≠ 0 := by
    have : i ∈ support := by simp [hsupp]
    simpa [support] using this
  have hj : z j ≠ 0 := by
    have : j ∈ support := by simp [hsupp]
    simpa [support] using this
  obtain ⟨si, hsi⟩ := (hunit i).resolve_left hi
  obtain ⟨sj, hsj⟩ := (hunit j).resolve_left hj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · let r : DRoot m := ⟨i, j, hijlt, si, sj⟩
    refine ⟨r, funext fun k => ?_⟩
    by_cases hki : k = i
    · subst k
      change (if i = i then signedUnit si else
        if i = j then signedUnit sj else 0) = z i
      rw [ite_eq_left rfl]
      exact hsi
    · by_cases hkj : k = j
      · subst k
        change (if j = i then signedUnit si else
          if j = j then signedUnit sj else 0) = z j
        rw [ite_eq_right (ne_of_gt hijlt), ite_eq_left rfl]
        exact hsj
      · have hknot : k ∉ support := by simp [hsupp, hki, hkj]
        have hkzero : z k = 0 := by simpa [support] using hknot
        simp [r, DRoot.vector, hki, hkj, hkzero]
  · let r : DRoot m := ⟨j, i, hjilt, sj, si⟩
    refine ⟨r, funext fun k => ?_⟩
    by_cases hkj : k = j
    · subst k
      change (if j = j then signedUnit sj else
        if j = i then signedUnit si else 0) = z j
      rw [ite_eq_left rfl]
      exact hsj
    · by_cases hki : k = i
      · subst k
        change (if i = j then signedUnit sj else
          if i = i then signedUnit si else 0) = z i
        rw [ite_eq_right (ne_of_gt hjilt), ite_eq_left rfl]
        exact hsi
      · have hknot : k ∉ support := by simp [hsupp, hki, hkj]
        have hkzero : z k = 0 := by simpa [support] using hknot
        simp [r, DRoot.vector, hki, hkj, hkzero]

noncomputable def DRoot.vectorEquiv (m : ℕ) :
    DRoot m ≃ {z : Fin m → ℤ // intDot z z = 2} :=
  Equiv.ofBijective (fun r => ⟨r.vector, r.intDot_self⟩) ⟨
    fun r s h => DRoot.vector_injective (Subtype.ext_iff.mp h),
    fun z => by
      obtain ⟨r, hr⟩ := DRoot.exists_vector_eq_of_intDot_self_eq_two z.1 z.2
      exact ⟨r, Subtype.ext hr⟩⟩

end SRG266.Lattice
