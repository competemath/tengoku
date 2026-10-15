/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import Tengoku

/-!
# Odd-even transposition routes

An n-round sorting network gives the alternating permutation route used for complete flags.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

@[expose] public section

namespace MooreBound

namespace OddEvenSorting

/-- Sort each disjoint consecutive pair of list entries. -/
def pairPhase {α : Type*} [LinearOrder α] : List α → List α
  | a :: b :: xs => min a b :: max a b :: pairPhase xs
  | xs => xs

/-- Apply a comparator layer, optionally leaving the first entry fixed. -/
def phase {α : Type*} [LinearOrder α] (shifted : Bool) (xs : List α) : List α :=
  if shifted then
    match xs with
    | [] => []
    | x :: xs => x :: pairPhase xs
  else
    pairPhase xs

/--
@isnad1 id=eq.0h1v.s3.eb6b173cbc4b from=translated src=- shape=9dd68f90 vocab=6c428635
-/
@[simp] theorem pairPhase_nil {α : Type*} [LinearOrder α] :
    pairPhase ([] : List α) = [] := rfl

/--
@isnad1 id=eq.0h2v.s4.1e05c3a266ab from=translated src=- shape=67d480a1 vocab=ebe60fda
-/
@[simp] theorem pairPhase_singleton {α : Type*} [LinearOrder α] (a : α) :
    pairPhase [a] = [a] := rfl

/--
@isnad1 id=eq.0h4v.s5.3e3b0bf92c99 from=translated src=- shape=712a330c vocab=7b76896c
-/
@[simp] theorem pairPhase_cons_cons {α : Type*} [LinearOrder α] (a b : α) (xs : List α) :
    pairPhase (a :: b :: xs) = min a b :: max a b :: pairPhase xs := rfl

/--
@isnad1 id=eq.0h2v.s4.e45cc5c4f00b from=translated src=- shape=cefdfddf vocab=39d33e98
-/
@[simp] theorem phase_false {α : Type*} [LinearOrder α] (xs : List α) :
    phase false xs = pairPhase xs := rfl

/--
@isnad1 id=eq.0h1v.s4.e2d5f5bc47b4 from=translated src=- shape=a7227927 vocab=4b102fce
-/
@[simp] theorem phase_true_nil {α : Type*} [LinearOrder α] :
    phase true ([] : List α) = [] := rfl

/--
@isnad1 id=eq.0h3v.s4.7aa871d2a8fa from=translated src=- shape=80771de9 vocab=1b6d82d5
-/
@[simp] theorem phase_true_cons {α : Type*} [LinearOrder α] (a : α) (xs : List α) :
    phase true (a :: xs) = a :: pairPhase xs := rfl

/--
@isnad1 id=eq.0h2v.s4.2f047e168356 from=translated src=- shape=1ecb6dcd vocab=cb41807a
-/
@[simp] theorem length_pairPhase {α : Type*} [LinearOrder α] (xs : List α) :
    (pairPhase xs).length = xs.length := by
  induction xs using pairPhase.induct <;> simp_all [pairPhase]

/--
@isnad1 id=eq.0h3v.s4.a7d5f59e6dc3 from=translated src=- shape=63173502 vocab=ed1a6159
-/
@[simp] theorem length_phase {α : Type*} [LinearOrder α] (p : Bool) (xs : List α) :
    (phase p xs).length = xs.length := by
  cases p <;> cases xs <;> simp [phase]

/-- The integer count of true bits among the first i entries. -/
def pref (xs : List Bool) (i : ℕ) : ℤ := ((xs.take i).count true : ℤ)

/-- Interpret a Boolean bit as zero or one in the integers. -/
def bitInt (b : Bool) : ℤ := if b then 1 else 0

/--
@isnad1 id=eq.0h1v.s3.a4e1b25a9dbc from=translated src=- shape=12facff3 vocab=24f18a50
-/
@[simp] theorem pref_nil (i : ℕ) : pref [] i = 0 := by simp [pref]

/--
@isnad1 id=eq.0h1v.s4.739209fff954 from=translated src=- shape=98672205 vocab=0279d0ce
-/
@[simp] theorem pref_zero (xs : List Bool) : pref xs 0 = 0 := by simp [pref]

/--
@isnad1 id=eq.0h3v.s5.a677d7b218ca from=translated src=- shape=2c9ea9f4 vocab=86f38804
-/
@[simp] theorem pref_cons_succ (a : Bool) (xs : List Bool) (i : ℕ) :
    pref (a :: xs) (i + 1) = bitInt a + pref xs i := by
  cases a <;> simp [pref, bitInt, add_comm]

/--
@isnad1 id=eq.0h4v.s5.049f101b1e76 from=translated src=- shape=d9c2d8e7 vocab=86f38804
-/
theorem pref_cons_cons_add (a b : Bool) (xs : List Bool) (i : ℕ) :
    pref (a :: b :: xs) (i + 2) = bitInt a + bitInt b + pref xs i := by
  rw [show i + 2 = (i + 1) + 1 by omega, pref_cons_succ, pref_cons_succ]
  omega

/--
@isnad1 id=eq.0h2v.s5.fd833df8fd6c from=translated src=- shape=f8f43f23 vocab=09fd4920
-/
theorem bitInt_min_add_max (a b : Bool) :
    bitInt (min a b) + bitInt (max a b) = bitInt a + bitInt b := by
  cases a <;> cases b <;> decide

/--
@isnad1 id=eq.0h2v.s5.e5418090fd49 from=translated src=- shape=1a134231 vocab=cb312fc0
-/
theorem pref_pairPhase_even (xs : List Bool) (k : ℕ) :
    pref (pairPhase xs) (2 * k) = pref xs (2 * k) := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
      cases xs with
      | nil => simp
      | cons a xs =>
          cases xs with
          | nil => simp [pairPhase, pref]
          | cons b xs =>
              rw [show 2 * (k + 1) = 2 * k + 2 by omega]
              rw [pairPhase_cons_cons, pref_cons_cons_add, pref_cons_cons_add,
                bitInt_min_add_max, ih]

/--
@isnad1 id=eq.1h2v.s6.fa383aeacb9f from=translated src=- shape=45b366cc vocab=3b609f45
-/
theorem pref_pairPhase_odd (xs : List Bool) (k : ℕ)
    (hk : 2 * k + 1 < xs.length) :
    pref (pairPhase xs) (2 * k + 1) =
      max (pref xs (2 * k)) (pref xs (2 * k + 2) - 1) := by
  induction k generalizing xs with
  | zero =>
      cases xs with
      | nil => simp at hk
      | cons a xs =>
          cases xs with
          | nil => simp at hk
          | cons b xs => cases a <;> cases b <;> simp [pairPhase, pref]
  | succ k ih =>
      cases xs with
      | nil => simp at hk
      | cons a xs =>
          cases xs with
          | nil => simp at hk
          | cons b xs =>
              simp only [List.length_cons] at hk
              have hk' : 2 * k + 1 < xs.length := by omega
              have h := ih xs hk'
              rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega]
              rw [show 2 * (k + 1) = 2 * k + 2 by omega]
              rw [pairPhase_cons_cons, pref_cons_cons_add, pref_cons_cons_add,
                pref_cons_cons_add, bitInt_min_add_max, h]
              simp only [max_def]
              split <;> split <;> omega

/--
@isnad1 id=eq.0h2v.s5.36301df226e4 from=translated src=- shape=3ade5c9a vocab=c77379f2
-/
theorem pref_phase_false_even (xs : List Bool) (k : ℕ) :
    pref (phase false xs) (2 * k) = pref xs (2 * k) := by
  exact pref_pairPhase_even xs k

/--
@isnad1 id=eq.1h2v.s6.e392ed825c4f from=translated src=- shape=76d53a9f vocab=0ac08b8f
-/
theorem pref_phase_false_odd (xs : List Bool) (k : ℕ)
    (hk : 2 * k + 1 < xs.length) :
    pref (phase false xs) (2 * k + 1) =
      max (pref xs (2 * k)) (pref xs (2 * k + 2) - 1) := by
  exact pref_pairPhase_odd xs k hk

/--
@isnad1 id=eq.0h2v.s6.adf6f67cc7da from=translated src=- shape=5de66ae9 vocab=42f03735
-/
theorem pref_phase_true_odd (xs : List Bool) (k : ℕ) :
    pref (phase true xs) (2 * k + 1) = pref xs (2 * k + 1) := by
  cases xs with
  | nil => simp [phase, pref]
  | cons a xs =>
      rw [phase_true_cons]
      rw [show 2 * k + 1 = 2 * k + 1 by rfl, pref_cons_succ, pref_cons_succ,
        pref_pairPhase_even]

/--
@isnad1 id=eq.1h2v.s7.f0abe61ed71c from=translated src=- shape=b9c5ec77 vocab=b43163c5
-/
theorem pref_phase_true_even (xs : List Bool) (k : ℕ)
    (hk : 2 * k + 2 < xs.length) :
    pref (phase true xs) (2 * k + 2) =
      max (pref xs (2 * k + 1)) (pref xs (2 * k + 3) - 1) := by
  cases xs with
  | nil => simp at hk
  | cons a xs =>
      simp only [List.length_cons] at hk
      have hk' : 2 * k + 1 < xs.length := by omega
      rw [phase_true_cons]
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, pref_cons_succ]
      rw [show 2 * k + 1 = 2 * k + 1 by rfl, pref_pairPhase_odd xs k hk']
      rw [show 2 * k + 1 = 2 * k + 1 by rfl, pref_cons_succ]
      rw [show 2 * k + 3 = (2 * k + 2) + 1 by omega, pref_cons_succ]
      simp only [max_def]
      split <;> split <;> omega

/-- Whether a prefix boundary participates in comparator round q. -/
def active (q i : ℕ) : Bool := decide (i % 2 = (q + 1) % 2)

/-- The comparator layer whose offset alternates with the round number. -/
def phaseN {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) : List α :=
  phase (decide (q % 2 = 1)) xs

/--
@isnad1 id=eq.2h3v.s6.8630edf5e4be from=translated src=- shape=5e59766d vocab=5d4652eb
-/
theorem pref_phaseN (q : ℕ) (xs : List Bool) (i : ℕ)
    (hi0 : 0 < i) (hin : i < xs.length) :
    pref (phaseN q xs) i =
      if active q i then max (pref xs (i - 1)) (pref xs (i + 1) - 1)
      else pref xs i := by
  classical
  have hq : q % 2 = 0 ∨ q % 2 = 1 := by omega
  have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases hq with hq | hq <;> rcases hi with hi | hi
  · have hphase : phaseN q xs = phase false xs := by simp [phaseN, hq]
    have hactive : active q i = false := by simp [active]; omega
    have heq : i = 2 * (i / 2) := by omega
    rw [hphase, hactive]
    simp only [Bool.false_eq_true, ite_false]
    rw [heq]
    exact pref_phase_false_even xs (i / 2)
  · have hphase : phaseN q xs = phase false xs := by simp [phaseN, hq]
    have hactive : active q i = true := by simp [active]; omega
    have heq : i = 2 * (i / 2) + 1 := by omega
    rw [hphase, hactive]
    simp only [ite_true]
    rw [heq]
    rw [show 2 * (i / 2) + 1 - 1 = 2 * (i / 2) by omega]
    rw [show 2 * (i / 2) + 1 + 1 = 2 * (i / 2) + 2 by omega]
    exact pref_phase_false_odd xs (i / 2) (by omega)
  · have hphase : phaseN q xs = phase true xs := by simp [phaseN, hq]
    have hactive : active q i = true := by simp [active]; omega
    have heq : i = 2 * ((i - 2) / 2) + 2 := by omega
    rw [hphase, hactive]
    simp only [ite_true]
    rw [heq]
    rw [show 2 * ((i - 2) / 2) + 2 - 1 = 2 * ((i - 2) / 2) + 1 by omega]
    rw [show 2 * ((i - 2) / 2) + 2 + 1 = 2 * ((i - 2) / 2) + 3 by omega]
    exact pref_phase_true_even xs ((i - 2) / 2) (by omega)
  · have hphase : phaseN q xs = phase true xs := by simp [phaseN, hq]
    have hactive : active q i = false := by simp [active]; omega
    have heq : i = 2 * (i / 2) + 1 := by omega
    rw [hphase, hactive]
    simp only [Bool.false_eq_true, ite_false]
    rw [heq]
    exact pref_phase_true_odd xs (i / 2)

/-- The total number of true bits in a Boolean list. -/
def countTrue (xs : List Bool) : ℕ := xs.count true

/--
@isnad1 id=eq.0h1v.s3.69433e215d6a from=translated src=- shape=83723a48 vocab=98444514
-/
@[simp] theorem countTrue_pairPhase (xs : List Bool) :
    countTrue (pairPhase xs) = countTrue xs := by
  induction xs using pairPhase.induct with
  | case1 a b xs ih => cases a <;> cases b <;> simp_all [countTrue, pairPhase]
  | case2 xs h =>
      cases xs with
      | nil => rfl
      | cons a xs =>
          cases xs with
          | nil => rfl
          | cons b xs => exact (h a b xs rfl).elim

/--
@isnad1 id=eq.0h2v.s3.e0c86f66f5ed from=translated src=- shape=d24e0e71 vocab=17218587
-/
@[simp] theorem countTrue_phase (p : Bool) (xs : List Bool) :
    countTrue (phase p xs) = countTrue xs := by
  cases p with
  | false => exact countTrue_pairPhase xs
  | true =>
      cases xs with
      | nil => rfl
      | cons a xs =>
          change (a :: pairPhase xs).count true = (a :: xs).count true
          have h := countTrue_pairPhase xs
          unfold countTrue at h
          simp only [List.count_cons]
          rw [h]

/--
@isnad1 id=eq.0h2v.s3.e323cc8e8fff from=translated src=- shape=0701bb2a vocab=5cb37734
-/
@[simp] theorem countTrue_phaseN (q : ℕ) (xs : List Bool) :
    countTrue (phaseN q xs) = countTrue xs := by
  simp [phaseN]

/-- Iterate alternating comparator layers starting with round q. -/
def evolve {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) : ℕ → List α
  | 0 => xs
  | t + 1 => phaseN (q + t) (evolve q xs t)

/--
@isnad1 id=eq.0h3v.s4.77aa84116768 from=translated src=- shape=d0c1057c vocab=8e7c9e3b
-/
@[simp] theorem evolve_zero {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) :
    evolve q xs 0 = xs := rfl

/--
@isnad1 id=eq.0h4v.s5.3382b06d9bbb from=translated src=- shape=6192cf7d vocab=7913fd75
-/
@[simp] theorem evolve_succ {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) (t : ℕ) :
    evolve q xs (t + 1) = phaseN (q + t) (evolve q xs t) := rfl

/--
@isnad1 id=eq.0h3v.s4.c7abe7a0a38f from=translated src=- shape=bcfc0bf9 vocab=98bc42ae
-/
@[simp] theorem length_phaseN {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) :
    (phaseN q xs).length = xs.length := by simp [phaseN]

/--
@isnad1 id=eq.0h4v.s4.c2e2bba98fed from=translated src=- shape=0a8e590b vocab=9d86be8c
-/
@[simp] theorem length_evolve {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) (t : ℕ) :
    (evolve q xs t).length = xs.length := by
  induction t with
  | zero => rfl
  | succ t ih => simp [evolve, ih]

/--
@isnad1 id=eq.0h3v.s4.d72f66226af6 from=translated src=- shape=7c23ebe2 vocab=464200d6
-/
@[simp] theorem countTrue_evolve (q : ℕ) (xs : List Bool) (t : ℕ) :
    countTrue (evolve q xs t) = countTrue xs := by
  induction t with
  | zero => rfl
  | succ t ih => simp [evolve, ih]

/-- Prefix count in the sorted Boolean word with `z` zeroes. -/
def low (z i : ℕ) : ℤ := max 0 ((i : ℤ) - (z : ℤ))

/-- The potential used to rule out a bad prefix surviving all layers. -/
def potential (z i : ℕ) (h : ℤ) : ℤ :=
  if i ≤ z then (i : ℤ) - 2 * h else 2 * (z : ℤ) - (i : ℤ) - 2 * h

/-- A positive excess of the prefix count above its sorted lower bound. -/
def Bad (z : ℕ) (xs : List Bool) (i : ℕ) (h : ℤ) : Prop :=
  1 ≤ h ∧ low z i + h ≤ pref xs i

/--
@isnad1 id=le.0h2v.s3.37e64c1ca712 from=translated src=- shape=c8f743ec vocab=d3b62fa6
-/
theorem pref_le_index (xs : List Bool) (i : ℕ) : pref xs i ≤ i := by
  unfold pref
  have h := List.count_le_length (a := true) (l := xs.take i)
  have ht := List.length_take_le i xs
  omega

/--
@isnad1 id=le.0h2v.s4.a44543cfdbb6 from=translated src=- shape=8410fc4d vocab=62ced51c
-/
theorem pref_le_total (xs : List Bool) (i : ℕ) : pref xs i ≤ countTrue xs := by
  unfold pref countTrue
  exact_mod_cast (List.take_sublist i xs).count_le true

/--
@isnad1 id=eq.0h1v.s3.254ca1232f4e from=translated src=- shape=796988c2 vocab=18ca7bc8
-/
theorem pref_at_length (xs : List Bool) : pref xs xs.length = countTrue xs := by
  simp [pref, countTrue]

/--
@isnad1 id=le.3h4v.s5.c00d75331de4 from=translated src=- shape=aaf64ba2 vocab=051aa5fe
-/
theorem pref_lower (xs : List Bool) (z r i : ℕ)
    (hlen : xs.length = r + z) (hcount : countTrue xs = r) (hi : i ≤ xs.length) :
    low z i ≤ pref xs i := by
  have hsplit : xs.take i ++ xs.drop i = xs := List.take_append_drop i xs
  have hc : (xs.take i).count true + (xs.drop i).count true = xs.count true := by
    simpa only [List.count_append] using congrArg (List.count true) hsplit
  have hd := List.count_le_length (a := true) (l := xs.drop i)
  have hdl : (xs.drop i).length = xs.length - i := List.length_drop
  unfold low pref countTrue at *
  simp only [max_def]
  split <;> omega

/--
@isnad1 id=le.1h3v.s5.872faadb31e6 from=translated src=- shape=c4180d77 vocab=61990626
-/
theorem potential_upper (z i : ℕ) (h : ℤ) (hh : 1 ≤ h) :
    potential z i h ≤ (z : ℤ) - 2 := by
  unfold potential
  split <;> omega

/--
@isnad1 id=le.2h5v.s5.42248c191941 from=translated src=- shape=ae8418b1 vocab=5fe95d5d
-/
theorem potential_lower_of_initial_bad (xs : List Bool) (z r i : ℕ) (h : ℤ)
    (hcount : countTrue xs = r) (hb : Bad z xs i h) :
    -(r : ℤ) ≤ potential z i h := by
  have hpi := pref_le_index xs i
  have hpr := pref_le_total xs i
  unfold Bad at hb
  unfold low at hb
  unfold potential
  rcases hb with ⟨hh, hb⟩
  simp only [max_def] at hb
  split at hb <;> split <;> omega

/--
@isnad1 id=eq.1h3v.s6.271a7f8c0279 from=translated src=- shape=af6f280a vocab=0fb74b13
-/
theorem potential_left (z i : ℕ) (h : ℤ) (hi : 0 < i) :
    potential z (i - 1) (h + low z i - low z (i - 1)) = potential z i h - 1 := by
  unfold potential low
  simp only [max_def]
  split <;> split <;> split <;> split <;> omega

/--
@isnad1 id=eq.0h3v.s6.9b02d91ae794 from=translated src=- shape=65ae61fa vocab=0b00f990
-/
theorem potential_right (z i : ℕ) (h : ℤ) :
    potential z (i + 1) (h + 1 + low z i - low z (i + 1)) = potential z i h - 1 := by
  unfold potential low
  simp only [max_def]
  split <;> split <;> split <;> split <;> omega

/--
@isnad1 id=not.0h3v.s4.344c0f8814fe from=translated src=- shape=0778d082 vocab=c80a701c
-/
theorem not_bad_zero (z : ℕ) (xs : List Bool) (h : ℤ) : ¬Bad z xs 0 h := by
  unfold Bad low
  simp
  omega

/--
@isnad1 id=not.2h4v.s5.0f5493afca9b from=translated src=- shape=d651b755 vocab=4c8458f5
-/
theorem not_bad_length (z r : ℕ) (xs : List Bool) (h : ℤ)
    (hlen : xs.length = r + z) (hcount : countTrue xs = r) :
    ¬Bad z xs xs.length h := by
  intro hb
  have hp := pref_at_length xs
  unfold Bad low at hb
  rcases hb with ⟨hh, hb⟩
  simp only [max_def] at hb
  split at hb <;> omega

/--
@isnad1 id=ex.6h6v.s7.6acf911c9779 from=translated src=- shape=480111f3 vocab=e1254eaa
-/
theorem bad_predecessor (z r q i : ℕ) (xs : List Bool) (h : ℤ)
    (hlen : xs.length = r + z) (hcount : countTrue xs = r)
    (hi0 : 0 < i) (hin : i < xs.length) (hact : active q i = true)
    (hb : Bad z (phaseN q xs) i h) :
    ∃ j : ℕ, ∃ h' : ℤ,
      (j = i - 1 ∨ j = i + 1) ∧ 0 < j ∧ j < xs.length ∧
      Bad z xs j h' ∧ potential z j h' = potential z i h - 1 := by
  have hp := pref_phaseN q xs i hi0 hin
  rw [hact] at hp
  simp only [ite_true] at hp
  unfold Bad at hb
  rw [hp] at hb
  rcases hb with ⟨hh, hb⟩
  by_cases hc : pref xs (i - 1) ≤ pref xs (i + 1) - 1
  · have hbR : low z i + h ≤ pref xs (i + 1) - 1 := by
      simpa [max_eq_right hc] using hb
    let h' : ℤ := h + 1 + low z i - low z (i + 1)
    have hh' : 1 ≤ h' := by
      dsimp [h']
      unfold low
      simp only [max_def]
      split <;> split <;> omega
    have hbad : Bad z xs (i + 1) h' := by
      refine ⟨hh', ?_⟩
      dsimp [h']
      omega
    have hjlt : i + 1 < xs.length := by
      by_contra hn
      have heq : i + 1 = xs.length := by omega
      exact not_bad_length z r xs h' hlen hcount (heq ▸ hbad)
    exact ⟨i + 1, h', Or.inr rfl, by omega, hjlt, hbad, potential_right z i h⟩
  · have hbL : low z i + h ≤ pref xs (i - 1) := by
      simpa [max_eq_left (le_of_not_ge hc)] using hb
    let h' : ℤ := h + low z i - low z (i - 1)
    have hh' : 1 ≤ h' := by
      dsimp [h']
      unfold low
      simp only [max_def]
      split <;> split <;> omega
    have hbad : Bad z xs (i - 1) h' := by
      refine ⟨hh', ?_⟩
      dsimp [h']
      omega
    have hjpos : 0 < i - 1 := by
      by_contra hn
      have heq : i - 1 = 0 := by omega
      exact not_bad_zero z xs h' (heq ▸ hbad)
    exact ⟨i - 1, h', Or.inl rfl, hjpos, by omega, hbad, potential_left z i h hi0⟩

/--
@isnad1 id=eq.4h3v.s6.7eed0eed7541 from=translated src=- shape=d4c06cb6 vocab=4332509c
-/
theorem active_previous_neighbor (q i j : ℕ) (hq : 0 < q) (hi0 : 0 < i)
    (hi : active q i = true) (hj : j = i - 1 ∨ j = i + 1) :
    active (q - 1) j = true := by
  unfold active at hi ⊢
  simp only [decide_eq_true_eq] at hi ⊢
  rw [show q - 1 + 1 = q by omega]
  rcases hj with rfl | rfl <;> omega

/--
@isnad1 id=eq.2h2v.s5.29fc3cf6e6e9 from=translated src=- shape=68dd5c11 vocab=e32b808f
-/
theorem active_previous_same (q i : ℕ) (hq : 0 < q)
    (hi : active q i = false) : active (q - 1) i = true := by
  unfold active at hi ⊢
  simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hi ⊢
  rw [show q - 1 + 1 = q by omega]
  omega

/--
@isnad1 id=ex.5h7v.s7.500bd779a9f0 from=translated src=- shape=298b740d vocab=be16c75a
-/
theorem trace_bad_active (z r q : ℕ) (xs : List Bool) (t i : ℕ) (h : ℤ)
    (hlen : xs.length = r + z) (hcount : countTrue xs = r) (ht : 0 < t)
    (hact : active (q + t - 1) i = true)
    (hb : Bad z (evolve q xs t) i h) :
    ∃ j : ℕ, ∃ h' : ℤ,
      0 < j ∧ j < xs.length ∧ Bad z xs j h' ∧
      potential z j h' = potential z i h - t := by
  induction t generalizing i h with
  | zero => omega
  | succ t ih =>
      have hphase : q + (t + 1) - 1 = q + t := by omega
      rw [hphase] at hact
      have hi0 : 0 < i := by
        by_contra hn
        have hi : i = 0 := by omega
        have := not_bad_zero z (evolve q xs (t + 1)) h
        exact this (hi ▸ hb)
      have hin : i < (evolve q xs t).length := by
        by_contra hn
        have hle : (evolve q xs t).length ≤ i := by omega
        have hpref := pref_le_total (evolve q xs (t + 1)) i
        have hc : countTrue (evolve q xs (t + 1)) = r := by simpa using hcount
        have hl : (evolve q xs t).length = r + z := by simpa using hlen
        unfold Bad at hb
        unfold low at hb
        rcases hb with ⟨hh, hb⟩
        simp only [max_def] at hb
        split at hb <;> omega
      have hbPhase : Bad z (phaseN (q + t) (evolve q xs t)) i h := by
        simpa [evolve] using hb
      obtain ⟨j, h', hj, hj0, hjn, hb', hpot⟩ :=
        bad_predecessor z r (q + t) i (evolve q xs t) h
          (by simpa using hlen) (by simpa using hcount) hi0 hin hact hbPhase
      by_cases ht0 : t = 0
      · subst t
        refine ⟨j, h', ?_, ?_, ?_, ?_⟩
        · exact hj0
        · simpa using hjn
        · simpa using hb'
        · simpa using hpot
      · have htpos : 0 < t := by omega
        have hprev : active (q + t - 1) j = true := by
          exact active_previous_neighbor (q + t) i j (by omega) hi0 hact hj
        obtain ⟨j0, h0, hj00, hj0n, hb0, hpot0⟩ :=
          ih j h' htpos hprev hb'
        refine ⟨j0, h0, hj00, hj0n, hb0, ?_⟩
        rw [hpot0, hpot]
        push_cast
        omega

/--
@isnad1 id=eq.3h5v.s5.c28be2fac68c from=translated src=- shape=0c4545dc vocab=a25e742c
-/
theorem pref_evolve_full (z r q : ℕ) (xs : List Bool)
    (hlen : xs.length = r + z) (hcount : countTrue xs = r)
    (i : ℕ) (hi : i ≤ xs.length) :
    pref (evolve q xs (r + z)) i = low z i := by
  have hlower : low z i ≤ pref (evolve q xs (r + z)) i :=
    pref_lower (evolve q xs (r + z)) z r i (by simpa using hlen) (by simpa using hcount) (by simpa)
  apply le_antisymm ?_ hlower
  by_contra hnle
  have hstrict : low z i < pref (evolve q xs (r + z)) i := by omega
  let h : ℤ := pref (evolve q xs (r + z)) i - low z i
  have hh : 1 ≤ h := by dsimp [h]; omega
  have hb : Bad z (evolve q xs (r + z)) i h := by
    refine ⟨hh, ?_⟩
    dsimp [h]
    omega
  have hi0 : 0 < i := by
    by_contra hz
    have : i = 0 := by omega
    exact not_bad_zero z (evolve q xs (r + z)) h (this ▸ hb)
  have hin : i < xs.length := by
    by_contra hni
    have : i = xs.length := by omega
    have heql : i = (evolve q xs (r + z)).length := by simpa using this
    exact not_bad_length z r (evolve q xs (r + z)) h
      (by simpa using hlen) (by simpa using hcount) (heql ▸ hb)
  have hnpos : 0 < r + z := by omega
  by_cases hact : active (q + (r + z) - 1) i = true
  · obtain ⟨j, h', hj0, hjn, hbad, hpot⟩ :=
      trace_bad_active z r q xs (r + z) i h hlen hcount hnpos hact hb
    have hlo := potential_lower_of_initial_bad xs z r j h' hcount hbad
    have hup := potential_upper z i h hh
    push_cast at hpot
    omega
  · have hactFalse : active (q + (r + z) - 1) i = false := by
      cases ha : active (q + (r + z) - 1) i <;> simp_all
    have htwo : 2 ≤ r + z := by omega
    have htpos : 0 < r + z - 1 := by omega
    have hevolve : evolve q xs (r + z) =
        phaseN (q + (r + z - 1)) (evolve q xs (r + z - 1)) := by
      rw [show r + z = (r + z - 1) + 1 by omega, evolve_succ]
      congr 2
    have hp := pref_phaseN (q + (r + z - 1)) (evolve q xs (r + z - 1)) i
      (by omega) (by simpa using hin)
    have hindex : q + (r + z - 1) = q + (r + z) - 1 := by omega
    have hactSmall : active (q + (r + z - 1)) i = false := by
      rw [hindex]
      exact hactFalse
    rw [hactSmall] at hp
    simp only [Bool.false_eq_true, ite_false] at hp
    have hbPrev : Bad z (evolve q xs (r + z - 1)) i h := by
      rw [hevolve] at hb
      unfold Bad at hb ⊢
      rw [hp] at hb
      exact hb
    have hlastpos : 0 < q + (r + z) - 1 := by omega
    have hprev0 := active_previous_same (q + (r + z) - 1) i hlastpos hactFalse
    have hprev : active (q + (r + z - 1) - 1) i = true := by
      rw [show q + (r + z - 1) - 1 = (q + (r + z) - 1) - 1 by omega]
      exact hprev0
    obtain ⟨j, h', hj0, hjn, hbad, hpot⟩ :=
      trace_bad_active z r q xs (r + z - 1) i h hlen hcount htpos hprev hbPrev
    have hlo := potential_lower_of_initial_bad xs z r j h' hcount hbad
    have hup := potential_upper z i h hh
    omega

/-- The monotone Boolean threshold used in the zero-one sorting argument. -/
def threshold {α : Type*} [LinearOrder α] (a x : α) : Bool := decide (a ≤ x)

/--
@isnad1 id=eq.0h4v.s5.ed743c864adc from=translated src=- shape=7213597b vocab=9089e789
-/
theorem threshold_min {α : Type*} [LinearOrder α] (a x y : α) :
    threshold a (min x y) = min (threshold a x) (threshold a y) := by
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy]
    by_cases hx : a ≤ x
    · have hy : a ≤ y := hx.trans hxy
      simp [threshold, hx, hy]
    · by_cases hy : a ≤ y <;> simp [threshold, hx, hy]
  · rw [min_eq_right hyx]
    by_cases hy : a ≤ y
    · have hx : a ≤ x := hy.trans hyx
      simp [threshold, hx, hy]
    · by_cases hx : a ≤ x <;> simp [threshold, hx, hy]

/--
@isnad1 id=eq.0h4v.s5.c2c71925306e from=translated src=- shape=7213597b vocab=4bf50706
-/
theorem threshold_max {α : Type*} [LinearOrder α] (a x y : α) :
    threshold a (max x y) = max (threshold a x) (threshold a y) := by
  rcases le_total x y with hxy | hyx
  · rw [max_eq_right hxy]
    by_cases hy : a ≤ y
    · by_cases hx : a ≤ x <;> simp [threshold, hx, hy]
    · have hx : ¬a ≤ x := fun hx ↦ hy (hx.trans hxy)
      simp [threshold, hx, hy]
  · rw [max_eq_left hyx]
    by_cases hx : a ≤ x
    · by_cases hy : a ≤ y <;> simp [threshold, hx, hy]
    · have hy : ¬a ≤ y := fun hy ↦ hx (hy.trans hyx)
      simp [threshold, hx, hy]

/--
@isnad1 id=eq.0h3v.s5.3e94f1f1bb86 from=translated src=- shape=d4710eee vocab=b026b986
-/
theorem map_threshold_pairPhase {α : Type*} [LinearOrder α] (a : α) (xs : List α) :
    (pairPhase xs).map (threshold a) = pairPhase (xs.map (threshold a)) := by
  induction xs using pairPhase.induct with
  | case1 x y xs ih => simp [pairPhase, ih, threshold_min, threshold_max]
  | case2 xs h =>
      cases xs with
      | nil => rfl
      | cons x xs =>
          cases xs with
          | nil => rfl
          | cons y xs => exact (h x y xs rfl).elim

/--
@isnad1 id=eq.0h4v.s5.63d12746b3ff from=translated src=- shape=5f31a146 vocab=f3424618
-/
theorem map_threshold_phase {α : Type*} [LinearOrder α]
    (a : α) (p : Bool) (xs : List α) :
    (phase p xs).map (threshold a) = phase p (xs.map (threshold a)) := by
  cases p with
  | false => exact map_threshold_pairPhase a xs
  | true =>
      cases xs with
      | nil => rfl
      | cons x xs => simp [phase, map_threshold_pairPhase]

/--
@isnad1 id=eq.0h4v.s5.d2674ed0fd7a from=translated src=- shape=b2712589 vocab=ad417818
-/
theorem map_threshold_phaseN {α : Type*} [LinearOrder α]
    (a : α) (q : ℕ) (xs : List α) :
    (phaseN q xs).map (threshold a) = phaseN q (xs.map (threshold a)) := by
  exact map_threshold_phase a _ xs

/--
@isnad1 id=eq.0h5v.s5.dd39cd38a9dd from=translated src=- shape=4b18e49b vocab=3bf0f418
-/
theorem map_threshold_evolve {α : Type*} [LinearOrder α]
    (a : α) (q t : ℕ) (xs : List α) :
    (evolve q xs t).map (threshold a) = evolve q (xs.map (threshold a)) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [evolve, map_threshold_phaseN, ih]

/--
@isnad1 id=eq.1h2v.s5.6e64353731dc from=translated src=- shape=8a83f05b vocab=303a8ffa
-/
theorem pref_succ (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    pref xs (i + 1) = pref xs i + bitInt xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => cases x <;> simp [pref, bitInt]
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          have h := ih i hi'
          rw [show i + 1 + 1 = (i + 1) + 1 by rfl, pref_cons_succ, pref_cons_succ]
          simpa [List.getElem_cons_succ, add_assoc] using congrArg (fun z : ℤ ↦ bitInt x + z) h

/--
@isnad1 id=eq.3h5v.s6.46c11b52b94b from=translated src=- shape=6f459cd7 vocab=7dc8bc86
-/
theorem bool_getElem_of_pref_full (z r q : ℕ) (xs : List Bool)
    (hlen : xs.length = r + z) (hcount : countTrue xs = r)
    (i : ℕ) (hi : i < xs.length) :
    (evolve q xs (r + z))[i]'(by simpa using hi) = decide (z ≤ i) := by
  let ys := evolve q xs (r + z)
  have hiy : i < ys.length := by simpa [ys] using hi
  have hp0 := pref_evolve_full z r q xs hlen hcount i (by omega)
  have hp1 := pref_evolve_full z r q xs hlen hcount (i + 1) (by omega)
  have hs := pref_succ ys i hiy
  have hbit : bitInt (ys[i]'hiy) = low z (i + 1) - low z i := by
    have hp0' : pref ys i = low z i := by simpa [ys] using hp0
    have hp1' : pref ys (i + 1) = low z (i + 1) := by simpa [ys] using hp1
    rw [hp0', hp1'] at hs
    omega
  by_cases hz : z ≤ i
  · have : bitInt (ys[i]'hiy) = 1 := by
      rw [hbit]
      unfold low
      simp only [max_def]
      split <;> split <;> omega
    cases hval : ys[i]'hiy <;> simp_all [bitInt, ys]
  · have : bitInt (ys[i]'hiy) = 0 := by
      rw [hbit]
      unfold low
      simp only [max_def]
      split <;> split <;> omega
    cases hval : ys[i]'hiy <;> simp_all [bitInt, ys]

/--
@isnad1 id=eq.0h3v.s4.1b50dcd3929d from=translated src=- shape=5e6bd8a6 vocab=b5a2756c
-/
theorem countTrue_map_threshold {α : Type*} [LinearOrder α] (a : α) (xs : List α) :
    countTrue (xs.map (threshold a)) = (xs.filter (threshold a)).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      unfold countTrue at ih ⊢
      by_cases hx : a ≤ x <;> simp [threshold, hx, ih]

/--
@isnad1 id=eq.0h2v.s4.74f6a923a2e7 from=translated src=- shape=0b2700ab vocab=c5f80da7
-/
theorem countTrue_map_threshold_finRange {n : ℕ} (a : Fin n) :
    countTrue ((List.finRange n).map (threshold a)) = n - a.val := by
  rw [countTrue_map_threshold]
  have hn : ((List.finRange n).filter (threshold a)).Nodup :=
    (List.nodup_finRange n).filter _
  rw [← List.toFinset_card_of_nodup hn]
  rw [List.toFinset_filter, List.toFinset_finRange]
  have heq : ({x : Fin n | threshold a x = true} : Finset (Fin n)) = Finset.Ici a := by
    ext x
    simp [threshold]
  rw [heq, Fin.card_Ici]

/--
@isnad1 id=eq.1h3v.s5.3de48a9d3a51 from=translated src=- shape=a67c5a58 vocab=9eca4fa1
-/
theorem countTrue_map_threshold_of_perm_finRange {n : ℕ} (a : Fin n)
    (xs : List (Fin n)) (hp : xs.Perm (List.finRange n)) :
    countTrue (xs.map (threshold a)) = n - a.val := by
  rw [countTrue_map_threshold]
  rw [(hp.filter (threshold a)).length_eq]
  rw [← countTrue_map_threshold]
  exact countTrue_map_threshold_finRange a

/--
@isnad1 id=eq.2h5v.s6.95c1645b70a3 from=translated src=- shape=5b05faf2 vocab=f0688112
-/
theorem threshold_evolve_perm_finRange {n : ℕ} (xs : List (Fin n))
    (hp : xs.Perm (List.finRange n)) (q : ℕ) (a : Fin n) (i : ℕ)
    (hi : i < n) :
    threshold a ((evolve q xs n)[i]'(by
      have hl : xs.length = n := by simpa using hp.length_eq
      simpa [hl] using hi)) =
      decide (a.val ≤ i) := by
  let bs := xs.map (threshold a)
  have hlenxs : xs.length = n := by simpa using hp.length_eq
  have hlenbs : bs.length = n := by simp [bs, hlenxs]
  have hcountbs : countTrue bs = n - a.val := by
    dsimp [bs]
    exact countTrue_map_threshold_of_perm_finRange a xs hp
  have hsum : (n - a.val) + a.val = n := by omega
  have hb := bool_getElem_of_pref_full a.val (n - a.val) q bs
    (by omega) hcountbs i (by omega)
  simp only [hsum] at hb
  dsimp [bs] at hb
  have hmap := map_threshold_evolve a q n xs
  have hie : i < (evolve q xs n).length := by simpa [hlenxs] using hi
  have hib : i < (evolve q (xs.map (threshold a)) n).length := by simp [hlenxs, hi]
  have hbOpt : (evolve q (xs.map (threshold a)) n)[i]? = some (decide (a.val ≤ i)) := by
    rw [List.getElem?_eq_getElem hib]
    exact congrArg some hb
  have hmapAt := congrArg (fun l : List Bool ↦ l[i]?) hmap
  have houtOpt : ((evolve q xs n).map (threshold a))[i]? =
      some (threshold a ((evolve q xs n)[i]'hie)) := by
    simp [List.getElem?_map, List.getElem?_eq_getElem hie]
  have hsome : some (threshold a ((evolve q xs n)[i]'hie)) =
      some (decide (a.val ≤ i)) := by
    rw [← houtOpt, hmapAt, hbOpt]
  exact Option.some.inj hsome

/--
@isnad1 id=eq.1h3v.s4.81206d30bdde from=translated src=- shape=47c43ccb vocab=ae825a68
-/
theorem evolve_perm_finRange_eq {n : ℕ} (xs : List (Fin n))
    (hp : xs.Perm (List.finRange n)) (q : ℕ) :
    evolve q xs n = List.finRange n := by
  apply List.ext_getElem (by simpa using hp.length_eq)
  intro i hi1 hi2
  have hi : i < n := by simpa using hi2
  let y : Fin n := (evolve q xs n)[i]'hi1
  have hy := threshold_evolve_perm_finRange xs hp q y i hi
  have hk := threshold_evolve_perm_finRange xs hp q (⟨i, hi⟩ : Fin n) i hi
  have hy_le : y.val ≤ i := by
    change threshold y y = decide (y.val ≤ i) at hy
    simpa [threshold] using hy
  have hi_le : i ≤ y.val := by
    change threshold (⟨i, hi⟩ : Fin n) y = decide (i ≤ i) at hk
    have hk' : (⟨i, hi⟩ : Fin n) ≤ y := by simpa [threshold] using hk
    change i ≤ y.val at hk'
    exact hk'
  have hyval : y = (⟨i, hi⟩ : Fin n) := Fin.ext (Nat.le_antisymm hy_le hi_le)
  change y = (List.finRange n)[i]
  rw [hyval]
  apply Fin.ext
  simp

/--
@isnad1 id=perm.0h4v.s5.4ac8d2bf757e from=translated src=- shape=17a108ad vocab=854d3578
-/
theorem pair_minmax_perm {α : Type*} [LinearOrder α] (a b : α) (xs : List α) :
    (min a b :: max a b :: xs).Perm (a :: b :: xs) := by
  by_cases h : a ≤ b
  · simp [min_eq_left h, max_eq_right h]
  · have h' : b ≤ a := le_of_not_ge h
    simpa [min_eq_right h', max_eq_left h'] using List.Perm.swap a b xs

/--
@isnad1 id=perm.0h2v.s3.8c25a4270d78 from=translated src=- shape=903e385d vocab=98ce2e57
-/
@[simp] theorem pairPhase_perm {α : Type*} [LinearOrder α] (xs : List α) :
    (pairPhase xs).Perm xs := by
  induction xs using pairPhase.induct with
  | case1 a b xs ih =>
      exact ((ih.cons (max a b)).cons (min a b)).trans (pair_minmax_perm a b xs)
  | case2 xs h =>
      cases xs with
      | nil => exact .refl _
      | cons a xs =>
          cases xs with
          | nil => exact .refl _
          | cons b xs => exact (h a b xs rfl).elim

/--
@isnad1 id=perm.0h3v.s4.652da4e35de7 from=translated src=- shape=4268aa99 vocab=649e7a8d
-/
@[simp] theorem phase_perm {α : Type*} [LinearOrder α] (p : Bool) (xs : List α) :
    (phase p xs).Perm xs := by
  cases p with
  | false => exact pairPhase_perm xs
  | true =>
      cases xs with
      | nil => exact .refl _
      | cons a xs => exact (pairPhase_perm xs).cons a

/--
@isnad1 id=perm.0h3v.s4.84882707e83c from=translated src=- shape=4268aa99 vocab=bd1f0c99
-/
@[simp] theorem phaseN_perm {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) :
    (phaseN q xs).Perm xs := phase_perm _ xs

/--
@isnad1 id=perm.0h4v.s4.bf4243964061 from=translated src=- shape=08c406ba vocab=e4a97790
-/
@[simp] theorem evolve_perm {α : Type*} [LinearOrder α] (q t : ℕ) (xs : List α) :
    (evolve q xs t).Perm xs := by
  induction t with
  | zero => exact .refl _
  | succ t ih => exact (phaseN_perm _ _).trans ih

/--
@isnad1 id=perm.0h3v.s5.d018e0a7ca2e from=translated src=- shape=2817aa36 vocab=f13f21d5
-/
theorem take_pairPhase_even_perm {α : Type*} [LinearOrder α]
    (xs : List α) (k : ℕ) :
    ((pairPhase xs).take (2 * k)).Perm (xs.take (2 * k)) := by
  induction k generalizing xs with
  | zero => exact .refl _
  | succ k ih =>
      cases xs with
      | nil => exact .refl _
      | cons a xs =>
          cases xs with
          | nil => exact .refl _
          | cons b xs =>
              simp only [pairPhase_cons_cons]
              rw [show 2 * (k + 1) = 2 * k + 2 by omega]
              simp only [List.take_succ_cons]
              exact (((ih xs).cons (max a b)).cons (min a b)).trans
                (pair_minmax_perm a b (xs.take (2 * k)))

/--
@isnad1 id=perm.0h3v.s5.0a2710f641b8 from=translated src=- shape=24299b39 vocab=7f60d11b
-/
theorem take_phase_false_even_perm {α : Type*} [LinearOrder α]
    (xs : List α) (k : ℕ) :
    ((phase false xs).take (2 * k)).Perm (xs.take (2 * k)) :=
  take_pairPhase_even_perm xs k

/--
@isnad1 id=perm.0h3v.s6.3d252f117dcf from=translated src=- shape=995ef80f vocab=cdef961f
-/
theorem take_phase_true_odd_perm {α : Type*} [LinearOrder α]
    (xs : List α) (k : ℕ) :
    ((phase true xs).take (2 * k + 1)).Perm (xs.take (2 * k + 1)) := by
  cases xs with
  | nil => exact .refl _
  | cons a xs =>
      rw [phase_true_cons]
      rw [show 2 * k + 1 = 2 * k + 1 by rfl]
      simp only [List.take_succ_cons]
      exact (take_pairPhase_even_perm xs k).cons a

/--
@isnad1 id=perm.1h4v.s5.530d615cf648 from=translated src=- shape=916044f7 vocab=8c045ca8
-/
theorem take_phaseN_perm_of_inactive {α : Type*} [LinearOrder α]
    (q : ℕ) (xs : List α) (i : ℕ) (hact : active q i = false) :
    ((phaseN q xs).take i).Perm (xs.take i) := by
  have hq : q % 2 = 0 ∨ q % 2 = 1 := by omega
  have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases hq with hq | hq <;> rcases hi with hi | hi
  · have hphase : phaseN q xs = phase false xs := by simp [phaseN, hq]
    have heq : i = 2 * (i / 2) := by omega
    rw [hphase, heq]
    exact take_phase_false_even_perm xs (i / 2)
  · exfalso
    unfold active at hact
    simp only [decide_eq_false_iff_not] at hact
    omega
  · exfalso
    unfold active at hact
    simp only [decide_eq_false_iff_not] at hact
    omega
  · have hphase : phaseN q xs = phase true xs := by simp [phaseN, hq]
    have heq : i = 2 * (i / 2) + 1 := by omega
    rw [hphase, heq]
    exact take_phase_true_odd_perm xs (i / 2)

/-- The permutation whose one-line notation is `l`. -/
noncomputable def permOfList {n : ℕ} (l : List (Fin n))
    (hp : l.Perm (List.finRange n)) : Equiv.Perm (Fin n) := by
  let hlen : l.length = n := by simpa using hp.length_eq
  exact (finCongr hlen.symm).trans
    (List.Nodup.getEquivOfForallMemList l
      (hp.nodup_iff.mpr (List.nodup_finRange n))
      (fun x ↦ (hp.mem_iff).2 (List.mem_finRange x)))

/--
@isnad1 id=eq.1h3v.s6.9d353b4eea7e from=translated src=- shape=b244b870 vocab=ec7a15c4
-/
theorem permOfList_apply {n : ℕ} (l : List (Fin n))
    (hp : l.Perm (List.finRange n)) (i : Fin n) :
    permOfList l hp i = l[i.val]'(by
      have hlen : l.length = n := by simpa using hp.length_eq
      omega) := by
  simp [permOfList, List.Nodup.getEquivOfForallMemList_apply,
    List.get_eq_getElem]

/--
@isnad1 id=eq.0h2v.s5.225e32eef11e from=translated src=- shape=858f2791 vocab=4f47ea54
-/
theorem permOfList_map_finRange {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permOfList ((List.finRange n).map σ) σ.map_finRange_perm = σ := by
  ext i
  rw [permOfList_apply]
  simp

/--
@isnad1 id=eq.0h1v.s3.d4a0b0c1abd2 from=translated src=- shape=516f6ed4 vocab=0d673def
-/
theorem permOfList_finRange {n : ℕ} :
    permOfList (List.finRange n) (.refl _) = Equiv.refl _ := by
  simpa using permOfList_map_finRange (Equiv.refl (Fin n))

/-- The image of an initial rank segment under a permutation. -/
def PrefixSet2 {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin (n + 1)) : Set (Fin n) :=
  σ '' {j | j.castSucc < i}

/-- A layer preserves prefix sets at every inactive rank. -/
def OrderingStep2 {n : ℕ} (s : Fin n)
    (σ τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin (n + 1), i.val % 2 ≠ (s.val + 1) % 2 → PrefixSet2 σ i = PrefixSet2 τ i

/--
@isnad1 id=iff.1h4v.s6.6a4f12a575dd from=translated src=- shape=60182927 vocab=fd743fc6
-/
theorem mem_PrefixSet2_permOfList_iff {n : ℕ} (l : List (Fin n))
    (hp : l.Perm (List.finRange n)) (i : Fin (n + 1)) (x : Fin n) :
    x ∈ PrefixSet2 (permOfList l hp) i ↔ x ∈ l.take i.val := by
  have hlen : l.length = n := by simpa using hp.length_eq
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [List.mem_take_iff_getElem]
    refine ⟨j.val, ?_, ?_⟩
    · have hji : j.val < i.val := hj
      omega
    · exact permOfList_apply l hp j
  · intro hx
    rw [List.mem_take_iff_getElem] at hx
    obtain ⟨j, hj, hget⟩ := hx
    have hjn : j < n := by omega
    let jf : Fin n := ⟨j, hjn⟩
    refine ⟨jf, ?_, ?_⟩
    · change j < i.val
      omega
    · rw [permOfList_apply]
      exact hget

/--
@isnad1 id=iff.1h5v.s6.56fef233671d from=translated src=- shape=22872626 vocab=914f00d4
-/
theorem mem_PrefixSet2_trans_permOfList_iff {n : ℕ} (l : List (Fin n))
    (hp : l.Perm (List.finRange n)) (π : Equiv.Perm (Fin n))
    (i : Fin (n + 1)) (x : Fin n) :
    x ∈ PrefixSet2 ((permOfList l hp).trans π) i ↔ π.symm x ∈ l.take i.val := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [← mem_PrefixSet2_permOfList_iff l hp]
    refine ⟨j, hj, ?_⟩
    simp
  · intro hx
    rw [← mem_PrefixSet2_permOfList_iff l hp] at hx
    obtain ⟨j, hj, hget⟩ := hx
    refine ⟨j, hj, ?_⟩
    simp only [Equiv.trans_apply]
    rw [hget]
    simp

/--
@isnad1 id=eq.3h5v.s6.ea2866aa677e from=translated src=- shape=6f659f77 vocab=32948f06
-/
theorem prefixSet2_trans_eq_of_take_perm {n : ℕ}
    (l m : List (Fin n))
    (hl : l.Perm (List.finRange n)) (hm : m.Perm (List.finRange n))
    (π : Equiv.Perm (Fin n)) (i : Fin (n + 1))
    (htake : (l.take i.val).Perm (m.take i.val)) :
    PrefixSet2 ((permOfList l hl).trans π) i =
      PrefixSet2 ((permOfList m hm).trans π) i := by
  ext x
  rw [mem_PrefixSet2_trans_permOfList_iff,
    mem_PrefixSet2_trans_permOfList_iff]
  exact htake.mem_iff

/-- Odd--even transposition routing, in the exact combinatorial form needed
for Lemma 2.1.
@isnad1 id=ex.0h2v.s6.daa4feec4f88 from=translated src=- shape=94f91730 vocab=584d0b50
-/
theorem oddEvenRoute2 {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∃ route : Fin (n + 1) → Equiv.Perm (Fin n),
      route 0 = Equiv.refl _ ∧
      route (Fin.last n) = π ∧
      ∀ s : Fin n, OrderingStep2 s (route s.castSucc) (route s.succ) := by
  classical
  let keys : List (Fin n) := (List.finRange n).map π.symm
  have hkeys : keys.Perm (List.finRange n) := by
    dsimp [keys]
    exact Equiv.Perm.map_finRange_perm π.symm
  have hstate : ∀ t : ℕ, (evolve 0 keys t).Perm (List.finRange n) :=
    fun t ↦ (evolve_perm 0 t keys).trans hkeys
  let route : Fin (n + 1) → Equiv.Perm (Fin n) := fun t ↦
    (permOfList (evolve 0 keys t.val) (hstate t.val)).trans π
  refine ⟨route, ?_, ?_, ?_⟩
  · have hkappa : permOfList (evolve 0 keys 0) (hstate 0) = π.symm := by
      ext i
      rw [permOfList_apply]
      simp [keys]
    change (permOfList (evolve 0 keys 0) (hstate 0)).trans π = Equiv.refl _
    rw [hkappa]
    exact π.symm_trans_self
  · have hsort : evolve 0 keys n = List.finRange n :=
      evolve_perm_finRange_eq keys hkeys 0
    have hkappa : permOfList (evolve 0 keys n) (hstate n) = Equiv.refl _ := by
      ext i
      rw [permOfList_apply]
      simp only [hsort]
      simp
    change (permOfList (evolve 0 keys n) (hstate n)).trans π = π
    rw [hkappa]
    exact Equiv.refl_trans π
  · intro s
    unfold OrderingStep2
    intro i hi
    have hinactive : active s.val i.val = false := by
      unfold active
      simp only [decide_eq_false_iff_not]
      exact hi
    have htake := (take_phaseN_perm_of_inactive s.val
      (evolve 0 keys s.val) i.val hinactive).symm
    change PrefixSet2
        ((permOfList (evolve 0 keys s.val) (hstate s.val)).trans π) i =
      PrefixSet2
        ((permOfList (evolve 0 keys (s.val + 1)) (hstate (s.val + 1))).trans π) i
    apply prefixSet2_trans_eq_of_take_perm
    simpa using htake
end OddEvenSorting

end MooreBound
