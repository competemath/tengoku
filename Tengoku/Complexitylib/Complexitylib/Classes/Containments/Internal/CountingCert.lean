/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Tengoku.Complexitylib.Complexitylib.Classes.Containments.Internal.InductiveCounting
public import Tengoku.Complexitylib.Complexitylib.Classes.Containments.Internal.CodeSearch

/-!
# The certificate Immerman–Szelepcsényi's machine guesses

⚠️ Unreviewed by Bolton

`Complexitylib.Classes.Containments.Internal.InductiveCounting` isolates the counting principle:
a subset of a round as large as the round *is* the round. This file turns that principle into the
shape a machine can verify, which is what stands between it and `NL ⊆ coNL`.

Two things have to be checkable with only logarithmically many bits in hand.

*Membership in a round* becomes a **walk**: a code lies in round `i` exactly when there is a
sequence of `i` steps from the start, each of which either stays put or moves to a successor
(`Complexity.NTM.mem_reachCodes_iff_walk`). A machine verifies such a walk holding only the
current code and the step index — never the walk itself.

*Non-membership* becomes a **round list**: a list of distinct members of the round, at least as
long as the round (`Complexity.NTM.RoundList`). A machine never holds the list either; it guesses
the entries one at a time, checks each against a walk, counts them, and compares the count against
the round's size. `Complexity.NTM.not_mem_of_roundList` is what licenses the negative conclusion,
and `Complexity.NTM.roundList_exists` is what says an honest prover can always supply one.

## Main definitions

- `Complexity.NTM.RoundList` — a list that exhausts a round

## Main results

- `Complexity.NTM.mem_reachCodes_iff_walk` — membership in a round is a walk
- `Complexity.NTM.roundList_exists` — a round can always be listed
- `Complexity.NTM.not_mem_of_roundList`, `Complexity.NTM.mem_of_roundList` — what a list decides
- `Complexity.NTM.card_reachCodes_zero` — the count the machine starts from
- `Complexity.NL_complement_certificate_internal` — the complement as a certificate
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {k : ℕ} {tm : NTM k} {x : List Bool} {S : ℕ}

/-! ## Membership is a walk -/

/-- **Membership in a round is a walk.** A code lies in round `i` exactly when some sequence of
`i` steps from the start reaches it, each step either staying put or moving to a successor. This
is the form a machine verifies: it holds only the current code and the step index.
@isnad1 id=iff.0h7v.s8.9b41f24c2f9b from=translated src=- shape=aacce47b vocab=b2767280
-/
theorem mem_reachCodes_iff_walk (tm : NTM k) (x : List Bool) (S : ℕ)
    (a₀ : Code tm.Q k x.length S) :
    ∀ (i : ℕ) (a : Code tm.Q k x.length S),
      a ∈ reachCodes tm x S a₀ i ↔
        ∃ f : ℕ → Code tm.Q k x.length S, f 0 = a₀ ∧ f i = a ∧
          ∀ j < i, f (j + 1) = f j ∨ f (j + 1) ∈ codeSucc tm x S (f j) := by
  intro i
  induction i with
  | zero =>
      intro a
      constructor
      · intro h
        rw [reachCodes, Finset.mem_singleton] at h
        exact ⟨fun _ => a₀, rfl, h.symm, by omega⟩
      · rintro ⟨f, h0, hi, _⟩
        rw [reachCodes, Finset.mem_singleton, ← hi, ← h0]
  | succ i ih =>
      intro a
      rw [mem_reachCodes_succ_iff]
      constructor
      · intro h
        obtain ⟨b, hb, hstep⟩ : ∃ b ∈ reachCodes tm x S a₀ i,
            a = b ∨ a ∈ codeSucc tm x S b := by
          rcases h with h | ⟨b, hb, hab⟩
          · exact ⟨a, h, Or.inl rfl⟩
          · exact ⟨b, hb, Or.inr hab⟩
        obtain ⟨f, h0, hfi, hf⟩ := (ih b).mp hb
        refine ⟨fun j => if j ≤ i then f j else a, by simp [h0], by simp, fun j hj => ?_⟩
        dsimp only
        rcases Nat.lt_or_ge j i with hlt | hge
        · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
          exact hf j hlt
        · have hji : j = i := by omega
          subst hji
          rw [ite_eq_right (by omega), ite_eq_left (by omega), hfi]
          exact hstep
      · rintro ⟨f, h0, hfi, hf⟩
        have hmem : f i ∈ reachCodes tm x S a₀ i :=
          (ih (f i)).mpr ⟨f, h0, rfl, fun j hj => hf j (by omega)⟩
        rcases hf i (by omega) with h | h
        · exact Or.inl (by rw [← hfi, h]; exact hmem)
        · exact Or.inr ⟨f i, hmem, by rw [← hfi]; exact h⟩

/-! ## A round as a list -/

/-- A list that exhausts a round: distinct members, at least as many as the round has. The
machine never holds such a list — it guesses the entries one at a time and counts them. -/
def RoundList (tm : NTM k) (x : List Bool) (S : ℕ) (a₀ : Code tm.Q k x.length S) (i : ℕ)
    (l : List (Code tm.Q k x.length S)) : Prop :=
  l.Nodup ∧ (∀ a ∈ l, a ∈ reachCodes tm x S a₀ i) ∧
    (reachCodes tm x S a₀ i).card ≤ l.length

/-- **A round can always be listed**, so an honest prover can supply the certificate.
@isnad1 id=ex.0h6v.s5.4f5ec3cdf4fc from=translated src=- shape=bb11d5a5 vocab=4c9a3d14
-/
theorem roundList_exists (tm : NTM k) (x : List Bool) (S : ℕ)
    (a₀ : Code tm.Q k x.length S) (i : ℕ) :
    ∃ l, RoundList tm x S a₀ i l :=
  ⟨(reachCodes tm x S a₀ i).toList, Finset.nodup_toList _,
    fun _ ha => Finset.mem_toList.mp ha, le_of_eq (Finset.length_toList _).symm⟩

open Classical in
/--
@isnad1 id=eq.1h7v.s6.538a7d746e07 from=translated src=- shape=c46174c2 vocab=f6ff3761
-/
theorem roundList_toFinset {a₀ : Code tm.Q k x.length S} {i : ℕ}
    {l : List (Code tm.Q k x.length S)} (h : RoundList tm x S a₀ i l) :
    l.toFinset = reachCodes tm x S a₀ i := by
  classical
  refine eq_reachCodes_of_card_le (fun a ha => h.2.1 a (List.mem_toFinset.mp ha)) ?_
  rw [List.toFinset_card_of_nodup h.1]
  exact h.2.2

open Classical in
/-- **What a round list decides, negatively.** A code absent from a list that exhausts the round
is not in the round — a negative fact, certified by a count.
@isnad1 id=not.2h8v.s7.c9673470406e from=translated src=- shape=553b1049 vocab=2bc193ec
-/
theorem not_mem_of_roundList {a₀ : Code tm.Q k x.length S} {i : ℕ}
    {l : List (Code tm.Q k x.length S)} (h : RoundList tm x S a₀ i l)
    {a : Code tm.Q k x.length S} (ha : a ∉ l) : a ∉ reachCodes tm x S a₀ i := by
  classical
  rw [← roundList_toFinset h, List.mem_toFinset]
  exact ha

open Classical in
/-- And positively: every member of the round appears.
@isnad1 id=mem.2h8v.s7.e1fc9844c4b7 from=translated src=- shape=88e92bd1 vocab=2bc193ec
-/
theorem mem_of_roundList {a₀ : Code tm.Q k x.length S} {i : ℕ}
    {l : List (Code tm.Q k x.length S)} (h : RoundList tm x S a₀ i l)
    {a : Code tm.Q k x.length S} (ha : a ∈ reachCodes tm x S a₀ i) : a ∈ l := by
  classical
  rw [← List.mem_toFinset, roundList_toFinset h]
  exact ha

/-- The list is exactly as long as the round, so the count a machine accumulates is the round's
size.
@isnad1 id=eq.1h7v.s6.572ee9550334 from=translated src=- shape=565a7a0f vocab=e612f34f
-/
theorem roundList_length {a₀ : Code tm.Q k x.length S} {i : ℕ}
    {l : List (Code tm.Q k x.length S)} (h : RoundList tm x S a₀ i l) :
    l.length = (reachCodes tm x S a₀ i).card := by
  classical
  rw [← List.toFinset_card_of_nodup h.1, roundList_toFinset h]

/-! ## The count the machine starts from -/

/--
@isnad1 id=eq.0h5v.s5.e929f8a5a076 from=translated src=- shape=96b8ef46 vocab=01e1dcd8
-/
@[simp] theorem card_reachCodes_zero (tm : NTM k) (x : List Bool) (S : ℕ)
    (a₀ : Code tm.Q k x.length S) : (reachCodes tm x S a₀ 0).card = 1 := by
  rw [reachCodes, Finset.card_singleton]

end NTM

/-! ## The complement, as a certificate -/

/-- **The complement of an `NL` language is a certificate a machine can guess.** An input is
*outside* the language exactly when the last round of the search can be listed with none of its
members accepting. Every quantity here is an explicit arithmetic function of the input length,
and the list is only ever consumed one entry at a time: the machine guesses an entry, verifies it
by a walk (`Complexity.NTM.mem_reachCodes_iff_walk`), checks it is not accepting, counts it, and
at the end compares the count against the round's size. That comparison is what makes the
absence of an accepting code a *positive* certificate.
@isnad1 id=ex.1h1v.s8.bc47b9ea27a8 from=translated src=- shape=cf818a6f vocab=86b2c1c7
-/
theorem NL_complement_certificate_internal {L : Language} (hL : L ∈ NL) :
    ∃ (k : ℕ) (tm : NTM k) (C D A B : ℕ),
      ∀ x : List Bool, x ∉ L ↔
        ∃ l : List (Code tm.Q k x.length (logWindow C D x.length)),
          NTM.RoundList tm x (logWindow C D x.length)
              (cfgCode x.length (logWindow C D x.length) (tm.initCfg x))
              (A * (x.length + 1) ^ B) l ∧
            ∀ a ∈ l, ¬ ((decodeCfg x (logWindow C D x.length) a).state = tm.qhalt ∧
              (decodeCfg x (logWindow C D x.length) a).output.cells 1 = Γ.one) := by
  obtain ⟨k, tm, C, D, A, B, hsearch⟩ := NL_finite_search hL
  refine ⟨k, tm, C, D, A, B, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨l, hl⟩ := NTM.roundList_exists tm x (logWindow C D x.length)
      (cfgCode x.length (logWindow C D x.length) (tm.initCfg x)) (A * (x.length + 1) ^ B)
    refine ⟨l, hl, fun a ha hacc => hx ?_⟩
    exact (hsearch x).mpr ⟨a, hl.2.1 a ha, hacc⟩
  · rintro ⟨l, hl, hno⟩ hx
    obtain ⟨a, hmem, hacc⟩ := (hsearch x).mp hx
    exact hno a (NTM.mem_of_roundList hl hmem) hacc

end Complexity
