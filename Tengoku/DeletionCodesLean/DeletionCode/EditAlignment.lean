import Tengoku.Seed.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Script.trans` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Script.reverse` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Script.length_balance` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Script.surviving_subsequence` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms alignment_of_common_subsequence` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms equal_length_confusability` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Equal-length confusability from genuine insertion/deletion scripts.
Each elementary edit inserts or removes one bit at an arbitrary list split.
Alignments are built from actual matched, deletion, and insertion columns.
-/
namespace DeletionCode.EditAlignment

abbrev Word := List Bool

/-- A script with its exact numbers of deletions and insertions.-/
inductive Script : Word → Word → ℕ → ℕ → Prop
  | refl (word : Word) : Script word word 0 0
  | delete {y pre suffix : Word} {bit : Bool} {d i : ℕ} :
      Script y (pre ++ bit :: suffix) d i → Script y (pre ++ suffix) (d + 1) i
  | insert {y pre suffix : Word} {bit : Bool} {d i : ℕ} :
      Script y (pre ++ suffix) d i → Script y (pre ++ bit :: suffix) d (i + 1)

/-- An alignment made exclusively of the three column types in the manuscript.-/
inductive Alignment : Word → Word → ℕ → ℕ → Prop
  | nil : Alignment [] [] 0 0
  | matched (bit : Bool) {y z : Word} {d i : ℕ} :
      Alignment y z d i → Alignment (bit :: y) (bit :: z) d i
  | deletion (bit : Bool) {y z : Word} {d i : ℕ} :
      Alignment y z d i → Alignment (bit :: y) z (d + 1) i
  | insertion (bit : Bool) {y z : Word} {d i : ℕ} :
      Alignment y z d i → Alignment y (bit :: z) d (i + 1)

/--
@isnad1 id=script.2h7v.s5.62eb2141146b from=translated src=- shape=6ef787de vocab=eb3d9095
-/
theorem Script.trans {x y z : Word} {d₁ i₁ d₂ i₂ : ℕ}
    (hxy : Script x y d₁ i₁) (hyz : Script y z d₂ i₂) :
    Script x z (d₁ + d₂) (i₁ + i₂) := by
  induction hyz with
  | refl => simpa using hxy
  | delete h ih => simpa only [Nat.add_assoc] using Script.delete ih
  | insert h ih => simpa only [Nat.add_assoc] using Script.insert ih

/--
@isnad1 id=script.1h4v.s4.9301f9c66cd1 from=translated src=- shape=d0969956 vocab=9170a4c7
-/
theorem Script.reverse {y z : Word} {d i : ℕ} (h : Script y z d i) :
    Script z y i d := by
  induction h with
  | refl => exact Script.refl _
  | @delete pre suffix bit d i h ih =>
    have hfirst : Script (pre ++ suffix) (pre ++ bit :: suffix) 0 1 :=
      Script.insert (Script.refl _)
    simpa only [Nat.zero_add, Nat.add_comm 1 d] using hfirst.trans ih
  | @insert pre suffix bit d i h ih =>
    have hfirst : Script (pre ++ bit :: suffix) (pre ++ suffix) 1 0 :=
      Script.delete (Script.refl _)
    simpa only [Nat.zero_add, Nat.add_comm 1 i] using hfirst.trans ih

/--
@isnad1 id=eq.1h4v.s5.b5cdc9bba5f8 from=translated src=- shape=e386ca40 vocab=8043e5c3
-/
theorem Script.length_balance {y z : Word} {d i : ℕ} (h : Script y z d i) :
    z.length + d = y.length + i := by
  induction h with
  | refl => omega
  | delete h ih => simp only [List.length_append, List.length_cons] at *; omega
  | insert h ih => simp only [List.length_append, List.length_cons] at *; omega

/-- Deleting one target position loses at most one letter of any surviving subsequence.
@isnad1 id=ex.1h4v.s6.7f04857a8545 from=translated src=- shape=b7240022 vocab=d15263c5
-/
theorem sublist_survives_delete (w pre suffix : Word) (bit : Bool)
    (h : w.Sublist (pre ++ bit :: suffix)) :
    ∃ v : Word, v.Sublist w ∧ v.Sublist (pre ++ suffix) ∧ w.length ≤ v.length + 1 := by
  obtain ⟨left, right, rfl, hleft, hright⟩ := List.sublist_append_iff.mp h
  cases hright with
  | cons _ htail =>
    exact ⟨left ++ right, List.Sublist.refl _, hleft.append htail, by omega⟩
  | cons_cons _ htail =>
    rename_i tail
    refine ⟨left ++ tail, (List.Sublist.refl left).append ((List.Sublist.refl tail).cons bit),
      hleft.append htail, ?_⟩
    simp only [List.length_append, List.length_cons]
    omega

/-- At most d original letters are lost during a script with d deletions.
@isnad1 id=ex.1h4v.s5.b59b76b92438 from=translated src=- shape=bd23561d vocab=bbbc099f
-/
theorem Script.surviving_subsequence {y z : Word} {d i : ℕ} (h : Script y z d i) :
    ∃ w : Word, w.Sublist y ∧ w.Sublist z ∧ y.length ≤ w.length + d := by
  induction h with
  | refl => exact ⟨y, List.Sublist.refl _, List.Sublist.refl _, by omega⟩
  | @delete pre suffix bit d i h ih =>
    obtain ⟨w, hwy, hwz, hlen⟩ := ih
    obtain ⟨v, hvw, hvz, hvlen⟩ := sublist_survives_delete w pre suffix bit hwz
    exact ⟨v, hvw.trans hwy, hvz, by omega⟩
  | @insert pre suffix bit d i h ih =>
    obtain ⟨w, hwy, hwz, hlen⟩ := ih
    have hstep : (pre ++ suffix).Sublist (pre ++ bit :: suffix) :=
      (List.Sublist.refl pre).append ((List.Sublist.refl suffix).cons bit)
    exact ⟨w, hwy, hwz.trans hstep, hlen⟩

/--
@isnad1 id=alignmen.0h1v.s3.6fa95aa8edf7 from=translated src=- shape=879bdacf vocab=e3c687d7
-/
theorem Alignment.from_empty (z : Word) : Alignment [] z 0 z.length := by
  induction z with
  | nil => exact Alignment.nil
  | cons bit tail ih => exact Alignment.insertion bit ih

/-- Match a common subsequence and put every remaining letter in its own edit column.
@isnad1 id=alignmen.2h3v.s5.4d1cdb97f403 from=translated src=- shape=e08595c1 vocab=e34cccb9
-/
theorem alignment_of_common_subsequence {w y z : Word}
    (hy : w.Sublist y) (hz : w.Sublist z) :
    Alignment y z (y.length - w.length) (z.length - w.length) := by
  induction hy generalizing z with
  | slnil => simpa using Alignment.from_empty z
  | cons bit h ih =>
    have hlength := h.length_le
    have halign := Alignment.deletion bit (ih hz)
    convert halign using 1
    simp only [List.length_cons]
    omega
  | @cons_cons w y bit h ih =>
    revert hz
    induction z with
    | nil => intro hz; cases hz
    | cons other z ihz =>
      intro hz
      cases hz with
      | cons _ hskip =>
        have hlength := hskip.length_le
        have halign := Alignment.insertion other (ihz hskip)
        convert halign using 1
        simp only [List.length_cons] at *
        omega
      | cons_cons _ hmatch =>
        simpa only [List.length_cons, Nat.add_sub_add_right] using
          Alignment.matched bit (ih hmatch)

/-- At most t single insertions/deletions in total, with an actual script witness.-/
def WithinEdits (t : ℕ) (y z : Word) : Prop :=
  ∃ d i, Script y z d i ∧ d + i ≤ t

/-- Manuscript lemma `lem:confuse`. Distinctness is unnecessary for this conclusion.
@isnad1 id=ex.4h5v.s5.f14d294de8f5 from=translated src=- shape=b54df2e9 vocab=b74ec7b5
-/
theorem equal_length_confusability (y z u : Word) (n t : ℕ)
    (hy : y.length = n) (hz : z.length = n)
    (hyu : WithinEdits t y u) (hzu : WithinEdits t z u) :
    ∃ d, d ≤ t ∧ Alignment y z d d := by
  obtain ⟨dy, iy, hyu, hcosty⟩ := hyu
  obtain ⟨dz, iz, hzu, hcostz⟩ := hzu
  have hscript : Script y z (dy + iz) (iy + dz) := hyu.trans hzu.reverse
  have hbalance := hscript.length_balance
  have hdeletions : dy + iz ≤ t := by omega
  obtain ⟨w, hwy, hwz, hsurvive⟩ := hscript.surviving_subsequence
  refine ⟨n - w.length, by omega, ?_⟩
  simpa only [hy, hz] using alignment_of_common_subsequence hwy hwz

end DeletionCode.EditAlignment
