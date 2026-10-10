/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Interop.Cslib.FromMultiTape.Defs

/-!
# Proof internals for simulating CSLib machines on Complexitylib machines

Folding lemmas for the simulator `Complexity.FromMultiTape.toTM`: the cell
layout of a folded two-way tape, and the head moves of the three phases of a
simulated step.
-/

public section

namespace Complexity

namespace FromMultiTape

/-- Our symbol storing a binary CSLib cell. -/
def enc (c : Option Bool) : Γ := (Γw.ofCell c).toΓ

/-- Our cell holding CSLib cell `z` of a folded tape: `2 z + 1` for `z ≥ 0`
and `-2 z` for `z < 0`. -/
def fold (z : ℤ) : ℕ := if 0 ≤ z then 2 * z.toNat + 1 else 2 * (-z).toNat

/-- Folded cells are never the left-end cell. -/
theorem one_le_fold (z : ℤ) : 1 ≤ fold z := by
  unfold fold; split <;> omega

/-- Folding is injective. -/
theorem fold_injective : Function.Injective fold := by
  intro a b h
  unfold fold at h
  split at h <;> split at h <;> omega

/-- Every cell past the left end is a folded cell. -/
theorem exists_fold_eq {n : ℕ} (hn : 1 ≤ n) : ∃ z, fold z = n := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨-(m : ℤ), by unfold fold; split <;> omega⟩
  · exact ⟨(m : ℤ), by unfold fold; split <;> omega⟩

/-- Encoded cells are never `▷`. -/
@[simp] theorem enc_ne_start (c : Option Bool) : enc c ≠ Γ.start := by
  rcases c with _ | _ | _ <;> simp [enc, Γw.ofCell, Γw.toΓ]

/-- Decoding an encoded cell recovers it. -/
@[simp] theorem toCell_enc (c : Option Bool) : (enc c).toCell = c := by
  rcases c with _ | _ | _ <;> rfl

/-- Rewriting an encoded cell stores it again. -/
@[simp] theorem keep_enc (c : Option Bool) : (enc c).keep = Γw.ofCell c := by
  rcases c with _ | _ | _ <;> rfl

/-- Rewriting a symbol other than `▷` leaves it unchanged. -/
theorem keep_toΓ {r : Γ} (h : r ≠ Γ.start) : r.keep.toΓ = r := by
  cases r <;> simp_all [Γ.keep, Γw.toΓ]

/-- On a tape whose only `▷` is cell 0, rewriting the symbol under the head
changes nothing. -/
theorem write_keep {t : Tape} (hC : ∀ n, t.cells n = Γ.start ↔ n = 0) :
    t.write t.read.keep.toΓ = t := by
  unfold Tape.write
  split
  · rfl
  · next h =>
    have hr : t.read ≠ Γ.start := fun h' => h ((hC _).mp h')
    rw [keep_toΓ hr]
    ext <;> simp [Tape.read]

/-- A folded tape simulating the CSLib tape `f` with head at `z`; the sign flag
`s` records whether `z` is negative. -/
structure FoldRel (t : Tape) (f : ℤ → Option Bool) (z : ℤ) (s : Bool) : Prop where
  /-- The head is on the folded cell of `z`. -/
  head : t.head = fold z
  /-- The sign flag says whether `z` is negative. -/
  sign : s = decide (z < 0)
  /-- Cell 0 holds `▷`. -/
  start : t.cells 0 = Γ.start
  /-- Every folded cell stores its CSLib cell. -/
  cells : ∀ y, t.cells (fold y) = enc (f y)

/-- On a folded tape, `▷` sits exactly at cell 0. -/
theorem FoldRel.start_iff {t : Tape} {f : ℤ → Option Bool} {z : ℤ} {s : Bool}
    (h : FoldRel t f z s) (n : ℕ) : t.cells n = Γ.start ↔ n = 0 := by
  constructor
  · intro hn
    by_contra hne
    obtain ⟨y, rfl⟩ := exists_fold_eq (Nat.one_le_iff_ne_zero.mpr hne)
    exact enc_ne_start _ (h.cells y ▸ hn)
  · rintro rfl; exact h.start

/-- A folded tape reads the CSLib symbol under the CSLib head. -/
theorem FoldRel.read {t : Tape} {f : ℤ → Option Bool} {z : ℤ} {s : Bool}
    (h : FoldRel t f z s) : t.read = enc (f z) := by
  simp [Tape.read, h.head, h.cells]

/-- Writing the encoding of `c` on a folded tape simulates CSLib's write. -/
theorem FoldRel.write {t : Tape} {f : ℤ → Option Bool} {z : ℤ} {s : Bool}
    (h : FoldRel t f z s) (c : Option Bool) :
    FoldRel (t.write (Γw.ofCell c).toΓ) (Function.update f z c) z s := by
  have hz : t.head ≠ 0 := by rw [h.head]; exact Nat.one_le_iff_ne_zero.mp (one_le_fold z)
  have hw : t.write (Γw.ofCell c).toΓ =
      { t with cells := Function.update t.cells t.head (Γw.ofCell c).toΓ } := by
    unfold Tape.write; simp only [hz, ↓reduceIte]
  rw [hw]
  refine ⟨h.head, h.sign, ?_, fun y => ?_⟩
  · simp only [Function.update_of_ne hz.symm]; exact h.start
  · by_cases hy : y = z
    · subst hy; simp [h.head, enc]
    · have : fold y ≠ t.head := h.head ▸ fun e => hy (fold_injective e)
      simp only [Function.update_of_ne this, Function.update_of_ne hy]; exact h.cells y

/-- A left move decrements the head. -/
@[simp] theorem move_left_head (u : Tape) : (u.move .left).head = u.head - 1 := rfl

/-- A right move increments the head. -/
@[simp] theorem move_right_head (u : Tape) : (u.move .right).head = u.head + 1 := rfl

/-- Staying keeps the head. -/
@[simp] theorem move_stay (u : Tape) : u.move .stay = u := rfl

/-- The head moves of phases `0`, `1` and `2` on a folded tape whose only `▷`
is cell 0 carry the head from the folded cell of `z` to that of `z + m`, and
update the sign flag. -/
theorem fold_moves {t : Tape} (hC : ∀ n, t.cells n = Γ.start ↔ n = 0) {z : ℤ}
    (hh : t.head = fold z) (m : SignType) :
    let s := decide (z < 0)
    let t1 := t.move (Dir3.guard t.read (plan0 s m).2)
    let r1 := plan1 (plan0 s m).1 s t1.read
    let t2 := t1.move (Dir3.guard t1.read r1.2.2)
    let r2 := plan2 r1.1 r1.2.1 t2.read
    let t3 := t2.move (Dir3.guard t2.read r2.2)
    t3.head = fold (z + m) ∧ (r2.1 = true ↔ z + (m : ℤ) < 0) := by
  intro s t1 r1 t2 r2 t3
  have hf : ∀ y, (0 ≤ y ∧ (fold y : ℤ) = 2 * y + 1) ∨ (y < 0 ∧ (fold y : ℤ) = -2 * y) :=
    fun y => by unfold fold; split <;> omega
  have h1 := hf z
  have h2 := hf (z + 1)
  have h3 := hf (z + -1)
  cases m <;> rcases lt_or_ge z 0 with hz | hz <;>
    simp [t3, t2, r2, t1, r1, s, plan0, plan1, plan2, Dir3.guard, Tape.read, Tape.move_cells,
      hC, hh, hz] <;> (try split_ifs) <;>
    (try simp only [move_left_head, move_right_head, move_stay, hh, decide_eq_true_eq,
      false_iff, true_iff] at *) <;>
    omega

/-- The CSLib tape after the write `wr`. -/
def applyWr (f : ℤ → Option Bool) (z : ℤ) : Option (Option Bool) → ℤ → Option Bool
  | none => f
  | some c => Function.update f z c

/-- The phase-`0` write on a folded tape simulates CSLib's write. -/
theorem FoldRel.writePhase {t : Tape} {f : ℤ → Option Bool} {z : ℤ} {s : Bool}
    (h : FoldRel t f z s) (wr : Option (Option Bool)) :
    FoldRel (t.write (writeSym t.read wr).toΓ) (applyWr f z wr) z s := by
  cases wr with
  | none => simp only [writeSym, applyWr]; rw [write_keep h.start_iff]; exact h
  | some c => exact h.write c

/-- A moved tape keeps its cells. -/
theorem FoldRel.move_start_iff {t : Tape} {f : ℤ → Option Bool} {z : ℤ} {s : Bool}
    (h : FoldRel t f z s) (d : Dir3) (n : ℕ) : (t.move d).cells n = Γ.start ↔ n = 0 := by
  rw [Tape.move_cells]; exact h.start_iff n

/-- **One simulated step on a folded work tape.** Phases `0`, `1` and `2` carry a
folded tape simulating CSLib tape `f` with head `z` to one simulating the
CSLib tape after the write `wr` and the move `m`. -/
theorem FoldRel.phases {t : Tape} {f : ℤ → Option Bool} {z : ℤ} {s : Bool}
    (h : FoldRel t f z s) (wr : Option (Option Bool)) (m : SignType) :
    let t1 := t.writeAndMove (writeSym t.read wr).toΓ (Dir3.guard t.read (plan0 s m).2)
    let r1 := plan1 (plan0 s m).1 s t1.read
    let t2 := t1.writeAndMove t1.read.keep.toΓ (Dir3.guard t1.read r1.2.2)
    let r2 := plan2 r1.1 r1.2.1 t2.read
    let t3 := t2.writeAndMove t2.read.keep.toΓ (Dir3.guard t2.read r2.2)
    FoldRel t3 (applyWr f z wr) (z + m) r2.1 := by
  intro t1 r1 t2 r2 t3
  have hu := h.writePhase wr
  set u := t.write (writeSym t.read wr).toΓ with hu_def
  have hread : t.read ≠ Γ.start := by
    rw [h.read]; exact enc_ne_start _
  have hread' : u.read ≠ Γ.start := by
    rw [hu.read]; exact enc_ne_start _
  have hg : Dir3.guard t.read (plan0 s m).2 = Dir3.guard u.read (plan0 s m).2 := by
    simp [Dir3.guard, hread, hread']
  have hs : s = decide (z < 0) := h.sign
  have hC1 := hu.move_start_iff (Dir3.guard u.read (plan0 s m).2)
  have ht1 : t1 = u.move (Dir3.guard u.read (plan0 s m).2) := by
    simp only [t1, Tape.writeAndMove, ← hu_def, hg]
  have hC2 : ∀ n, t1.cells n = Γ.start ↔ n = 0 := by rw [ht1]; exact hC1
  have ht2 : t2 = t1.move (Dir3.guard t1.read r1.2.2) := by
    simp only [t2, Tape.writeAndMove, write_keep hC2]
  have hC3 : ∀ n, t2.cells n = Γ.start ↔ n = 0 := by
    rw [ht2, Tape.move_cells]; exact hC2
  have ht3 : t3 = t2.move (Dir3.guard t2.read r2.2) := by
    simp only [t3, Tape.writeAndMove, write_keep hC3]
  obtain ⟨hh3, hs3⟩ := fold_moves hu.start_iff hu.head m
  subst hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ht3]; simp only [r2]; simp only [ht2]; simp only [r1]; simp only [ht1]
    exact hh3
  · simp only [r2]; simp only [ht2]; simp only [r1]; simp only [ht1]
    exact Bool.eq_iff_iff.mpr (by simpa using hs3)
  · rw [ht3, ht2, ht1]; simp only [Tape.move_cells]; exact hu.start
  · intro y; rw [ht3, ht2, ht1]; simp only [Tape.move_cells]; exact hu.cells y

/-- The input tape holds `▷` exactly at cell 0. -/
theorem input_start_iff (x : List Bool) (i : ℕ) :
    (Tape.init (x.map Γ.ofBool)).cells i = Γ.start ↔ i = 0 := by
  rcases i with _ | i
  · simp
  · rw [Tape.init_cells_succ]
    simp only [List.getElem?_map, Nat.add_one_ne_zero, iff_false]
    cases h : x[i]? with
    | none => simp
    | some b => cases b <;> simp [Γ.ofBool]

/-- Past `▷`, the input tape is blank exactly after the input. -/
theorem input_blank_iff (x : List Bool) (i : ℕ) :
    (Tape.init (x.map Γ.ofBool)).cells (i + 1) = Γ.blank ↔ x.length ≤ i := by
  rw [Tape.init_cells_succ]
  simp only [List.getElem?_map]
  cases h : x[i]? with
  | none =>
    simp only [Option.map_none, Option.getD_none, true_iff]
    exact List.getElem?_eq_none_iff.mp h
  | some b =>
    have : i < x.length := (List.getElem?_eq_some_iff.mp h).1
    cases b <;> simp [Γ.ofBool] <;> omega

/-- Our output tape holds the CSLib output `out` after `▷`, with the head just
past it. -/
structure OutRel (t : Tape) (out : List Bool) : Prop where
  /-- The head is just past the output. -/
  head : t.head = out.length + 1
  /-- `▷` sits exactly at cell 0. -/
  start_iff : ∀ n, t.cells n = Γ.start ↔ n = 0
  /-- Cells `1, …, |out|` hold the output. -/
  cells : ∀ i (h : i < out.length), t.cells (i + 1) = Γ.ofBool out[i]

/-- A tape whose only `▷` is cell 0, with its head off cell 0, stays put in the
idle phases. -/
theorem idle_phase {t : Tape} (hC : ∀ n, t.cells n = Γ.start ↔ n = 0) (hh : t.head ≠ 0) :
    t.writeAndMove t.read.keep.toΓ (Dir3.guard t.read .stay) = t := by
  have : t.read ≠ Γ.start := by simp only [Tape.read, ne_eq, hC]; exact hh
  simp only [Tape.writeAndMove, write_keep hC, Dir3.guard, this, ↓reduceIte, move_stay]

/-- **One simulated step on the output tape.** Phase `0` appends the emitted
bit `e`; phases `1` and `2` leave the tape alone. -/
theorem OutRel.phase0 {t : Tape} {out : List Bool} (h : OutRel t out) (e : Option Bool) :
    OutRel (t.writeAndMove (outSym t.read e).toΓ (Dir3.guard t.read (outDir e)))
      (out ++ e.toList) := by
  have hh : t.head ≠ 0 := by rw [h.head]; omega
  have hr : t.read ≠ Γ.start := by simp only [Tape.read, ne_eq, h.start_iff]; exact hh
  cases e with
  | none =>
    have := idle_phase h.start_iff hh
    simp only [outSym, outDir, Option.toList_none, List.append_nil]
    rw [this]; exact h
  | some b =>
    have hw : t.write (Γw.ofBool b).toΓ =
        { t with cells := Function.update t.cells t.head (Γw.ofBool b).toΓ } := by
      unfold Tape.write; simp only [hh, ↓reduceIte]
    simp only [outSym, outDir, Tape.writeAndMove, hw, Dir3.guard, hr, ↓reduceIte]
    refine ⟨by simp [h.head], fun n => ?_, fun i hi => ?_⟩
    · simp only [Tape.move_cells]
      by_cases hn : n = t.head
      · subst hn; simp only [Function.update_self]
        cases b <;> simp [Γw.ofBool, Γw.toΓ, hh]
      · rw [Function.update_of_ne hn]; exact h.start_iff n
    · simp only [Tape.move_cells, Option.toList_some, List.length_append,
        List.length_cons, List.length_nil] at hi ⊢
      by_cases hi' : i < out.length
      · rw [Function.update_of_ne (by rw [h.head]; omega), h.cells i hi',
          List.getElem_append_left hi']
      · have hio : i = out.length := by omega
        subst hio
        rw [← h.head, Function.update_self]
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem_cons_zero]
        cases b <;> rfl

variable {k : ℕ} {S : Type}

/-- The first move off `▷` on an initialized tape. -/
theorem init_move (l : List Γ) (d : Dir3) :
    (Tape.init l).move (Dir3.guard (Tape.init l).read d) =
      { head := 1, cells := (Tape.init l).cells } := by
  have : (Tape.init l).read = Γ.start := by simp [Tape.read]
  rw [this, Dir3.guard_start]; rfl

/-- The first step on an initialized tape: the write is dropped and the head
moves off `▷`. -/
theorem init_writeAndMove (l : List Γ) (s : Γ) (d : Dir3) :
    (Tape.init l).writeAndMove s (Dir3.guard (Tape.init l).read d) =
      { head := 1, cells := (Tape.init l).cells } := by
  have hw : (Tape.init l).write s = Tape.init l := by simp [Tape.write]
  rw [Tape.writeAndMove, hw, init_move]

/-- The blank tape holds `▷` exactly at cell 0. -/
theorem init_nil_start_iff (n : ℕ) : (Tape.init []).cells n = Γ.start ↔ n = 0 := by
  simpa using input_start_iff [] n

end FromMultiTape

end Complexity
