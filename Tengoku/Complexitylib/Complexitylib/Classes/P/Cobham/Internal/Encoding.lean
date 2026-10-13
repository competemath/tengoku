/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Tengoku.Complexitylib.Complexitylib.Classes.P.Cobham.Internal.Blocks
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine
import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Internal

/-!
# Encoding machine configurations as bitstrings — proof internals

The completeness direction of Cobham's theorem simulates a polynomial-time
machine inside the function algebra, so a configuration has to become a single
bitstring. This module fixes that encoding and proves the arithmetic facts about
it; the algebra-side operations that act on it live in
`Complexitylib.Classes.P.Cobham.Internal.StepAlgebra`.

## The two design choices

**Two bits per symbol, with blank `= 00`.** Fixed-width blocks are padded with
zeros (`Complexity.padTo`), so making blank the all-zero code means padding a
tape block with zeros *is* extending it with blanks — the padding needs no
special treatment anywhere.

**Tapes split at the head.** A tape is stored as its cells to the left of the
head, nearest first, and its cells from the head rightwards. Then a head move is
transferring one symbol between the two sides, i.e. a `take`/`drop`/`append` of
two bits, rather than arithmetic on a position index. Reading is the first two
bits of the right part.

Cell `0` is the only `▷` (the writable alphabet `Γw` excludes it), so "the head
is at cell 0" is exactly "the read symbol is `▷`" — and in that case
`TM.δ_right_of_start` forces a move right. The left part is therefore never
consulted when it is empty, which is why it needs no emptiness test.

## Main definitions

- `Complexity.Cobham.symCode` — two-bit code for `Γ`
- `Complexity.Cobham.cellsCode` — a window of cells as a bitstring
- `Complexity.Cobham.leftCode`, `Complexity.Cobham.rightCode` — a tape split at
  its head

## Main results

The six lemmas that make the split representation simulate `Tape.writeAndMove`,
each expressing one head move as two bits crossing the split:

- `leftCode_write_stay`, `rightCode_write_stay`
- `leftCode_write_right`, `rightCode_write_right`
- `leftCode_write_left`, `rightCode_write_left`

Every right-hand side is built from `take 2`, `drop 2`, `++` and the constant
`symCode s` — all of which the algebra has (`Cobham.takeFn`, `Cobham.dropFn`,
`Cobham.appendFn`, `Cobham.const`).
-/

@[expose] public section

namespace Complexity

namespace Cobham

/-! ## The symbol code -/

/-- Two-bit code for the tape alphabet. Blank is `00`, so zero-padding a block is
blank-padding it. -/
def symCode : Γ → List Bool
  | .blank => [false, false]
  | .start => [false, true]
  | .zero => [true, false]
  | .one => [true, true]

/-- Decode the leading two bits of a string as a tape symbol; anything shorter
than two bits reads as blank. -/
def symDecode : List Bool → Γ
  | false :: false :: _ => .blank
  | false :: true :: _ => .start
  | true :: false :: _ => .zero
  | true :: true :: _ => .one
  | _ => .blank

/--
@isnad1 id=eq.0h1v.s3.fd6ce5c01285 from=translated src=- shape=8e1bdd70 vocab=228641dd
-/
@[simp] theorem symCode_length (g : Γ) : (symCode g).length = 2 := by cases g <;> rfl

/--
@isnad1 id=eq.0h0v.s3.0b50f0f88427 from=translated src=- shape=898355e7 vocab=18dd03d1
-/
@[simp] theorem symCode_blank : symCode Γ.blank = [false, false] := rfl

/-- The code round-trips, even with arbitrary trailing bits — which is what lets
the decoder read a symbol off the front of a longer block.
@isnad1 id=eq.0h2v.s4.8d1412ed4a96 from=translated src=- shape=5b3d5834 vocab=42492e96
-/
@[simp] theorem symDecode_symCode (g : Γ) (rest : List Bool) :
    symDecode (symCode g ++ rest) = g := by cases g <;> rfl

/-- The decoder only ever looks at two bits, so truncating first changes
nothing.
@isnad1 id=eq.0h1v.s4.e77cf1e3ab36 from=translated src=- shape=f1ac4e78 vocab=29848f67
-/
theorem symDecode_take_two (l : List Bool) : symDecode (l.take 2) = symDecode l := by
  match l with
  | [] => rfl
  | [b] => cases b <;> rfl
  | b :: b' :: t => cases b <;> cases b' <;> rfl

/-- Zero padding decodes as blank: the reason `symCode Γ.blank = [0,0]`.
@isnad1 id=eq.1h1v.s4.ecf85d45cb55 from=translated src=- shape=19e54370 vocab=5128917a
-/
theorem symDecode_replicate_false {n : ℕ} (h : 2 ≤ n) :
    symDecode (List.replicate n false) = Γ.blank := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 = 2 + m from by omega, List.replicate_add]
  rfl

/-- The code is injective.
@isnad1 id=injectiv.0h0v.s2.9e352991c460 from=translated src=- shape=4b736592 vocab=793ed0fe
-/
theorem symCode_injective : Function.Injective symCode := by
  intro a b hab
  have h1 : symDecode (symCode a ++ []) = a := symDecode_symCode a []
  rw [hab, symDecode_symCode] at h1
  exact h1.symm

/-- Every symbol costs two bits, so a run of coded symbols has twice the
length. -/
private theorem length_flatMap_symCode (l : List ℕ) (f : ℕ → Γ) :
    ((l.flatMap fun j => symCode (f j)).length) = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, ih,
      symCode_length, List.length_cons]; omega

/-! ## The control state

The state is stored one-hot: `|Q|` bits with a single `1`. Fixed width and
injective, and — the point — every state's code is a *constant* for a fixed
machine, so the transition table is finitely many `Cobham.matchPrefixFn` tests
against constants (`Cobham.tableFn`). Binary would need arithmetic; one-hot needs
none. -/

/-- One-hot code for a control state: one bit per element of `Q`, set exactly at
the state itself.

Noncomputable only because `Finset.toList` picks an enumeration order; the code
appears solely in specifications, never in a machine that must run. -/
noncomputable def stateCode {Q : Type} [Fintype Q] [DecidableEq Q] (q : Q) :
    List Bool :=
  (Finset.univ.toList (α := Q)).map fun p => decide (p = q)

/--
@isnad1 id=eq.0h2v.s4.a58c4b6c0093 from=translated src=- shape=ae8cecbf vocab=53b61632
-/
@[simp] theorem stateCode_length {Q : Type} [Fintype Q] [DecidableEq Q] (q : Q) :
    (stateCode q).length = Fintype.card Q := by
  rw [stateCode, List.length_map, Finset.length_toList, Finset.card_univ]

/-- Distinct states get distinct codes.
@isnad1 id=injectiv.0h1v.s4.e7f68e401a8d from=translated src=- shape=6f088699 vocab=b060fe14
-/
theorem stateCode_injective {Q : Type} [Fintype Q] [DecidableEq Q] :
    Function.Injective (stateCode (Q := Q)) := by
  intro a b hab
  rw [stateCode, stateCode, List.map_inj_left] at hab
  have h := hab a (by simp)
  simpa using h.symm

/-! ## Windows of cells -/

/-- The `w` cells of `t` starting at cell `i`, two bits each. -/
def cellsCode (t : Tape) (i w : ℕ) : List Bool :=
  (List.range w).flatMap fun j => symCode (t.cells (i + j))

/--
@isnad1 id=eq.0h2v.s4.14662eb4fe43 from=translated src=- shape=bf78e4ac vocab=cff02a8d
-/
@[simp] theorem cellsCode_zero (t : Tape) (i : ℕ) : cellsCode t i 0 = [] := rfl

/--
@isnad1 id=eq.0h3v.s4.8516ba59690e from=translated src=- shape=7c95ef91 vocab=f2716857
-/
@[simp] theorem cellsCode_length (t : Tape) (i w : ℕ) :
    (cellsCode t i w).length = 2 * w := by
  rw [cellsCode, length_flatMap_symCode, List.length_range]

/-- Peeling the first cell off a window.
@isnad1 id=eq.0h3v.s5.596ee1e035af from=translated src=- shape=e8306ba1 vocab=51a749bd
-/
theorem cellsCode_succ_left (t : Tape) (i w : ℕ) :
    cellsCode t i (w + 1) = symCode (t.cells i) ++ cellsCode t (i + 1) w := by
  rw [cellsCode, cellsCode, List.range_succ_eq_map, List.flatMap_cons]
  simp [List.flatMap_map, Nat.add_comm, Nat.add_left_comm]

/-! ## Tapes split at the head -/

/-- The cells `n-1, n-2, …, 0` of `t`, nearest first. -/
def leftCodeFrom (t : Tape) : ℕ → List Bool
  | 0 => []
  | n + 1 => symCode (t.cells n) ++ leftCodeFrom t n

/-- The cells strictly left of the head, nearest first. -/
def leftCode (t : Tape) : List Bool := leftCodeFrom t t.head

/--
@isnad1 id=eq.0h1v.s3.aac91bc59b00 from=translated src=- shape=fa63633d vocab=530bdc57
-/
@[simp] theorem leftCodeFrom_zero (t : Tape) : leftCodeFrom t 0 = [] := rfl

/--
@isnad1 id=eq.0h2v.s5.96b7ab9afa32 from=translated src=- shape=9146a759 vocab=f5c10e51
-/
@[simp] theorem leftCodeFrom_succ (t : Tape) (n : ℕ) :
    leftCodeFrom t (n + 1) = symCode (t.cells n) ++ leftCodeFrom t n := rfl

/--
@isnad1 id=eq.0h2v.s4.1445845d333b from=translated src=- shape=72614a36 vocab=cdf14bcd
-/
@[simp] theorem leftCodeFrom_length (t : Tape) (n : ℕ) :
    (leftCodeFrom t n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [leftCodeFrom_succ, List.length_append, ih, symCode_length]; omega

/-- The nearest-left window depends only on the cells it covers.
@isnad1 id=eq.1h3v.s5.a8da2ca921d4 from=translated src=- shape=d364a76c vocab=03bdbe38
-/
theorem leftCodeFrom_congr {t t' : Tape} {n : ℕ}
    (h : ∀ j, j < n → t.cells j = t'.cells j) :
    leftCodeFrom t n = leftCodeFrom t' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [leftCodeFrom_succ, leftCodeFrom_succ, h n (by omega),
        ih fun j hj => h j (by omega)]

/-- The cells from the head rightwards, out to cell `W`.

The width is `W + 1 - head`, complementary to `leftCode`'s `head`, so the two
parts always account for exactly the cells `0 … W`: their total width is the
constant `2 · (W + 1)` and a head move just shifts two bits across the split. -/
def rightCode (t : Tape) (W : ℕ) : List Bool := cellsCode t t.head (W + 1 - t.head)

/--
@isnad1 id=eq.0h1v.s4.72139a48fb65 from=translated src=- shape=5e412272 vocab=77a11caf
-/
@[simp] theorem leftCode_length (t : Tape) : (leftCode t).length = 2 * t.head :=
  leftCodeFrom_length t t.head

/--
@isnad1 id=eq.0h2v.s5.bf9f5b5deaf2 from=translated src=- shape=945f14db vocab=84c055a4
-/
@[simp] theorem rightCode_length (t : Tape) (W : ℕ) :
    (rightCode t W).length = 2 * (W + 1 - t.head) := cellsCode_length _ _ _

/-- The two halves together always span the same window.
@isnad1 id=eq.1h2v.s6.f3bb11d70242 from=translated src=- shape=f18fef33 vocab=258d7d79
-/
theorem leftCode_rightCode_length (t : Tape) {W : ℕ} (h : t.head ≤ W + 1) :
    (leftCode t).length + (rightCode t W).length = 2 * (W + 1) := by
  simp only [leftCode_length, rightCode_length]
  omega

/-- The read symbol is the first two bits of the right part.
@isnad1 id=eq.1h2v.s4.42e17240736b from=translated src=- shape=18cc1905 vocab=f590cb64
-/
theorem symDecode_rightCode (t : Tape) {W : ℕ} (hw : t.head ≤ W) :
    symDecode (rightCode t W) = t.read := by
  rw [rightCode, show W + 1 - t.head = (W - t.head) + 1 from by omega,
    cellsCode_succ_left]
  exact symDecode_symCode _ _

/-! ### Congruence

Both halves read only the cells in their own window, so an update outside that
window is invisible to them. These are the lemmas that let a single-cell write be
localized. -/

/-- A window depends only on the cells it covers.
@isnad1 id=eq.1h4v.s5.63bc4d361471 from=translated src=- shape=ce649051 vocab=ab9b47da
-/
theorem cellsCode_congr {t t' : Tape} {i w : ℕ}
    (h : ∀ j, j < w → t.cells (i + j) = t'.cells (i + j)) :
    cellsCode t i w = cellsCode t' i w := by
  rw [cellsCode, cellsCode]
  refine List.flatMap_congr fun j hj => ?_
  rw [h j (List.mem_range.mp hj)]

/-- The left half depends only on the head and the cells strictly below it.
@isnad1 id=eq.2h2v.s5.15f342be8d56 from=translated src=- shape=67e7f8d7 vocab=1009367f
-/
theorem leftCode_congr {t t' : Tape} (hh : t.head = t'.head)
    (h : ∀ j, j < t.head → t.cells j = t'.cells j) : leftCode t = leftCode t' := by
  rw [leftCode, leftCode, ← hh]
  exact leftCodeFrom_congr h

/-! ### Writing and moving

`Tape.write` never touches cell `0` (the model makes writing there a no-op), and
`Γw` cannot produce `▷`, so cell `0` is permanently the unique `▷`. Hence "the
head is at `0`" is exactly "the read symbol is `▷`", and `TM.δ_right_of_start`
then forces a right move — which is why the left half is never consulted while
empty. -/

/-- Writing at the head leaves every other cell alone.
@isnad1 id=eq.1h3v.s4.bd5d7240c51f from=translated src=- shape=1bef4d07 vocab=102986e7
-/
theorem write_cells_of_ne {t : Tape} {s : Γ} {j : ℕ} (h : j ≠ t.head) :
    (t.write s).cells j = t.cells j := by
  rw [Tape.write]
  split
  · rfl
  · exact Function.update_of_ne h _ _

/-- Writing at the head sets exactly that cell — except at cell `0`, where the
model makes the write a no-op, so callers must establish that the modeled symbol
already agrees with what is there. A raw `TM` transition writes only `Γw`, which
excludes `▷`; the encoded simulator later supplies the corrected symbol through
`correctWrite`.
@isnad1 id=eq.1h2v.s4.8fb5d3c106bd from=translated src=- shape=d12c33d5 vocab=102986e7
-/
theorem write_cells_head {t : Tape} {s : Γ} (hs : t.head = 0 → s = t.cells t.head) :
    (t.write s).cells t.head = s := by
  rw [Tape.write]
  split
  · next h => exact (hs h).symm
  · exact Function.update_self _ _ _

/-- Writing at the head sets exactly that cell, away from cell `0`.
@isnad1 id=eq.1h2v.s4.1b42fd480783 from=translated src=- shape=2745c307 vocab=102986e7
-/
theorem write_cells_self {t : Tape} {s : Γ} (h : t.head ≠ 0) :
    (t.write s).cells t.head = s :=
  write_cells_head fun h0 => absurd h0 h

/-- **Staying put**: the left half is untouched and the right half gets its
leading symbol replaced.
@isnad1 id=eq.0h2v.s3.79ca055c89b5 from=translated src=- shape=2d4c3d36 vocab=578dc4eb
-/
theorem leftCode_write_stay {t : Tape} {s : Γ} :
    leftCode ((t.write s).move Dir3.stay) = leftCode t := by
  have hhead : ((t.write s).move Dir3.stay).head = t.head := Tape.write_head t s
  refine leftCode_congr hhead fun j hj => ?_
  rw [hhead] at hj
  show (t.write s).cells j = t.cells j
  exact write_cells_of_ne (by omega)

/-- **Moving right**: the written symbol crosses over to the left half. This is
the one direction a head at cell `0` can take, so it is stated with the weaker
hypothesis that the write agrees with cell `0` when the head is there.
@isnad1 id=eq.1h2v.s5.d93c7ffc29b9 from=translated src=- shape=fc7e74d4 vocab=4b248af2
-/
theorem leftCode_write_right {t : Tape} {s : Γ}
    (h : t.head = 0 → s = t.cells t.head) :
    leftCode ((t.write s).move Dir3.right) = symCode s ++ leftCode t := by
  have hhead : ((t.write s).move Dir3.right).head = t.head + 1 := by
    rw [Tape.move, Tape.write_head]
  rw [leftCode, leftCode, hhead, leftCodeFrom_succ]
  congr 1
  · show symCode (((t.write s).move Dir3.right).cells t.head) = _
    rw [Tape.move_cells, write_cells_head h]
  · exact leftCodeFrom_congr fun j hj => by
      rw [Tape.move_cells]; exact write_cells_of_ne (by omega)

/-- **Moving left**: the nearest left symbol crosses over to the right half, so
the left half loses its first two bits.
@isnad1 id=eq.1h2v.s5.06efed9205b3 from=translated src=- shape=7d868d75 vocab=43c855fd
-/
theorem leftCode_write_left {t : Tape} {s : Γ} (h : t.head ≠ 0) :
    leftCode ((t.write s).move Dir3.left) = (leftCode t).drop 2 := by
  have hhead : ((t.write s).move Dir3.left).head = t.head - 1 := by
    rw [Tape.move, Tape.write_head]
  obtain ⟨m, hm⟩ : ∃ m, t.head = m + 1 := ⟨t.head - 1, by omega⟩
  rw [leftCode, leftCode, hhead, hm, Nat.add_sub_cancel, leftCodeFrom_succ]
  rw [show (symCode (t.cells m) ++ leftCodeFrom t m).drop 2
      = leftCodeFrom t m from by
        rw [List.drop_left' (by simp)]]
  exact leftCodeFrom_congr fun j hj => by
    rw [Tape.move_cells]; exact write_cells_of_ne (by omega)

/-- **Staying put**, right half: the leading symbol is replaced.
@isnad1 id=eq.2h3v.s5.3b290473962a from=translated src=- shape=4d635d4f vocab=bc3c70b5
-/
theorem rightCode_write_stay {t : Tape} {s : Γ} {W : ℕ} (h : t.head ≠ 0)
    (hW : t.head ≤ W) :
    rightCode ((t.write s).move Dir3.stay) W = symCode s ++ (rightCode t W).drop 2 := by
  have hhead : ((t.write s).move Dir3.stay).head = t.head := Tape.write_head t s
  rw [rightCode, rightCode, hhead, show W + 1 - t.head = (W - t.head) + 1 from by omega,
    cellsCode_succ_left, cellsCode_succ_left]
  congr 1
  · show symCode ((t.write s).cells t.head) = _
    rw [write_cells_self h]
  · rw [List.drop_left' (by simp)]
    exact cellsCode_congr fun j _ => write_cells_of_ne (by omega)

/-- **Moving right**, right half: the leading symbol is consumed.
@isnad1 id=eq.1h3v.s5.62c2559c86a1 from=translated src=- shape=bfbeb67c vocab=13069c35
-/
theorem rightCode_write_right {t : Tape} {s : Γ} {W : ℕ} (hW : t.head ≤ W) :
    rightCode ((t.write s).move Dir3.right) W = (rightCode t W).drop 2 := by
  have hhead : ((t.write s).move Dir3.right).head = t.head + 1 := by
    rw [Tape.move, Tape.write_head]
  rw [rightCode, rightCode, hhead, show W + 1 - t.head = (W - t.head) + 1 from by omega,
    cellsCode_succ_left, List.drop_left' (by simp),
    show W + 1 - (t.head + 1) = W - t.head from by omega]
  exact cellsCode_congr fun j _ => by
    rw [Tape.move_cells]; exact write_cells_of_ne (by omega)

/-- **Moving left**, right half: the nearest left symbol and the written symbol
both join it.
@isnad1 id=eq.2h3v.s6.6e214e955989 from=translated src=- shape=2f9c9102 vocab=0eadb861
-/
theorem rightCode_write_left {t : Tape} {s : Γ} {W : ℕ} (h : t.head ≠ 0)
    (hW : t.head ≤ W) :
    rightCode ((t.write s).move Dir3.left) W =
      (leftCode t).take 2 ++ symCode s ++ (rightCode t W).drop 2 := by
  have hhead : ((t.write s).move Dir3.left).head = t.head - 1 := by
    rw [Tape.move, Tape.write_head]
  obtain ⟨m, hm⟩ : ∃ m, t.head = m + 1 := ⟨t.head - 1, by omega⟩
  have hleft : (leftCode t).take 2 = symCode (t.cells m) := by
    rw [leftCode, hm, leftCodeFrom_succ, List.take_left' (by simp)]
  rw [rightCode, rightCode, hhead, hm, Nat.add_sub_cancel, hleft,
    show W + 1 - m = (W - m) + 1 from by omega, cellsCode_succ_left,
    show W + 1 - (m + 1) = (W - (m + 1)) + 1 from by omega, cellsCode_succ_left,
    List.drop_left' (by simp), List.append_assoc]
  have hwrite : (t.write s).cells (m + 1) = s := by
    rw [← hm]; exact write_cells_self h
  congr 1
  · show symCode (((t.write s).move Dir3.left).cells m) = _
    rw [Tape.move_cells]
    exact congrArg symCode (write_cells_of_ne (by omega))
  · rw [show W - m = (W - (m + 1)) + 1 from by omega, cellsCode_succ_left]
    congr 1
    · show symCode (((t.write s).move Dir3.left).cells (m + 1)) = _
      rw [Tape.move_cells]
      exact congrArg symCode hwrite
    · refine cellsCode_congr fun j _ => ?_
      rw [Tape.move_cells]
      exact write_cells_of_ne (by omega)

/-! ## Whole configurations

Every field occupies a block of the same width, so field `i` is recovered by
`Cobham.blockFn … i` — the algebra never needs a self-delimiting decoder. A tape
costs two blocks (its two halves); the state costs one, padded to the same
width. -/

/-- The block width used throughout: wide enough for either half of a tape whose
head stays within `0 … W`. -/
def blockWidth (W : ℕ) : ℕ := 2 * (W + 1)

/-- The canonical ruler of one block's width. -/
def blockRuler (W : ℕ) : List Bool := List.replicate (blockWidth W) false

/--
@isnad1 id=eq.0h1v.s3.00a5722cfe45 from=translated src=- shape=1e92cebf vocab=ef745c3b
-/
@[simp] theorem blockRuler_length (W : ℕ) : (blockRuler W).length = blockWidth W := by
  simp [blockRuler]

/-- A tape as two padded half-blocks: the cells left of the head (nearest first)
and the cells from the head rightwards. -/
def tapeBlocks (W : ℕ) (t : Tape) : List (List Bool) :=
  [padTo (blockRuler W) (leftCode t), padTo (blockRuler W) (rightCode t W)]

/-- Both halves of a tape occupy one block each.
@isnad1 id=eq.1h3v.s4.a622eeb15dc1 from=translated src=- shape=e1aabc11 vocab=d3aa72ca
-/
theorem tapeBlocks_width (W : ℕ) (t : Tape) :
    ∀ b ∈ tapeBlocks W t, b.length = (blockRuler W).length := by
  intro b hb
  rw [blockRuler_length]
  rcases List.mem_cons.mp hb with rfl | hb
  · simp
  · rcases List.mem_cons.mp hb with rfl | hb
    · simp
    · simp at hb

/--
@isnad1 id=eq.0h2v.s4.2a5099f4ac24 from=translated src=- shape=f2da567f vocab=705a8166
-/
@[simp] theorem tapeBlocks_length (W : ℕ) (t : Tape) :
    (tapeBlocks W t).length = 2 := rfl

/-- A tape as a bitstring: its two half-blocks concatenated. -/
def tapeCode (W : ℕ) (t : Tape) : List Bool := (tapeBlocks W t).flatten

/--
@isnad1 id=eq.0h2v.s4.8ba6ebcfec8e from=translated src=- shape=1da97a20 vocab=79d5a17f
-/
@[simp] theorem tapeCode_length (W : ℕ) (t : Tape) :
    (tapeCode W t).length = 2 * blockWidth W := by
  rw [tapeCode, tapeBlocks, List.flatten_cons, List.flatten_cons,
    List.flatten_nil, List.length_append, List.length_append, padTo_length,
    padTo_length, blockRuler_length]
  simp
  omega

/-- Blocks of a common width concatenate to a predictable length. -/
private theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β)
    (m : ℕ) (h : ∀ a, (f a).length = m) : (l.flatMap f).length = l.length * m := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, ih, h a, List.length_cons,
        Nat.succ_mul]
      exact Nat.add_comm _ _

/-- The work tapes, one after another. -/
def worksCode {k : ℕ} (W : ℕ) (work : Fin k → Tape) : List Bool :=
  (List.finRange k).flatMap fun i => tapeCode W (work i)

/--
@isnad1 id=eq.0h3v.s5.d14d2f090cf0 from=translated src=- shape=f1cc7a95 vocab=507a63ab
-/
@[simp] theorem worksCode_length {k : ℕ} (W : ℕ) (work : Fin k → Tape) :
    (worksCode W work).length = k * (2 * blockWidth W) := by
  rw [worksCode, length_flatMap_const _ _ _ (fun i => tapeCode_length W (work i)),
    List.length_finRange]

/-! ### The window invariant

A head moves at most one cell per step and starts at cell `0`, so after `t` steps
every head is within `0 … t`. Taking the window `W` to be the machine's time
bound therefore discharges the `head ≤ W` side condition of every encoding lemma
— the simulated machine can never reach outside the encoded window. -/

/-- After `t` steps from the initial configuration every head is at most `t`.
@isnad1 id=and.1h5v.s6.c7f90c9dcc98 from=translated src=- shape=f55e7988 vocab=ea2a5053
-/
theorem heads_le_of_reachesIn {k : ℕ} (tm : TM k) {x : List Bool} {t : ℕ}
    {c : Cfg k tm.Q} (h : tm.reachesIn t (tm.initCfg x) c) :
    c.input.head ≤ t ∧ c.output.head ≤ t ∧ ∀ i, (c.work i).head ≤ t := by
  obtain ⟨hin, hout, hwork⟩ := TM.head_le_start_add_of_reachesIn tm h
  exact ⟨by simpa using hin, by simpa using hout, fun i => by simpa using hwork i⟩

/-- **Reading a symbol out of an encoded tape.** The head symbol is the first two
bits of the padded right half-block — one `takeFn` in the algebra.
@isnad1 id=eq.1h2v.s4.1a694fb846e8 from=translated src=- shape=abc9cd8b vocab=d7a3fd97
-/
theorem symDecode_take_padTo_rightCode {W : ℕ} (t : Tape) (hW : t.head ≤ W) :
    symDecode ((padTo (blockRuler W) (rightCode t W)).take 2) = t.read := by
  rw [take_padTo _ _ 2 (by rw [rightCode_length]; omega)
      (by rw [rightCode_length, blockRuler_length, blockWidth]; omega),
    symDecode_take_two]
  exact symDecode_rightCode t hW

/-! ### One tape's step

The encoded step on a tape's two half-blocks. Every right-hand side is
`take 2` / `drop 2` / `++` / a constant and a re-pad, so the algebra realizes it
with `Cobham.takeFn`, `Cobham.dropFn`, `Cobham.appendFn`, `Cobham.const` and
`Cobham.padFn` — and within one branch of `Cobham.tableFn` the symbol `s` and the
direction `d` are *constants*. -/

/-- The two half-blocks of a tape after writing `s` and moving `d`. -/
def tapeStepBlocks (R : List Bool) (s : Γ) (d : Dir3) (L Rt : List Bool) :
    List Bool × List Bool :=
  match d with
  | .stay => (L, padTo R (symCode s ++ Rt.drop 2))
  | .right => (padTo R (symCode s ++ L), padTo R (Rt.drop 2))
  | .left => (padTo R (L.drop 2), padTo R (L.take 2 ++ symCode s ++ Rt.drop 2))

/-- **The encoded step simulates `Tape.writeAndMove`** on both half-blocks.

The hypotheses are exactly what the corrected encoded action supplies. `hs`: at
cell `0` the write is a no-op, so `correctWrite` replaces the raw `Γw` symbol by
the existing `▷`. `hne`: `TM.δ_right_of_start` ensures that a head at cell `0`
can only move *right*, so the stay and left cases never arise there.
@isnad1 id=eq.3h4v.s6.58ebdcbc8cb0 from=translated src=- shape=a9ec283d vocab=40fb48c7
-/
theorem tapeStepBlocks_eq {W : ℕ} (t : Tape) (s : Γ) (d : Dir3)
    (hs : t.head = 0 → s = t.cells t.head)
    (hne : d ≠ Dir3.right → t.head ≠ 0) (hW : t.head ≤ W) :
    tapeStepBlocks (blockRuler W) s d
        (padTo (blockRuler W) (leftCode t)) (padTo (blockRuler W) (rightCode t W))
      = (padTo (blockRuler W) (leftCode ((t.write s).move d)),
          padTo (blockRuler W) (rightCode ((t.write s).move d) W)) := by
  have hLlen : (leftCode t).length ≤ (blockRuler W).length := by
    rw [leftCode_length, blockRuler_length, blockWidth]; omega
  have hRlen : (rightCode t W).length ≤ (blockRuler W).length := by
    rw [rightCode_length, blockRuler_length, blockWidth]; omega
  have hR2 : 2 ≤ (rightCode t W).length := by rw [rightCode_length]; omega
  have hdrop : (padTo (blockRuler W) (rightCode t W)).drop 2
      = (rightCode t W).drop 2 ++
        List.replicate ((blockRuler W).length - (rightCode t W).length) false :=
    drop_padTo _ _ 2 hR2 hRlen
  cases d with
  | stay =>
      have h0 : t.head ≠ 0 := hne (by decide)
      rw [tapeStepBlocks, leftCode_write_stay, rightCode_write_stay h0 hW, hdrop,
        ← List.append_assoc, padTo_append_replicate]
  | right =>
      rw [tapeStepBlocks, leftCode_write_right hs, rightCode_write_right hW, hdrop,
        padTo_append_padTo _ _ _ hLlen, padTo_append_replicate]
  | left =>
      have h0 : t.head ≠ 0 := hne (by decide)
      have hL2 : 2 ≤ (leftCode t).length := by
        rw [leftCode_length]; omega
      rw [tapeStepBlocks, leftCode_write_left h0, rightCode_write_left h0 hW,
        padTo_drop _ _ 2 hL2 hLlen, take_padTo _ _ 2 hL2 hLlen, hdrop,
        ← List.append_assoc, padTo_append_replicate]

/-! ### All the tapes at once

`TM.step` writes and moves on every tape independently, so the encoded step is
the same operation applied tapewise. Treating the tapes as one list — input,
output, then work tapes, the order the encoding uses — makes that a
`List.zipWith` against the transition's per-tape actions, with no positional
index arithmetic. -/

/-- Writing back the symbol already under the head changes nothing. This is what
lets the read-only input tape take part in the uniform tapewise step: its action
is "write what you read, then move".
@isnad1 id=eq.0h1v.s3.160828ec4002 from=translated src=- shape=86a320aa vocab=a720de91
-/
theorem write_read_self (t : Tape) : t.write t.read = t := by
  rw [Tape.write]
  split
  · rfl
  · exact Tape.ext rfl (by rw [Tape.read]; exact Function.update_eq_self _ _)

/-- All of a configuration's tapes in encoding order. -/
def cfgTapes {k : ℕ} {Q : Type} (c : Cfg k Q) : List Tape :=
  c.input :: c.output :: List.ofFn c.work

/--
@isnad1 id=eq.0h3v.s4.6df0aee52d38 from=translated src=- shape=ecb61107 vocab=baeee4b4
-/
@[simp] theorem cfgTapes_length {k : ℕ} {Q : Type} (c : Cfg k Q) :
    (cfgTapes c).length = k + 2 := by
  rw [cfgTapes, List.length_cons, List.length_cons, List.length_ofFn]

/-! ### The transition key

The transition function is indexed by the current state together with the symbol
under every head. Packing those into one string turns the whole finite case
analysis into `Cobham.tableFn`: each (state, symbols) combination is a *constant*
pattern, and there are finitely many of them for a fixed machine. -/

/-- The state and the symbols under every head, in tape order. -/
noncomputable def keyCode {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (c : Cfg k Q) : List Bool :=
  stateCode c.state ++ (cfgTapes c).flatMap fun t => symCode t.read

/--
@isnad1 id=eq.0h3v.s5.434a323c5eda from=translated src=- shape=59ab3829 vocab=79ce4d8f
-/
@[simp] theorem keyCode_length {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (c : Cfg k Q) : (keyCode c).length = Fintype.card Q + 2 * (k + 2) := by
  rw [keyCode, List.length_append, stateCode_length,
    length_flatMap_const (cfgTapes c) (fun t => symCode t.read) 2
      (fun t => symCode_length t.read), cfgTapes_length, Nat.mul_comm]

/-- The first two bits of a tape's right half-block are its read symbol.
@isnad1 id=eq.1h2v.s4.4dfe36371ec3 from=translated src=- shape=41121719 vocab=7c20e257
-/
theorem take_rightCode (t : Tape) {W : ℕ} (hW : t.head ≤ W) :
    (rightCode t W).take 2 = symCode t.read := by
  rw [rightCode, show W + 1 - t.head = (W - t.head) + 1 from by omega,
    cellsCode_succ_left, List.take_left' (by simp)]
  rfl

/-- The blocks of a list of tapes: two per tape. -/
def tapesBlocks (W : ℕ) (ts : List Tape) : List (List Bool) :=
  ts.flatMap (tapeBlocks W)

/--
@isnad1 id=eq.0h2v.s4.434da5197286 from=translated src=- shape=e9976b2c vocab=151572bf
-/
@[simp] theorem tapesBlocks_length (W : ℕ) (ts : List Tape) :
    (tapesBlocks W ts).length = 2 * ts.length := by
  rw [tapesBlocks, length_flatMap_const _ _ 2 (fun t => tapeBlocks_length W t)]
  omega

/-- The tapes after one step, given each tape's write and move. -/
def tapesStep (acts : List (Γ × Dir3)) (ts : List Tape) : List Tape :=
  List.zipWith (fun a t => (t.write a.1).move a.2) acts ts

/-- `zipWith` over two tuples is the tuple of the pointwise results. -/
private theorem zipWith_ofFn {α β γ : Type} {n : ℕ} (f : α → β → γ)
    (g : Fin n → α) (h : Fin n → β) :
    List.zipWith f (List.ofFn g) (List.ofFn h) = List.ofFn fun i => f (g i) (h i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.zipWith_cons_cons, ih]

/-- The write a transition *really* performs: at cell `0` the model makes the
write a no-op, and this records that. Under `Tape.StartInvariant` the test is on
the **read symbol**, which the transition table already branches on — so the
correction costs the algebra nothing, it just picks a different constant in the
`▷` branch. -/
def correctWriteSym (r s : Γ) : Γ := if r = Γ.start then Γ.start else s

/-- The corrected write on a tape — a function of its read symbol alone, which is
what puts it inside the transition key. -/
def correctWrite (t : Tape) (s : Γ) : Γ := correctWriteSym t.read s

/-- Correcting the write does not change what the write does.
@isnad1 id=eq.1h2v.s4.dd7ed5f811b4 from=translated src=- shape=2a722cb4 vocab=f7d5f617
-/
theorem write_correctWrite {t : Tape} (s : Γ) (h : t.StartInvariant) :
    t.write (correctWrite t s) = t.write s := by
  rw [correctWrite, correctWriteSym]
  split
  · next hr =>
      have hh : t.head = 0 := by
        by_contra hne
        exact h.read_ne_start (by omega) hr
      rw [Tape.write, ite_eq_left hh, Tape.write, ite_eq_left hh]
  · rfl

/-- Under the invariant, the corrected write agrees with cell `0` when the head
is there — the hypothesis `tapeStepBlocks_eq` needs.
@isnad1 id=eq.2h2v.s4.1f57c0a3a970 from=translated src=- shape=95573b2f vocab=37de2dff
-/
theorem correctWrite_at_zero {t : Tape} (s : Γ) (h : t.StartInvariant)
    (hh : t.head = 0) : correctWrite t s = t.cells t.head := by
  have hr : t.read = Γ.start := by rw [Tape.read, hh]; exact h.1
  rw [correctWrite, correctWriteSym, ite_eq_left hr]
  show Γ.start = t.cells t.head
  rw [hh]
  exact h.1.symm

/-- The per-tape (write, move) actions a transition prescribes, in encoding
order. The input tape's "write" is the symbol it just read, which by
`write_read_self` leaves it unchanged — so the read-only input tape fits the
uniform tapewise step with no special case. -/
def stepActs {k : ℕ} (tm : TM k) (c : Cfg k tm.Q) : List (Γ × Dir3) :=
  let d := tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read
  (c.input.read, d.2.2.2.1) ::
    (correctWrite c.output d.2.2.1.toΓ, d.2.2.2.2.2) ::
    List.ofFn fun i => (correctWrite (c.work i) (d.2.1 i).toΓ, d.2.2.2.2.1 i)

/-! ### The transition key determines the step

Everything the successor configuration depends on — the new state and every
tape's write and direction — is a function of the state together with the symbol
under each head. That is exactly what a `Cobham.tableFn` entry can be indexed by,
and it is why any entry matching a configuration's key carries the right
branch. -/

/-- The symbols under a configuration's heads, in `cfgTapes` order. -/
def cfgReads {k : ℕ} {Q : Type} (c : Cfg k Q) : Fin (k + 2) → Γ :=
  Fin.cons c.input.read (Fin.cons c.output.read fun i => (c.work i).read)

/-- A transition key's pattern string: the state's one-hot code followed by the
symbol under each head. Constant for each key, so it is what a
`Cobham.tableFn` entry matches against. -/
noncomputable def keyPattern {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (p : Q × (Fin (k + 2) → Γ)) : List Bool :=
  stateCode p.1 ++ (List.ofFn p.2).flatMap symCode

/--
@isnad1 id=eq.0h3v.s6.f63f38201399 from=translated src=- shape=8892d3a2 vocab=abb41a15
-/
@[simp] theorem keyPattern_length {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (p : Q × (Fin (k + 2) → Γ)) :
    (keyPattern p).length = Fintype.card Q + 2 * (k + 2) := by
  rw [keyPattern, List.length_append, stateCode_length,
    length_flatMap_const (List.ofFn p.2) symCode 2 symCode_length, List.length_ofFn,
    Nat.mul_comm]

/-- Runs of coded symbols determine their symbols. -/
private theorem flatMap_symCode_injective :
    ∀ l₁ l₂ : List Γ, l₁.length = l₂.length →
      l₁.flatMap symCode = l₂.flatMap symCode → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ hlen _; exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons a l₁ ih =>
      intro l₂ hlen heq
      cases l₂ with
      | nil => simp at hlen
      | cons b l₂ =>
          rw [List.flatMap_cons, List.flatMap_cons] at heq
          obtain ⟨h1, h2⟩ := List.append_inj heq (by simp)
          rw [symCode_injective h1, ih l₂ (by simpa using hlen) h2]

/-- **Distinct keys get distinct patterns.** Together with the fact that all
patterns have the same length, this is what makes at most one table entry match a
given key.
@isnad1 id=injectiv.0h2v.s5.cd81be3110c8 from=translated src=- shape=96cb8f4b vocab=1b54bfb0
-/
theorem keyPattern_injective {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] :
    Function.Injective (keyPattern (k := k) (Q := Q)) := by
  rintro ⟨q₁, s₁⟩ ⟨q₂, s₂⟩ h
  rw [keyPattern, keyPattern] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  have hq := stateCode_injective h1
  have hs := flatMap_symCode_injective _ _ (by simp) h2
  subst hq
  simp only [Prod.mk.injEq, true_and]
  exact List.ofFn_inj.mp hs

/-- The tapes' read symbols, listed, are the configuration's read tuple.
@isnad1 id=eq.0h3v.s5.6e228f758b5c from=translated src=- shape=b03ef21a vocab=0e575244
-/
theorem cfgTapes_map_read {k : ℕ} {Q : Type} (c : Cfg k Q) :
    (cfgTapes c).map Tape.read = List.ofFn (cfgReads c) := by
  rw [cfgTapes, cfgReads]
  simp [List.ofFn_succ, Function.comp_def]

/-- **A configuration's key is its key's pattern.** So the table entry indexed by
`(state, reads)` is the one that matches.
@isnad1 id=eq.0h3v.s5.f02b18a9fba4 from=translated src=- shape=89a4e669 vocab=40fdc728
-/
theorem keyCode_eq {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q] (c : Cfg k Q) :
    keyCode c = keyPattern (c.state, cfgReads c) := by
  rw [keyCode, keyPattern]
  congr 1
  rw [← cfgTapes_map_read]
  simp [List.flatMap_map]

/-- The per-tape actions determined by a transition key. -/
def stepActsOf {k : ℕ} (tm : TM k) (q : tm.Q) (syms : Fin (k + 2) → Γ) :
    List (Γ × Dir3) :=
  let d := tm.δ q (syms 0) (fun i => syms i.succ.succ) (syms 1)
  (syms 0, d.2.2.2.1) ::
    (correctWriteSym (syms 1) d.2.2.1.toΓ, d.2.2.2.2.2) ::
    List.ofFn fun i =>
      (correctWriteSym (syms i.succ.succ) (d.2.1 i).toΓ, d.2.2.2.2.1 i)

/-- The successor state determined by a transition key. -/
def stepStateOf {k : ℕ} (tm : TM k) (q : tm.Q) (syms : Fin (k + 2) → Γ) : tm.Q :=
  (tm.δ q (syms 0) (fun i => syms i.succ.succ) (syms 1)).1

/-- The actions a configuration prescribes are the ones its key prescribes.
@isnad1 id=eq.0h3v.s5.8262c09d62f2 from=translated src=- shape=2228d286 vocab=e6118134
-/
theorem stepActs_eq_stepActsOf {k : ℕ} (tm : TM k) (c : Cfg k tm.Q) :
    stepActs tm c = stepActsOf tm c.state (cfgReads c) := rfl

/-- The successor state is the one the key prescribes.
@isnad1 id=eq.1h4v.s5.9e06fa518cdf from=translated src=- shape=2d42ec68 vocab=3eab23fa
-/
theorem step_state_eq {k : ℕ} (tm : TM k) {c c' : Cfg k tm.Q}
    (h : tm.step c = some c') : c'.state = stepStateOf tm c.state (cfgReads c) := by
  have hne : ¬ c.state = tm.qhalt := fun hq => by simp [TM.step, hq] at h
  rw [TM.step, ite_eq_right hne] at h
  injection h with h
  subst h
  rfl

/-- **`TM.step` is the tapewise action.** Every tape writes and moves according
to `stepActs`, so the whole configuration's tapes step uniformly.
@isnad1 id=eq.3h4v.s6.fde2ae642991 from=translated src=- shape=01b3cc8d vocab=1eeed3b5
-/
theorem cfgTapes_step {k : ℕ} (tm : TM k) {c c' : Cfg k tm.Q}
    (h : tm.step c = some c') (hout : c.output.StartInvariant)
    (hwork : ∀ i, (c.work i).StartInvariant) :
    cfgTapes c' = tapesStep (stepActs tm c) (cfgTapes c) := by
  have hne : ¬ c.state = tm.qhalt := fun hq => by simp [TM.step, hq] at h
  rw [TM.step, ite_eq_right hne] at h
  injection h with h
  subst h
  rw [cfgTapes, cfgTapes, stepActs, tapesStep]
  dsimp only
  rw [List.zipWith_cons_cons, List.zipWith_cons_cons, zipWith_ofFn]
  dsimp only
  simp only [write_read_self, write_correctWrite _ hout,
    write_correctWrite _ (hwork _)]

/-- **One tape's blocks after a step.** Immediate from `tapeStepBlocks_eq`; this
is the form that lifts tapewise across a whole configuration.
@isnad1 id=eq.3h3v.s7.9b1968f540c8 from=translated src=- shape=60048a70 vocab=3fda92ac
-/
theorem tapeBlocks_step {W : ℕ} (a : Γ × Dir3) (t : Tape)
    (hs : t.head = 0 → a.1 = t.cells t.head)
    (hne : a.2 ≠ Dir3.right → t.head ≠ 0) (hW : t.head ≤ W) :
    tapeBlocks W ((t.write a.1).move a.2) =
      [(tapeStepBlocks (blockRuler W) a.1 a.2 (padTo (blockRuler W) (leftCode t))
          (padTo (blockRuler W) (rightCode t W))).1,
       (tapeStepBlocks (blockRuler W) a.1 a.2 (padTo (blockRuler W) (leftCode t))
          (padTo (blockRuler W) (rightCode t W))).2] := by
  rw [tapeStepBlocks_eq t a.1 a.2 hs hne hW]
  rfl

/-- The tapewise step acts blockwise on the encoding.
@isnad1 id=eq.1h3v.s7.9c94f196e170 from=translated src=- shape=fc30198e vocab=858dda13
-/
theorem tapesBlocks_tapesStep {W : ℕ} :
    ∀ (acts : List (Γ × Dir3)) (ts : List Tape),
      List.Forall₂ (fun (a : Γ × Dir3) (t : Tape) =>
        (t.head = 0 → a.1 = t.cells t.head) ∧
        (a.2 ≠ Dir3.right → t.head ≠ 0) ∧ t.head ≤ W) acts ts →
      tapesBlocks W (tapesStep acts ts) =
        (List.zipWith (fun a t =>
          [(tapeStepBlocks (blockRuler W) a.1 a.2 (padTo (blockRuler W) (leftCode t))
              (padTo (blockRuler W) (rightCode t W))).1,
           (tapeStepBlocks (blockRuler W) a.1 a.2 (padTo (blockRuler W) (leftCode t))
              (padTo (blockRuler W) (rightCode t W))).2]) acts ts).flatten := by
  intro acts ts h
  induction h with
  | nil => rfl
  | @cons a t acts ts hat _ ih =>
      rw [tapesStep, List.zipWith_cons_cons, tapesBlocks, List.flatMap_cons,
        tapeBlocks_step a t hat.1 hat.2.1 hat.2.2, List.zipWith_cons_cons,
        List.flatten_cons]
      exact congrArg (List.append _) ih

/-- A whole configuration as a list of equal-width blocks: the one-hot state
padded to a block, then the input tape, the output tape, and the work tapes,
each as two half-blocks. -/
noncomputable def cfgBlocks {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) : List (List Bool) :=
  padTo (blockRuler W) (stateCode c.state) :: tapesBlocks W (cfgTapes c)

/--
@isnad1 id=eq.0h4v.s5.b148b761270c from=translated src=- shape=33e3bdf9 vocab=cb2bd48f
-/
theorem cfgBlocks_eq {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) :
    cfgBlocks W c =
      padTo (blockRuler W) (stateCode c.state) :: tapesBlocks W (cfgTapes c) := rfl

/-- Every field of a configuration occupies exactly one block.
@isnad1 id=eq.1h5v.s5.a7c1dd4b0f9a from=translated src=- shape=055a3199 vocab=64c606ae
-/
theorem cfgBlocks_width {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) :
    ∀ b ∈ cfgBlocks W c, b.length = (blockRuler W).length := by
  intro b hb
  rw [cfgBlocks, List.mem_cons] at hb
  rcases hb with rfl | hb
  · simp
  · obtain ⟨t, _, ht⟩ := List.mem_flatMap.mp hb
    exact tapeBlocks_width W t b ht

/-- A whole configuration as a bitstring. -/
noncomputable def cfgCode {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) : List Bool := (cfgBlocks W c).flatten

/-- **Field access.** Block `i` of an encoded configuration is field `i` — so
`Cobham.blockFn … i` reads it, and no self-delimiting decoder is ever needed.
@isnad1 id=eq.1h5v.s6.9abd3285ee2f from=translated src=- shape=5ab9c291 vocab=595deeea
-/
theorem blockAt_cfgCode {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) (i : ℕ) (hi : i < (cfgBlocks W c).length) :
    blockAt (blockRuler W) (cfgCode W c) i = (cfgBlocks W c)[i] :=
  blockAt_flatten _ _ (cfgBlocks_width W c) i hi

/-- A configuration has `2(k+2) + 1` blocks: one per tape half plus the state.
@isnad1 id=eq.0h4v.s6.22ace731f0fa from=translated src=- shape=9ba742fb vocab=af20a2ef
-/
@[simp] theorem cfgBlocks_length {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) : (cfgBlocks W c).length = 2 * (k + 2) + 1 := by
  rw [cfgBlocks, List.length_cons, tapesBlocks,
    length_flatMap_const _ _ 2 (fun t => tapeBlocks_length W t), cfgTapes_length]
  omega

/-- **The encoded configuration steps blockwise.** Composing `cfgTapes_step`
(`TM.step` is the tapewise action) with `tapesBlocks_tapesStep` (that action is
blockwise on the encoding): the successor's blocks are the new state block
followed by the old blocks transformed two at a time by `tapeStepBlocks`.

The `Forall₂` hypothesis pairs each tape with its own action, which is what a run
supplies: `δ_right_of_start` constrains a tape at cell `0` only through *its own*
transition entry.
@isnad1 id=eq.4h5v.s7.3c28eefbfd21 from=translated src=- shape=5c7442dd vocab=0e246a55
-/
theorem cfgBlocks_step {k : ℕ} (tm : TM k) {c c' : Cfg k tm.Q} {W : ℕ}
    (h : tm.step c = some c') (hout : c.output.StartInvariant)
    (hwork : ∀ i, (c.work i).StartInvariant)
    (hgood : List.Forall₂ (fun (a : Γ × Dir3) (t : Tape) =>
      (t.head = 0 → a.1 = t.cells t.head) ∧
      (a.2 ≠ Dir3.right → t.head ≠ 0) ∧ t.head ≤ W) (stepActs tm c) (cfgTapes c)) :
    cfgBlocks W c' =
      padTo (blockRuler W) (stateCode c'.state) ::
        (List.zipWith (fun a t =>
          [(tapeStepBlocks (blockRuler W) a.1 a.2 (padTo (blockRuler W) (leftCode t))
              (padTo (blockRuler W) (rightCode t W))).1,
           (tapeStepBlocks (blockRuler W) a.1 a.2 (padTo (blockRuler W) (leftCode t))
              (padTo (blockRuler W) (rightCode t W))).2])
          (stepActs tm c) (cfgTapes c)).flatten := by
  rw [cfgBlocks, cfgTapes_step tm h hout hwork,
    tapesBlocks_tapesStep (stepActs tm c) (cfgTapes c) hgood]

/-- `Forall₂` over two tuples follows pointwise. -/
private theorem forall₂_ofFn {α β : Type} {R : α → β → Prop} {n : ℕ}
    {f : Fin n → α} {g : Fin n → β} (h : ∀ i, R (f i) (g i)) :
    List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => exact List.Forall₂.nil
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact List.Forall₂.cons (h 0) (ih fun i => h i.succ)

/-- **The step's side conditions hold in any run.** The write-agreement at cell
`0` is `correctWrite_at_zero`, and "a head at cell `0` can only move right" is
exactly `TM.δ_right_of_start` read through the invariant: at cell `0` the tape
reads `▷`, which is the hypothesis that rule fires on.
@isnad1 id=forall.2h4v.s6.5206391216b1 from=translated src=- shape=639c4112 vocab=a061b690
-/
theorem stepActs_forall₂ {k : ℕ} (tm : TM k) (c : Cfg k tm.Q) {W : ℕ}
    (hinv : ∀ t ∈ cfgTapes c, t.StartInvariant)
    (hW : ∀ t ∈ cfgTapes c, t.head ≤ W) :
    List.Forall₂ (fun (a : Γ × Dir3) (t : Tape) =>
      (t.head = 0 → a.1 = t.cells t.head) ∧
      (a.2 ≠ Dir3.right → t.head ≠ 0) ∧ t.head ≤ W)
      (stepActs tm c) (cfgTapes c) := by
  obtain ⟨hri, hrw, hro⟩ :=
    tm.δ_right_of_start c.state c.input.read (fun i => (c.work i).read) c.output.read
  have hmem_in : c.input ∈ cfgTapes c := by simp [cfgTapes]
  have hmem_out : c.output ∈ cfgTapes c := by simp [cfgTapes]
  have hmem_work : ∀ i, c.work i ∈ cfgTapes c := fun i => by
    simp only [cfgTapes, List.mem_cons]
    exact Or.inr (Or.inr (List.mem_ofFn.mpr ⟨i, rfl⟩))
  -- At cell `0` a tape reads `▷`, which is what `δ_right_of_start` fires on.
  have hzero : ∀ t ∈ cfgTapes c, t.head = 0 → t.read = Γ.start := fun t ht h0 => by
    rw [Tape.read, h0]; exact (hinv t ht).1
  rw [stepActs, cfgTapes]
  refine List.Forall₂.cons ⟨fun _ => rfl, fun hd h0 => hd ?_, hW _ hmem_in⟩
    (List.Forall₂.cons
      ⟨fun h0 => correctWrite_at_zero _ (hinv _ hmem_out) h0,
        fun hd h0 => hd ?_, hW _ hmem_out⟩
      (forall₂_ofFn fun i =>
        ⟨fun h0 => correctWrite_at_zero _ (hinv _ (hmem_work i)) h0,
          fun hd h0 => hd ?_, hW _ (hmem_work i)⟩))
  · exact hri (hzero _ hmem_in h0)
  · exact hro (hzero _ hmem_out h0)
  · exact hrw i (hzero _ (hmem_work i) h0)

/-- **Tape `j` lives in blocks `2j` and `2j+1`** of the tape-block list. Combined
with the state block at the front of `cfgBlocks`, tape `j` of a configuration
occupies blocks `2j+1` and `2j+2` — which is how `Cobham.blockFn` addresses
them.
@isnad1 id=and.0h3v.s7.c494e3196a38 from=translated src=- shape=a2ad7fdb vocab=dd56aa06
-/
theorem getElem?_tapesBlocks (W : ℕ) :
    ∀ (ts : List Tape) (j : ℕ),
      (tapesBlocks W ts)[2 * j]? =
        (ts[j]?).map (fun t => padTo (blockRuler W) (leftCode t)) ∧
      (tapesBlocks W ts)[2 * j + 1]? =
        (ts[j]?).map (fun t => padTo (blockRuler W) (rightCode t W)) := by
  intro ts
  induction ts with
  | nil => intro j; simp [tapesBlocks]
  | cons t ts ih =>
      intro j
      cases j with
      | zero => simp [tapesBlocks, tapeBlocks]
      | succ j =>
          have hlen : (tapeBlocks W t).length = 2 := rfl
          have e1 : 2 * (j + 1) = (tapeBlocks W t).length + 2 * j := by
            rw [hlen]; omega
          rw [tapesBlocks, List.flatMap_cons, e1,
            List.getElem?_append_right (by omega),
            List.getElem?_append_right (by omega)]
          simp only [Nat.add_sub_cancel_left, List.getElem?_cons_succ,
            show (tapeBlocks W t).length + 2 * j + 1 - (tapeBlocks W t).length
              = 2 * j + 1 from by omega]
          exact ⟨(ih j).1, (ih j).2⟩

/-! ### Field accessors

The first three blocks — the state and the input tape's two halves — read out
directly. Each is one `Cobham.blockFn` on the algebra side. -/

/-- Block `0` holds the state.
@isnad1 id=eq.0h4v.s5.e5bbae0b0212 from=translated src=- shape=08f3b8d2 vocab=700669b0
-/
theorem blockAt_cfgCode_state {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) :
    blockAt (blockRuler W) (cfgCode W c) 0
      = padTo (blockRuler W) (stateCode c.state) := by
  rw [blockAt_cfgCode W c 0 (by simp)]
  rfl

/-- Unpadding block `0` recovers the one-hot state code, which the transition
table then matches against its finitely many constants.
@isnad1 id=eq.1h4v.s5.9f5e4041cd74 from=translated src=- shape=3346fda0 vocab=c761b6ff
-/
theorem state_of_cfgCode {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) (hW : Fintype.card Q ≤ blockWidth W) :
    (blockAt (blockRuler W) (cfgCode W c) 0).take (Fintype.card Q)
      = stateCode c.state := by
  rw [blockAt_cfgCode_state,
    take_padTo _ _ _ (by simp) (by rw [stateCode_length, blockRuler_length]; omega),
    List.take_of_length_le (by simp)]

/-- Block `1` is the input tape's left half.
@isnad1 id=eq.0h4v.s5.03a635cdf240 from=translated src=- shape=51bde4a2 vocab=5d9159c2
-/
theorem blockAt_cfgCode_inputLeft {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) :
    blockAt (blockRuler W) (cfgCode W c) 1
      = padTo (blockRuler W) (leftCode c.input) := by
  rw [blockAt_cfgCode W c 1 (by simp)]
  rfl

/-- Block `2` is the input tape's right half — the one the read symbol comes
from.
@isnad1 id=eq.0h4v.s5.899c2ba4eb4a from=translated src=- shape=605e4c30 vocab=8919401f
-/
theorem blockAt_cfgCode_inputRight {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) :
    blockAt (blockRuler W) (cfgCode W c) 2
      = padTo (blockRuler W) (rightCode c.input W) := by
  rw [blockAt_cfgCode W c 2 (by rw [cfgBlocks_length]; omega)]
  rfl

/-- The input head's symbol, read straight out of the encoding.
@isnad1 id=eq.1h4v.s5.3324a5b59ef9 from=translated src=- shape=c3c62291 vocab=9b1b6b20
-/
theorem inputRead_of_cfgCode {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) (hW : c.input.head ≤ W) :
    symDecode ((blockAt (blockRuler W) (cfgCode W c) 2).take 2) = c.input.read := by
  rw [blockAt_cfgCode_inputRight]
  exact symDecode_take_padTo_rightCode c.input hW

end Cobham

end Complexity
