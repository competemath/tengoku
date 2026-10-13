/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine

/-!
# Binary string encodings on Turing-machine tapes

Generic predicates and lemmas for tapes containing canonical binary strings.
`Tape.HasBinaryPrefix` describes a string being written from left to right,
`Tape.HasBinaryString` describes the same contents after rewinding the head to
cell one, `Tape.HasBinaryContent` forgets the head while an in-place arithmetic
cursor moves, and `Tape.HasBinarySuffix` describes a read cursor at the
beginning of a remaining suffix. These shapes are shared by deterministic and
nondeterministic machine constructions.
-/

@[expose] public section

namespace Complexity

namespace Tape

/-- A tape while a binary string is being written: cells `1..|bits|` contain
    the bits, the head is at the next cell, and the remaining tail is blank. -/
def HasBinaryPrefix (t : Tape) (bits : List Bool) : Prop :=
  t.head = bits.length + 1 ∧
  (∀ i, (h : i < bits.length) → t.cells (i + 1) = Γ.ofBool (bits[i]'h)) ∧
  (∀ i, bits.length ≤ i → t.cells (i + 1) = Γ.blank)

/-- A completed binary string: the bits are present and the head has been
    rewound to cell one. -/
def HasBinaryString (t : Tape) (bits : List Bool) : Prop :=
  t.head = 1 ∧
  (∀ i, (h : i < bits.length) → t.cells (i + 1) = Γ.ofBool (bits[i]'h)) ∧
  (∀ i, bits.length ≤ i → t.cells (i + 1) = Γ.blank)

/-- Canonical binary contents independently of the tape head. This is the
stable invariant for in-place arithmetic cursors that scan and rewind. -/
def HasBinaryContent (t : Tape) (bits : List Bool) : Prop :=
  (∀ i, (h : i < bits.length) → t.cells (i + 1) = Γ.ofBool (bits[i]'h)) ∧
  ∀ i, bits.length ≤ i → t.cells (i + 1) = Γ.blank

/-- A read cursor at the beginning of a remaining binary suffix. The suffix
starts under the current off-marker head, is followed immediately by blank,
and the tape has no stray left markers. -/
def HasBinarySuffix (t : Tape) (bits : List Bool) : Prop :=
  t.head ≥ 1 ∧
  (∀ i, (h : i < bits.length) →
    t.cells (t.head + i) = Γ.ofBool (bits[i]'h)) ∧
  t.cells (t.head + bits.length) = Γ.blank ∧
  (∀ j, j ≥ 1 → t.cells j ≠ Γ.start)

/-- A completed binary string whose length is at most `B`. -/
def HasBoundedBinaryString (t : Tape) (B : ℕ) : Prop :=
  ∃ bits : List Bool, bits.length ≤ B ∧ t.HasBinaryString bits

/-- A completed binary string has the same canonical contents after forgetting
its parked head.
@isnad1 id=hasbinar.1h2v.s3.a70feb2a0b65 from=translated src=- shape=8f6c20a1 vocab=b0a2dcf3
-/
theorem HasBinaryString.hasBinaryContent {t : Tape} {bits : List Bool}
    (h : t.HasBinaryString bits) : t.HasBinaryContent bits :=
  h.2

/-- Canonical contents become a completed binary string when the head is at
cell one.
@isnad1 id=hasbinar.2h2v.s4.60280e07dd11 from=translated src=- shape=c363db39 vocab=d611f5c6
-/
theorem HasBinaryContent.hasBinaryString {t : Tape} {bits : List Bool}
    (h : t.HasBinaryContent bits) (hhead : t.head = 1) :
    t.HasBinaryString bits :=
  ⟨hhead, h⟩

/-- Moving a cursor preserves its canonical binary contents.
@isnad1 id=hasbinar.1h3v.s4.c855afcba393 from=translated src=- shape=bdf7d0bd vocab=9de20cbd
-/
theorem HasBinaryContent.move {t : Tape} {bits : List Bool}
    (h : t.HasBinaryContent bits) (dir : Dir3) :
    (t.move dir).HasBinaryContent bits := by
  simpa only [HasBinaryContent, Tape.move_cells] using h

/-- Canonical binary contents contain no stray left marker after cell zero.
@isnad1 id=ne.2h3v.s4.8195d008fbcc from=translated src=- shape=7b504902 vocab=f24d013e
-/
theorem HasBinaryContent.cells_ne_start {t : Tape} {bits : List Bool}
    (h : t.HasBinaryContent bits) :
    ∀ j, 1 ≤ j → t.cells j ≠ Γ.start := by
  intro j hj
  let i := j - 1
  have hji : j = i + 1 := by omega
  by_cases hi : i < bits.length
  · rw [hji, h.1 i hi]
    exact Γ.ofBool_ne_start _
  · rw [hji, h.2 i (Nat.le_of_not_gt hi)]
    decide

/-- Canonical binary contents with the left marker at cell zero have exactly
the initialized cell contents, independently of the tape head.
@isnad1 id=eq.2h2v.s5.f455d3254e75 from=translated src=- shape=33970326 vocab=2ce028a4
-/
theorem HasBinaryContent.cells_eq_init {t : Tape} {bits : List Bool}
    (h : t.HasBinaryContent bits) (h0 : t.cells 0 = Γ.start) :
    t.cells = (Tape.init (bits.map Γ.ofBool)).cells := by
  funext j
  cases j with
  | zero => simpa using h0
  | succ i =>
      by_cases hi : i < bits.length
      · rw [h.1 i hi, Tape.init_ofBool_cells_lt bits i hi]
      · have hge : bits.length ≤ i := by omega
        rw [h.2 i hge, Tape.init_ofBool_cells_ge bits i hge]

/-- Overwriting one in-range binary cell preserves canonical contents and
updates exactly that bit.
@isnad1 id=hasbinar.3h4v.s5.43dea4b16112 from=translated src=- shape=85eb0dbd vocab=37cb1c79
-/
theorem HasBinaryContent.write_set {t : Tape} {bits : List Bool}
    {i : ℕ} (bit : Bool) (h : t.HasBinaryContent bits)
    (hhead : t.head = i + 1) (hi : i < bits.length) :
    (t.write (Γ.ofBool bit)).HasBinaryContent (bits.set i bit) := by
  rcases h with ⟨hbits, htail⟩
  have hhead0 : ¬t.head = 0 := by omega
  constructor
  · intro j hj
    rw [Tape.write, ite_eq_right hhead0]
    simp only
    rw [List.length_set] at hj
    rw [hhead]
    by_cases hij : i = j
    · subst j
      rw [Function.update_self, List.getElem_set]
      simp
    · have hne : i + 1 ≠ j + 1 := by omega
      rw [Function.update_of_ne (Ne.symm hne), hbits j hj,
        List.getElem_set]
      simp [hij]
  · intro j hj
    rw [Tape.write, ite_eq_right hhead0]
    simp only
    rw [List.length_set] at hj
    rw [hhead]
    have hne : i + 1 ≠ j + 1 := by omega
    rw [Function.update_of_ne (Ne.symm hne)]
    exact htail j hj

/-- Writing away from cell zero and then moving preserves the left marker.
@isnad1 id=eq.1h3v.s4.fe706aa0ce44 from=translated src=- shape=f865c676 vocab=feac8f2f
-/
theorem write_move_cell0 {t : Tape} (symbol : Γ) (dir : Dir3)
    (h0 : t.cells 0 = Γ.start) :
    ((t.write symbol).move dir).cells 0 = Γ.start := by
  rw [Tape.move_cells, Tape.write]
  split
  · exact h0
  · simp only
    rw [Function.update_of_ne (by omega)]
    exact h0

/-- A completed binary tape encodes exactly `bits` as its output string.
@isnad1 id=hasoutpu.1h2v.s3.036189784d39 from=translated src=- shape=8f6c20a1 vocab=90a9c0d7
-/
theorem hasOutput_of_hasBinaryString {t : Tape} {bits : List Bool}
    (h : t.HasBinaryString bits) : t.HasOutput bits :=
  ⟨h.2.1, h.2.2 bits.length le_rfl⟩

/-- A completed binary tape never contains `▷` after the left-end marker.
@isnad1 id=ne.2h3v.s4.cd4fab3b0f57 from=translated src=- shape=178de2f5 vocab=abaccc46
-/
theorem cells_ne_start_of_hasBinaryString {t : Tape} {bits : List Bool}
    (h : t.HasBinaryString bits) :
    ∀ j, j ≥ 1 → t.cells j ≠ Γ.start :=
  h.hasBinaryContent.cells_ne_start

/-- A completed binary tape with the left marker at cell `0` is exactly the
    standard initialized tape for those bits, moved to cell `1`. -/
theorem eq_init_move_right_of_hasBinaryString {t : Tape} {bits : List Bool}
    (h : t.HasBinaryString bits) (h0 : t.cells 0 = Γ.start) :
    t = (Tape.init (bits.map Γ.ofBool)).move Dir3.right := by
  apply Tape.ext
  · simpa only [Tape.move, Tape.init_head, Nat.zero_add] using h.1
  · exact h.hasBinaryContent.cells_eq_init h0

/-- A binary prefix with the left marker at cell zero has exactly the
canonical initialized cell contents, independently of its current head.
@isnad1 id=eq.2h2v.s5.d432fde28338 from=translated src=- shape=33970326 vocab=8ead51f5
-/
theorem HasBinaryPrefix.cells_eq_init {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) (h0 : t.cells 0 = Γ.start) :
    t.cells = (Tape.init (bits.map Γ.ofBool)).cells :=
  HasBinaryContent.cells_eq_init h.2 h0

/-- Bounded completed binary tapes expose exact initialized tape shape for
    some string whose length satisfies the same bound.
@isnad1 id=ex.2h2v.s5.7ed453569918 from=translated src=- shape=0c44fffa vocab=271cc294
-/
theorem exists_eq_init_move_right_of_hasBoundedBinaryString {t : Tape} {B : ℕ}
    (h : t.HasBoundedBinaryString B) (h0 : t.cells 0 = Γ.start) :
    ∃ bits : List Bool, bits.length ≤ B ∧
      t = (Tape.init (bits.map Γ.ofBool)).move Dir3.right := by
  obtain ⟨bits, hlen, hbits⟩ := h
  exact ⟨bits, hlen, eq_init_move_right_of_hasBinaryString hbits h0⟩

/-- A freshly initialized empty tape, moved right past `▷`, is an empty
    binary prefix.
@isnad1 id=hasbinar.0h0v.s3.d194e3031041 from=translated src=- shape=cf475935 vocab=7386517d
-/
theorem init_nil_move_right_hasBinaryPrefix_nil :
    ((Tape.init []).move Dir3.right).HasBinaryPrefix [] := by
  simp [HasBinaryPrefix, Tape.init, Tape.move]

/-- A standard initialized binary tape moved right to its first data cell is
a completed binary string.
@isnad1 id=hasbinar.0h1v.s3.1b45c498f6a4 from=translated src=- shape=00fa128c vocab=37314249
-/
theorem init_move_right_hasBinaryString (bits : List Bool) :
    ((Tape.init (bits.map Γ.ofBool)).move Dir3.right).HasBinaryString bits := by
  refine ⟨by simp [Tape.move], ?_, ?_⟩
  · intro i hi
    exact Tape.init_ofBool_cells_lt bits i hi
  · intro i hi
    exact Tape.init_ofBool_cells_ge bits i hi

/-- The head of an appendable binary prefix reads its first trailing blank.
@isnad1 id=eq.1h2v.s3.8a2e77fc128a from=translated src=- shape=8bbc0304 vocab=4a167b33
-/
theorem HasBinaryPrefix.read_blank {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : t.read = Γ.blank := by
  rw [Tape.read, h.1]
  exact h.2.2 bits.length le_rfl

/-- An appendable binary prefix already contains the advertised delimited
output, independently of its current head.
@isnad1 id=hasoutpu.1h2v.s3.20f30ecaaa17 from=translated src=- shape=8f6c20a1 vocab=d5c180bd
-/
theorem HasBinaryPrefix.hasOutput {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : t.HasOutput bits :=
  ⟨h.2.1, h.2.2 bits.length le_rfl⟩

/-- A freshly initialized binary tape starts with its whole string as the
remaining suffix.
@isnad1 id=hasbinar.0h1v.s3.09699754e4e5 from=translated src=- shape=00fa128c vocab=2af952a3
-/
theorem init_move_right_hasBinarySuffix (bits : List Bool) :
    ((Tape.init (bits.map Γ.ofBool)).move Dir3.right).HasBinarySuffix bits := by
  refine ⟨by simp [Tape.move, Tape.init], ?_, ?_, ?_⟩
  · intro i hi
    simpa [Tape.move, Tape.init, Nat.add_comm] using
      Tape.init_ofBool_cells_lt bits i hi
  · simp [Tape.move, Tape.init, Nat.add_comm]
  · intro j hj
    simp [Tape.move]
    exact Tape.init_ofBool_cells_ne_start bits j hj

/-- A completed binary string exposes the same bits as its remaining suffix.
@isnad1 id=hasbinar.1h2v.s3.a019bf078420 from=translated src=- shape=8f6c20a1 vocab=004f107a
-/
theorem HasBinaryString.hasBinarySuffix {t : Tape} {bits : List Bool}
    (h : t.HasBinaryString bits) : t.HasBinarySuffix bits := by
  refine ⟨by rw [h.1], ?_, ?_, cells_ne_start_of_hasBinaryString h⟩
  · intro i hi
    rw [h.1]
    simpa [Nat.add_comm] using h.2.1 i hi
  · rw [h.1]
    simpa [Nat.add_comm] using h.2.2 bits.length le_rfl

/-- A delimited output parked at cell one is a binary suffix cursor when the
tape has no stray left-end markers.
@isnad1 id=hasbinar.3h2v.s4.93878c8b3dae from=translated src=- shape=42ec85b5 vocab=fd3b048e
-/
theorem HasOutput.hasBinarySuffix {t : Tape} {bits : List Bool}
    (h : t.HasOutput bits) (hhead : t.head = 1) (hinv : t.StartInvariant) :
    t.HasBinarySuffix bits := by
  refine ⟨by rw [hhead], ?_, ?_, hinv.2⟩
  · intro i hi
    simpa [hhead, Nat.add_comm] using h.1 i hi
  · simpa [hhead, Nat.add_comm] using h.2

/-- The first symbol of a nonempty binary suffix is under the tape head.
@isnad1 id=eq.1h3v.s4.8bb9ccd7a751 from=translated src=- shape=ef96eea3 vocab=5f12c0e8
-/
theorem HasBinarySuffix.read_cons {t : Tape} {bit : Bool} {bits : List Bool}
    (h : t.HasBinarySuffix (bit :: bits)) :
    t.read = Γ.ofBool bit := by
  have hzero := h.2.1 0 (by simp)
  simpa [Tape.read] using hzero

/-- Moving right after reading the first bit exposes the remaining suffix.
@isnad1 id=hasbinar.1h3v.s4.28d8185ff91b from=translated src=- shape=842f9598 vocab=2b559687
-/
theorem HasBinarySuffix.move_right_cons {t : Tape} {bit : Bool}
    {bits : List Bool} (h : t.HasBinarySuffix (bit :: bits)) :
    (t.move Dir3.right).HasBinarySuffix bits := by
  refine ⟨by simp [Tape.move], ?_, ?_, ?_⟩
  · intro i hi
    have hcell := h.2.1 (i + 1) (by simpa using hi)
    simpa [Tape.move, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcell
  · have hcell := h.2.2.1
    simpa [Tape.move, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcell
  · intro j hj
    simpa [Tape.move_cells] using h.2.2.2 j hj

/-- An empty remaining suffix reads the terminating blank.
@isnad1 id=eq.1h1v.s3.92d9710ec114 from=translated src=- shape=5a6f9627 vocab=c71ea174
-/
theorem HasBinarySuffix.read_nil {t : Tape} (h : t.HasBinarySuffix []) :
    t.read = Γ.blank := by
  simpa [Tape.read] using h.2.2.1

/-- A binary suffix cursor never reads the left-end marker.
@isnad1 id=ne.1h2v.s3.78d87d6a8990 from=translated src=- shape=8bbc0304 vocab=d2a03401
-/
theorem HasBinarySuffix.read_ne_start {t : Tape} {bits : List Bool}
    (h : t.HasBinarySuffix bits) : t.read ≠ Γ.start :=
  h.2.2.2 t.head h.1

/-- Writing the next bit extends a binary prefix by one cell.
@isnad1 id=hasbinar.1h3v.s5.c5848bf04aa1 from=translated src=- shape=7e996cd6 vocab=2e3c8f5c
-/
theorem hasBinaryPrefix_write_bit {t : Tape} {bits : List Bool} (bit : Bool)
    (h : t.HasBinaryPrefix bits) :
    (t.writeAndMove (Γ.ofBool bit) Dir3.right).HasBinaryPrefix (bits ++ [bit]) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Tape.writeAndMove, Tape.write, Tape.move, h.1]
  · intro i hi
    unfold Tape.writeAndMove
    simp only [Tape.move]
    unfold Tape.write
    have hhead_ne : ¬t.head = 0 := by rw [h.1]; omega
    simp only [hhead_ne, ↓reduceIte]
    by_cases hidx : i = bits.length
    · have hcellidx : i + 1 = t.head := by rw [h.1, hidx]
      have hget : (bits ++ [bit])[i]'hi = bit := by
        subst hidx
        simp
      rw [hcellidx, Function.update_self, hget]
    · have hi_bits : i < bits.length := by
        rw [List.length_append, List.length_singleton] at hi
        omega
      have hcell := h.2.1 i hi_bits
      have hget : (bits ++ [bit])[i]'hi = bits[i]'hi_bits := by
        exact List.getElem_append_left (as := bits) (bs := [bit]) hi_bits
      have hne : t.head ≠ i + 1 := by rw [h.1]; omega
      rw [Function.update_of_ne (Ne.symm hne), hcell, hget]
  · intro i hi
    unfold Tape.writeAndMove
    simp only [Tape.move]
    unfold Tape.write
    have hhead_ne : ¬t.head = 0 := by rw [h.1]; omega
    simp only [hhead_ne, ↓reduceIte]
    have hne : t.head ≠ i + 1 := by
      rw [List.length_append, List.length_singleton] at hi
      rw [h.1]
      omega
    rw [Function.update_of_ne (Ne.symm hne)]
    exact h.2.2 i (by
      rw [List.length_append, List.length_singleton] at hi
      omega)

/-- Writing at the first blank appends one canonical binary cell.
@isnad1 id=hasbinar.2h3v.s5.47e88087e614 from=translated src=- shape=061180ba vocab=bd5a0be5
-/
theorem HasBinaryContent.write_append {t : Tape} {bits : List Bool}
    (bit : Bool) (h : t.HasBinaryContent bits)
    (hhead : t.head = bits.length + 1) :
    (t.write (Γ.ofBool bit)).HasBinaryContent (bits ++ [bit]) := by
  have hprefix : t.HasBinaryPrefix bits := ⟨hhead, h⟩
  exact (hasBinaryPrefix_write_bit bit hprefix).2

/-- Writing the next bit preserves the left-end marker cell.
@isnad1 id=eq.2h3v.s5.56c5052fdbed from=translated src=- shape=c7d8114f vocab=fa10e57d
-/
theorem hasBinaryPrefix_write_bit_cell0 {t : Tape} {bits : List Bool} (bit : Bool)
    (h : t.HasBinaryPrefix bits) (h0 : t.cells 0 = Γ.start) :
    (t.writeAndMove (Γ.ofBool bit) Dir3.right).cells 0 = Γ.start := by
  unfold Tape.writeAndMove
  rw [Tape.move_cells]
  unfold Tape.write
  have hhead_ne : ¬t.head = 0 := by rw [h.1]; omega
  simp only [hhead_ne, ↓reduceIte]
  have hne : t.head ≠ 0 := by rw [h.1]; omega
  rw [Function.update_of_ne (Ne.symm hne)]
  exact h0

/-- A binary prefix never contains `▷` after the left-end marker.
@isnad1 id=ne.2h3v.s4.2ded2e739235 from=translated src=- shape=178de2f5 vocab=e73e0e09
-/
theorem cells_ne_start_of_hasBinaryPrefix {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) :
    ∀ j, j ≥ 1 → t.cells j ≠ Γ.start :=
  HasBinaryContent.cells_ne_start h.2

/-- Moving a completed binary string's head to the first blank, without
    changing its cells, yields the corresponding appendable prefix.
@isnad1 id=hasbinar.3h3v.s5.557bcdfc62c7 from=translated src=- shape=4279ba8e vocab=2e608469
-/
theorem hasBinaryPrefix_of_hasBinaryString {t t' : Tape} {bits : List Bool}
    (hstring : t.HasBinaryString bits)
    (hhead : t'.head = bits.length + 1)
    (hcells : t'.cells = t.cells) :
    t'.HasBinaryPrefix bits := by
  refine ⟨hhead, ?_, ?_⟩
  · intro i hi
    rw [hcells]
    exact hstring.2.1 i hi
  · intro i hi
    rw [hcells]
    exact hstring.2.2 i hi

/-- Rewinding a binary prefix to cell one yields a completed binary string.
@isnad1 id=hasbinar.3h3v.s5.480567fdf522 from=translated src=- shape=d60dee7d vocab=bc6f1d48
-/
theorem hasBinaryString_of_hasBinaryPrefix {t t' : Tape} {bits : List Bool}
    (hprefix : t.HasBinaryPrefix bits)
    (hhead : t'.head = 1)
    (hcells : t'.cells = t.cells) :
    t'.HasBinaryString bits := by
  refine ⟨hhead, ?_, ?_⟩
  · intro i hi
    rw [hcells]
    exact hprefix.2.1 i hi
  · intro i hi
    rw [hcells]
    exact hprefix.2.2 i hi

end Tape

end Complexity
