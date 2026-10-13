/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Combinators
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Tape.Encoding
public import Tengoku

/-!
# Tape cursors for the streaming circuit evaluator

The evaluator repeatedly rewinds, indexes, and extends canonical binary tapes.
`BinaryCursor` keeps the complete canonical cell contents fixed while exposing
the current zero-based read position. This is intentionally internal: the
neutral endpoint and suffix predicates remain the public tape API.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- A zero-based cursor into a tape with exact canonical binary contents. The
position may also equal the string length, in which case the cursor reads the
first trailing blank. -/
def BinaryCursor (t : Tape) (bits : List Bool) (position : ℕ) : Prop :=
  position ≤ bits.length ∧
  t.head = position + 1 ∧
  t.cells = (Tape.init (bits.map Γ.ofBool)).cells

/-- The boundary state reached after rewinding a canonical binary tape onto
its left-end marker. -/
def BinaryAtMarker (t : Tape) (bits : List Bool) : Prop :=
  t.head = 0 ∧ t.cells = (Tape.init (bits.map Γ.ofBool)).cells

namespace BinaryCursor

/-- An appendable binary prefix is a cursor at its first trailing blank once
its left marker is known.
@isnad1 id=binarycu.2h2v.s4.6f6d400085bc from=translated src=- shape=541cfb38 vocab=8b8f8f02
-/
theorem ofHasBinaryPrefix {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) (h₀ : t.cells 0 = Γ.start) :
    BinaryCursor t bits bits.length :=
  ⟨le_rfl, h.1, h.cells_eq_init h₀⟩

/-- Exact canonical cells and a head at cell one form the position-zero
cursor.
@isnad1 id=binarycu.2h2v.s5.96a7bb488735 from=translated src=- shape=345fc251 vocab=19f81bf9
-/
theorem atFirstBit {t : Tape} {bits : List Bool}
    (hhead : t.head = 1)
    (hcells : t.cells = (Tape.init (bits.map Γ.ofBool)).cells) :
    BinaryCursor t bits 0 :=
  ⟨Nat.zero_le _, by omega, hcells⟩

/-- A binary cursor carries the standard unique-left-marker invariant.
@isnad1 id=startinv.1h3v.s3.92049686f6f8 from=translated src=- shape=ddedd5d5 vocab=2a0a9fc9
-/
theorem startInvariant {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) : t.StartInvariant := by
  unfold Tape.StartInvariant
  rw [h.2.2]
  simpa [Tape.StartInvariant] using Tape.StartInvariant.init_ofBool bits

/-- A binary cursor is always parked away from the left-end marker.
@isnad1 id=ne.1h3v.s4.3fc9c32e5550 from=translated src=- shape=d194536f vocab=fdc766f6
-/
theorem read_ne_start {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) : t.read ≠ Γ.start :=
  h.startInvariant.read_ne_start (by rw [h.2.1]; omega)

/-- The controller's preserve action leaves a cursor tape unchanged.
@isnad1 id=eq.1h3v.s4.739eee7747ca from=translated src=- shape=aa19ac10 vocab=fe1e858e
-/
theorem preserve {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) :
    t.writeAndMove (TM.readBackWrite t.read) (TM.idleDir t.read) = t := by
  rw [TM.writeAndMove_readBack t h.read_ne_start]
  simp [TM.idleDir, h.read_ne_start, Tape.move]

/-- The controller's right action changes only the cursor head.
@isnad1 id=eq.1h3v.s4.79e6273387d8 from=translated src=- shape=b4400f27 vocab=8c4e6de8
-/
theorem applyMoveRight {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) :
    t.writeAndMove (TM.readBackWrite t.read) Dir3.right =
      t.move Dir3.right :=
  TM.writeAndMove_readBack t h.read_ne_start Dir3.right

/-- The controller's guarded-left action is an ordinary left move for a
binary cursor.
@isnad1 id=eq.1h3v.s4.1e7a89194354 from=translated src=- shape=60112539 vocab=641411ed
-/
theorem applyMoveLeft {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) :
    t.writeAndMove (TM.readBackWrite t.read) (TM.moveLeftDir t.read) =
      t.move Dir3.left := by
  rw [TM.writeAndMove_readBack t h.read_ne_start]
  simp [TM.moveLeftDir, h.read_ne_start]

/-- The guarded-left action from position zero enters the left-marker state
used by every controller rewind.
@isnad1 id=binaryat.1h2v.s4.e124f827f5b1 from=translated src=- shape=4e551072 vocab=0ad109ec
-/
theorem toMarker {t : Tape} {bits : List Bool}
    (h : BinaryCursor t bits 0) :
    BinaryAtMarker
      (t.writeAndMove (TM.readBackWrite t.read) (TM.moveLeftDir t.read)) bits := by
  rw [h.applyMoveLeft]
  refine ⟨?_, ?_⟩
  · simp [Tape.move, h.2.1]
  · simpa [Tape.move_cells] using h.2.2

/-- Reading a cursor strictly inside the string returns that indexed bit.
@isnad1 id=eq.2h3v.s5.838cfc1705f4 from=translated src=- shape=8aeb8b32 vocab=26696ad3
-/
theorem read_of_lt {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) (hlt : position < bits.length) :
    t.read = Γ.ofBool (bits[position]'hlt) := by
  rw [Tape.read, h.2.1, h.2.2]
  exact Tape.init_ofBool_cells_lt bits position hlt

/-- A cursor at the frontier reads the first trailing blank.
@isnad1 id=eq.1h2v.s4.e6c3f0fe6c7d from=translated src=- shape=8504e17b vocab=a32d93f3
-/
theorem read_frontier {t : Tape} {bits : List Bool}
    (h : BinaryCursor t bits bits.length) :
    t.read = Γ.blank := by
  rw [Tape.read, h.2.1, h.2.2]
  exact Tape.init_ofBool_cells_ge bits bits.length le_rfl

/-- A position-zero cursor exposes the neutral completed-string contract.
@isnad1 id=hasbinar.1h2v.s4.276ac9e5765c from=translated src=- shape=025d983e vocab=05e0deb5
-/
theorem hasBinaryString {t : Tape} {bits : List Bool}
    (h : BinaryCursor t bits 0) : t.HasBinaryString bits := by
  refine ⟨by simpa using h.2.1, ?_, ?_⟩
  · intro i hi
    rw [h.2.2]
    exact Tape.init_ofBool_cells_lt bits i hi
  · intro i hi
    rw [h.2.2]
    exact Tape.init_ofBool_cells_ge bits i hi

/-- A position-zero cursor exposes the whole string as its remaining suffix.
@isnad1 id=hasbinar.1h2v.s4.241d9795706f from=translated src=- shape=025d983e vocab=54da1813
-/
theorem hasBinarySuffix {t : Tape} {bits : List Bool}
    (h : BinaryCursor t bits 0) : t.HasBinarySuffix bits :=
  h.hasBinaryString.hasBinarySuffix

/-- Moving right advances an in-bounds cursor and preserves its contents.
@isnad1 id=binarycu.2h3v.s5.0cb6f3cc2915 from=translated src=- shape=bcddbc39 vocab=a653f65a
-/
theorem moveRight {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) (hlt : position < bits.length) :
    BinaryCursor (t.move Dir3.right) bits (position + 1) := by
  refine ⟨by omega, ?_, ?_⟩
  · simp [Tape.move, h.2.1]
  · simpa [Tape.move_cells] using h.2.2

/-- Moving left retreats a positive cursor and preserves its contents.
@isnad1 id=binarycu.2h3v.s5.6c710825097e from=translated src=- shape=78db7c4a vocab=5de5ae27
-/
theorem moveLeft {t : Tape} {bits : List Bool} {position : ℕ}
    (h : BinaryCursor t bits position) (hpos : 0 < position) :
    BinaryCursor (t.move Dir3.left) bits (position - 1) := by
  refine ⟨(Nat.sub_le position 1).trans h.1, ?_, ?_⟩
  · simp [Tape.move, h.2.1]
    omega
  · simpa [Tape.move_cells] using h.2.2

/-- A frontier cursor exposes the existing appendable-prefix contract.
@isnad1 id=hasbinar.1h2v.s3.258de11b0da9 from=translated src=- shape=faa1982f vocab=d59d67a2
-/
theorem hasBinaryPrefix {t : Tape} {bits : List Bool}
    (h : BinaryCursor t bits bits.length) :
    t.HasBinaryPrefix bits := by
  refine ⟨h.2.1, ?_, ?_⟩
  · intro i hi
    rw [h.2.2]
    exact Tape.init_ofBool_cells_lt bits i hi
  · intro i hi
    rw [h.2.2]
    exact Tape.init_ofBool_cells_ge bits i hi

/-- Writing at the frontier and moving right appends one bit and leaves a new
frontier cursor.
@isnad1 id=binarycu.1h3v.s5.7c491ea1cd07 from=translated src=- shape=b97a44a0 vocab=e9b5cadf
-/
theorem append {t : Tape} {bits : List Bool} (bit : Bool)
    (h : BinaryCursor t bits bits.length) :
    BinaryCursor (t.writeAndMove (Γ.ofBool bit) Dir3.right)
      (bits ++ [bit]) (bits ++ [bit]).length := by
  have hprefix := h.hasBinaryPrefix
  have hprefix' := Tape.hasBinaryPrefix_write_bit bit hprefix
  have hzero' := Tape.hasBinaryPrefix_write_bit_cell0 bit hprefix h.startInvariant.1
  exact ofHasBinaryPrefix hprefix' hzero'

/-- Writable-alphabet form of `append`, matching the controller transition
exactly.
@isnad1 id=binarycu.1h3v.s5.edfeab34f76e from=translated src=- shape=bb07e8dd vocab=31dc249b
-/
theorem appendWritable {t : Tape} {bits : List Bool} (bit : Bool)
    (h : BinaryCursor t bits bits.length) :
    BinaryCursor (t.writeAndMove (Γw.ofBool bit).toΓ Dir3.right)
      (bits ++ [bit]) (bits ++ [bit]).length := by
  rw [Γw.ofBool_toΓ]
  exact h.append bit

end BinaryCursor

namespace BinaryAtMarker

/-- A canonical marker state reads the unique left-end marker.
@isnad1 id=eq.1h2v.s3.1e5466ed6a10 from=translated src=- shape=8bbc0304 vocab=98507f79
-/
theorem read_start {t : Tape} {bits : List Bool}
    (h : BinaryAtMarker t bits) : t.read = Γ.start := by
  rw [Tape.read, h.1, h.2]
  simp

/-- A canonical marker state carries the standard tape invariant.
@isnad1 id=startinv.1h2v.s3.86e8ed5d5fcb from=translated src=- shape=cc170e3a vocab=85cbaa97
-/
theorem startInvariant {t : Tape} {bits : List Bool}
    (h : BinaryAtMarker t bits) : t.StartInvariant := by
  unfold Tape.StartInvariant
  rw [h.2]
  simpa [Tape.StartInvariant] using Tape.StartInvariant.init_ofBool bits

/-- Writing back at the immutable marker and moving right is exactly an
ordinary right move.
@isnad1 id=eq.1h2v.s4.73ba4f2453c8 from=translated src=- shape=4d28182b vocab=91eb24c7
-/
theorem applyMoveRight {t : Tape} {bits : List Bool}
    (h : BinaryAtMarker t bits) :
    t.writeAndMove (TM.readBackWrite t.read) Dir3.right =
      t.move Dir3.right := by
  show (t.write (TM.readBackWrite t.read)).move Dir3.right = _
  rw [Tape.write, ite_eq_left h.1]

/-- The controller's marker bounce returns to the position-zero cursor.
@isnad1 id=binarycu.1h2v.s4.7a9a38bdada7 from=translated src=- shape=8c689ef1 vocab=e4535967
-/
theorem returnToFirstBit {t : Tape} {bits : List Bool}
    (h : BinaryAtMarker t bits) :
    BinaryCursor
      (t.writeAndMove (TM.readBackWrite t.read) Dir3.right) bits 0 := by
  rw [h.applyMoveRight]
  apply BinaryCursor.atFirstBit
  · simp [Tape.move, h.1]
  · simpa [Tape.move_cells] using h.2

end BinaryAtMarker

end Internal

end Machine

end CircuitCode

end Complexity
