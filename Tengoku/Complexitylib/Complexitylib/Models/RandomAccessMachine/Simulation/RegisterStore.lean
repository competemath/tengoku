/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Internal

/-!
# Sparse RAM register stores on Turing tapes

This module exposes the representation boundary used by the RAM-to-Turing-
machine simulation. A canonical finite list of nonzero address/value pairs
decodes to the RAM model's total register file. Functional reads and writes are
exact, every finite-support register file has a canonical representation, and
the self-delimiting binary snapshot codec round-trips.

The concrete length theorem is the first resource bridge for the reverse
simulation: if the program counter, entry count, addresses, and values all have
bit-width at most `w`, a snapshot with `m` entries occupies at most
`(m + 1) * (4 * w + 2)` tape cells.
-/

public section

namespace Complexity

namespace RAM

namespace RegisterStore

/-- Sparse writing implements functional update exactly when addresses are
unique.
@isnad1 id=eq.1h4v.s4.dfb033289b2a from=translated src=- shape=01a10f29 vocab=af548151
-/
theorem read_write (store : Store) (hstore : AddressesNodup store)
    (address value target : ℕ) :
    read (write store address value) target =
      Function.update (read store) address value target :=
  read_write_internal store hstore address value target

/-- Sparse writing preserves unique addresses and omission of zero values.
@isnad1 id=canonica.1h3v.s3.0e14022d0b66 from=translated src=- shape=a5572226 vocab=957062aa
-/
theorem write_canonical (store : Store) (hstore : Canonical store)
    (address value : ℕ) :
    Canonical (write store address value) :=
  write_canonical_internal store hstore address value

/-- Decoding after a sparse write is exactly functional update.
@isnad1 id=eq.1h3v.s4.dcd0a52d6188 from=translated src=- shape=f974db60 vocab=50217085
-/
theorem decode_write (store : Store) (hstore : AddressesNodup store)
    (address value : ℕ) :
    decode (write store address value) = Function.update (decode store) address value :=
  decode_write_internal store hstore address value

/-- Materializing any finite-support register file gives a canonical exact
representation.
@isnad1 id=represen.1h1v.s4.e2b62782af45 from=translated src=- shape=d890d4fd vocab=c990fac9
-/
theorem ofRegs_represents (regs : ℕ → ℕ)
    (hfinite : (Function.support regs).Finite) :
    Represents (ofRegs regs hfinite) regs :=
  ofRegs_represents_internal regs hfinite

/-- The canonical public-input store has at most one entry per initialized
register.
@isnad1 id=le.0h1v.s4.bba9eaa0203c from=translated src=- shape=8b217881 vocab=e344f6ec
-/
theorem initialStore_length_le (input : List Bool) :
    (initialStore input).length ≤ input.length + 1 :=
  initialStore_length_le_internal input

namespace WordCode

/-- A canonical word code parses to its value and leaves any suffix untouched.
@isnad1 id=eq.0h2v.s5.8aa19bb81ee8 from=translated src=- shape=8e107f55 vocab=a37c6498
-/
theorem decodePrefix?_encode_append (value : ℕ) (suffix : List Bool) :
    decodePrefix? (encode value ++ suffix) = some (value, suffix) :=
  decodePrefix?_encode_append_internal value suffix

/-- One self-delimiting word occupies twice its bit-width plus one cell.
@isnad1 id=eq.0h1v.s5.b7004e2397ed from=translated src=- shape=b25ace09 vocab=9eed61f5
-/
theorem encode_length (value : ℕ) :
    (encode value).length = 2 * bitlen value + 1 :=
  encode_length_internal value

end WordCode

namespace Entry

/-- A canonical address/value code parses exactly and leaves its suffix.
@isnad1 id=eq.0h2v.s5.9f83d9c043bd from=translated src=- shape=8e107f55 vocab=13f33d5a
-/
theorem decodePrefix?_encode_append (entry : Entry) (suffix : List Bool) :
    decodePrefix? (encode entry ++ suffix) = some (entry, suffix) :=
  decodePrefix?_encode_append_internal entry suffix

/-- An encoded entry charges twice the address width, twice the value width,
and two separators.
@isnad1 id=eq.0h1v.s5.1a705793cc67 from=translated src=- shape=e5aebdc2 vocab=598c03ac
-/
theorem encode_length (entry : Entry) :
    (encode entry).length = 2 * bitlen entry.1 + 2 * bitlen entry.2 + 2 :=
  encode_length_internal entry

end Entry

/-- One sparse write increases the actual encoded store by at most the code of
the address/value pair being written. Replacement and deletion can only make
this estimate smaller.
@isnad1 id=le.0h3v.s4.deb6b90b68a7 from=translated src=- shape=8ee337d3 vocab=d5247206
-/
theorem encodedStoreLength_write_le (store : Store) (address value : ℕ) :
    encodedStoreLength (write store address value) ≤
      encodedStoreLength store + (Entry.encode (address, value)).length :=
  encodedStoreLength_write_le_internal store address value

namespace Snapshot

/-- The explicit finite public-input snapshot decodes to `RAM.initCfg`.
@isnad1 id=represen.0h1v.s3.965720c21ce5 from=translated src=- shape=410a86eb vocab=43415d57
-/
theorem initial_represents (input : List Bool) :
    (initial input).Represents (RAM.initCfg input) :=
  initial_represents_internal input

/-- The public-input snapshot's intrinsic width is at most the width of
`|input| + 1`.
@isnad1 id=le.0h1v.s4.2ded6f01bd81 from=translated src=- shape=42862892 vocab=95d76a08
-/
theorem initial_width_le (input : List Bool) :
    (initial input).width ≤ bitlen (input.length + 1) :=
  initial_width_le_internal input

/-- Materializing a finite-support RAM configuration gives a canonical exact
snapshot.
@isnad1 id=represen.1h1v.s4.185df68694d1 from=translated src=- shape=589763ee vocab=5704827a
-/
theorem ofCfg_represents (cfg : Cfg)
    (hfinite : (Function.support cfg.regs).Finite) :
    (ofCfg cfg hfinite).Represents cfg :=
  ofCfg_represents_internal cfg hfinite

/-- One sparse interpreter instruction preserves canonicality.
@isnad1 id=canonica.1h2v.s3.87e63f5292c7 from=translated src=- shape=f9eba881 vocab=5e684a3b
-/
theorem stepInstr_canonical (instruction : Instr) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    Canonical (stepInstr instruction snapshot).store :=
  stepInstr_canonical_internal instruction snapshot hcanonical

/-- Decoding commutes exactly with one sparse interpreter instruction.
@isnad1 id=eq.1h2v.s4.9495d1ec564b from=translated src=- shape=2c7bf08c vocab=b4ca6d82
-/
theorem decode_stepInstr (instruction : Instr) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    (stepInstr instruction snapshot).decode =
      RAM.stepInstr instruction snapshot.decode :=
  decode_stepInstr_internal instruction snapshot hcanonical

/-- The selected sparse step preserves canonicality.
@isnad1 id=canonica.1h2v.s3.32bdc15dff5b from=translated src=- shape=f9eba881 vocab=05ba82d1
-/
theorem step_canonical (program : Program) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    Canonical (snapshot.step program).store :=
  step_canonical_internal program snapshot hcanonical

/-- Decoding commutes exactly with the selected RAM step.
@isnad1 id=eq.1h2v.s4.97f3c9a707bf from=translated src=- shape=2c7bf08c vocab=515009b5
-/
theorem decode_step (program : Program) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    (snapshot.step program).decode = RAM.step program snapshot.decode :=
  decode_step_internal program snapshot hcanonical

/-- One sparse interpreter instruction grows the intrinsic width only to the
maximum of the old width plus one, its fixed literal width, and its charged
logarithmic runtime width.
@isnad1 id=le.0h2v.s3.54aed0cc0e07 from=translated src=- shape=33e5716c vocab=f5e3b750
-/
theorem width_stepInstr_le (instruction : Instr) (snapshot : Snapshot) :
    (stepInstr instruction snapshot).width ≤ snapshot.stepWidthBound instruction :=
  width_stepInstr_le_internal instruction snapshot

/-- A selected sparse step is bounded by the fixed program's literal width and
the RAM step's logarithmic charge.
@isnad1 id=le.0h2v.s5.350edeac6e23 from=translated src=- shape=9deae861 vocab=7a714622
-/
theorem width_step_le (program : Program) (snapshot : Snapshot) :
    (snapshot.step program).width ≤
      max (snapshot.width + 1)
        (max (programStaticWidth program) (RAM.stepLogCost program snapshot.decode)) :=
  width_step_le_internal program snapshot

/-- Every finite sparse run preserves canonicality.
@isnad1 id=canonica.1h3v.s4.31472a8300d5 from=translated src=- shape=06e38695 vocab=7a7b8d6e
-/
theorem run_canonical (program : Program) (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    Canonical (snapshot.run program fuel).store :=
  run_canonical_internal program fuel snapshot hcanonical

/-- The complete sparse interpreter run decodes to the executable RAM run.
@isnad1 id=eq.1h3v.s4.67cb06e48cd0 from=translated src=- shape=47c119bc vocab=c3195a6d
-/
theorem decode_run (program : Program) (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).decode = RAM.run program fuel snapshot.decode :=
  decode_run_internal program fuel snapshot hcanonical

/-- Each RAM instruction materializes at most one additional sparse entry.
@isnad1 id=le.1h3v.s5.fa93e188b4b7 from=translated src=- shape=6993ba58 vocab=3fa0f057
-/
theorem length_run_le (program : Program) (fuel : ℕ) (snapshot : Snapshot) :
    Canonical snapshot.store →
    (snapshot.run program fuel).store.length ≤
      snapshot.store.length + RAM.unitTimeUpto program fuel snapshot.decode :=
  length_run_le_internal program fuel snapshot

/-- Along a canonical sparse run, width grows linearly with executed fuel, the
fixed program literal width, and accumulated logarithmic RAM time.
@isnad1 id=le.1h3v.s6.49b8ccce62ca from=translated src=- shape=e5a0ddfd vocab=67679855
-/
theorem width_run_le (program : Program) (fuel : ℕ) (snapshot : Snapshot)
    (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).width ≤
      snapshot.width + RAM.unitTimeUpto program fuel snapshot.decode *
        (programStaticWidth program + 1) +
        RAM.logTimeUpto program fuel snapshot.decode :=
  width_run_le_internal program fuel snapshot hcanonical

/-- The live sparse-store code has amortized growth controlled by the resources actually
charged by the RAM run. In particular, this avoids the spurious product of the
number of entries and the maximum entry width: each executed instruction pays
once for its fixed destination width and for the operand/result bits in its
logarithmic cost.
@isnad1 id=le.1h3v.s6.21a8492ac6d4 from=translated src=- shape=4eccc986 vocab=647294b1
-/
theorem encodedStoreLength_run_le (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    encodedStoreLength (snapshot.run program fuel).store ≤
      encodedStoreLength snapshot.store +
        4 * (RAM.unitTimeUpto program fuel snapshot.decode *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel snapshot.decode) :=
  encodedStoreLength_run_le_internal program fuel snapshot hcanonical

/-- Canonical snapshot serialization round-trips exactly.
@isnad1 id=eq.0h1v.s3.ea8e73c96fbb from=translated src=- shape=edb93955 vocab=369efae8
-/
theorem decode?_encode (snapshot : Snapshot) :
    decode? snapshot.encode = some snapshot :=
  decode?_encode_internal snapshot

/-- A width-`w`, `m`-entry RAM snapshot occupies at most
`(m + 1) * (4 * w + 2)` Turing-tape cells.
@isnad1 id=le.3h2v.s6.1badbcc71ea8 from=translated src=- shape=506687e1 vocab=81ded2d3
-/
theorem encode_length_le (snapshot : Snapshot) (width : ℕ)
    (hpc : bitlen snapshot.pc ≤ width)
    (hcount : bitlen snapshot.store.length ≤ width)
    (hstore : ∀ entry ∈ snapshot.store,
      bitlen entry.1 ≤ width ∧ bitlen entry.2 ≤ width) :
    snapshot.encode.length ≤ (snapshot.store.length + 1) * (4 * width + 2) :=
  encode_length_le_internal snapshot width hpc hcount hstore

/-- Every canonical snapshot code satisfies its intrinsic concrete tape-cell
envelope, without external side conditions.
@isnad1 id=le.0h1v.s3.7baf48facefe from=translated src=- shape=981f0160 vocab=1f770193
-/
theorem encode_length_le_sizeBound (snapshot : Snapshot) :
    snapshot.encode.length ≤ snapshot.sizeBound :=
  encode_length_le_sizeBound_internal snapshot

/-- A snapshot code is bounded by its actual live-entry encoding plus the two
header words. This is the width-sensitive alternative to the product envelope
`Snapshot.sizeBound`.
@isnad1 id=le.0h1v.s5.fbf063c1d851 from=translated src=- shape=6acbf135 vocab=dd4f12a9
-/
theorem encode_length_le_encodedStore (snapshot : Snapshot) :
    snapshot.encode.length ≤
      encodedStoreLength snapshot.store + 4 * snapshot.width + 2 :=
  encode_length_le_encodedStore_internal snapshot

/-- Combining the actual live-store charge with the width invariant gives a
linear-in-accumulated-cost representation bound for every canonical sparse
run, relative to the initial sparse encoding.
@isnad1 id=le.1h3v.s6.c8ea43c14def from=translated src=- shape=d7028e00 vocab=1c707ece
-/
theorem encode_run_length_le_amortized (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).encode.length ≤
      encodedStoreLength snapshot.store + 4 * snapshot.width +
        8 * (RAM.unitTimeUpto program fuel snapshot.decode *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel snapshot.decode) + 2 :=
  encode_run_length_le_amortized_internal program fuel snapshot hcanonical

/-- The materialized public-input store occupies at most one fixed-width entry
per initialized register. This records the current ABI's explicit
`O(n log n)` initialization term.
@isnad1 id=le.0h1v.s6.b1e37aa9c623 from=translated src=- shape=3d31c738 vocab=c816d5f3
-/
theorem encodedStoreLength_initial_le (input : List Bool) :
    encodedStoreLength (initialStore input) ≤
      (input.length + 1) * (4 * bitlen (input.length + 1) + 2) :=
  encodedStoreLength_initial_le_internal input

/-- Public-input specialization of the amortized live-representation bound.
The accumulated part is linear in charged RAM time; the separate
`n * bitlen n` term comes from eagerly materializing all nonzero input
registers in the current snapshot ABI.
@isnad1 id=le.0h3v.s7.48af76d3e867 from=translated src=- shape=95db6b6f vocab=769b5627
-/
theorem encode_initial_run_length_le_amortized
    (program : Program) (fuel : ℕ) (input : List Bool) :
    ((initial input).run program fuel).encode.length ≤
      (input.length + 1) * (4 * bitlen (input.length + 1) + 2) +
        4 * bitlen (input.length + 1) +
        8 * (RAM.logTimeUpto program fuel (RAM.initCfg input) *
          (programStaticWidth program + 2)) + 2 :=
  encode_initial_run_length_le_amortized_internal program fuel input

/-- The canonical code of every reachable snapshot has an explicit product
bound: entry count grows by at most one per step, while width grows only with
fixed program literals and charged logarithmic RAM time.
@isnad1 id=le.1h3v.s6.f2a878792526 from=translated src=- shape=786f8ce3 vocab=6bb57251
-/
theorem encode_run_length_le (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).encode.length ≤
      (snapshot.store.length + RAM.unitTimeUpto program fuel snapshot.decode + 1) *
        (4 * (snapshot.width + RAM.unitTimeUpto program fuel snapshot.decode *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel snapshot.decode) + 2) :=
  encode_run_length_le_internal program fuel snapshot hcanonical

/-- Eliminating actual step count via `unitTimeUpto ≤ logTimeUpto` gives a
pure logarithmic-time tape-size envelope. This is the quadratic representation
bound needed by the RAM-to-TM simulation.
@isnad1 id=le.1h3v.s6.375a01db82a0 from=translated src=- shape=1173be79 vocab=b745104f
-/
theorem encode_run_length_le_logTime (program : Program) (fuel : ℕ)
    (snapshot : Snapshot) (hcanonical : Canonical snapshot.store) :
    (snapshot.run program fuel).encode.length ≤
      (snapshot.store.length + RAM.logTimeUpto program fuel snapshot.decode + 1) *
        (4 * (snapshot.width + RAM.logTimeUpto program fuel snapshot.decode *
          (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel snapshot.decode) + 2) :=
  encode_run_length_le_logTime_internal program fuel snapshot hcanonical

/-- From the public RAM ABI, every reachable snapshot code has an explicit
quadratic envelope in input length, logarithmic RAM time, and one fixed program
constant.
@isnad1 id=le.0h3v.s7.238d93bb12a9 from=translated src=- shape=0a4ec66f vocab=769b5627
-/
theorem encode_initial_run_length_le_logTime
    (program : Program) (fuel : ℕ) (input : List Bool) :
    ((initial input).run program fuel).encode.length ≤
      (input.length + 1 + RAM.logTimeUpto program fuel (RAM.initCfg input) + 1) *
        (4 * (bitlen (input.length + 1) +
          RAM.logTimeUpto program fuel (RAM.initCfg input) *
            (programStaticWidth program + 1) +
          RAM.logTimeUpto program fuel (RAM.initCfg input)) + 2) :=
  encode_initial_run_length_le_logTime_internal program fuel input

end Snapshot

end RegisterStore

end RAM

end Complexity
