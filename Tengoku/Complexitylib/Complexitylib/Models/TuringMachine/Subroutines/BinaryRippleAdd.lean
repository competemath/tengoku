/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Internal

/-!
# Linear-time canonical binary addition

This module exposes a concrete three-tape ripple-carry adder. It preserves two
canonical little-endian operands, writes their canonical sum to a fresh zero
result tape, restores every owned head to cell one, and preserves the complete
external tape frame. Its running time is linear in the operand bit widths.

The older `TM.binaryAddIntoTM` remains useful as a value-iterating count-up
routine; complexity-sensitive RAM simulation should use this width-linear
machine instead.
-/

public section

namespace Complexity

namespace BinaryRippleAdd

/-- Ripple carry over canonical little-endian encodings computes addition.
@isnad1 id=eq.0h2v.s4.d82aeeea3dff from=translated src=- shape=2a6c52fd vocab=1a265611
-/
theorem ripple_natBits (lhs rhs : ℕ) :
    ripple false lhs.bits rhs.bits = (lhs + rhs).bits :=
  ripple_natBits_internal lhs rhs

end BinaryRippleAdd

namespace TM

/-- The scan bound is one more than the larger operand width.
@isnad1 id=eq.0h2v.s4.6072d611da7c from=translated src=- shape=5175d73b vocab=a6a28ab8
-/
theorem binaryRippleAddScanTime_natBits (lhs rhs : ℕ) :
    binaryRippleAddScanTime lhs.bits rhs.bits =
      max lhs.size rhs.size + 1 :=
  binaryRippleAddScanTime_natBits_internal lhs rhs

/-- Addition increases binary width by at most one over the larger operand.
@isnad1 id=le.0h2v.s5.3e8ec7acb64a from=translated src=- shape=67d5ad27 vocab=fc226128
-/
theorem binaryRippleAdd_sum_size_le (lhs rhs : ℕ) :
    (lhs + rhs).size ≤ max lhs.size rhs.size + 1 :=
  size_add_le_max_add_one_internal lhs rhs

/-- The complete scan-and-rewind machine has a linear bit-width envelope.
@isnad1 id=le.0h2v.s5.c9fc0290a194 from=translated src=- shape=6f1d15fb vocab=01b8c483
-/
theorem binaryRippleAddTime_le (lhs rhs : ℕ) :
    binaryRippleAddTime lhs rhs ≤
      3 * (lhs.size + rhs.size) + 14 :=
  binaryRippleAddTime_le_internal lhs rhs

/-- Framed time contract for canonical addition. Both operands are restored,
the initially-zero result becomes their sum, and every unrelated tape is
preserved exactly.
@isnad1 id=hoaretim.7h9v.s7.1db4b89118ef from=translated src=- shape=85c77d4f vocab=dc34fafc
-/
theorem binaryRippleAddTM_hoareTime_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryRippleAddTM lhsIdx rhsIdx resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work lhsIdx).HasBinaryNat lhs ∧
        (work rhsIdx).HasBinaryNat rhs ∧
        (work resultIdx).HasBinaryNat (lhs + rhs) ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (binaryRippleAddTime lhs rhs) :=
  binaryRippleAddTM_hoareTime_frame_internal lhsIdx rhsIdx resultIdx
    hdistinct lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother
    houtput

/-- Reachability form of the framed addition theorem.
@isnad1 id=ex.7h9v.s8.8f7694f78cf0 from=translated src=- shape=5b69d73d vocab=166d1721
-/
theorem binaryRippleAddTM_reachesIn_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀) :
    ∃ c' time,
      time ≤ binaryRippleAddTime lhs rhs ∧
      (binaryRippleAddTM lhsIdx rhsIdx resultIdx).reachesIn time
        { state := (binaryRippleAddTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryRippleAddTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work lhsIdx).HasBinaryNat lhs ∧
      (c'.work rhsIdx).HasBinaryNat rhs ∧
      (c'.work resultIdx).HasBinaryNat (lhs + rhs) ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  exact binaryRippleAddTM_hoareTime_frame lhsIdx rhsIdx resultIdx hdistinct
    lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother houtput
    inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩

/-- All-prefix auxiliary-space contract obtained from the concrete linear
time bound.
@isnad1 id=hoaretim.8h11v.s7.1e13428375cf from=translated src=- shape=e98a7881 vocab=d8484ad4
-/
theorem binaryRippleAddTM_hoareTimeSpace_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleAddDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀)
    (hinitial :
      ({ state := (binaryRippleAddTM lhsIdx rhsIdx resultIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (binaryRippleAddTM lhsIdx rhsIdx resultIdx).Q).WithinAuxSpace
          inputLength initialSpace) :
    (binaryRippleAddTM lhsIdx rhsIdx resultIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work lhsIdx).HasBinaryNat lhs ∧
        (work rhsIdx).HasBinaryNat rhs ∧
        (work resultIdx).HasBinaryNat (lhs + rhs) ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (binaryRippleAddTime lhs rhs) inputLength
      (initialSpace + binaryRippleAddTime lhs rhs) :=
  binaryRippleAddTM_hoareTimeSpace_frame_internal lhsIdx rhsIdx resultIdx
    hdistinct lhs rhs inputLength initialSpace inp₀ work₀ out₀ hlhs hrhs
    hresult hinput hother houtput hinitial

/-- Canonical addition never moves the public output head left.
@isnad1 id=istransd.0h4v.s4.051116410af2 from=translated src=- shape=0b195b8b vocab=17a8832c
-/
theorem binaryRippleAddTM_isTransducer {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) :
    (binaryRippleAddTM lhsIdx rhsIdx resultIdx).IsTransducer :=
  binaryRippleAddTM_isTransducer_internal lhsIdx rhsIdx resultIdx

end TM

end Complexity
