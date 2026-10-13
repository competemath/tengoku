/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Internal.Sem
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Internal.Out

/-!
# Linear-time canonical binary subtraction

This module exposes a concrete three-tape ripple-borrow subtractor. It preserves
two canonical little-endian operands, writes their truncated natural-number
difference to a fresh zero result tape, restores every owned head to cell one,
and preserves the complete external tape frame. Its running time is linear in
the operand bit widths.
-/

public section

namespace Complexity

namespace BinaryRippleSub

/-- Canonical ripple-borrow subtraction agrees with natural-number monus.
@isnad1 id=eq.0h2v.s4.772a026966f3 from=translated src=- shape=cd8271d2 vocab=eaee75c9
-/
theorem subtract_natBits (lhs rhs : ℕ) :
    subtract lhs.bits rhs.bits = (lhs - rhs).bits :=
  subtract_natBits_internal lhs rhs

end BinaryRippleSub

namespace TM

/-- The complete subtractor has a linear bit-width envelope.
@isnad1 id=le.0h2v.s5.f0b5536318eb from=translated src=- shape=6f1d15fb vocab=aa4274c1
-/
theorem binaryRippleSubTime_le (lhs rhs : ℕ) :
    binaryRippleSubTime lhs rhs ≤ 3 * (lhs.size + rhs.size) + 10 :=
  binaryRippleSubTime_le_internal lhs rhs

/-- Framed time contract for truncated subtraction. Both operands are restored,
the initially-zero result becomes their natural-number difference, and every
unrelated tape is preserved exactly.
@isnad1 id=hoaretim.7h9v.s7.7e29604f8895 from=translated src=- shape=85c77d4f vocab=1840a119
-/
theorem binaryRippleSubTM_hoareTime_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryNat lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryNat rhs)
    (hresult : (work₀ resultIdx).HasBinaryNat 0)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      Parked (work₀ i))
    (houtput : Parked out₀) :
    (binaryRippleSubTM lhsIdx rhsIdx resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work lhsIdx).HasBinaryNat lhs ∧
        (work rhsIdx).HasBinaryNat rhs ∧
        (work resultIdx).HasBinaryNat (lhs - rhs) ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (binaryRippleSubTime lhs rhs) :=
  binaryRippleSubTM_hoareTime_frame_internal lhsIdx rhsIdx resultIdx
    hdistinct lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother
    houtput

/-- Reachability form of the framed subtraction theorem.
@isnad1 id=ex.7h9v.s8.2ce041c84c3f from=translated src=- shape=5b69d73d vocab=56dfddf1
-/
theorem binaryRippleSubTM_reachesIn_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
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
      time ≤ binaryRippleSubTime lhs rhs ∧
      (binaryRippleSubTM lhsIdx rhsIdx resultIdx).reachesIn time
        { state := (binaryRippleSubTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryRippleSubTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work lhsIdx).HasBinaryNat lhs ∧
      (c'.work rhsIdx).HasBinaryNat rhs ∧
      (c'.work resultIdx).HasBinaryNat (lhs - rhs) ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  exact binaryRippleSubTM_hoareTime_frame lhsIdx rhsIdx resultIdx hdistinct
    lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother houtput
    inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩

/-- All-prefix auxiliary-space contract obtained from the concrete linear
time bound.
@isnad1 id=hoaretim.8h11v.s7.2a010382696c from=translated src=- shape=c8d00981 vocab=b6da8ee3
-/
theorem binaryRippleSubTM_hoareTimeSpace_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryRippleSubDistinct lhsIdx rhsIdx resultIdx)
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
      ({ state := (binaryRippleSubTM lhsIdx rhsIdx resultIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (binaryRippleSubTM lhsIdx rhsIdx resultIdx).Q).WithinAuxSpace
          inputLength initialSpace) :
    (binaryRippleSubTM lhsIdx rhsIdx resultIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work lhsIdx).HasBinaryNat lhs ∧
        (work rhsIdx).HasBinaryNat rhs ∧
        (work resultIdx).HasBinaryNat (lhs - rhs) ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (binaryRippleSubTime lhs rhs) inputLength
      (initialSpace + binaryRippleSubTime lhs rhs) :=
  binaryRippleSubTM_hoareTimeSpace_frame_internal lhsIdx rhsIdx resultIdx
    hdistinct lhs rhs inputLength initialSpace inp₀ work₀ out₀ hlhs hrhs
    hresult hinput hother houtput hinitial

/-- Canonical subtraction never moves the public output head left.
@isnad1 id=istransd.0h4v.s4.51f61becfbaf from=translated src=- shape=0b195b8b vocab=3c7422f2
-/
theorem binaryRippleSubTM_isTransducer {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) :
    (binaryRippleSubTM lhsIdx rhsIdx resultIdx).IsTransducer :=
  binaryRippleSubTM_isTransducer_internal lhsIdx rhsIdx resultIdx

end TM

end Complexity
