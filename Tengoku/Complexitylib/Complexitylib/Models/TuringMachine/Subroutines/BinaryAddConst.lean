/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst.Internal

/-!
# Addition of a fixed natural to a canonical binary tape

This module exposes the literal-frame and resource contracts for a finite
sequence of binary successors compiled from a hardwired natural constant.

## Main results

- `binaryAddConstTM_reachesIn_frame` gives the exact runtime and endpoint.
- `binaryAddConstTM_hoareTime_frame` packages the exact literal frame.
- `binaryAddConstTM_hoareTimeSpace_frame` gives a width-based prefix bound.
- `binaryAddConstTM_isTransducer` proves append-only-output safety.
-/

public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Fixed-constant addition has the advertised exact runtime and changes only
the destination tape.
@isnad1 id=reachesi.4h7v.s6.c3333f41cf21 from=translated src=- shape=0a340e48 vocab=c1cb1de4
-/
theorem binaryAddConstTM_reachesIn_frame
    (idx : Fin n) (constant dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hdst : (work₀ idx).HasBinaryNat dstValue)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryAddConstTM idx constant).reachesIn
      (binaryAddConstTime constant dstValue)
      { state := (binaryAddConstTM idx constant).qstart
        input := inp₀
        work := work₀
        output := out₀ }
      { state := (binaryAddConstTM idx constant).qhalt
        input := inp₀
        work := Function.update work₀ idx
          ((Tape.init ((dstValue + constant).bits.map Γ.ofBool)).move
            Dir3.right)
        output := out₀ } :=
  binaryAddConstTM_reachesIn_frame_internal idx constant dstValue inp₀ work₀
    out₀ hdst hinp hother hout

/-- Time-bounded literal-frame contract for fixed-constant addition.
@isnad1 id=hoaretim.4h7v.s7.ba48aa734094 from=translated src=- shape=7853f819 vocab=dc00f7dc
-/
theorem binaryAddConstTM_hoareTime_frame
    (idx : Fin n) (constant dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hdst : (work₀ idx).HasBinaryNat dstValue)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryAddConstTM idx constant).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx
          ((Tape.init ((dstValue + constant).bits.map Γ.ofBool)).move
            Dir3.right) ∧
        out = out₀)
      (binaryAddConstTime constant dstValue) :=
  binaryAddConstTM_hoareTime_frame_internal idx constant dstValue inp₀ work₀
    out₀ hdst hinp hother hout

/-- Every prefix of fixed-constant addition respects a bound controlled by
the final destination width.
@isnad1 id=hoaretim.6h9v.s7.fe373bbf97af from=translated src=- shape=78cef197 vocab=a9101d62
-/
theorem binaryAddConstTM_hoareTimeSpace_frame
    (idx : Fin n) (constant dstValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hdst : (work₀ idx).HasBinaryNat dstValue)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryAddConstTM idx constant).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx
          ((Tape.init ((dstValue + constant).bits.map Γ.ofBool)).move
            Dir3.right) ∧
        out = out₀)
      (binaryAddConstTime constant dstValue) inputLength
      (binaryAddConstSpace initialSpace constant dstValue) :=
  binaryAddConstTM_hoareTimeSpace_frame_internal idx constant dstValue
    inputLength initialSpace inp₀ work₀ out₀ hdst hinp hother hout
    hworkSpace hinputSpace

/-- Fixed-constant addition never moves its output head left.
@isnad1 id=istransd.0h3v.s3.a9fb4cfcaa2b from=translated src=- shape=1e848c5f vocab=9b869187
-/
theorem binaryAddConstTM_isTransducer (idx : Fin n) (constant : ℕ) :
    (binaryAddConstTM idx constant).IsTransducer :=
  binaryAddConstTM_isTransducer_internal idx constant

end TM

end Complexity
