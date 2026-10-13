/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.ClearWork
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.ResetBinary.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.ResetBinary.Internal

/-!
# Resetting a binary work tape

This module exposes the framed time and space contracts for rewinding an
arbitrary canonical binary cursor and clearing it to the standard blank tape.
-/

public section

namespace Complexity

namespace TM

/-- Rewind canonical binary contents to cell one while preserving the complete
external tape frame.
@isnad1 id=hoaretim.6h7v.s7.62290eb39129 from=translated src=- shape=c9c5d645 vocab=2c7152bd
-/
theorem rewindBinaryWorkTM_hoareTime_frame {n : ℕ}
    (idx : Fin n) (bits : List Bool) (headBound : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : (work₀ idx).HasBinaryContent bits)
    (htargetStart : (work₀ idx).cells 0 = Γ.start)
    (htargetHead : 1 ≤ (work₀ idx).head ∧ (work₀ idx).head ≤ headBound)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (houtput : Parked out₀) :
    (rewindWorkTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work idx = (Tape.init (bits.map Γ.ofBool)).move Dir3.right ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        out = out₀)
      (headBound + 2) :=
  rewindBinaryWorkTM_hoareTime_frame_internal idx bits headBound inp₀ work₀
    out₀ htarget htargetStart htargetHead hinput hother houtput

/-- Rewind and clear canonical binary contents while preserving the complete
external tape frame.
@isnad1 id=hoaretim.6h7v.s7.5acdde5875d3 from=translated src=- shape=be39eff5 vocab=1f07d8fc
-/
theorem resetBinaryWorkTM_hoareTime_frame {n : ℕ}
    (idx : Fin n) (bits : List Bool) (headBound : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : (work₀ idx).HasBinaryContent bits)
    (htargetStart : (work₀ idx).cells 0 = Γ.start)
    (htargetHead : 1 ≤ (work₀ idx).head ∧ (work₀ idx).head ≤ headBound)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ idx → Parked (work₀ i))
    (houtput : Parked out₀) :
    (resetBinaryWorkTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx ((Tape.init []).move Dir3.right) ∧
        out = out₀)
      (resetBinaryWorkTime headBound bits.length) :=
  resetBinaryWorkTM_hoareTime_frame_internal idx bits headBound inp₀ work₀ out₀
    htarget htargetStart htargetHead hinput hother houtput

/-- Coarse all-prefix auxiliary-space envelope for binary reset.
@isnad1 id=withinau.3h9v.s6.eecab0f0b939 from=translated src=- shape=29b73ef7 vocab=b2e4a4e9
-/
theorem resetBinaryWorkTM_prefix_withinAuxSpace {n : ℕ}
    (idx : Fin n) (headBound bitLength inputLength initialSpace time : ℕ)
    (start current : Cfg n (resetBinaryWorkTM idx).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (resetBinaryWorkTM idx).reachesIn time start current)
    (htime : time ≤ resetBinaryWorkTime headBound bitLength) :
    current.WithinAuxSpace inputLength
      (initialSpace + resetBinaryWorkTime headBound bitLength) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Binary reset preserves one-way output safety.
@isnad1 id=istransd.0h2v.s3.ee6c1a77e67a from=translated src=- shape=20553ef8 vocab=19bde15d
-/
theorem resetBinaryWorkTM_isTransducer {n : ℕ} (idx : Fin n) :
    (resetBinaryWorkTM idx).IsTransducer := by
  unfold resetBinaryWorkTM
  exact (rewindWorkTM_isTransducer idx).seqTM (clearWorkTM_isTransducer idx)

end TM

end Complexity
