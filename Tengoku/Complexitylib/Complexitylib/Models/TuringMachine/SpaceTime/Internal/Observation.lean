/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.SpaceTime.Defs
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Bounded-observation extensionality — proof internals

This module extracts the information recorded by a bounded tape observation
and a finite transducer snapshot. In particular, equal bounded work-tape
observations determine the symbols read by the transition function and remain
equal after applying the same write and move, provided both successor heads
remain inside the observed window.
-/

public section

namespace Complexity

namespace Tape

/-- Equal bounded observations have equal underlying head positions.
@isnad1 id=eq.3h3v.s5.d1edf13e3a6f from=translated src=- shape=02d11a9d vocab=79f5d14d
-/
theorem head_eq_of_boundedObs_eq {t u : Tape} {space : ℕ}
    (ht : t.head ≤ space) (hu : u.head ≤ space)
    (hobs : t.boundedObs space ht = u.boundedObs space hu) :
    t.head = u.head := by
  have h := congrArg (fun obs : BoundedObs space => obs.1.val) hobs
  simpa [boundedObs] using h

/-- Equal bounded observations agree on every cell in the observed window.
@isnad1 id=eq.3h4v.s6.65972f3b7126 from=translated src=- shape=272c317b vocab=d0bcb580
-/
theorem cells_eq_of_boundedObs_eq {t u : Tape} {space : ℕ}
    (ht : t.head ≤ space) (hu : u.head ≤ space)
    (hobs : t.boundedObs space ht = u.boundedObs space hu)
    (i : Fin (space + 1)) :
    t.cells i = u.cells i := by
  have h := congrArg (fun obs : BoundedObs space => obs.2 i) hobs
  simpa [boundedObs] using h

/-- Equal bounded observations read the same symbol.
@isnad1 id=eq.3h3v.s5.2413586b16cc from=translated src=- shape=cac1dd62 vocab=a11468be
-/
theorem read_eq_of_boundedObs_eq {t u : Tape} {space : ℕ}
    (ht : t.head ≤ space) (hu : u.head ≤ space)
    (hobs : t.boundedObs space ht = u.boundedObs space hu) :
    t.read = u.read := by
  have hhead := head_eq_of_boundedObs_eq ht hu hobs
  rw [Tape.read, Tape.read, hhead]
  exact cells_eq_of_boundedObs_eq ht hu hobs
    ⟨u.head, Nat.lt_succ_iff.mpr hu⟩

/-- Applying the same write and move to equal bounded observations produces
equal successor observations, as long as both successor heads remain inside
the same observed window.
@isnad1 id=eq.5h5v.s6.7ca74c6d4230 from=translated src=- shape=bbfb61a4 vocab=f1af25f1
-/
theorem boundedObs_writeAndMove_congr {t u : Tape} {space : ℕ}
    (ht : t.head ≤ space) (hu : u.head ≤ space)
    (hobs : t.boundedObs space ht = u.boundedObs space hu)
    (s : Γ) (d : Dir3)
    (ht' : (t.writeAndMove s d).head ≤ space)
    (hu' : (u.writeAndMove s d).head ≤ space) :
    (t.writeAndMove s d).boundedObs space ht' =
      (u.writeAndMove s d).boundedObs space hu' := by
  have hhead := head_eq_of_boundedObs_eq ht hu hobs
  apply Prod.ext
  · apply Fin.ext
    simp only [boundedObs, Tape.writeAndMove]
    cases d <;> simp only [Tape.move, Tape.write_head, hhead]
  · funext i
    simp only [boundedObs, Tape.writeAndMove, Tape.move_cells]
    have hcell := cells_eq_of_boundedObs_eq ht hu hobs i
    simp only [Tape.write]
    by_cases ht0 : t.head = 0
    · have hu0 : u.head = 0 := hhead.symm.trans ht0
      simp only [ht0, hu0, ↓reduceIte]
      exact hcell
    · have hu0 : u.head ≠ 0 := fun h => ht0 (hhead.trans h)
      simp only [ht0, hu0, ↓reduceIte]
      rw [← hhead]
      by_cases hi : (i : ℕ) = t.head
      · rw [hi, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hi, Function.update_of_ne hi]
        exact hcell

end Tape

namespace TM

variable {k : ℕ} {tm : TM k} {inputLength space : ℕ}

/-- Equal transducer snapshots record the same machine state.
@isnad1 id=eq.3h6v.s6.49da6768fd7c from=translated src=- shape=d70cadbf vocab=5f1824d0
-/
theorem state_eq_of_transducerSnapshot_eq {c d : Cfg k tm.Q}
    (hc : c.WithinAuxSpace inputLength space)
    (hd : d.WithinAuxSpace inputLength space)
    (hsnap : tm.transducerSnapshot c inputLength space hc =
      tm.transducerSnapshot d inputLength space hd) :
    c.state = d.state := by
  have h := congrArg (fun snap : tm.TransducerSnapshot inputLength space => snap.1) hsnap
  simpa [transducerSnapshot] using h

/-- Equal transducer snapshots record the same input-head position.
@isnad1 id=eq.3h6v.s6.1af833c3bbf3 from=translated src=- shape=d35fe01c vocab=ff9d45eb
-/
theorem input_head_eq_of_transducerSnapshot_eq {c d : Cfg k tm.Q}
    (hc : c.WithinAuxSpace inputLength space)
    (hd : d.WithinAuxSpace inputLength space)
    (hsnap : tm.transducerSnapshot c inputLength space hc =
      tm.transducerSnapshot d inputLength space hd) :
    c.input.head = d.input.head := by
  have h := congrArg
    (fun snap : tm.TransducerSnapshot inputLength space => snap.2.1.val) hsnap
  simpa [transducerSnapshot] using h

/-- When two snapshotted configurations share their read-only input contents,
equal snapshots make their input heads read the same symbol.
@isnad1 id=eq.4h6v.s6.0487cf860a2a from=translated src=- shape=352431b8 vocab=050b1126
-/
theorem input_read_eq_of_transducerSnapshot_eq {c d : Cfg k tm.Q}
    (hc : c.WithinAuxSpace inputLength space)
    (hd : d.WithinAuxSpace inputLength space)
    (hsnap : tm.transducerSnapshot c inputLength space hc =
      tm.transducerSnapshot d inputLength space hd)
    (hinput : c.input.cells = d.input.cells) :
    c.input.read = d.input.read := by
  rw [Tape.read, Tape.read, hinput,
    input_head_eq_of_transducerSnapshot_eq hc hd hsnap]

/-- Equal transducer snapshots contain equal bounded observations of each work
tape.
@isnad1 id=eq.3h7v.s6.eab5706d851a from=translated src=- shape=e7cc7181 vocab=3a487dea
-/
theorem work_boundedObs_eq_of_transducerSnapshot_eq {c d : Cfg k tm.Q}
    (hc : c.WithinAuxSpace inputLength space)
    (hd : d.WithinAuxSpace inputLength space)
    (hsnap : tm.transducerSnapshot c inputLength space hc =
      tm.transducerSnapshot d inputLength space hd) (i : Fin k) :
    (c.work i).boundedObs space (hc.1 i) =
      (d.work i).boundedObs space (hd.1 i) := by
  have h := congrArg
    (fun snap : tm.TransducerSnapshot inputLength space => snap.2.2.1 i) hsnap
  simpa [transducerSnapshot] using h

/-- Equal transducer snapshots record the same head position on each work
tape.
@isnad1 id=eq.3h7v.s6.56a2de651170 from=translated src=- shape=d1d3674b vocab=e914ca68
-/
theorem work_head_eq_of_transducerSnapshot_eq {c d : Cfg k tm.Q}
    (hc : c.WithinAuxSpace inputLength space)
    (hd : d.WithinAuxSpace inputLength space)
    (hsnap : tm.transducerSnapshot c inputLength space hc =
      tm.transducerSnapshot d inputLength space hd) (i : Fin k) :
    (c.work i).head = (d.work i).head :=
  Tape.head_eq_of_boundedObs_eq (hc.1 i) (hd.1 i)
    (work_boundedObs_eq_of_transducerSnapshot_eq hc hd hsnap i)

/-- Equal transducer snapshots read the same symbol on each work tape.
@isnad1 id=eq.3h7v.s6.216afd8efee4 from=translated src=- shape=e3ce4947 vocab=c603eb7d
-/
theorem work_read_eq_of_transducerSnapshot_eq {c d : Cfg k tm.Q}
    (hc : c.WithinAuxSpace inputLength space)
    (hd : d.WithinAuxSpace inputLength space)
    (hsnap : tm.transducerSnapshot c inputLength space hc =
      tm.transducerSnapshot d inputLength space hd) (i : Fin k) :
    (c.work i).read = (d.work i).read :=
  Tape.read_eq_of_boundedObs_eq (hc.1 i) (hd.1 i)
    (work_boundedObs_eq_of_transducerSnapshot_eq hc hd hsnap i)

/-- Equal transducer snapshots have equal output-head zero flags.
@isnad1 id=eq.3h6v.s6.cc57b6f28162 from=translated src=- shape=cff20f78 vocab=dd55e8a8
-/
theorem output_head_zero_eq_of_transducerSnapshot_eq {c d : Cfg k tm.Q}
    (hc : c.WithinAuxSpace inputLength space)
    (hd : d.WithinAuxSpace inputLength space)
    (hsnap : tm.transducerSnapshot c inputLength space hc =
      tm.transducerSnapshot d inputLength space hd) :
    decide (c.output.head = 0) = decide (d.output.head = 0) := by
  have h := congrArg
    (fun snap : tm.TransducerSnapshot inputLength space => snap.2.2.2.1) hsnap
  simpa [transducerSnapshot] using h

/-- Equal transducer snapshots agree on whether the output head is at the
exceptional immutable left-marker cell.
@isnad1 id=iff.3h6v.s6.9a3e5aef1731 from=translated src=- shape=dd8331e7 vocab=1276aa1b
-/
theorem output_head_eq_zero_iff_of_transducerSnapshot_eq {c d : Cfg k tm.Q}
    (hc : c.WithinAuxSpace inputLength space)
    (hd : d.WithinAuxSpace inputLength space)
    (hsnap : tm.transducerSnapshot c inputLength space hc =
      tm.transducerSnapshot d inputLength space hd) :
    c.output.head = 0 ↔ d.output.head = 0 := by
  have hflag := output_head_zero_eq_of_transducerSnapshot_eq hc hd hsnap
  constructor
  · intro hc0
    by_contra hd0
    simp [hc0, hd0] at hflag
  · intro hd0
    by_contra hc0
    simp [hc0, hd0] at hflag

/-- Equal transducer snapshots read the same output symbol.
@isnad1 id=eq.3h6v.s6.fe30ca746939 from=translated src=- shape=2297409c vocab=108bd653
-/
theorem output_read_eq_of_transducerSnapshot_eq {c d : Cfg k tm.Q}
    (hc : c.WithinAuxSpace inputLength space)
    (hd : d.WithinAuxSpace inputLength space)
    (hsnap : tm.transducerSnapshot c inputLength space hc =
      tm.transducerSnapshot d inputLength space hd) :
    c.output.read = d.output.read := by
  have h := congrArg
    (fun snap : tm.TransducerSnapshot inputLength space => snap.2.2.2.2) hsnap
  simpa [transducerSnapshot] using h

end TM

end Complexity
