/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Tengoku.Seed.Algebra.BigOperators.Fin
public import Tengoku.Cslib.Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Redirecting the output to a work tape

`outputToTape tm` behaves like `tm`, except that whatever `tm` would append to the write-only
output tape is written on a fresh work tape instead, whose head always stands at the write
frontier.

Since the output is append-only, the frontier position is a *function of the configuration* —
the length of the output so far — so the redirected machine mirrors the original through the
configuration map `outCfg`. The main lemmas show that one step and an entire run of the redirected
machine mirror the corresponding step and run of `tm`.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `tm`, with its output writes redirected onto a fresh last work tape, whose head always stands
at the write frontier.-/
@[expose] public def outputToTape (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol State where
  q₀ := tm.q₀
  tr q inp work :=
    let a := tm.tr q inp fun j => work j.castSucc
    { inputTape := a.inputTape
      workTapes := Fin.lastCases
        (match a.output with
          | none => (none, 0)
          | some s => (some (some s), 1))
        (fun j => a.workTapes j)
      output := none
      state := a.state }

/-- A configuration of `tm`, as the redirected machine sees it: the output so far sits on the
last work tape with the head at its end, and the real output is empty.-/
@[expose] public def outCfg (c : Cfg k Symbol State input) :
    Cfg (k + 1) Symbol State input :=
  ⟨c.state, c.inputPos,
    Fin.lastCases (tapeOfList c.output) (fun j => c.workTapes j),
    Fin.lastCases (c.output.length : ℤ) (fun j => c.workTapePos j),
    []⟩

/--
@isnad1 id=eq.0h5v.s5.8f2aa9b2c95a from=translated src=- shape=3fcb6d00 vocab=26bb7695
-/
@[simp]
public lemma outCfg_inputSymbol (c : Cfg k Symbol State input) :
    (outCfg c).inputSymbol = c.inputSymbol := rfl

/--
@isnad1 id=eq.0h5v.s5.2f94d3a3bd75 from=translated src=- shape=01854c13 vocab=492cf212
-/
@[simp]
public lemma outCfg_workTapes_last (c : Cfg k Symbol State input) :
    (outCfg c).workTapes (Fin.last k) = tapeOfList c.output := by
  simp [outCfg]

/--
@isnad1 id=eq.0h6v.s5.49339fcf93f3 from=translated src=- shape=524af2e5 vocab=1974a6bc
-/
@[simp]
public lemma outCfg_workTapes_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapes j.castSucc = c.workTapes j := by
  simp [outCfg]

/--
@isnad1 id=eq.0h5v.s5.f8f27f4578e8 from=translated src=- shape=534909fe vocab=6a695bb6
-/
@[simp]
public lemma outCfg_workTapePos_last (c : Cfg k Symbol State input) :
    (outCfg c).workTapePos (Fin.last k) = (c.output.length : ℤ) := by
  simp [outCfg]

/--
@isnad1 id=eq.0h6v.s5.80cac6a3634a from=translated src=- shape=096a29ee vocab=8e5cc93b
-/
@[simp]
public lemma outCfg_workTapePos_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapePos j.castSucc = c.workTapePos j := by
  simp [outCfg]

/--
@isnad1 id=eq.0h6v.s5.e179f9ec29bf from=translated src=- shape=126668a5 vocab=fc8aad1b
-/
@[simp]
public lemma outCfg_workTapeSymbols_castSucc (c : Cfg k Symbol State input) (j : Fin k) :
    (outCfg c).workTapeSymbols j.castSucc = c.workTapeSymbols j := by
  simp [Cfg.workTapeSymbols]

/-- The redirection is a step-semiconjugation.
@isnad1 id=eq.0h6v.s6.6239eb3448df from=translated src=- shape=a44e64b9 vocab=96d108b4
-/
public lemma step_outCfg (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input) :
    tm.outputToTape.step (outCfg c) = outCfg (tm.step c) := by
  cases hq : c.state with
  | none => simp [outCfg, hq]
  | some q =>
    rw [step_apply_of_state (cfg := outCfg c) hq, step_apply_of_state hq]
    simp only [outputToTape, outCfg_inputSymbol, outCfg_workTapeSymbols_castSucc]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases with
    | cast j => simp
    | last =>
      cases h : (tm.tr q c.inputSymbol c.workTapeSymbols).output <;>
        simp [h, tapeOfList_append_single, SignType.cast]

/-- The redirected run mirrors the original.
@isnad1 id=eq.0h7v.s6.73a6646df79d from=translated src=- shape=64d0282f vocab=3cb1d90d
-/
public lemma runFrom_outCfg (tm : MultiTapeTM k Symbol State) (c : Cfg k Symbol State input)
    (n : ℕ) :
    tm.outputToTape.runFrom (outCfg c) n = outCfg (tm.runFrom c n) :=
  (Function.Semiconj.iterate_right (fun c => (step_outCfg tm c).symm) n c).symm

section WithOutput

/-- `outputToTape tm` never writes the real output, so replacing it commutes with a step.
@isnad1 id=eq.0h7v.s7.5084e406ae36 from=translated src=- shape=44cc8e1c vocab=f4eaba60
-/
public lemma step_outputToTape_withOutput (tm : MultiTapeTM k Symbol State)
    (c : Cfg (k + 1) Symbol State input) (out : List Symbol) :
    tm.outputToTape.step (c.withOutput out) = (tm.outputToTape.step c).withOutput out := by
  cases hq : c.state with
  | none => simp [hq]
  | some q =>
    rw [step_apply_of_state (cfg := c.withOutput out) hq, step_apply_of_state hq]
    exact Cfg.ext rfl rfl rfl rfl (by simp [outputToTape])

/-- The redirected run commutes with the real output already present.
@isnad1 id=eq.0h8v.s7.a386383e992f from=translated src=- shape=eefd6e60 vocab=af0a3f38
-/
public lemma runFrom_outputToTape_withOutput (tm : MultiTapeTM k Symbol State)
    (c : Cfg (k + 1) Symbol State input) (out : List Symbol) (n : ℕ) :
    tm.outputToTape.runFrom (c.withOutput out) n = (tm.outputToTape.runFrom c n).withOutput out :=
  (Function.Semiconj.iterate_right (f := (Cfg.withOutput · out))
    (fun c => (step_outputToTape_withOutput tm c out).symm) n c).symm

/-- `outputToTape`'s space does not depend on the real output already present.
@isnad1 id=eq.0h8v.s6.502221f31ad8 from=translated src=- shape=b1534229 vocab=f9e922cf
-/
public lemma spaceUsed_outputToTape_withOutput (tm : MultiTapeTM k Symbol State)
    (c : Cfg (k + 1) Symbol State input) (out : List Symbol) (u : ℕ) :
    tm.outputToTape.spaceUsed (c.withOutput out) u = tm.outputToTape.spaceUsed c u := by
  refine spaceUsed_eq_of_workTapePos _ _ u fun m hm => ?_
  rw [runFrom_outputToTape_withOutput]; rfl

end WithOutput

/-- The initial configuration of the redirected machine is the original's through `outCfg`.
@isnad1 id=eq.0h5v.s6.ca93795b0b14 from=translated src=- shape=e21c0391 vocab=320ab9bf
-/
public lemma initCfg_outputToTape (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.outputToTape.initCfg input = outCfg (tm.initCfg input) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [initCfg, Cfg.init]

/-- **Space of the output-redirected machine.** The `k` inner tapes visit exactly what the original
does, and the frontier head only walks between the initial and the final length of the output, so
the redirection costs at most the final output length plus one.
@isnad1 id=le.0h7v.s6.2f5293501e46 from=translated src=- shape=49d83446 vocab=f3e01a0b
-/
public lemma spaceUsed_outputToTape (tm : MultiTapeTM k Symbol State)
    (c : Cfg k Symbol State input) (u : ℕ) :
    tm.outputToTape.spaceUsed (outCfg c) u ≤
      tm.spaceUsed c u + ((tm.runFrom c u).output.length + 1) := by
  simpa using tm.spaceUsed_le_of_workTapePos_embedding Fin.castSuccEmb c (outCfg c)
    ((tm.runFrom c u).output.length + 1) (fun m _ j => by simp [runFrom_outCfg])
    fun l hl => by
      induction l using Fin.lastCases with
      | last =>
        refine (spaceUsedByTape_le_card _
          (S := .Icc (c.output.length : ℤ) (tm.runFrom c u).output.length) fun m hm => ?_).trans
          (by simp)
        have h0 : c.output.length ≤ (tm.runFrom c m).output.length := by
          simpa [runFrom] using tm.length_output_mono c (Nat.zero_le m)
        have hu : (tm.runFrom c m).output.length ≤ (tm.runFrom c u).output.length :=
          tm.length_output_mono c hm
        simp only [runFrom_outCfg, outCfg_workTapePos_last, Finset.mem_Icc]
        omega
      | cast j => exact absurd ⟨j, rfl⟩ hl

end Turing.MultiTapeTM
