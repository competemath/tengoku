/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.SAT.Verifier
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Subroutines.Counter
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget

/-!
# SAT verifier TMs

Machine-level implementation of the deterministic SAT verifier, in the
`SAT.VerifierTM` namespace (recently renamed from a namespace that shadowed
`TM`). Building blocks, in dependency order:

* a deterministic checker for the witness-length side-condition
  `|α| ≤ |z| + 1` (`satLengthCheckTM` and its retargeted variants);
* a streaming evaluator `satEvalOnInputTM` for a SAT-encoded CNF against a
  staged assignment tape, together with its pure semantic model
  (`SatEvalSemState`, `satEvalSemStep`, `satEvalSemRun`, `satEvalSemBits`);
* the three-work-tape machine `verifyPairTM`, which computes the Boolean
  reference verifier `SAT.verifyPair` and hence decides `pairLang Witness`
  within the quadratic budget `verifyPairTMTime`
  (`verifyPairTM_decidesInTime`).

The pure model is tied to the reference verifier by `verifyPairSem` and
`verifyPairSem_eq_verifyPair`, so membership in `pairLang Witness` — the
paired witness language underlying `SAT.language ∈ NP` — is characterized
both semantically and at the machine level.
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace VerifierTM

-- ════════════════════════════════════════════════════════════════════════
-- Small tape helpers
-- ════════════════════════════════════════════════════════════════════════

private abbrev hasBoolSuffix := Tape.HasBinarySuffix

private theorem retargetInput_step_preserves_input_of_read_ne_start {k : ℕ} (M : TM k)
    {c c' : Cfg (k + 1) (TM.retargetInput M).Q}
    (hstep : (TM.retargetInput M).step c = some c')
    (hinp : c.input.read ≠ Γ.start) :
    c'.input = c.input := by
  simp only [TM.step, TM.retargetInput] at hstep
  split at hstep
  · simp at hstep
  · injection hstep with hstep
    subst hstep
    simp [TM.idleDir, hinp, Tape.move]

private theorem retargetInput_reachesIn_preserves_input_of_read_ne_start {k : ℕ}
    (M : TM k)
    {t : ℕ} {c c' : Cfg (k + 1) (TM.retargetInput M).Q}
    (hreach : (TM.retargetInput M).reachesIn t c c')
    (hinp : c.input.read ≠ Γ.start) :
    c'.input = c.input := by
  induction hreach with
  | zero =>
      rfl
  | step hstep hrest ih =>
      have hmid : _ := retargetInput_step_preserves_input_of_read_ne_start M hstep hinp
      rw [← hmid]
      exact ih (by simpa [hmid] using hinp)

private theorem started_blank_output_read_ne_start :
    (((Tape.init []).move Dir3.right).read) ≠ Γ.start := by
  rw [Tape.init_nil_move_right_read]
  decide

private theorem unaryCounter_read_ne_start {t : Tape} {B : ℕ}
    (h : t.HasUnaryCounter B) : t.read ≠ Γ.start := by
  by_cases hB : B = 0
  · subst hB
    rw [Tape.hasUnaryCounter_read_zero h]
    simp
  · have hpos : 0 < B := Nat.pos_of_ne_zero hB
    rw [Tape.hasUnaryCounter_read_pos h hpos]
    simp

private theorem started_input_read_ne_start (α : List Bool) :
    (((Tape.init (α.map Γ.ofBool)).move Dir3.right).read) ≠ Γ.start := by
  exact Tape.init_ofBool_move_right_read_ne_start α

private theorem fin2_ne_zero_eq_one (i : Fin 2) (h : i ≠ ⟨0, by omega⟩) :
    i = ⟨1, by omega⟩ := by
  apply Fin.ext
  have hne0 : (i : ℕ) ≠ 0 := by
    intro hi0
    apply h
    apply Fin.ext
    simpa using hi0
  have hlt : (i : ℕ) < 2 := i.isLt
  have hi1 : (i : ℕ) = 1 := by
    omega
  simpa using hi1

-- ════════════════════════════════════════════════════════════════════════
-- Deterministic witness-length checker
-- ════════════════════════════════════════════════════════════════════════

/-- Control states for the SAT witness-length checker. -/
inductive SatLengthCheckPhase where
  /-- Initial state: step off the left marker before scanning. -/
  | init
  /-- Scanning state: consume one counter mark per input bit. -/
  | scan
  /-- Halt state: the verdict has been written to the output tape. -/
  | done
  deriving DecidableEq

instance : Fintype SatLengthCheckPhase where
  elems := {.init, .scan, .done}
  complete := by
    intro q
    cases q <;> simp

/-- Deterministic checker for `|input| ≤ B`, where `B` is given as a unary
counter on work tape `0`. The machine scans one input bit per counter mark,
accepts when the input ends, and rejects if the counter is exhausted first. -/
def satLengthCheckTM : TM 1 where
  Q := SatLengthCheckPhase
  qstart := .init
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    let counterHead := wHeads ⟨0, by omega⟩
    match state with
    | .init =>
        (.scan,
          fun _ => TM.readBackWrite counterHead,
          TM.readBackWrite oHead,
          TM.idleDir iHead,
          fun _ => TM.idleDir counterHead,
          TM.idleDir oHead)
    | .scan =>
        if iHead = Γ.blank then
          (.done,
            fun _ => TM.readBackWrite counterHead,
            Γw.one,
            TM.idleDir iHead,
            fun _ => TM.idleDir counterHead,
            TM.idleDir oHead)
        else if counterHead = Γ.one then
          (.scan,
            fun _ => Γw.blank,
            TM.readBackWrite oHead,
            Dir3.right,
            fun _ => Dir3.right,
            TM.idleDir oHead)
        else
          (.done,
            fun _ => TM.readBackWrite counterHead,
            Γw.zero,
            TM.idleDir iHead,
            fun _ => TM.idleDir counterHead,
            TM.idleDir oHead)
    | .done =>
        TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    let counterHead := wHeads ⟨0, by omega⟩
    match state with
    | .init =>
        refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
        intro i hi
        have hi0 : i = ⟨0, by omega⟩ := by
          apply Fin.ext
          omega
        subst hi0
        simpa [counterHead] using TM.idleDir_right_of_start hi
    | .scan =>
        dsimp only []
        split
        · refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
          intro i hi
          have hi0 : i = ⟨0, by omega⟩ := by
            apply Fin.ext
            omega
          subst hi0
          simpa [counterHead] using TM.idleDir_right_of_start hi
        · split
          · refine ⟨fun _ => rfl, ?_, TM.idleDir_right_of_start⟩
            intro i _
            have hi0 : i = ⟨0, by omega⟩ := by
              apply Fin.ext
              omega
            subst hi0
            rfl
          · refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
            intro i hi
            have hi0 : i = ⟨0, by omega⟩ := by
              apply Fin.ext
              omega
            subst hi0
            simpa [counterHead] using TM.idleDir_right_of_start hi
    | .done =>
        exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- A convenient linear upper bound for the length checker. -/
def satLengthCheckTime (n : ℕ) : ℕ :=
  n + 2

-- ════════════════════════════════════════════════════════════════════════
-- Step lemmas
-- ════════════════════════════════════════════════════════════════════════

private theorem satLengthCheck_init_step (α : List Bool) (B : ℕ)
    (c : Cfg 1 satLengthCheckTM.Q)
    (hstate : c.state = .init)
    (hinput : c.input = (Tape.init (α.map Γ.ofBool)).move Dir3.right)
    (hcounter : (c.work ⟨0, by omega⟩).HasUnaryCounter B)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckTM.step c = some c' ∧
      c'.state = .scan ∧
      c'.input = c.input ∧
      c'.work ⟨0, by omega⟩ = c.work ⟨0, by omega⟩ ∧
      c'.output = c.output := by
  have hinp : c.input.read ≠ Γ.start := by
    rw [hinput]
    exact started_input_read_ne_start α
  have hwork : (c.work ⟨0, by omega⟩).read ≠ Γ.start := unaryCounter_read_ne_start hcounter
  have hout' : c.output.read ≠ Γ.start := by
    rw [hout]
    exact started_blank_output_read_ne_start
  simp only [TM.step, hstate, satLengthCheckTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · change TM.transitionInput c.input = c.input
    exact TM.transitionInput_eq_self hinp
  · change TM.transitionTape (c.work ⟨0, by omega⟩) = c.work ⟨0, by omega⟩
    exact TM.transitionTape_eq_self hwork
  · change TM.transitionTape c.output = c.output
    exact TM.transitionTape_eq_self hout'

private theorem satLengthCheck_scan_continue_step (α : List Bool) (B k : ℕ)
    (c : Cfg 1 satLengthCheckTM.Q)
    (hk : k < α.length)
    (hkB : k < B)
    (hstate : c.state = .scan)
    (hinput_cells : c.input.cells = (Tape.init (α.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = k + 1)
    (hcounter : (c.work ⟨0, by omega⟩).HasCounterRemainder k B)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckTM.step c = some c' ∧
      c'.state = .scan ∧
      c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
      c'.input.head = k + 2 ∧
      (c'.work ⟨0, by omega⟩).HasCounterRemainder (k + 1) B ∧
      c'.output = c.output := by
  have hread_input : c.input.read = Γ.ofBool (α[k]'hk) := by
    show c.input.cells c.input.head = _
    rw [hinput_head, hinput_cells]
    exact Tape.init_ofBool_cells_lt α k hk
  have hinput_nb : c.input.read ≠ Γ.blank := by
    rw [hread_input]
    exact Γ.ofBool_ne_blank _
  have hcounter_read : (c.work ⟨0, by omega⟩).read = Γ.one :=
    Tape.hasCounterRemainder_read_one_of_remaining hcounter hkB
  have hout' : c.output.read ≠ Γ.start := by
    rw [hout]
    exact started_blank_output_read_ne_start
  simp only [TM.step, hstate, satLengthCheckTM, hinput_nb, hcounter_read]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [Tape.move_cells]
    exact hinput_cells
  · simp [Tape.move, hinput_head]
  · simpa using Tape.hasCounterRemainder_consume hcounter hkB
  · change TM.transitionTape c.output = c.output
    exact TM.transitionTape_eq_self hout'

private theorem satLengthCheck_scan_accept_step (α : List Bool) (B : ℕ)
    (c : Cfg 1 satLengthCheckTM.Q)
    (hstate : c.state = .scan)
    (hinput_cells : c.input.cells = (Tape.init (α.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = α.length + 1)
    (_hcounter : (c.work ⟨0, by omega⟩).HasCounterRemainder α.length B)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckTM.step c = some c' ∧
      satLengthCheckTM.halted c' ∧
      c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
      c'.output.cells 1 = Γ.one := by
  have hread_input : c.input.read = Γ.blank := by
    show c.input.cells c.input.head = Γ.blank
    rw [hinput_head, hinput_cells]
    exact Tape.init_ofBool_cells_ge α α.length le_rfl
  have hout_read : c.output.read = Γ.blank := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  simp only [TM.step, hstate, satLengthCheckTM, hread_input, hout_read]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · rw [Tape.move_cells]
    exact hinput_cells
  · have ho_head : c.output.head = 1 := by
      rw [hout]
      simp [Tape.move, Tape.init]
    simp [Tape.writeAndMove, Tape.move, Tape.write, ho_head, TM.idleDir, Γw.toΓ]

private theorem satLengthCheck_scan_reject_step (α : List Bool) (B : ℕ)
    (c : Cfg 1 satLengthCheckTM.Q)
    (hB : B < α.length)
    (hstate : c.state = .scan)
    (hinput_cells : c.input.cells = (Tape.init (α.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = B + 1)
    (hcounter : (c.work ⟨0, by omega⟩).HasCounterRemainder B B)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckTM.step c = some c' ∧
      satLengthCheckTM.halted c' ∧
      c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
      c'.output.cells 1 = Γ.zero := by
  have hread_input : c.input.read ≠ Γ.blank := by
    have hcell : c.input.read = Γ.ofBool (α[B]'hB) := by
      show c.input.cells c.input.head = _
      rw [hinput_head, hinput_cells]
      exact Tape.init_ofBool_cells_lt α B hB
    rw [hcell]
    exact Γ.ofBool_ne_blank _
  have hread_counter : (c.work ⟨0, by omega⟩).read = Γ.blank :=
    Tape.hasCounterRemainder_read_blank_of_done hcounter
  have hout_read : c.output.read = Γ.blank := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  simp only [TM.step, hstate, satLengthCheckTM, hread_input, hread_counter, hout_read]
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · rw [Tape.move_cells]
    exact hinput_cells
  · have ho_head : c.output.head = 1 := by
      rw [hout]
      simp [Tape.move, Tape.init]
    simp [Tape.writeAndMove, Tape.move, Tape.write, ho_head, TM.idleDir, Γw.toΓ]

-- ════════════════════════════════════════════════════════════════════════
-- Prefix scan loop
-- ════════════════════════════════════════════════════════════════════════

private theorem satLengthCheck_scan_prefix_loop (α : List Bool) (B : ℕ) :
    ∀ (m k : ℕ) (c : Cfg 1 satLengthCheckTM.Q),
      k + m ≤ α.length →
      k + m ≤ B →
      c.state = .scan →
      c.input.cells = (Tape.init (α.map Γ.ofBool)).cells →
      c.input.head = k + 1 →
      (c.work ⟨0, by omega⟩).HasCounterRemainder k B →
      c.output = (Tape.init []).move Dir3.right →
      ∃ c',
        satLengthCheckTM.reachesIn m c c' ∧
        c'.state = .scan ∧
        c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
        c'.input.head = k + m + 1 ∧
        (c'.work ⟨0, by omega⟩).HasCounterRemainder (k + m) B ∧
        c'.output = (Tape.init []).move Dir3.right := by
  intro m
  induction m with
  | zero =>
      intro k c _ _ hstate hinput_cells hinput_head hcounter hout
      refine ⟨c, .zero, hstate, hinput_cells, ?_, ?_, hout⟩
      · omega
      · simpa using hcounter
  | succ m ih =>
      intro k c hlen hbound hstate hinput_cells hinput_head hcounter hout
      have hk : k < α.length := by omega
      have hkB : k < B := by omega
      obtain ⟨c1, hstep, hstate1, hcells1, hhead1, hcounter1, hout1⟩ :=
        satLengthCheck_scan_continue_step α B k c hk hkB hstate hinput_cells
          hinput_head hcounter hout
      have hlen1 : k + 1 + m ≤ α.length := by omega
      have hbound1 : k + 1 + m ≤ B := by omega
      have hout1_started : c1.output = (Tape.init []).move Dir3.right := by
        rw [hout1]
        exact hout
      obtain ⟨c', hreach, hstate', hcells', hhead', hcounter', hout'⟩ :=
        ih (k + 1) c1 hlen1 hbound1 hstate1 hcells1 hhead1 hcounter1 hout1_started
      refine ⟨c', .step hstep hreach, hstate', hcells', ?_, ?_, hout'⟩
      · rw [hhead']
        omega
      · convert hcounter' using 1
        omega

-- ════════════════════════════════════════════════════════════════════════
-- Main started Hoare theorem
-- ════════════════════════════════════════════════════════════════════════

/-- Started-tape correctness for the witness-length checker. The input tape is
already positioned at cell `1`, the counter tape stores a unary bound `B`, and
the output tape is the started blank tape. The machine halts with output `1`
iff `|α| ≤ B`.
@isnad1 id=hoaretim.0h2v.s6.0a2f6bf96b59 from=translated src=- shape=fb882fc8 vocab=cf4a5519
-/
theorem satLengthCheckTM_started_hoareTime (B : ℕ) (α : List Bool) :
    satLengthCheckTM.HoareTime
      (fun inp work out =>
        inp = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter B ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp _work out =>
        inp.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
        out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero))
      (satLengthCheckTime α.length) := by
  intro inp work out hpre
  rcases hpre with ⟨hinput, hcounter, hout⟩
  let c0 : Cfg 1 satLengthCheckTM.Q :=
    { state := satLengthCheckTM.qstart, input := inp, work := work, output := out }
  obtain ⟨c1, hstep1, hstate1, hinput1, hwork1, hout1⟩ :=
    satLengthCheck_init_step α B c0 rfl hinput hcounter hout
  have hcells0 : c0.input.cells = (Tape.init (α.map Γ.ofBool)).cells := by
    change inp.cells = (Tape.init (α.map Γ.ofBool)).cells
    rw [hinput]
    exact Tape.move_cells _ _
  have hhead0 : c0.input.head = 1 := by
    change inp.head = 1
    rw [hinput]
    simp [Tape.move, Tape.init]
  have hcells1 : c1.input.cells = (Tape.init (α.map Γ.ofBool)).cells := by
    rw [hinput1]
    exact hcells0
  have hhead1 : c1.input.head = 1 := by
    rw [hinput1]
    exact hhead0
  have hcounter1 : (c1.work ⟨0, by omega⟩).HasCounterRemainder 0 B := by
    rw [hwork1]
    exact (Tape.hasUnaryCounter_iff_remainder_zero).mp hcounter
  have hout1_started : c1.output = (Tape.init []).move Dir3.right := by
    rw [hout1]
    exact hout
  by_cases hle : α.length ≤ B
  · obtain ⟨c2, hreach2, hstate2, hcells2, hhead2, hcounter2, hout2⟩ :=
      satLengthCheck_scan_prefix_loop α B α.length 0 c1
        (by omega) (by simpa using hle) hstate1 hcells1 hhead1 hcounter1 hout1_started
    obtain ⟨c3, hstep3, hhalt3, hcells3, hout3⟩ :=
      satLengthCheck_scan_accept_step α B c2 hstate2 hcells2
        (by simpa using hhead2) (by simpa using hcounter2) hout2
    have hreach_total : satLengthCheckTM.reachesIn (1 + α.length + 1) c0 c3 := by
      simpa [Nat.add_assoc] using
        TM.reachesIn_trans _ (.step hstep1 .zero)
          (TM.reachesIn_trans _ hreach2 (.step hstep3 .zero))
    refine ⟨c3, 1 + α.length + 1, by
      simp [satLengthCheckTime]
      omega, hreach_total, hhalt3, ?_⟩
    refine ⟨hcells3, ?_⟩
    simpa [hle] using hout3
  · have hlt : B < α.length := by omega
    obtain ⟨c2, hreach2, hstate2, hcells2, hhead2, hcounter2, hout2⟩ :=
      satLengthCheck_scan_prefix_loop α B B 0 c1
        (by omega) (by omega) hstate1 hcells1 hhead1 hcounter1 hout1_started
    obtain ⟨c3, hstep3, hhalt3, hcells3, hout3⟩ :=
      satLengthCheck_scan_reject_step α B c2 hlt hstate2 hcells2
        (by simpa using hhead2) (by simpa using hcounter2) hout2
    have hreach_total : satLengthCheckTM.reachesIn (1 + B + 1) c0 c3 := by
      simpa [Nat.add_assoc] using
        TM.reachesIn_trans _ (.step hstep1 .zero)
          (TM.reachesIn_trans _ hreach2 (.step hstep3 .zero))
    refine ⟨c3, 1 + B + 1, by
      simp [satLengthCheckTime]
      omega, hreach_total, hhalt3, ?_⟩
    refine ⟨hcells3, ?_⟩
    simpa [hle] using hout3

/-- Virtual-input/work-tape version of `satLengthCheckTM_started_hoareTime`.
The last work tape supplies the witness bits, work tape `0` supplies a unary
counter bound, and the output tape receives `1` iff the witness length is at
most that bound. The counter tape precondition includes the structural
no-`▷` invariant required by `retargetInput`.
@isnad1 id=hoaretim.0h2v.s8.e956aae268bd from=translated src=- shape=4d90ef49 vocab=491ca6ae
-/
theorem retargetInput_satLengthCheckTM_started_hoareTime (B : ℕ) (α : List Bool) :
    (TM.retargetInput satLengthCheckTM).HoareTime
      (fun _inp work out =>
        work ⟨1, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter B ∧
        (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp work out =>
        (work ⟨1, by omega⟩).cells = (Tape.init (α.map Γ.ofBool)).cells ∧
        out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero))
      (satLengthCheckTime α.length) := by
  have hmove_right_invariant : ∀ {t : Tape}, Tape.StartInvariant t →
      Tape.StartInvariant (t.move Dir3.right) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · simpa [Tape.move_cells] using ht.1
    · intro j hj
      simpa [Tape.move_cells] using ht.2 j hj
  have hlen :
      satLengthCheckTM.HoareTime
        (fun inp work out =>
          inp = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
          (work ⟨0, by omega⟩).HasUnaryCounter B ∧
          (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
          (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
          out = (Tape.init []).move Dir3.right)
        (fun inp _work out =>
          inp.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
          out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero))
        (satLengthCheckTime α.length) :=
    (satLengthCheckTM_started_hoareTime B α).weaken_pre (by
      intro inp work out hpre
      exact ⟨hpre.1, hpre.2.1, hpre.2.2.2.2⟩)
  have hret := TM.retargetInput_hoareTime (M := satLengthCheckTM)
    hlen
    (hpre_inp := by
      intro _inp work out hpre
      rcases hpre with ⟨hvin, _hcounter, _hcell0, _hnostart, _hout⟩
      rw [hvin]
      exact hmove_right_invariant (Tape.StartInvariant.init_ofBool α))
    (hpre_work := by
      intro _inp work out hpre i
      rcases hpre with ⟨_hvin, _hcounter, hcell0, hnostart, _hout⟩
      have hi0 : i = ⟨0, by omega⟩ := by
        apply Fin.ext
        omega
      subst hi0
      exact ⟨hcell0, hnostart⟩)
    (hpre_out := by
      intro _inp work out hpre
      rcases hpre with ⟨_hvin, _hcounter, _hcell0, _hnostart, hout⟩
      rw [hout]
      exact hmove_right_invariant (Tape.StartInvariant.init_nil))
  refine hret.strengthen_post ?_
  intro _inp work out hpost
  rcases hpost with ⟨vin, innerWork, hinner, hmap, hvin⟩
  exact ⟨by rw [hvin]; exact hinner.1,
    by simpa using hinner.2⟩

-- ════════════════════════════════════════════════════════════════════════
-- Counter-builder verifier slice
-- ════════════════════════════════════════════════════════════════════════

/-- Three-work-tape counter builder obtained by retargeting the input of
`inputLengthPlusOneCounterTM` to work tape `2`. Tape `0` stores the unary
counter, tape `1` is preserved, and tape `2` provides the formula bits. -/
def satCounter3TM : TM 3 :=
  TM.retargetInput (TM.inputLengthPlusOneCounterTM ⟨0, by omega⟩)

/-- Build the unary counter `|z| + 1` on tape `0` from staged formula tape `2`
while preserving the staged witness on tape `1` and leaving the output tape in
the started blank configuration.
@isnad1 id=hoaretim.0h2v.s8.b898ddab429e from=translated src=- shape=3536ec75 vocab=a23a1ee9
-/
theorem satCounter3TM_started_hoareTime (z α : List Bool) :
    satCounter3TM.HoareTime
      (fun _inp work out =>
        work ⟨2, by omega⟩ = (Tape.init (z.map Γ.ofBool)).move Dir3.right ∧
        work ⟨0, by omega⟩ = (Tape.init []).move Dir3.right ∧
        work ⟨1, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp work out =>
        (work ⟨2, by omega⟩).cells = (Tape.init (z.map Γ.ofBool)).cells ∧
        (work ⟨2, by omega⟩).head = z.length + 1 ∧
        work ⟨1, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter (z.length + 1) ∧
        (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
        out = (Tape.init []).move Dir3.right)
      (TM.inputLengthPlusOneCounterTime z.length) := by
  let counterIdx : Fin 2 := ⟨0, by decide⟩
  let passiveIdx : Fin 2 := ⟨1, by decide⟩
  have hmove_right_invariant : ∀ {t : Tape}, Tape.StartInvariant t →
      Tape.StartInvariant (t.move Dir3.right) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · simpa [Tape.move_cells] using ht.1
    · intro j hj
      simpa [Tape.move_cells] using ht.2 j hj
  have hcounter :
      (TM.inputLengthPlusOneCounterTM counterIdx).HoareTime
        (fun inp work out =>
          inp = (Tape.init (z.map Γ.ofBool)).move Dir3.right ∧
          work counterIdx = (Tape.init []).move Dir3.right ∧
          work passiveIdx = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
          out = (Tape.init []).move Dir3.right)
        (fun inp work out =>
          inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
          inp.head = z.length + 1 ∧
          work passiveIdx = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
          (work counterIdx).HasUnaryCounter (z.length + 1) ∧
          (work counterIdx).cells 0 = Γ.start ∧
          (∀ j, j ≥ 1 → (work counterIdx).cells j ≠ Γ.start) ∧
          out = (Tape.init []).move Dir3.right)
        (TM.inputLengthPlusOneCounterTime z.length) :=
    TM.inputLengthPlusOneCounterTM_started_tracksInput_preserves_work_hoareTime
      counterIdx passiveIdx (by decide) z α
  have hret := TM.retargetInput_hoareTime
      (M := TM.inputLengthPlusOneCounterTM counterIdx)
      hcounter
    (hpre_inp := by
      intro _inp work out hpre
      rcases hpre with ⟨hvin, _hblank, _hpassive, _hout⟩
      rw [hvin]
      exact hmove_right_invariant (Tape.StartInvariant.init_ofBool z))
    (hpre_work := by
      intro _inp work out hpre i
      rcases hpre with ⟨_hvin, hblank, hpassive, _hout⟩
      by_cases hi0 : i = counterIdx
      · subst hi0
        rw [hblank]
        exact hmove_right_invariant (Tape.StartInvariant.init_nil)
      · have hi1 := fin2_ne_zero_eq_one i hi0
        subst hi1
        rw [hpassive]
        exact hmove_right_invariant (Tape.StartInvariant.init_ofBool α))
    (hpre_out := by
      intro _inp work out hpre
      rcases hpre with ⟨_hvin, _hblank, _hpassive, hout⟩
      rw [hout]
      exact hmove_right_invariant (Tape.StartInvariant.init_nil))
  have hret' : satCounter3TM.HoareTime
      (fun _inp work out =>
        work ⟨2, by omega⟩ = (Tape.init (z.map Γ.ofBool)).move Dir3.right ∧
        work ⟨0, by omega⟩ = (Tape.init []).move Dir3.right ∧
        work ⟨1, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp work out =>
        ∃ vin : Tape, ∃ innerWork : Fin 2 → Tape,
          (vin.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
            vin.head = z.length + 1 ∧
            innerWork passiveIdx = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
            (innerWork counterIdx).HasUnaryCounter (z.length + 1) ∧
            (innerWork counterIdx).cells 0 = Γ.start ∧
            (∀ j, j ≥ 1 → (innerWork counterIdx).cells j ≠ Γ.start) ∧
            out = (Tape.init []).move Dir3.right) ∧
          (∀ i : Fin 2, work ⟨i.val, by omega⟩ = innerWork i) ∧
          work ⟨2, by omega⟩ = vin)
      (TM.inputLengthPlusOneCounterTime z.length) := by
    exact hret
  refine hret'.strengthen_post ?_
  intro _inp work out hpost
  rcases hpost with ⟨vin, innerWork, hinner, hmap, hvin⟩
  have hmap0 : work ⟨0, by omega⟩ = innerWork counterIdx := by
    simpa [counterIdx] using hmap counterIdx
  exact ⟨by rw [hvin]; exact hinner.1,
    by rw [hvin]; exact hinner.2.1,
    (hmap passiveIdx).trans hinner.2.2.1,
    by rw [hmap0]; exact hinner.2.2.2.1,
    by rw [hmap0]; exact hinner.2.2.2.2.1,
    by rw [hmap0]; exact hinner.2.2.2.2.2.1,
    hinner.2.2.2.2.2.2⟩

/-- Richer started-tape wrapper for `satCounter3TM` that also records that the
real input tape remains stable when it starts past `▷`.
@isnad1 id=hoaretim.0h2v.s8.5b16d29d75e2 from=translated src=- shape=7feebd4a vocab=9dfc4d64
-/
theorem satCounter3TM_started_stableInput_hoareTime (z α : List Bool) :
    satCounter3TM.HoareTime
      (fun inp work out =>
        inp.read ≠ Γ.start ∧
        work ⟨2, by omega⟩ = (Tape.init (z.map Γ.ofBool)).move Dir3.right ∧
        work ⟨0, by omega⟩ = (Tape.init []).move Dir3.right ∧
        work ⟨1, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp.read ≠ Γ.start ∧
        (work ⟨2, by omega⟩).cells = (Tape.init (z.map Γ.ofBool)).cells ∧
        (work ⟨2, by omega⟩).head = z.length + 1 ∧
        work ⟨1, by omega⟩ = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter (z.length + 1) ∧
        (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
        out = (Tape.init []).move Dir3.right)
      (TM.inputLengthPlusOneCounterTime z.length) := by
  intro inp work out hpre
  let counterIdx : Fin 2 := ⟨0, by omega⟩
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
    satCounter3TM_started_hoareTime z α inp work out hpre.2
  have hinput_keep :
      c'.input = inp :=
    retargetInput_reachesIn_preserves_input_of_read_ne_start
      (TM.inputLengthPlusOneCounterTM (n := 2) counterIdx)
      (by simp only [satCounter3TM] at hreach; exact hreach)
      hpre.1
  refine ⟨c', t, ht, hreach, hhalt, ?_⟩
  rw [hinput_keep]
  exact ⟨hpre.1, hpost⟩

-- ════════════════════════════════════════════════════════════════════════
-- Passive-preserving verifier slice
-- ════════════════════════════════════════════════════════════════════════

/-- A two-work-tape version of the SAT witness-length checker. Work tape `0`
stores the unary bound, while work tape `1` is preserved exactly. -/
def satLengthCheckPassiveTM : TM 2 where
  Q := SatLengthCheckPhase
  qstart := .init
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    let counterHead := wHeads ⟨0, by omega⟩
    let passiveHead := wHeads ⟨1, by omega⟩
    match state with
    | .init =>
        (.scan,
          fun i =>
            if i = ⟨0, by omega⟩ then TM.readBackWrite counterHead
            else TM.readBackWrite passiveHead,
          TM.readBackWrite oHead,
          TM.idleDir iHead,
          fun i =>
            if i = ⟨0, by omega⟩ then TM.idleDir counterHead
            else TM.idleDir passiveHead,
          TM.idleDir oHead)
    | .scan =>
        if iHead = Γ.blank then
          (.done,
            fun i =>
              if i = ⟨0, by omega⟩ then TM.readBackWrite counterHead
              else TM.readBackWrite passiveHead,
            Γw.one,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨0, by omega⟩ then TM.idleDir counterHead
              else TM.idleDir passiveHead,
            TM.idleDir oHead)
        else if counterHead = Γ.one then
          (.scan,
            fun i => if i = ⟨0, by omega⟩ then Γw.blank else TM.readBackWrite passiveHead,
            TM.readBackWrite oHead,
            Dir3.right,
            fun i => if i = ⟨0, by omega⟩ then Dir3.right else TM.idleDir passiveHead,
            TM.idleDir oHead)
        else
          (.done,
            fun i =>
              if i = ⟨0, by omega⟩ then TM.readBackWrite counterHead
              else TM.readBackWrite passiveHead,
            Γw.zero,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨0, by omega⟩ then TM.idleDir counterHead
              else TM.idleDir passiveHead,
            TM.idleDir oHead)
    | .done =>
        TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    let counterHead := wHeads ⟨0, by omega⟩
    let passiveHead := wHeads ⟨1, by omega⟩
    match state with
    | .init =>
        refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
        intro i hi
        by_cases hi0 : i = ⟨0, by omega⟩
        · subst hi0
          simpa [counterHead] using TM.idleDir_right_of_start hi
        · have hi1 := fin2_ne_zero_eq_one i hi0
          subst hi1
          simpa [passiveHead] using TM.idleDir_right_of_start hi
    | .scan =>
        dsimp only []
        split
        · refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
          intro i hi
          by_cases hi0 : i = ⟨0, by omega⟩
          · subst hi0
            simpa [counterHead] using TM.idleDir_right_of_start hi
          · have hi1 := fin2_ne_zero_eq_one i hi0
            subst hi1
            simpa [passiveHead] using TM.idleDir_right_of_start hi
        · split
          · refine ⟨fun _ => rfl, ?_, TM.idleDir_right_of_start⟩
            intro i hi
            by_cases hi0 : i = ⟨0, by omega⟩
            · subst hi0
              rfl
            · have hi1 := fin2_ne_zero_eq_one i hi0
              subst hi1
              simpa [passiveHead] using TM.idleDir_right_of_start hi
          · refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
            intro i hi
            by_cases hi0 : i = ⟨0, by omega⟩
            · subst hi0
              simpa [counterHead] using TM.idleDir_right_of_start hi
            · have hi1 := fin2_ne_zero_eq_one i hi0
              subst hi1
              simpa [passiveHead] using TM.idleDir_right_of_start hi
    | .done =>
        exact TM.rightOfStart_allIdle iHead wHeads oHead

private theorem satLengthCheckPassive_init_step (α β : List Bool) (B : ℕ)
    (c : Cfg 2 satLengthCheckPassiveTM.Q)
    (hstate : c.state = .init)
    (hinput : c.input = (Tape.init (α.map Γ.ofBool)).move Dir3.right)
    (hcounter : (c.work ⟨0, by omega⟩).HasUnaryCounter B)
    (hpassive : c.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckPassiveTM.step c = some c' ∧
      c'.state = .scan ∧
      c'.input = c.input ∧
      c'.work ⟨0, by omega⟩ = c.work ⟨0, by omega⟩ ∧
      c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
      c'.output = c.output := by
  have hinp : c.input.read ≠ Γ.start := by
    rw [hinput]
    exact started_input_read_ne_start α
  have hwork0 : (c.work ⟨0, by omega⟩).read ≠ Γ.start := unaryCounter_read_ne_start hcounter
  have hwork1 : (c.work ⟨1, by omega⟩).read ≠ Γ.start := by
    rw [hpassive]
    exact started_input_read_ne_start β
  have hout' : c.output.read ≠ Γ.start := by
    rw [hout]
    exact started_blank_output_read_ne_start
  simp only [TM.step, hstate, satLengthCheckPassiveTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · change TM.transitionInput c.input = c.input
    exact TM.transitionInput_eq_self hinp
  · change TM.transitionTape (c.work ⟨0, by omega⟩) = c.work ⟨0, by omega⟩
    exact TM.transitionTape_eq_self hwork0
  · change TM.transitionTape (c.work ⟨1, by omega⟩) = c.work ⟨1, by omega⟩
    exact TM.transitionTape_eq_self hwork1
  · change TM.transitionTape c.output = c.output
    exact TM.transitionTape_eq_self hout'

private theorem satLengthCheckPassive_scan_continue_step (α β : List Bool) (B k : ℕ)
    (c : Cfg 2 satLengthCheckPassiveTM.Q)
    (hk : k < α.length)
    (hkB : k < B)
    (hstate : c.state = .scan)
    (hinput_cells : c.input.cells = (Tape.init (α.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = k + 1)
    (hcounter : (c.work ⟨0, by omega⟩).HasCounterRemainder k B)
    (hpassive : c.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckPassiveTM.step c = some c' ∧
      c'.state = .scan ∧
      c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
      c'.input.head = k + 2 ∧
      (c'.work ⟨0, by omega⟩).HasCounterRemainder (k + 1) B ∧
      c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
      c'.output = c.output := by
  have hread_input : c.input.read = Γ.ofBool (α[k]'hk) := by
    show c.input.cells c.input.head = _
    rw [hinput_head, hinput_cells]
    exact Tape.init_ofBool_cells_lt α k hk
  have hinput_nb : c.input.read ≠ Γ.blank := by
    rw [hread_input]
    exact Γ.ofBool_ne_blank _
  have hcounter_read : (c.work ⟨0, by omega⟩).read = Γ.one :=
    Tape.hasCounterRemainder_read_one_of_remaining hcounter hkB
  have hpassive_read : (c.work ⟨1, by omega⟩).read ≠ Γ.start := by
    rw [hpassive]
    exact started_input_read_ne_start β
  have hout' : c.output.read ≠ Γ.start := by
    rw [hout]
    exact started_blank_output_read_ne_start
  simp only [TM.step, hstate, satLengthCheckPassiveTM, hinput_nb, hcounter_read]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Tape.move_cells]
    exact hinput_cells
  · simp [Tape.move, hinput_head]
  · simpa using Tape.hasCounterRemainder_consume hcounter hkB
  · change TM.transitionTape (c.work ⟨1, by omega⟩) = c.work ⟨1, by omega⟩
    exact TM.transitionTape_eq_self hpassive_read
  · change TM.transitionTape c.output = c.output
    exact TM.transitionTape_eq_self hout'

private theorem satLengthCheckPassive_scan_accept_step (α β : List Bool) (B : ℕ)
    (c : Cfg 2 satLengthCheckPassiveTM.Q)
    (hstate : c.state = .scan)
    (hinput_cells : c.input.cells = (Tape.init (α.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = α.length + 1)
    (_hcounter : (c.work ⟨0, by omega⟩).HasCounterRemainder α.length B)
    (hpassive : c.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckPassiveTM.step c = some c' ∧
      satLengthCheckPassiveTM.halted c' ∧
      c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
      c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
      c'.output.cells 1 = Γ.one := by
  have hread_input : c.input.read = Γ.blank := by
    show c.input.cells c.input.head = Γ.blank
    rw [hinput_head, hinput_cells]
    exact Tape.init_ofBool_cells_ge α α.length le_rfl
  have hpassive_read : (c.work ⟨1, by omega⟩).read ≠ Γ.start := by
    rw [hpassive]
    exact started_input_read_ne_start β
  have hout_read : c.output.read = Γ.blank := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  simp only [TM.step, hstate, satLengthCheckPassiveTM, hread_input, hout_read]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · rw [Tape.move_cells]
    exact hinput_cells
  · change TM.transitionTape (c.work ⟨1, by omega⟩) = c.work ⟨1, by omega⟩
    exact TM.transitionTape_eq_self hpassive_read
  · have ho_head : c.output.head = 1 := by
      rw [hout]
      simp [Tape.move, Tape.init]
    simp [Tape.writeAndMove, Tape.move, Tape.write, ho_head, TM.idleDir, Γw.toΓ]

private theorem satLengthCheckPassive_scan_reject_step (α β : List Bool) (B : ℕ)
    (c : Cfg 2 satLengthCheckPassiveTM.Q)
    (hB : B < α.length)
    (hstate : c.state = .scan)
    (hinput_cells : c.input.cells = (Tape.init (α.map Γ.ofBool)).cells)
    (hinput_head : c.input.head = B + 1)
    (hcounter : (c.work ⟨0, by omega⟩).HasCounterRemainder B B)
    (hpassive : c.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right)
    (hout : c.output = (Tape.init []).move Dir3.right) :
    ∃ c', satLengthCheckPassiveTM.step c = some c' ∧
      satLengthCheckPassiveTM.halted c' ∧
      c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
      c'.work ⟨1, by omega⟩ = c.work ⟨1, by omega⟩ ∧
      c'.output.cells 1 = Γ.zero := by
  have hread_input : c.input.read ≠ Γ.blank := by
    have hcell : c.input.read = Γ.ofBool (α[B]'hB) := by
      show c.input.cells c.input.head = _
      rw [hinput_head, hinput_cells]
      exact Tape.init_ofBool_cells_lt α B hB
    rw [hcell]
    exact Γ.ofBool_ne_blank _
  have hread_counter : (c.work ⟨0, by omega⟩).read = Γ.blank :=
    Tape.hasCounterRemainder_read_blank_of_done hcounter
  have hpassive_read : (c.work ⟨1, by omega⟩).read ≠ Γ.start := by
    rw [hpassive]
    exact started_input_read_ne_start β
  have hout_read : c.output.read = Γ.blank := by
    rw [hout]
    simp [Tape.read, Tape.move, Tape.init]
  simp only [TM.step, hstate, satLengthCheckPassiveTM, hread_input, hread_counter, hout_read]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · rw [Tape.move_cells]
    exact hinput_cells
  · change TM.transitionTape (c.work ⟨1, by omega⟩) = c.work ⟨1, by omega⟩
    exact TM.transitionTape_eq_self hpassive_read
  · have ho_head : c.output.head = 1 := by
      rw [hout]
      simp [Tape.move, Tape.init]
    simp [Tape.writeAndMove, Tape.move, Tape.write, ho_head, TM.idleDir, Γw.toΓ]

private theorem satLengthCheckPassive_scan_prefix_loop (α β : List Bool) (B : ℕ) :
    ∀ (m k : ℕ) (c : Cfg 2 satLengthCheckPassiveTM.Q),
      k + m ≤ α.length →
      k + m ≤ B →
      c.state = .scan →
      c.input.cells = (Tape.init (α.map Γ.ofBool)).cells →
      c.input.head = k + 1 →
      (c.work ⟨0, by omega⟩).HasCounterRemainder k B →
      c.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right →
      c.output = (Tape.init []).move Dir3.right →
      ∃ c',
        satLengthCheckPassiveTM.reachesIn m c c' ∧
        c'.state = .scan ∧
        c'.input.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
        c'.input.head = k + m + 1 ∧
        (c'.work ⟨0, by omega⟩).HasCounterRemainder (k + m) B ∧
        c'.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
        c'.output = (Tape.init []).move Dir3.right := by
  intro m
  induction m with
  | zero =>
      intro k c _ _ hstate hinput_cells hinput_head hcounter hpassive hout
      refine ⟨c, .zero, hstate, hinput_cells, ?_, ?_, hpassive, hout⟩
      · omega
      · simpa using hcounter
  | succ m ih =>
      intro k c hlen hbound hstate hinput_cells hinput_head hcounter hpassive hout
      have hk : k < α.length := by omega
      have hkB : k < B := by omega
      obtain ⟨c1, hstep, hstate1, hcells1, hhead1, hcounter1, hpassive1, hout1⟩ :=
        satLengthCheckPassive_scan_continue_step α β B k c hk hkB hstate hinput_cells
          hinput_head hcounter hpassive hout
      have hlen1 : k + 1 + m ≤ α.length := by omega
      have hbound1 : k + 1 + m ≤ B := by omega
      have hpassive1_started :
          c1.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right := by
        rw [hpassive1]
        exact hpassive
      have hout1_started : c1.output = (Tape.init []).move Dir3.right := by
        rw [hout1]
        exact hout
      obtain ⟨c', hreach, hstate', hcells', hhead', hcounter', hpassive', hout'⟩ :=
        ih (k + 1) c1 hlen1 hbound1 hstate1 hcells1 hhead1 hcounter1 hpassive1_started
          hout1_started
      refine ⟨c', .step hstep hreach, hstate', hcells', ?_, ?_, hpassive', hout'⟩
      · rw [hhead']
        omega
      · convert hcounter' using 1
        omega

/-- Started-tape correctness for `satLengthCheckPassiveTM`: the machine checks
`|α| ≤ B` while leaving work tape `1` unchanged.
@isnad1 id=hoaretim.0h3v.s7.912be6c1c718 from=translated src=- shape=7f131899 vocab=9296fa51
-/
theorem satLengthCheckPassiveTM_started_hoareTime (B : ℕ) (α β : List Bool) :
    satLengthCheckPassiveTM.HoareTime
      (fun inp work out =>
        inp = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter B ∧
        work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
        work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
        out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero))
      (satLengthCheckTime α.length) := by
  intro inp work out hpre
  rcases hpre with ⟨hinput, hcounter, hpassive, hout⟩
  let c0 : Cfg 2 satLengthCheckPassiveTM.Q :=
    { state := satLengthCheckPassiveTM.qstart, input := inp, work := work, output := out }
  obtain ⟨c1, hstep1, hstate1, hinput1, hwork01, hwork11, hout1⟩ :=
    satLengthCheckPassive_init_step α β B c0 rfl hinput hcounter hpassive hout
  have hcells0 : c0.input.cells = (Tape.init (α.map Γ.ofBool)).cells := by
    change inp.cells = (Tape.init (α.map Γ.ofBool)).cells
    rw [hinput]
    exact Tape.move_cells _ _
  have hhead0 : c0.input.head = 1 := by
    change inp.head = 1
    rw [hinput]
    simp [Tape.move, Tape.init]
  have hcells1 : c1.input.cells = (Tape.init (α.map Γ.ofBool)).cells := by
    rw [hinput1]
    exact hcells0
  have hhead1 : c1.input.head = 1 := by
    rw [hinput1]
    exact hhead0
  have hcounter1 : (c1.work ⟨0, by omega⟩).HasCounterRemainder 0 B := by
    rw [hwork01]
    exact (Tape.hasUnaryCounter_iff_remainder_zero).mp hcounter
  have hpassive1 : c1.work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right := by
    rw [hwork11]
    exact hpassive
  have hout1_started : c1.output = (Tape.init []).move Dir3.right := by
    rw [hout1]
    exact hout
  by_cases hle : α.length ≤ B
  · obtain ⟨c2, hreach2, hstate2, hcells2, hhead2, hcounter2, hpassive2, hout2⟩ :=
      satLengthCheckPassive_scan_prefix_loop α β B α.length 0 c1
        (by omega) (by simpa using hle) hstate1 hcells1 hhead1 hcounter1 hpassive1 hout1_started
    obtain ⟨c3, hstep3, hhalt3, hcells3, hpassive3, hout3⟩ :=
      satLengthCheckPassive_scan_accept_step α β B c2 hstate2 hcells2
        (by simpa using hhead2) (by simpa using hcounter2) hpassive2 hout2
    have hreach_total : satLengthCheckPassiveTM.reachesIn (1 + α.length + 1) c0 c3 := by
      simpa [Nat.add_assoc] using
        TM.reachesIn_trans _ (.step hstep1 .zero)
          (TM.reachesIn_trans _ hreach2 (.step hstep3 .zero))
    refine ⟨c3, 1 + α.length + 1, by
      simp [satLengthCheckTime]
      omega, hreach_total, hhalt3, ?_⟩
    exact ⟨hcells3, by rw [hpassive3]; exact hpassive2, by simpa [hle] using hout3⟩
  · have hlt : B < α.length := by omega
    obtain ⟨c2, hreach2, hstate2, hcells2, hhead2, hcounter2, hpassive2, hout2⟩ :=
      satLengthCheckPassive_scan_prefix_loop α β B B 0 c1
        (by omega) (by omega) hstate1 hcells1 hhead1 hcounter1 hpassive1 hout1_started
    obtain ⟨c3, hstep3, hhalt3, hcells3, hpassive3, hout3⟩ :=
      satLengthCheckPassive_scan_reject_step α β B c2 hlt hstate2 hcells2
        (by simpa using hhead2) (by simpa using hcounter2) hpassive2 hout2
    have hreach_total : satLengthCheckPassiveTM.reachesIn (1 + B + 1) c0 c3 := by
      simpa [Nat.add_assoc] using
        TM.reachesIn_trans _ (.step hstep1 .zero)
          (TM.reachesIn_trans _ hreach2 (.step hstep3 .zero))
    refine ⟨c3, 1 + B + 1, by
      simp [satLengthCheckTime]
      omega, hreach_total, hhalt3, ?_⟩
    exact ⟨hcells3, by rw [hpassive3]; exact hpassive2, by simpa [hle] using hout3⟩

/-- Three-work-tape length checker obtained by retargeting the input of
`satLengthCheckPassiveTM` to work tape `2`. Tape `0` stores the unary bound,
tape `1` is preserved, and tape `2` provides the witness bits. -/
def satLengthCheck3TM : TM 3 :=
  TM.retargetInput satLengthCheckPassiveTM

/-- Virtual-input/work-tape version of `satLengthCheckPassiveTM`: work tape
`2` supplies the witness bits, work tape `0` supplies the unary bound, and
work tape `1` is preserved exactly.
@isnad1 id=hoaretim.0h3v.s7.68c0db0e199b from=translated src=- shape=1914b4b8 vocab=de79a57a
-/
theorem satLengthCheck3TM_started_hoareTime (B : ℕ) (α β : List Bool) :
    satLengthCheck3TM.HoareTime
      (fun _inp work out =>
        (work ⟨2, by omega⟩) = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter B ∧
        work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp work out =>
        work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨2, by omega⟩).cells = (Tape.init (α.map Γ.ofBool)).cells ∧
        out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero))
      (satLengthCheckTime α.length) := by
  have hmove_right_invariant : ∀ {t : Tape}, Tape.StartInvariant t →
      Tape.StartInvariant (t.move Dir3.right) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · simpa [Tape.move_cells] using ht.1
    · intro j hj
      simpa [Tape.move_cells] using ht.2 j hj
  have hlen :
      satLengthCheckPassiveTM.HoareTime
        (fun inp work out =>
          inp = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
          (work ⟨0, by omega⟩).HasUnaryCounter B ∧
          work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
          (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
          (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
          out = (Tape.init []).move Dir3.right)
        (fun inp work out =>
          inp.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
          work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
          out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero))
        (satLengthCheckTime α.length) :=
    (satLengthCheckPassiveTM_started_hoareTime B α β).weaken_pre (by
      intro inp work out hpre
      exact ⟨hpre.1, hpre.2.1, hpre.2.2.1, hpre.2.2.2.2.2⟩)
  have hret := TM.retargetInput_hoareTime (M := satLengthCheckPassiveTM)
    hlen
    (hpre_inp := by
      intro _inp work out hpre
      rcases hpre with ⟨hvin, _hrest⟩
      rw [hvin]
      exact hmove_right_invariant (Tape.StartInvariant.init_ofBool α))
    (hpre_work := by
      intro _inp work out hpre i
      rcases hpre with ⟨_hvin, hrest⟩
      rcases hrest with ⟨_hcounter, hrest⟩
      rcases hrest with ⟨hpassive, hrest⟩
      rcases hrest with ⟨hcell0, hrest⟩
      rcases hrest with ⟨hnostart, _hout⟩
      by_cases hi0 : i = ⟨0, by omega⟩
      · subst hi0
        exact ⟨hcell0, hnostart⟩
      · have hi1 := fin2_ne_zero_eq_one i hi0
        subst hi1
        rw [hpassive]
        exact hmove_right_invariant (Tape.StartInvariant.init_ofBool β))
    (hpre_out := by
      intro _inp work out hpre
      rcases hpre with ⟨_hvin, hrest⟩
      rcases hrest with ⟨_hcounter, hrest⟩
      rcases hrest with ⟨_hpassive, hrest⟩
      rcases hrest with ⟨_hcell0, hrest⟩
      rcases hrest with ⟨_hnostart, hout⟩
      rw [hout]
      exact hmove_right_invariant (Tape.StartInvariant.init_nil))
  have hret' : satLengthCheck3TM.HoareTime
      (fun _inp work out =>
        (work ⟨2, by omega⟩) = (Tape.init (α.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).HasUnaryCounter B ∧
        work ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
        (work ⟨0, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work ⟨0, by omega⟩).cells j ≠ Γ.start) ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp work out =>
        ∃ vin : Tape, ∃ innerWork : Fin 2 → Tape,
          (vin.cells = (Tape.init (α.map Γ.ofBool)).cells ∧
            innerWork ⟨1, by omega⟩ = (Tape.init (β.map Γ.ofBool)).move Dir3.right ∧
            out.cells 1 = (if α.length ≤ B then Γ.one else Γ.zero)) ∧
          (∀ i : Fin 2, work ⟨i.val, by omega⟩ = innerWork i) ∧
          work ⟨2, by omega⟩ = vin)
      (satLengthCheckTime α.length) := by
    simpa [satLengthCheck3TM] using hret
  refine hret'.strengthen_post ?_
  intro _inp work out hpost
  rcases hpost with ⟨vin, innerWork, hinner, hmap, hvin⟩
  exact ⟨(hmap ⟨1, by omega⟩).trans hinner.2.1,
    by rw [hvin]; exact hinner.1,
    hinner.2.2⟩

/-- Tail of the SAT witness-length verifier after the witness has been copied
to tape `2`: rewind tapes `1` and `2`, then run `satLengthCheck3TM`. -/
def satWitnessLengthTailTM : TM 3 :=
  TM.seqTM (TM.rewindWorkTM ⟨1, by omega⟩) <|
    TM.seqTM (TM.rewindWorkTM ⟨2, by omega⟩) satLengthCheck3TM

/-- Time bound for `satWitnessLengthTailTM`. -/
def satWitnessLengthTailTime (αLen : ℕ) : ℕ :=
  (αLen + 1 + 2) + 1 + (αLen + 1 + 2) + 1 + satLengthCheckTime αLen

-- ════════════════════════════════════════════════════════════════════════
-- Streaming CNF evaluator
-- ════════════════════════════════════════════════════════════════════════

/-- Parser/evaluator mode for the deterministic CNF evaluator.

`boundary cnf clause empty` means the machine is between raw literals. `cnf`
is the value of all completed clauses so far, `clause` is the disjunction
accumulated for the current clause, and `empty` records whether the current
clause has no completed literals. `inLit ... sign` means a raw literal has
started with sign bit `sign`; each following raw bit must be `true`, and the
assignment work-tape head tracks the current unary variable index. -/
inductive SatEvalMode where
  /-- Between raw literals: `cnf` is the conjunction of completed clauses,
  `clause` the disjunction so far, `empty` whether the clause has no literals. -/
  | boundary (cnf clause empty : Bool)
  /-- Inside a raw literal with sign bit `sign`; the assignment head tracks
  the unary variable index. -/
  | inLit (cnf clause empty sign : Bool)
  deriving DecidableEq, Repr

instance : Fintype SatEvalMode where
  elems :=
    (Finset.univ.image fun p : Bool × Bool × Bool =>
      SatEvalMode.boundary p.1 p.2.1 p.2.2) ∪
    (Finset.univ.image fun p : Bool × Bool × Bool × Bool =>
      SatEvalMode.inLit p.1 p.2.1 p.2.2.1 p.2.2.2)
  complete := by
    intro m
    cases m with
    | boundary cnf clause empty =>
        simp
    | inLit cnf clause empty sign =>
        simp

/-- Control states for the streaming CNF evaluator. The input tape supplies the
SAT encoding `z`; work tape `0` supplies the assignment `α`. -/
inductive SatEvalPhase where
  /-- Reading the first bit of a doubled-bit token in mode `mode`. -/
  | readFirst (mode : SatEvalMode)
  /-- Reading the second bit of a token whose first bit was `first`. -/
  | readSecond (mode : SatEvalMode) (first : Bool)
  /-- Rewinding the assignment tape to its left marker before continuing
  in mode `mode`. -/
  | rewindAlpha (mode : SatEvalMode)
  /-- Halt state: the verdict has been written to the output tape. -/
  | done
  deriving DecidableEq, Repr

instance : Fintype SatEvalPhase where
  elems :=
    insert SatEvalPhase.done <|
      (Finset.univ.image SatEvalPhase.readFirst) ∪
      (Finset.univ.image fun p : SatEvalMode × Bool =>
        SatEvalPhase.readSecond p.1 p.2) ∪
      (Finset.univ.image SatEvalPhase.rewindAlpha)
  complete := by
    intro q
    cases q with
    | done =>
        simp
    | readFirst mode =>
        simp
    | readSecond mode first =>
        simp
    | rewindAlpha mode =>
        simp

/-- Writable tape symbol encoding of a Boolean. -/
def boolWrite (b : Bool) : Γw :=
  if b then Γw.one else Γw.zero

/-- Decodes a tape symbol as a bit when it is `0` or `1`. -/
def readBit? : Γ → Option Bool
  | Γ.zero => some false
  | Γ.one => some true
  | _ => none

/-- Assignment value represented by the symbol under the assignment-tape head. -/
def assignmentBitAtHead (g : Γ) : Bool :=
  g = Γ.one

/-- Truth value of a signed literal at the assignment-tape head. -/
def literalValueAtHead (sign : Bool) (g : Γ) : Bool :=
  assignmentBitAtHead g == sign

/-- Output written when the evaluator reaches the end of the encoded formula. -/
def finishEvalMode : SatEvalMode → Γw
  | .boundary cnf _clause empty => boolWrite (cnf && empty)
  | .inLit .. => Γw.zero

/-- Rejecting transition that preserves the current tape contents. -/
def satEvalReject {n : ℕ} (state : SatEvalPhase)
    (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    SatEvalPhase × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3 :=
  (state, fun i => TM.readBackWrite (wHeads i), Γw.zero,
    TM.idleDir iHead, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)

/-- Pure evaluator-state transition for one decoded encoding token. -/
def satEvalTokenStep (mode : SatEvalMode) (tok : EncToken) (αHead : Γ) :
    SatEvalPhase × Dir3 × Γw :=
  match mode with
  | .boundary cnf clause empty =>
      match tok with
      | .bit sign => (.readFirst (.inLit cnf clause empty sign), Dir3.stay, Γw.blank)
      | .litSep => (.done, Dir3.stay, Γw.zero)
      | .clauseSep => (.readFirst (.boundary (cnf && clause) false true), Dir3.stay, Γw.blank)
  | .inLit cnf clause _empty sign =>
      match tok with
      | .bit b =>
          if b then
            (.readFirst (.inLit cnf clause false sign), Dir3.right, Γw.blank)
          else
            (.done, Dir3.stay, Γw.zero)
      | .litSep =>
          let litVal := literalValueAtHead sign αHead
          (.rewindAlpha (.boundary cnf (clause || litVal) false), Dir3.stay, Γw.blank)
      | .clauseSep =>
          (.done, Dir3.stay, Γw.zero)

/-- Decodes the fixed two-bit representation of an encoding token. -/
def tokenOfBits (first second : Bool) : EncToken :=
  match first, second with
  | false, false => .bit false
  | true, true => .bit true
  | false, true => .litSep
  | true, false => .clauseSep

/-- Transition function of the one-work-tape SAT evaluator. -/
def satEvalDelta :
    SatEvalPhase → Γ → (Fin 1 → Γ) → Γ →
      SatEvalPhase × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3 :=
  fun state iHead wHeads oHead =>
    let αHead := wHeads ⟨0, by omega⟩
    match state with
    | .readFirst mode =>
        if iHead = Γ.blank then
          (.done,
            fun i => TM.readBackWrite (wHeads i),
            finishEvalMode mode,
            TM.idleDir iHead,
            fun i => TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          match readBit? iHead with
          | some b =>
              (.readSecond mode b,
                fun i => TM.readBackWrite (wHeads i),
                TM.readBackWrite oHead,
                Dir3.right,
                fun i => TM.idleDir (wHeads i),
                TM.idleDir oHead)
          | none =>
              satEvalReject .done iHead wHeads oHead
    | .readSecond mode first =>
        match readBit? iHead with
        | some second =>
            let (nextState, αDir, outWrite) :=
              satEvalTokenStep mode (tokenOfBits first second) αHead
            (nextState,
              fun i => TM.readBackWrite (wHeads i),
              outWrite,
              Dir3.right,
              fun i =>
                if i = ⟨0, by omega⟩ then
                  if αHead = Γ.start then Dir3.right else αDir
                else
                  TM.idleDir (wHeads i),
              TM.idleDir oHead)
        | none =>
            satEvalReject .done iHead wHeads oHead
    | .rewindAlpha mode =>
        if αHead = Γ.start then
          (.readFirst mode,
            fun i => TM.readBackWrite (wHeads i),
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i => if i = ⟨0, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          (.rewindAlpha mode,
            fun i => TM.readBackWrite (wHeads i),
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i => if i = ⟨0, by omega⟩ then Dir3.left else TM.idleDir (wHeads i),
            TM.idleDir oHead)
    | .done =>
        TM.allIdle .done iHead wHeads oHead

private theorem satEvalDelta_right_of_start
    (state : SatEvalPhase) (iHead : Γ) (wHeads : Fin 1 → Γ) (oHead : Γ) :
    let tr := satEvalDelta state iHead wHeads oHead
    (iHead = Γ.start → tr.2.2.2.1 = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → tr.2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → tr.2.2.2.2.2 = Dir3.right) := by
  aesop (add simp [satEvalDelta, satEvalReject, readBit?, satEvalTokenStep,
    tokenOfBits, TM.allIdle, TM.idleDir_right_of_start,
    TM.rightOfStart_allIdle])

/-- Deterministic evaluator for a SAT-encoded CNF on the input tape and an
assignment on work tape `0`.

The evaluator tokenizes the input in two-bit groups. It rejects odd-length
inputs and malformed raw literals, treats assignment positions beyond `α` as
`false` by reading blanks, and writes the Boolean value of the decoded CNF to
output cell `1`. The formal correctness theorem is the next layer; this
definition is the concrete finite-state machine that theorem targets. -/
def satEvalOnInputTM : TM 1 where
  Q := SatEvalPhase
  qstart := .readFirst (.boundary true false true)
  qhalt := .done
  δ := satEvalDelta
  δ_right_of_start := by
    intro state iHead wHeads oHead
    exact satEvalDelta_right_of_start state iHead wHeads oHead

/-- Pure parser/evaluator state for the streaming CNF evaluator, abstracting
the machine mode `SatEvalMode`: either at a token `boundary` (tracking the
CNF-so-far, clause-so-far, and clause-emptiness Booleans) or `inLit` scanning
a raw literal with its sign and unary variable counter `var`. -/
inductive SatEvalSemState where
  /-- Between tokens: `cnf` is the conjunction of completed clauses, `clause`
  the disjunction so far, `empty` whether the clause has no literals. -/
  | boundary (cnf clause empty : Bool)
  /-- Inside a raw literal with sign bit `sign` and unary variable counter
  `var`. -/
  | inLit (cnf clause empty sign : Bool) (var : Nat)
  deriving DecidableEq, Repr

/-- End-of-input result: at a `boundary` the value is `cnf && empty` (the CNF
so far, provided the trailing clause is empty, i.e. the last token was `#`);
ending inside a literal is malformed and yields `false`. -/
def SatEvalSemState.finish : SatEvalSemState → Bool
  | .boundary cnf _ empty => cnf && empty
  | .inLit .. => false

private def SatEvalMode.toSemState : SatEvalMode → ℕ → SatEvalSemState
  | .boundary cnf clause empty, _ => .boundary cnf clause empty
  | .inLit cnf clause empty sign, var => .inLit cnf clause empty sign var

private def SatEvalMode.assignmentHead : SatEvalMode → ℕ → ℕ
  | .boundary .., _ => 1
  | .inLit .., var => var + 1

/-- One-token transition of the pure evaluator under assignment `α`:
`none` on malformed input (a separator with no literal, or a `false` bit
inside a literal body); otherwise the updated `SatEvalSemState`, folding a
completed literal's value into the clause accumulator at each `litSep`. -/
def satEvalSemStep (α : Assignment) : SatEvalSemState → EncToken → Option SatEvalSemState
  | .boundary cnf clause empty, .bit sign => some (.inLit cnf clause empty sign 0)
  | .boundary _ _ _, .litSep => none
  | .boundary cnf clause _, .clauseSep => some (.boundary (cnf && clause) false true)
  | .inLit cnf clause _ sign var, .bit b =>
      if b then some (.inLit cnf clause false sign (var + 1)) else none
  | .inLit cnf clause _ sign var, .litSep =>
      some (.boundary cnf (clause || (Assignment.get α var == sign)) false)
  | .inLit _ _ _ _ _, .clauseSep => none

/-- Run the pure evaluator over a token stream from a given state: fold
`satEvalSemStep` over the tokens, returning `false` on any malformed step and
`SatEvalSemState.finish` at the end of input. -/
def satEvalSemRun (α : Assignment) : List EncToken → SatEvalSemState → Bool
  | [], st => st.finish
  | tok :: toks, st =>
      match satEvalSemStep α st tok with
      | none => false
      | some st' => satEvalSemRun α toks st'

/-- Bit-level pure evaluator: tokenize `z` (rejecting odd-length inputs) and
run `satEvalSemRun` from the initial state `.boundary true false true`.
Equals `CNF.eval α` on the decoded CNF by `satEvalSemBits_eq_decode_eval`. -/
def satEvalSemBits (α z : List Bool) : Bool :=
  match tokenize? z with
  | none => false
  | some toks => satEvalSemRun α toks (.boundary true false true)

/-- Coarse polynomial budget for the split-input evaluator. Rewinding the
assignment after each completed literal gives a quadratic upper bound once
`α.length ≤ z.length + 1`; this standalone bound keeps both lengths explicit. -/
def satEvalOnInputTime (zLen αLen : ℕ) : ℕ :=
  (zLen + 1) * (αLen + 3) + 2

private def parseEvalResult (α : Assignment) (toks : List EncToken)
    (rawRev : List Bool) (clauseRev : Clause) (cnfRev : CNF) : Bool :=
  match parseTokensAux toks rawRev clauseRev cnfRev with
  | none => false
  | some φ => CNF.eval α φ

private def RawInvalid (rawRev : List Bool) : Prop :=
  ∃ sign rest, rawRev.reverse = sign :: rest ∧ false ∈ rest

private lemma RawInvalid.cons (b : Bool) {rawRev : List Bool} (h : RawInvalid rawRev) :
    RawInvalid (b :: rawRev) := by
  rcases h with ⟨sign, rest, hrev, hmem⟩
  refine ⟨sign, rest ++ [b], ?_, ?_⟩ <;> simp [hrev, hmem]

private lemma RawInvalid.ne_nil {rawRev : List Bool} (h : RawInvalid rawRev) : rawRev ≠ [] := by
  rintro rfl
  rcases h with ⟨_sign, _rest, hrev, _⟩
  simp at hrev

private lemma RawInvalid.decodeRaw?_eq_none {rawRev : List Bool} (h : RawInvalid rawRev) :
    Lit.decodeRaw? rawRev.reverse = none := by
  rcases h with ⟨sign, rest, hrev, hmem⟩
  rw [hrev]
  simp only [Lit.decodeRaw?]
  split
  · have hfalse : false = true := ‹∀ b ∈ rest, b = true› false hmem
    cases hfalse
  · rfl

private lemma parseEvalResult_invalid_raw (α : Assignment) (toks : List EncToken)
    {rawRev : List Bool} (hbad : RawInvalid rawRev)
    (clauseRev : Clause) (cnfRev : CNF) :
    parseEvalResult α toks rawRev clauseRev cnfRev = false := by
  induction toks generalizing rawRev clauseRev cnfRev with
  | nil =>
      simp [parseEvalResult, parseTokensAux, RawInvalid.ne_nil hbad]
  | cons tok toks ih =>
      cases tok <;> simp [parseEvalResult, parseTokensAux]
      · exact ih (RawInvalid.cons _ hbad) clauseRev cnfRev
      · simp [RawInvalid.decodeRaw?_eq_none hbad]
      · simp [RawInvalid.ne_nil hbad]

/-- A singleton clause evaluates to the value of its unique literal.
@isnad1 id=eq.0h2v.s4.8721428d0cba from=translated src=- shape=84e112d7 vocab=75c3fc17
-/
@[simp] theorem Clause.eval_singleton (α : Assignment) (ℓ : Lit) :
    Clause.eval α [ℓ] = Lit.eval α ℓ := by
  simp [Clause.eval]

private def SatEvalSemRel (α : Assignment) :
    SatEvalSemState → List Bool → Clause → CNF → Prop
  | .boundary cnf clause empty, rawRev, clauseRev, cnfRev =>
      rawRev = [] ∧ cnf = CNF.eval α cnfRev.reverse ∧
      clause = Clause.eval α clauseRev.reverse ∧ empty = decide (clauseRev = [])
  | .inLit cnf clause _ sign var, rawRev, clauseRev, cnfRev =>
      rawRev = List.replicate var true ++ [sign] ∧
      cnf = CNF.eval α cnfRev.reverse ∧ clause = Clause.eval α clauseRev.reverse

private lemma rawInvalid_false_cons_valid (sign : Bool) (var : Nat) :
    RawInvalid (false :: (List.replicate var true ++ [sign])) := by
  refine ⟨sign, List.replicate var true ++ [false], ?_, ?_⟩
  · simp [List.reverse_append]
  · simp

private lemma lit_decode_replicate (sign : Bool) (var : Nat) :
    Lit.decodeRaw? (sign :: List.replicate var true) = some { sign := sign, var := var } := by
  simp [Lit.decodeRaw?]

private lemma satEvalSemRun_correct (α : Assignment) (toks : List EncToken) :
    ∀ (st : SatEvalSemState) (rawRev : List Bool) (clauseRev : Clause) (cnfRev : CNF),
      SatEvalSemRel α st rawRev clauseRev cnfRev →
      satEvalSemRun α toks st = parseEvalResult α toks rawRev clauseRev cnfRev := by
  induction toks with
  | nil =>
      intro st rawRev clauseRev cnfRev hrel
      cases st with
      | boundary cnf clause empty =>
          rcases hrel with ⟨hraw, hcnf, hclause, hempty⟩
          subst hraw; subst hcnf; subst hclause; subst hempty
          by_cases hcl : clauseRev = []
          · subst hcl
            simp [satEvalSemRun, SatEvalSemState.finish, parseEvalResult, parseTokensAux]
          · simp [satEvalSemRun, SatEvalSemState.finish, parseEvalResult, parseTokensAux, hcl]
      | inLit _ _ _ _ _ =>
          rcases hrel with ⟨hraw, _, _⟩
          subst hraw
          simp [satEvalSemRun, SatEvalSemState.finish, parseEvalResult, parseTokensAux]
  | cons tok toks ih =>
      intro st rawRev clauseRev cnfRev hrel
      cases st with
      | boundary cnf clause empty =>
          rcases hrel with ⟨hraw, hcnf, hclause, hempty⟩
          subst hraw; subst hcnf; subst hclause; subst hempty
          cases tok with
          | bit b =>
              simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux]
              exact ih (.inLit (CNF.eval α cnfRev.reverse) (Clause.eval α clauseRev.reverse)
                (decide (clauseRev = [])) b 0) [b] clauseRev cnfRev
                ⟨by simp, rfl, rfl⟩
          | litSep =>
              simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux, Lit.decodeRaw?]
          | clauseSep =>
              simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux]
              have h := ih
                (.boundary (CNF.eval α cnfRev.reverse && Clause.eval α clauseRev.reverse)
                  false true)
                [] [] (clauseRev.reverse :: cnfRev)
                ⟨rfl, ?_, ?_, ?_⟩
              · exact h
              · simp [CNF.eval, List.reverse_cons]
              · simp [Clause.eval]
              · simp
      | inLit _ _ _ sign var =>
          rcases hrel with ⟨hraw, hcnf, hclause⟩
          subst hraw; subst hcnf; subst hclause
          cases tok with
          | bit b =>
              cases b
              · simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux]
                exact parseEvalResult_invalid_raw α toks
                  (rawInvalid_false_cons_valid sign var) clauseRev cnfRev
              · simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux]
                exact ih
                  (.inLit (CNF.eval α cnfRev.reverse) (Clause.eval α clauseRev.reverse)
                    false sign (var + 1))
                  (true :: (List.replicate var true ++ [sign])) clauseRev cnfRev
                  ⟨by simp [List.replicate_succ, List.cons_append], rfl, rfl⟩
          | litSep =>
              simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux]
              have hdecode : Lit.decodeRaw? (sign :: List.replicate var true) =
                  some { sign := sign, var := var } := lit_decode_replicate sign var
              simp [hdecode]
              have h := ih
                (.boundary (CNF.eval α cnfRev.reverse)
                  (Clause.eval α clauseRev.reverse || (Assignment.get α var == sign)) false)
                [] ({ sign := sign, var := var } :: clauseRev) cnfRev
                ⟨rfl, rfl, ?_, ?_⟩
              · exact h
              · simp [Clause.eval, Lit.eval]
              · simp
          | clauseSep =>
              simp [satEvalSemRun, satEvalSemStep, parseEvalResult, parseTokensAux]

/-- Correctness of the pure evaluator: `satEvalSemBits α z` is `false` when
`z` fails to decode as a CNF, and otherwise is `CNF.eval α` of the decoded
formula.
@isnad1 id=eq.0h2v.s4.b305f141d793 from=translated src=- shape=d9b99313 vocab=13882a94
-/
theorem satEvalSemBits_eq_decode_eval (α z : List Bool) :
    satEvalSemBits α z =
      match CNF.decode? z with
      | none => false
      | some φ => CNF.eval α φ := by
  unfold satEvalSemBits CNF.decode?
  cases htok : tokenize? z with
  | none =>
      simp
  | some toks =>
      simp
      have h := satEvalSemRun_correct α toks (.boundary true false true) [] [] []
        ⟨rfl, by simp [CNF.eval], by simp [Clause.eval], by simp⟩
      exact h

/-- Pure semantic model of the paired SAT verifier: unpair `w` into `(z, α)`,
check the witness-length bound `|α| ≤ |z| + 1`, and evaluate the encoded CNF
`z` under `α` via `satEvalSemBits`; `false` on malformed pairs. -/
def verifyPairSem (w : List Bool) : Bool :=
  match unpair? w with
  | none => false
  | some (z, α) => decide (α.length ≤ z.length + 1) && satEvalSemBits α z

/-- The pure semantic model agrees with the reference Boolean verifier
`SAT.verifyPair` on every input.
@isnad1 id=eq.0h1v.s3.482b1e71b63c from=translated src=- shape=44e33ebc vocab=724abf1b
-/
theorem verifyPairSem_eq_verifyPair (w : List Bool) :
    verifyPairSem w = verifyPair w := by
  unfold verifyPairSem verifyPair
  cases hunpair : unpair? w with
  | none =>
      simp
  | some za =>
      rcases za with ⟨z, α⟩
      simp
      rw [satEvalSemBits_eq_decode_eval]
      cases CNF.decode? z <;> simp

/-- `verifyPairSem` accepts exactly the members of the paired witness
language `pairLang Witness`.
@isnad1 id=iff.0h1v.s4.87e971016042 from=translated src=- shape=b62a3d99 vocab=a472d758
-/
theorem verifyPairSem_eq_true_iff_mem_pairLang (w : List Bool) :
    verifyPairSem w = true ↔ w ∈ pairLang Witness := by
  rw [verifyPairSem_eq_verifyPair, verifyPair_eq_true_iff_mem_pairLang]

/-- Set-level restatement: `pairLang Witness` is the language accepted by the
pure semantic verifier `verifyPairSem`.
@isnad1 id=eq.0h0v.s3.3c17b2aeb4ef from=translated src=- shape=3255e942 vocab=5da96136
-/
theorem pairLang_witness_eq_verifyPairSemLang :
    pairLang Witness = {w | verifyPairSem w = true} := by
  ext w
  exact (verifyPairSem_eq_true_iff_mem_pairLang w).symm

-- ════════════════════════════════════════════════════════════════════════
-- Full paired SAT verifier machine
-- ════════════════════════════════════════════════════════════════════════

/-- Control states for the deterministic paired SAT verifier.

Work-tape layout:

* tape `0`: decoded formula encoding `z`,
* tape `1`: decoded assignment `α`,
* tape `2`: a unary counter initially holding `|z| + 1`, consumed while
  copying `α`.

The machine first validates and splits the outer `pair z α` encoding, checks
the SAT witness length bound during the split, rewinds the staged `z` and `α`
tapes, and then runs the same streaming CNF evaluator as `satEvalOnInputTM`
against the staged work tapes. -/
inductive VerifyPairPhase where
  /-- Initial state: step off the left markers. -/
  | init
  /-- Write the extra leading counter tally before the split scan. -/
  | initCounter
  /-- Split scan: expecting the first bit of a doubled input bit or of the
  separator `01`. -/
  | splitScan
  /-- Split scan after a first `false`: a `false` completes a doubled bit,
  a `true` completes the separator. -/
  | splitAfterFalse
  /-- Split scan after a first `true`: only a second `true` is valid. -/
  | splitAfterTrue
  /-- Rewind the counter tape before copying the assignment. -/
  | rewindCounterForAlpha
  /-- Copy the assignment suffix to work tape `1`, consuming counter tallies
  to enforce the witness-length bound. -/
  | copyAlpha
  /-- Rewind the staged formula tape to its left marker. -/
  | rewindFormula
  /-- Rewind the staged assignment tape to its left marker. -/
  | rewindAssignment
  /-- Evaluator phase mirroring `SatEvalPhase.readFirst`. -/
  | evalReadFirst (mode : SatEvalMode)
  /-- Evaluator phase mirroring `SatEvalPhase.readSecond`. -/
  | evalReadSecond (mode : SatEvalMode) (first : Bool)
  /-- Evaluator phase mirroring `SatEvalPhase.rewindAlpha`. -/
  | evalRewindAlpha (mode : SatEvalMode)
  /-- Halt state: the verdict has been written to the output tape. -/
  | done
  deriving DecidableEq, Repr

instance : Fintype VerifyPairPhase where
  elems :=
    insert VerifyPairPhase.init <|
    insert VerifyPairPhase.initCounter <|
    insert VerifyPairPhase.splitScan <|
    insert VerifyPairPhase.splitAfterFalse <|
    insert VerifyPairPhase.splitAfterTrue <|
    insert VerifyPairPhase.rewindCounterForAlpha <|
    insert VerifyPairPhase.copyAlpha <|
    insert VerifyPairPhase.rewindFormula <|
    insert VerifyPairPhase.rewindAssignment <|
    insert VerifyPairPhase.done <|
      (Finset.univ.image VerifyPairPhase.evalReadFirst) ∪
      (Finset.univ.image fun p : SatEvalMode × Bool =>
        VerifyPairPhase.evalReadSecond p.1 p.2) ∪
      (Finset.univ.image VerifyPairPhase.evalRewindAlpha)
  complete := by
    intro q
    cases q <;> simp

/-- Rejecting transition for the paired-formula verifier. -/
def verifyPairReject (iHead : Γ) (wHeads : Fin 3 → Γ) (oHead : Γ) :
    VerifyPairPhase × (Fin 3 → Γw) × Γw × Dir3 × (Fin 3 → Dir3) × Dir3 :=
  (.done, fun i => TM.readBackWrite (wHeads i), Γw.zero,
    TM.idleDir iHead, fun i => TM.idleDir (wHeads i),
    TM.idleDir oHead)

/-- Rewrites every paired-verifier work symbol without changing its value. -/
def verifyPairPreserveWork (wHeads : Fin 3 → Γ) : Fin 3 → Γw :=
  fun i => TM.readBackWrite (wHeads i)

/-- Work-tape writes while splitting the formula and assignment encodings. -/
def verifyPairSplitWrite (zBit : Bool) (wHeads : Fin 3 → Γ) : Fin 3 → Γw :=
  fun i =>
    if i = ⟨0, by omega⟩ then boolWrite zBit
    else if i = ⟨2, by omega⟩ then Γw.one
    else TM.readBackWrite (wHeads i)

/-- Work-tape head directions while splitting the paired encoding. -/
def verifyPairSplitDirs (wHeads : Fin 3 → Γ) : Fin 3 → Dir3 :=
  fun i =>
    if i = ⟨0, by omega⟩ then Dir3.right
    else if i = ⟨2, by omega⟩ then Dir3.right
    else TM.idleDir (wHeads i)

/-- Work-tape writes while copying the assignment component. -/
def verifyPairCopyAlphaWrite (aBit : Bool) (wHeads : Fin 3 → Γ) :
    Fin 3 → Γw :=
  fun i =>
    if i = ⟨1, by omega⟩ then boolWrite aBit
    else if i = ⟨2, by omega⟩ then Γw.blank
    else TM.readBackWrite (wHeads i)

/-- Work-tape head directions while copying the assignment component. -/
def verifyPairCopyAlphaDirs (wHeads : Fin 3 → Γ) : Fin 3 → Dir3 :=
  fun i =>
    if i = ⟨1, by omega⟩ then Dir3.right
    else if i = ⟨2, by omega⟩ then Dir3.right
    else TM.idleDir (wHeads i)

/-- Work-tape directions induced by one evaluator step. -/
def verifyPairEvalDirs (αHead : Γ) (αDir : Dir3) (wHeads : Fin 3 → Γ) :
    Fin 3 → Dir3 :=
  fun i =>
    if i = ⟨0, by omega⟩ then Dir3.right
    else if i = ⟨1, by omega⟩ then
      if αHead = Γ.start then Dir3.right else αDir
    else
      TM.idleDir (wHeads i)

/-- Transition function for verifying a paired formula-and-assignment encoding. -/
def verifyPairDelta :
    VerifyPairPhase → Γ → (Fin 3 → Γ) → Γ →
      VerifyPairPhase × (Fin 3 → Γw) × Γw × Dir3 × (Fin 3 → Dir3) × Dir3 :=
  fun state iHead wHeads oHead =>
    let zHead := wHeads ⟨0, by omega⟩
    let αHead := wHeads ⟨1, by omega⟩
    let counterHead := wHeads ⟨2, by omega⟩
    match state with
    | .init =>
        (.initCounter,
          verifyPairPreserveWork wHeads,
          TM.readBackWrite oHead,
          Dir3.right,
          fun _ => Dir3.right,
          Dir3.right)
    | .initCounter =>
        (.splitScan,
          fun i =>
            if i = ⟨2, by omega⟩ then Γw.one
            else TM.readBackWrite (wHeads i),
          TM.readBackWrite oHead,
          TM.idleDir iHead,
          fun i => if i = ⟨2, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
          TM.idleDir oHead)
    | .splitScan =>
        match readBit? iHead with
        | some false =>
            (.splitAfterFalse, verifyPairPreserveWork wHeads, TM.readBackWrite oHead,
              Dir3.right, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
        | some true =>
            (.splitAfterTrue, verifyPairPreserveWork wHeads, TM.readBackWrite oHead,
              Dir3.right, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
        | none =>
            verifyPairReject iHead wHeads oHead
    | .splitAfterFalse =>
        match readBit? iHead with
        | some false =>
            (.splitScan,
              verifyPairSplitWrite false wHeads,
              TM.readBackWrite oHead,
              Dir3.right,
              verifyPairSplitDirs wHeads,
              TM.idleDir oHead)
        | some true =>
            (.rewindCounterForAlpha,
              verifyPairPreserveWork wHeads,
              TM.readBackWrite oHead,
              Dir3.right,
              fun i => TM.idleDir (wHeads i),
              TM.idleDir oHead)
        | none =>
            verifyPairReject iHead wHeads oHead
    | .splitAfterTrue =>
        match readBit? iHead with
        | some true =>
            (.splitScan,
              verifyPairSplitWrite true wHeads,
              TM.readBackWrite oHead,
              Dir3.right,
              verifyPairSplitDirs wHeads,
              TM.idleDir oHead)
        | _ =>
            verifyPairReject iHead wHeads oHead
    | .rewindCounterForAlpha =>
        if counterHead = Γ.start then
          (.copyAlpha,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨2, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          (.rewindCounterForAlpha,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨2, by omega⟩ then Dir3.left else TM.idleDir (wHeads i),
            TM.idleDir oHead)
    | .copyAlpha =>
        if iHead = Γ.blank then
          (.rewindFormula,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i => TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          match readBit? iHead with
          | some b =>
              if counterHead = Γ.one then
                (.copyAlpha,
                  verifyPairCopyAlphaWrite b wHeads,
                  TM.readBackWrite oHead,
                  Dir3.right,
                  verifyPairCopyAlphaDirs wHeads,
                  TM.idleDir oHead)
              else
                verifyPairReject iHead wHeads oHead
          | none =>
              verifyPairReject iHead wHeads oHead
    | .rewindFormula =>
        if zHead = Γ.start then
          (.rewindAssignment,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨0, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          (.rewindFormula,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨0, by omega⟩ then Dir3.left else TM.idleDir (wHeads i),
            TM.idleDir oHead)
    | .rewindAssignment =>
        if αHead = Γ.start then
          (.evalReadFirst (.boundary true false true),
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨1, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          (.rewindAssignment,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨1, by omega⟩ then Dir3.left else TM.idleDir (wHeads i),
            TM.idleDir oHead)
    | .evalReadFirst mode =>
        if zHead = Γ.blank then
          (.done,
            verifyPairPreserveWork wHeads,
            finishEvalMode mode,
            TM.idleDir iHead,
            fun i => TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          match readBit? zHead with
          | some b =>
              (.evalReadSecond mode b,
                verifyPairPreserveWork wHeads,
                TM.readBackWrite oHead,
                TM.idleDir iHead,
                fun i =>
                  if i = ⟨0, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
                TM.idleDir oHead)
          | none =>
              verifyPairReject iHead wHeads oHead
    | .evalReadSecond mode first =>
        match readBit? zHead with
        | some second =>
            let (nextState, αDir, outWrite) :=
              satEvalTokenStep mode (tokenOfBits first second) αHead
            let nextState' : VerifyPairPhase :=
              match nextState with
              | .readFirst mode' => .evalReadFirst mode'
              | .readSecond mode' first' => .evalReadSecond mode' first'
              | .rewindAlpha mode' => .evalRewindAlpha mode'
              | .done => .done
            (nextState',
              verifyPairPreserveWork wHeads,
              outWrite,
              TM.idleDir iHead,
              verifyPairEvalDirs αHead αDir wHeads,
              TM.idleDir oHead)
        | none =>
            verifyPairReject iHead wHeads oHead
    | .evalRewindAlpha mode =>
        if αHead = Γ.start then
          (.evalReadFirst mode,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨1, by omega⟩ then Dir3.right else TM.idleDir (wHeads i),
            TM.idleDir oHead)
        else
          (.evalRewindAlpha mode,
            verifyPairPreserveWork wHeads,
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if i = ⟨1, by omega⟩ then Dir3.left else TM.idleDir (wHeads i),
            TM.idleDir oHead)
    | .done =>
        TM.allIdle .done iHead wHeads oHead

private theorem verifyPairDelta_right_of_start
    (state : VerifyPairPhase) (iHead : Γ) (wHeads : Fin 3 → Γ) (oHead : Γ) :
    let tr := verifyPairDelta state iHead wHeads oHead
    (iHead = Γ.start → tr.2.2.2.1 = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → tr.2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → tr.2.2.2.2.2 = Dir3.right) := by
  aesop (add simp [verifyPairDelta, verifyPairReject, verifyPairPreserveWork,
    verifyPairSplitWrite, verifyPairSplitDirs, verifyPairCopyAlphaWrite,
    verifyPairCopyAlphaDirs, verifyPairEvalDirs, readBit?, satEvalTokenStep,
    tokenOfBits, TM.allIdle, TM.idleDir_right_of_start,
    TM.rightOfStart_allIdle])

/-- Deterministic three-work-tape verifier for the Boolean function
`SAT.verifyPair`.

This is the machine-level verifier construction. The polynomial budget below
is proved quadratic, and the end-to-end tape simulation below shows that this
split/length/evaluation pipeline writes `1` exactly when
`verifyPair w = true`. -/
def verifyPairTM : TM 3 where
  Q := VerifyPairPhase
  qstart := .init
  qhalt := .done
  δ := verifyPairDelta
  δ_right_of_start := by
    intro state iHead wHeads oHead
    exact verifyPairDelta_right_of_start state iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Eval phase: projection onto the proven single-tape evaluator
-- ════════════════════════════════════════════════════════════════════════

/-- Project a `verifyPairTM` eval-phase state to the single-tape evaluator's. -/
private def projEvalState : VerifyPairPhase → SatEvalPhase
  | .evalReadFirst m => .readFirst m
  | .evalReadSecond m first => .readSecond m first
  | .evalRewindAlpha m => .rewindAlpha m
  | _ => .done

/-- Project a `verifyPairTM` configuration onto a `satEvalOnInputTM`
configuration: the formula tape `0` becomes the (read-only) input, the
assignment tape `1` becomes work tape `0`, and the output is shared. -/
private def projEvalCfg (c : Cfg 3 verifyPairTM.Q) : Cfg 1 satEvalOnInputTM.Q :=
  { state := projEvalState c.state
    input := c.work ⟨0, by omega⟩
    work := fun _ => c.work ⟨1, by omega⟩
    output := c.output }

/-- Coarse polynomial budget for `verifyPairTM`. The split/length prefix is
linear, and the staged evaluator is quadratic in the input length because each
literal may rewind the assignment tape. -/
def verifyPairTMTime (n : ℕ) : ℕ :=
  (n + 3) * (n + 3) + 6 * n + 20

/-- The verifier's time budget `verifyPairTMTime` is `O(n²)`.
@isnad1 id=bigo.0h0v.s4.04f7eda593fa from=translated src=- shape=3efa0af9 vocab=2cb6c9f3
-/
theorem verifyPairTMTime_bigO_quadratic :
    Complexity.BigO verifyPairTMTime ((· ^ 2) : ℕ → ℕ) := by
  unfold Complexity.BigO
  apply Asymptotics.IsBigO.of_bound 50
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp only [Real.norm_natCast]
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hcalc : ((verifyPairTMTime n : ℕ) : ℝ) ≤ 50 * ((n ^ 2 : ℕ) : ℝ) := by
    simp [verifyPairTMTime]
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  exact hcalc

/-- The verifier's time budget is polynomially bounded (witnessed by
degree `2`), the form needed for polynomial-time verifier packaging.
@isnad1 id=ex.0h0v.s4.1caeca8dc65c from=translated src=- shape=4337b07c vocab=2cb6c9f3
-/
theorem verifyPairTMTime_polynomial :
    ∃ d : ℕ, Complexity.BigO verifyPairTMTime ((· ^ d) : ℕ → ℕ) :=
  ⟨2, verifyPairTMTime_bigO_quadratic⟩

-- ════════════════════════════════════════════════════════════════════════
-- Lemma B (eval projection) + combine: `verifyPairTM` decides `pairLang Witness`
-- ════════════════════════════════════════════════════════════════════════

/-- Predicate isolating the three evaluator-phase states of `verifyPairTM`. -/
private def isEvalState : VerifyPairPhase → Prop
  | .evalReadFirst _ => True
  | .evalReadSecond _ _ => True
  | .evalRewindAlpha _ => True
  | _ => False

end VerifierTM

end SAT

end Complexity
