/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step.Internal
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Structured

/-!
# Fixed RAM transition blocks for bounded Turing-machine configurations

The public layer exposes the exact register layout, verified loading and action
phases, and the composed nested state/symbol dispatcher. Thus the fixed
structured program has exact one-step source semantics; its common resource
envelope and compiled-RAM transfer are the next M6 layer.
-/

public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Step

/-- Every alphabet symbol is a valid four-way dispatch code.
@isnad1 id=lt.0h1v.s3.f7efcd489f27 from=translated src=- shape=a311c14d vocab=585c00b2
-/
theorem symbolCode_lt (symbol : Γ) : symbolCode symbol < 4 :=
  symbolCode_lt_internal symbol

/-- Dispatching on an encoded alphabet symbol recovers that symbol.
@isnad1 id=eq.0h1v.s3.fa62e22b251c from=translated src=- shape=674c64a6 vocab=ee35e664
-/
theorem symbolAt_code (symbol : Γ) :
    symbolAt ⟨symbolCode symbol, symbolCode_lt symbol⟩ = symbol :=
  symbolAt_code_internal symbol

/-- Every canonical state code is valid for the machine's finite state count.
@isnad1 id=lt.0h3v.s4.e7fd31a870d2 from=translated src=- shape=9841dd51 vocab=4c3429d2
-/
theorem stateCode_lt (tm : TM n) (state : tm.Q) :
    stateCode tm state < Fintype.card tm.Q :=
  stateCode_lt_internal tm state

/-- The arithmetic head address agrees with the configuration-field layout.
@isnad1 id=eq.0h3v.s4.4af8748623e7 from=translated src=- shape=c59134b2 vocab=71f92a3a
-/
theorem headReg_eq_fieldReg (tape : Fin (n + 2)) :
    headReg tape = fieldReg (headField (bound := bound) tape) :=
  headReg_eq_fieldReg_internal tape

/-- A tape-block base plus an in-window position agrees with the corresponding
configuration-field address.
@isnad1 id=eq.0h4v.s6.38ebe912caa9 from=translated src=- shape=da524fd9 vocab=9e208893
-/
theorem cellBase_add_eq_fieldReg (tape : Fin (n + 2))
    (position : Fin (bound + 1)) :
    cellBase n bound tape + position.val = fieldReg (cellField tape position) :=
  cellBase_add_eq_fieldReg_internal tape position

/-- The canonical register encoding fits the one-step program's explicit store
envelope whenever all represented heads lie in the chosen window.
@isnad1 id=storebou.1h4v.s4.1ea61693310b from=translated src=- shape=9a9db025 vocab=1d8f81e0
-/
theorem encodeRegs_storeBounded (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) (hheads : HeadsBounded cfg bound) :
    StoreBounded tm bound (encodeRegs tm bound cfg) :=
  encodeRegs_storeBounded_internal tm bound cfg hheads

/-- The generated load block preserves the represented configuration and loads
the state and every symbol needed by the finite transition dispatcher.
@isnad1 id=other.2h5v.s6.277ddd4013db from=translated src=- shape=8bfe64c7 vocab=82c270fe
-/
theorem loadOps_correct {tm : TM n} {bound : ℕ}
    {cfg : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hrepresents : Represents tm bound cfg store)
    (hheads : HeadsBounded cfg bound) :
    let final := Structured.Basic.execList (loadOps n bound) store
    Represents tm bound cfg final ∧
      final (zeroReg n bound) = 0 ∧
      final (oneReg n bound) = 1 ∧
      final (stateScratchReg n bound) = stateCode tm cfg.state ∧
      ∀ tape, final (symbolReg n bound tape) =
        symbolCode (readSymbols cfg tape) :=
  loadOps_loaded_internal hrepresents hheads

/-- Once the state and head symbols select a concrete transition, its generated
straight-line action maps any represented configuration to the exact TM
successor. The assumptions are precisely those needed by the bounded tape
layout: all heads are in range, writable tapes retain the left-end marker, and
the loading phase has initialized the constant-one scratch register.
@isnad1 id=represen.6h6v.s6.5f904a693372 from=translated src=- shape=f3a0fedf vocab=f36b9541
-/
theorem actionOps_correct {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm bound cfg store)
    (hheads : HeadsBounded cfg bound)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (hone : store (oneReg n bound) = 1) :
    Represents tm bound next
      (Structured.Basic.execList
        (actionOps tm bound cfg.state (readSymbols cfg)) store) :=
  actionOps_represents_internal hstep hrepresents hheads hworkStart
    houtputStart hone

/-- The complete fixed structured program performs exactly one nonhalting TM
transition. The source execution has the advertised exact instruction count and
its final store represents the successor configuration.
@isnad1 id=ex.5h6v.s6.3ef833cb5b92 from=translated src=- shape=00a9a1ed vocab=4c570a04
-/
theorem program_correct {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm bound cfg store)
    (hwindow : WithinWindow cfg bound)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant) :
    ∃ final cost space,
      Structured.Exec (program tm bound) store final
        (stepCount tm bound cfg) cost space ∧
      Represents tm bound next final :=
  program_exec_internal hstep hrepresents hwindow
    (fun i => (hworkStart i).1) houtputStart.1

/-- If the successor also fits the chosen cell window, decoding the complete
program's final store returns that successor exactly.
@isnad1 id=ex.6h6v.s6.9a8dd3408a6a from=translated src=- shape=3329b9a4 vocab=f3e1e383
-/
theorem program_decodes {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm bound cfg store)
    (hwindow : WithinWindow cfg bound)
    (hnextBounded : Bounded next bound)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant) :
    ∃ final cost space,
      Structured.Exec (program tm bound) store final
        (stepCount tm bound cfg) cost space ∧
      decode tm bound final = next := by
  obtain ⟨final, cost, space, hexec, hfinal⟩ :=
    program_correct hstep hrepresents hwindow hworkStart houtputStart
  exact ⟨final, cost, space, hexec,
    decode_of_represents tm bound next final hfinal hnextBounded⟩

/-- The complete one-step source block satisfies its exact transition count,
explicit logarithmic-cost bound, and peak-space bound while preserving both the
successor representation and the store envelope needed for composition.
@isnad1 id=ex.6h6v.s7.78b52f07080e from=translated src=- shape=34ff3217 vocab=d4c3efc7
-/
theorem program_performance {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm bound cfg store)
    (hwindow : WithinWindow cfg bound)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant)
    (hstore : StoreBounded tm bound store) :
    ∃ final cost space,
      Structured.Exec (program tm bound) store final
        (stepCount tm bound cfg) cost space ∧
      cost ≤ timeBound tm bound cfg ∧ space ≤ spaceBound tm bound ∧
      Represents tm bound next final ∧ StoreBounded tm bound final := by
  let henvelope : Structured.Internal.StoreEnvelope
      (registerLimit n bound) (wordBound tm bound) store :=
    ⟨hstore.1, hstore.2⟩
  obtain ⟨final, hrun, hfinalRepresents, hfinalEnvelope⟩ :=
    program_measured_internal hstep hrepresents hwindow
      (fun i => (hworkStart i).1) houtputStart.1 henvelope
  obtain ⟨cost, space, hexec, hcost, hspace⟩ := hrun
  exact ⟨final, cost, space, hexec, hcost, hspace, hfinalRepresents,
    hfinalEnvelope.index_lt, hfinalEnvelope.value_le⟩

/-- End-to-end transfer of the measured source theorem to the concrete compiled
RAM block. After the exact step count, the RAM is stopped at the compiler's
terminal halt instruction with the successor represented in its registers.
@isnad1 id=ex.6h6v.s7.511e26d3469c from=translated src=- shape=1b76b7f8 vocab=80ccd87d
-/
theorem compiled_correct {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm bound cfg store)
    (hwindow : WithinWindow cfg bound)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant)
    (hstore : StoreBounded tm bound store) :
    ∃ final cost space,
      Structured.Exec (program tm bound) store final
        (stepCount tm bound cfg) cost space ∧
      run (compiled tm bound) (stepCount tm bound cfg) { pc := 0, regs := store } =
        { pc := (program tm bound).codeSize, regs := final } ∧
      Halted (compiled tm bound)
        (run (compiled tm bound) (stepCount tm bound cfg) { pc := 0, regs := store }) ∧
      logTimeUpto (compiled tm bound) (stepCount tm bound cfg)
          { pc := 0, regs := store } ≤ timeBound tm bound cfg ∧
      spaceUpto (compiled tm bound) (stepCount tm bound cfg)
          { pc := 0, regs := store } ≤ spaceBound tm bound ∧
      Represents tm bound next final ∧ StoreBounded tm bound final := by
  obtain ⟨final, cost, space, hexec, hcost, hspace, hfinal, hfinalStore⟩ :=
    program_performance hstep hrepresents hwindow hworkStart houtputStart hstore
  have hcompiled := Structured.Exec.compile_correct hexec
  refine ⟨final, cost, space, hexec, ?_, ?_, ?_, ?_, hfinal, hfinalStore⟩
  · simpa [compiled] using hcompiled.1
  · simpa [compiled] using Structured.Exec.compile_halted hexec
  · change logTimeUpto (program tm bound).compile (stepCount tm bound cfg)
        { pc := 0, regs := store } ≤ timeBound tm bound cfg
    rw [hcompiled.2.1]
    exact hcost
  · change spaceUpto (program tm bound).compile (stepCount tm bound cfg)
        { pc := 0, regs := store } ≤ spaceBound tm bound
    rw [hcompiled.2.2]
    exact hspace

/-- The canonical encoded configuration therefore runs through the concrete
compiled block and decodes to the exact TM successor.
@isnad1 id=other.5h5v.s7.1b591644ac73 from=translated src=- shape=2b145b4f vocab=7ecb1782
-/
theorem compiled_encode_decodes {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q}
    (hstep : tm.step cfg = some next)
    (hwindow : WithinWindow cfg bound)
    (hnextBounded : Bounded next bound)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant) :
    let initial := encodeRegs tm bound cfg
    ∃ final cost space,
      Structured.Exec (program tm bound) initial final
        (stepCount tm bound cfg) cost space ∧
      run (compiled tm bound) (stepCount tm bound cfg) { pc := 0, regs := initial } =
        { pc := (program tm bound).codeSize, regs := final } ∧
      Halted (compiled tm bound)
        (run (compiled tm bound) (stepCount tm bound cfg)
          { pc := 0, regs := initial }) ∧
      logTimeUpto (compiled tm bound) (stepCount tm bound cfg)
          { pc := 0, regs := initial } ≤ timeBound tm bound cfg ∧
      spaceUpto (compiled tm bound) (stepCount tm bound cfg)
          { pc := 0, regs := initial } ≤ spaceBound tm bound ∧
      decode tm bound
        (run (compiled tm bound) (stepCount tm bound cfg)
          { pc := 0, regs := initial }).regs = next := by
  let initial := encodeRegs tm bound cfg
  obtain ⟨final, cost, space, hexec, hrun, hhalted, htime, hspace,
      hfinal, _hfinalStore⟩ := compiled_correct hstep
        (encodeRegs_represents tm bound cfg) hwindow hworkStart houtputStart
        (encodeRegs_storeBounded tm bound cfg hwindow.2)
  refine ⟨final, cost, space, hexec, hrun, hhalted, htime, hspace, ?_⟩
  rw [hrun]
  exact decode_of_represents tm bound next final hfinal hnextBounded

end Step

end TMConfig

end RAM

end Complexity
