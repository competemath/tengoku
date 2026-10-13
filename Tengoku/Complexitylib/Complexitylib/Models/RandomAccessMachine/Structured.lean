/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Structured.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Structured.Internal
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Structured.Switch

/-!
# Structured logarithmic-cost RAM programs

This module exposes a minimal imperative authoring language above the concrete
logarithmic-cost RAM. Source commands have independent register-store semantics;
`Cmd.compile` lowers structured conditionals and loops to absolute RAM jumps.

The main transfer theorem, `Exec.compile_correct`, is exact in all three
dimensions carried by `Exec`: final registers, operand-sensitive logarithmic
time, and peak register space. Thus source proofs can remain at the structured
level without weakening the concrete RAM resource statement.

`Switch.select` supplies the verified finite numeric case split used by the
Turing-machine transition compiler. Its branch selection has exact step
accounting and preserves explicit logarithmic-cost and space envelopes.
-/

public section

namespace Complexity

namespace RAM

namespace Structured

namespace Cmd

/-- A closed compiled command consists of its generated code followed by one
halt instruction.
@isnad1 id=eq.0h1v.s4.272763ada713 from=translated src=- shape=802c6af4 vocab=5749c8da
-/
theorem length_compile (cmd : Cmd) : cmd.compile.length = cmd.codeSize + 1 := by
  simp [compile, length_compileAt]

end Cmd

namespace Exec

/-- Exact semantic and resource preservation for closed compilation.
@isnad1 id=and.1h6v.s6.c1afd587daad from=translated src=- shape=045a001c vocab=65bf4892
-/
theorem compile_correct {cmd : Cmd} {initial final : Store} {steps cost space : ℕ}
    (hexec : Exec cmd initial final steps cost space) :
    run cmd.compile steps { pc := 0, regs := initial } =
        { pc := cmd.codeSize, regs := final } ∧
      logTimeUpto cmd.compile steps { pc := 0, regs := initial } = cost ∧
      spaceUpto cmd.compile steps { pc := 0, regs := initial } = space := by
  simpa [Cmd.compile] using
    compileAt_correct_internal hexec ([] : Program) [Instr.halt]

/-- A source execution reaches the halt instruction appended by `Cmd.compile`.
@isnad1 id=halted.1h6v.s5.1dd4299be0e3 from=translated src=- shape=1083a237 vocab=352f4061
-/
theorem compile_halted {cmd : Cmd} {initial final : Store} {steps cost space : ℕ}
    (hexec : Exec cmd initial final steps cost space) :
    Halted cmd.compile (run cmd.compile steps { pc := 0, regs := initial }) := by
  rw [(compile_correct hexec).1]
  simp [Halted, curInstr, Cmd.compile, Cmd.length_compileAt]

end Exec

end Structured

end RAM

end Complexity
