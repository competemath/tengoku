/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Circuits.BarringtonCompiler.Defs
public import Tengoku.Complexitylib.Complexitylib.Circuits.BarringtonCompiler.Internal

/-!
# An executable Barrington compiler

This module turns the finite Barrington theorem into an explicit recursive
compiler. Earlier existence proofs selected `S₅` conjugators in `Prop`; here,
`allPermutationsFin` gives a computable enumeration and `firstConjugator5`
performs a deterministic finite search. The resulting `barringtonCompile`
contains no choice operation.

For every Boolean formula and target `5`-cycle, the compiler returns a width-`5`
permutation branching program with exact representation semantics and the
textbook length bound `4 ^ depth`. The remaining work for a fully uniform
Barrington theorem is therefore serialization and a resource-bounded generator
proof, not extraction of program data from an existential theorem.

## Main results

- `Complexity.firstConjugator5_spec` -- correctness of finite conjugator search.
- `Complexity.barrington_commutator` -- the searched factors decompose every
  target `5`-cycle.
- `Complexity.barringtonCompile_computes` -- exact compiler semantics.
- `Complexity.barringtonCompile_length_le` -- length at most `4 ^ depth`.
- `Complexity.barringtonCompile_var_bound` -- no new queried variables.
- `Complexity.barringtonCompile_representation` -- constructive finite
  Barrington theorem for the fixed canonical target cycle.
-/

public section

open scoped commutatorElement
open Equiv

namespace Complexity

/-- `allPermutationsFin n` contains every permutation of `Fin n`.
@isnad1 id=mem.0h2v.s4.71b9c596211e from=translated src=- shape=b27609e9 vocab=0c1b5fde
-/
theorem mem_allPermutationsFin {n : ℕ} (permutation : Perm (Fin n)) :
    permutation ∈ allPermutationsFin n :=
  mem_allPermutationsFin_internal permutation

/-- If two permutations are conjugate, the executable finite search returns a
valid conjugator.
@isnad1 id=eq.1h2v.s7.fe12c9b8fda4 from=translated src=- shape=2623e28a vocab=d03560c2
-/
theorem firstConjugator5_spec
    (source target : Perm (Fin 5))
    (hexists : ∃ g, g * source * g⁻¹ = target) :
    firstConjugator5 source target * source *
      (firstConjugator5 source target)⁻¹ = target :=
  firstConjugator5_spec_internal source target hexists

/-- The fixed left base permutation is a `5`-cycle.
@isnad1 id=and.0h0v.s5.c3f258801483 from=translated src=- shape=50ab1c8d vocab=9a813ba0
-/
theorem barringtonLeftBase_spec :
    barringtonLeftBase.IsCycle ∧ orderOf barringtonLeftBase = 5 :=
  barringtonLeftBase_spec_internal

/-- The fixed right base permutation is a `5`-cycle.
@isnad1 id=and.0h0v.s5.a68e13a27a97 from=translated src=- shape=50ab1c8d vocab=2e6c6683
-/
theorem barringtonRightBase_spec :
    barringtonRightBase.IsCycle ∧ orderOf barringtonRightBase = 5 :=
  barringtonRightBase_spec_internal

/-- The fixed commutator target is a `5`-cycle.
@isnad1 id=and.0h0v.s5.6374950ee708 from=translated src=- shape=50ab1c8d vocab=a18394a4
-/
theorem barringtonTargetBase_spec :
    barringtonTargetBase.IsCycle ∧ orderOf barringtonTargetBase = 5 :=
  barringtonTargetBase_spec_internal

/-- The canonical left factor is a `5`-cycle for every target value.
@isnad1 id=and.0h1v.s5.331086591f87 from=translated src=- shape=a2cd76f2 vocab=ab6e54f6
-/
theorem barringtonLeft_spec (target : Perm (Fin 5)) :
    (barringtonLeft target).IsCycle ∧
      orderOf (barringtonLeft target) = 5 :=
  barringtonLeft_spec_internal target

/-- The canonical right factor is a `5`-cycle for every target value.
@isnad1 id=and.0h1v.s5.30e15a885aa7 from=translated src=- shape=a2cd76f2 vocab=fc0f87cb
-/
theorem barringtonRight_spec (target : Perm (Fin 5)) :
    (barringtonRight target).IsCycle ∧
      orderOf (barringtonRight target) = 5 :=
  barringtonRight_spec_internal target

/-- The executable factors have commutator equal to any target `5`-cycle.
@isnad1 id=eq.2h1v.s6.c896ccf6162e from=translated src=- shape=2857600d vocab=0f091dc4
-/
theorem barrington_commutator
    (target : Perm (Fin 5)) (hcycle : target.IsCycle)
    (horder : orderOf target = 5) :
    ⁅barringtonLeft target, barringtonRight target⁆ = target :=
  barrington_commutator_internal target hcycle horder

namespace BP

/-- The four-block commutator program has exactly twice the sum of the source
lengths.
@isnad1 id=eq.0h3v.s5.dc9e98f9905e from=translated src=- shape=03b14e31 vocab=609d7d9f
-/
theorem length_commutatorProgram {w : ℕ} (p q : BP w) :
    (BP.commutatorProgram p q).length =
      2 * p.length + 2 * q.length :=
  BP.length_commutatorProgram_internal p q

end BP

/-- The executable compiler represents a formula through any target `5`-cycle.
@isnad1 id=computes.2h2v.s6.5087278df96c from=translated src=- shape=ccab4570 vocab=f7841f36
-/
theorem barringtonCompile_computes (formula : BoolFormula)
    (target : Perm (Fin 5)) (hcycle : target.IsCycle)
    (horder : orderOf target = 5) :
    BP.Computes target (barringtonCompile formula target)
      (fun assignment => BoolFormula.eval assignment formula) :=
  barringtonCompile_computes_internal formula target hcycle horder

/-- The executable compiler satisfies the textbook `4 ^ depth` length bound.
@isnad1 id=le.0h2v.s5.1fd22b7adfc3 from=translated src=- shape=e611e218 vocab=78d541bc
-/
theorem barringtonCompile_length_le
    (formula : BoolFormula) (target : Perm (Fin 5)) :
    (barringtonCompile formula target).length ≤ 4 ^ formula.depth :=
  barringtonCompile_length_le_internal formula target

/-- The executable compiler reads no formula-external variable: any bound on
the source formula's variable indices bounds every emitted instruction.
Constant instructions use variable zero, so the bound is stated for a natural
upper bound rather than as a literal subset of `formula.vars`.
@isnad1 id=le.2h4v.s6.a818936b0107 from=translated src=- shape=3860d8d2 vocab=d12f0562
-/
theorem barringtonCompile_var_bound
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) (bound : ℕ)
    (hvars : ∀ index ∈ formula.vars, index ≤ bound) :
    ∀ instruction ∈ barringtonCompile formula target,
      instruction.var ≤ bound :=
  barringtonCompile_var_bound_internal formula target bound hvars

/-- The canonical target cycle is nonidentity.
@isnad1 id=ne.0h0v.s5.974ff7b9520c from=translated src=- shape=d8fb023c vocab=ef891966
-/
theorem barringtonTargetBase_ne_one : barringtonTargetBase ≠ 1 := by
  intro heq
  have horder := barringtonTargetBase_spec.2
  rw [heq] at horder
  simp at horder

/-- **Constructive finite Barrington theorem.** The explicit compiled program
evaluates to the fixed target `barringtonTargetBase` exactly when the formula is
true (and to the identity otherwise), the target is not the identity, and the
program's length is at most `4 ^ depth`. That the target is a `5`-cycle is the
separate theorem `barringtonTargetBase_spec`; this statement records only that
it is nonidentity.
@isnad1 id=and.0h1v.s7.042e2904ad66 from=translated src=- shape=e8b6c6b6 vocab=aeeaedf7
-/
theorem barringtonCompile_representation (formula : BoolFormula) :
    barringtonTargetBase ≠ 1 ∧
      (∀ assignment,
        BP.eval assignment
          (barringtonCompile formula barringtonTargetBase) =
            if BoolFormula.eval assignment formula then
              barringtonTargetBase else 1) ∧
      (barringtonCompile formula barringtonTargetBase).length ≤
        4 ^ formula.depth :=
  ⟨barringtonTargetBase_ne_one,
    barringtonCompile_computes formula barringtonTargetBase
      barringtonTargetBase_spec.1 barringtonTargetBase_spec.2,
    barringtonCompile_length_le formula barringtonTargetBase⟩

end Complexity
