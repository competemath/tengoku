import Tengoku.ImmermanVardi.Lax979537Proofs.NodeInput

namespace Lax979537Proofs.NodeTrace

open Turing PersistentStack NodeMachine TimedNodes

variable {K Λ State Initial : Type} {Γ : K → Type} [DecidableEq K]

/-- Proof-side context for a represented initial configuration. The actual
input construction in NodeInput supplies every field. -/
structure Context (Γ : K → Type) (Λ State Initial : Type) where
  program : Λ → TM2.Stmt Γ Λ State
  heap : Records (Node Initial) Γ
  config : NodeMachine.Cfg Γ Λ State (Node Initial)
  raw : TM2Micro.Cfg Γ Λ State
  functional : Functional heap
  bounded : Bounded heap 0
  represents : Matches heap config raw

variable (C : Context Γ Λ State Initial)

noncomputable def snapshot (t : Nat) : Records (Node Initial) Γ × NodeMachine.Cfg Γ Λ State (Node Initial) :=
  let h := run_exists C.program C.heap C.config C.functional C.bounded C.raw C.represents t
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

/--
@isnad1 id=run.0h7v.s6.9b1ea2cefd98 from=translated src=- shape=c2d4ce4c vocab=4f2c67c3
-/
theorem snapshot_run (t : Nat) : Run C.program C.heap C.config t (snapshot C t).1 (snapshot C t).2 :=
  Classical.choose_spec (Classical.choose_spec (run_exists C.program C.heap C.config
    C.functional C.bounded C.raw C.represents t))

/--
@isnad1 id=eq.0h6v.s6.0e15ff7a8c75 from=translated src=- shape=a452022b vocab=59e4c123
-/
theorem snapshot_zero : snapshot C 0 = (C.heap, C.config) := by
  obtain ⟨hh, hc⟩ := run_unique C.functional C.bounded C.raw C.represents (snapshot_run C 0) Run.zero
  exact Prod.ext hh hc

/--
@isnad1 id=and.0h7v.s7.86fa5230e50c from=translated src=- shape=7e908c40 vocab=b05e2adb
-/
theorem snapshot_sound (t : Nat) : Functional (snapshot C t).1 ∧ Bounded (snapshot C t).1 t ∧
    Matches (snapshot C t).1 (snapshot C t).2 ((TM2Micro.next C.program)^[t] C.raw) :=
  run_sound (snapshot_run C t) C.functional C.bounded C.raw C.represents

/--
@isnad1 id=step.0h7v.s7.c48c069b6f5b from=translated src=- shape=19faf308 vocab=0d057645
-/
theorem snapshot_step (t : Nat) : Step C.program (.inr t) (snapshot C t).1 (snapshot C t).2
    (snapshot C (t + 1)).1 (snapshot C (t + 1)).2 := by
  obtain ⟨H, c, hs⟩ := step_exists C.program (.inr t) (snapshot C t).1 (snapshot C t).2
    ((TM2Micro.next C.program)^[t] C.raw).stk (snapshot_sound C t).2.2.2.2
  have hr := Run.succ (snapshot_run C t) hs
  obtain ⟨hh, hc⟩ := run_unique C.functional C.bounded C.raw C.represents hr (snapshot_run C (t + 1))
  simpa only [hh, hc] using hs

def input (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) (ids : Fin xs.length → Initial)
    (hi : Function.Injective ids) : Context tm.Γ tm.Λ tm.σ Initial :=
  ⟨tm.m, NodeInput.heap tm xs ids, NodeInput.config tm xs ids, TM2Micro.boundary (initList tm xs),
    NodeInput.heap_functional tm xs ids hi, NodeInput.heap_bounded tm xs ids, NodeInput.config_matches tm xs ids⟩

end Lax979537Proofs.NodeTrace
