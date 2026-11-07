/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Tengoku.Cslib.Cslib.Foundations.Semantics.LTS.Basic
public import Tengoku.Cslib.Cslib.Foundations.Semantics.LTS.Simulation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Trace Equivalence

Definitions and results on trace equivalence for `LTS`s.

## Main definitions

- `LTS.traces`: the set of traces of a state.
- `TraceEq s₁ s₂`: `s₁` and `s₂` are trace equivalent, i.e., they have the same sets of traces.

## Notations

- `s₁ ~tr[lts] s₂`: the states `s₁` and `s₂` are trace equivalent in `lts`.

## Main statements

- `TraceEq.eqv`: trace equivalence is an equivalence relation (see `Equivalence`).
- `Deterministic.isSimulation_traceEq`: in any deterministic `LTS`, trace equivalence is a
  simulation.

-/

@[expose] public section

namespace Cslib.LTS

open Deterministic

/-- If `s₁` is simulated by `s₂` all of `s₁`'s traces are also traces of `s₂`.
@isnad1 id=le.1h9v.s5.9873f8a858b6 from=translated src=- shape=2ea193ff vocab=c5ca38db
-/
theorem IsSimulation.traces_subset (hr : IsSimulation lts₁ lts₂ r) (hrel : r s₁ s₂) :
    lts₁.traces s₁ ⊆ lts₂.traces s₂ := by
  intro μs ⟨s₁', h₁⟩
  obtain ⟨s₂', h₂, _⟩ := hr.sim_trace hrel μs s₁' h₁
  exact ⟨s₂', h₂⟩

/-- Two states are trace equivalent if they have the same set of traces.-/
def TraceEq (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (s₁ : State₁) (s₂ : State₂) :=
  lts₁.traces s₁ = lts₂.traces s₂

/--
Notation for trace equivalence.

Differently from standard pen-and-paper presentations, we require the LTSs to be mentioned
explicitly.-/
scoped notation s " ~tr[" lts₁ "," lts₂ "] " s' => TraceEq lts₁ lts₂ s s'

/-- Homogeneous trace equivalence compares states on the same LTS.-/
abbrev HomTraceEq (lts : LTS State Label) := TraceEq lts lts

/-- Notation for homogeneous trace equivalence.-/
scoped notation s:max " ~tr[" lts "] " s':max => HomTraceEq lts s s'

/-- Homogeneous trace equivalence is reflexive.
@isnad1 id=homtrace.0h4v.s4.f290c7e6f3ed from=translated src=- shape=1afcdb06 vocab=edb3abe5
-/
@[refl] theorem HomTraceEq.refl (s : State) : s ~tr[lts] s := rfl

/--
@isnad1 id=eq.0h5v.s5.d90e291f9c36 from=translated src=- shape=47b0d6d4 vocab=e45b2455
-/
@[simp] theorem TraceEq.flip_eq : flip (TraceEq lts₁ lts₂) = TraceEq lts₂ lts₁ := by
  grind [flip, TraceEq]

/-- Trace equivalence is symmetric.
@isnad1 id=traceeq.1h7v.s5.d4497427323f from=translated src=- shape=c08f4d15 vocab=e636d1da
-/
theorem TraceEq.symm (h : s₁ ~tr[lts₁,lts₂] s₂) : s₂ ~tr[lts₂,lts₁] s₁ := by
  rwa [←flip_eq]

/-- Trace equivalence is transitive.
@isnad1 id=traceeq.2h10v.s5.74e05949e94b from=translated src=- shape=416464f7 vocab=e636d1da
-/
theorem TraceEq.trans (h1 : s₁ ~tr[lts₁,lts₂] s₂) (h2 : s₂ ~tr[lts₂,lts₃] s₃) :
    s₁ ~tr[lts₁,lts₃] s₃ := Eq.trans h1 h2

/-- Homogeneous trace equivalence is an equivalence relation.
@isnad1 id=equivale.0h3v.s4.987576f8d000 from=translated src=- shape=53376e9b vocab=1f29e476
-/
theorem HomTraceEq.eqv : Equivalence (· ~tr[lts] ·) where
  refl := HomTraceEq.refl
  symm := TraceEq.symm
  trans := TraceEq.trans

/-- `calc` support for simulation equivalence.-/
instance : Trans (TraceEq lts₁ lts₂) (TraceEq lts₂ lts₃) (TraceEq lts₁ lts₃) where
  trans := TraceEq.trans

/-- For trace-equivalent states, any multistep transition of one can be mimicked by the other.
@isnad1 id=ex.2h9v.s5.00c649a8783a from=translated src=- shape=6582ca38 vocab=bf6e8af9
-/
theorem TraceEq.exists_mTr_of_mTr {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (h : s₁ ~tr[lts₁,lts₂] s₂) (htr : lts₁.MTr s₁ μs s₁') : ∃ s₂', lts₂.MTr s₂ μs s₂' := by
  rw [←mem_traces_iff, ←h]
  exact ⟨s₁', htr⟩

/-- For trace-equivalent states, any single-step transition of one can be mimicked by the other.
@isnad1 id=ex.2h9v.s5.e1e1a5449d74 from=translated src=- shape=a92abbbf vocab=b42bafdd
-/
theorem TraceEq.exists_tr_of_tr {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (h : s₁ ~tr[lts₁,lts₂] s₂) (htr : lts₁.Tr s₁ μ s₁') : ∃ s₂', lts₂.Tr s₂ μ s₂' := by
  rw [←mem_traces_singleton_iff, ←h, mem_traces_singleton_iff]
  exact ⟨s₁', htr⟩

/-- For deterministic lts's, trace equivalence is preserved by respective transitions with the same
label.
@isnad1 id=traceeq.3h10v.s6.30928621b2e5 from=translated src=- shape=9f5945d4 vocab=2865d013
-/
theorem TraceEq.traceEq_of_tr_of_tr {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [hdet₁ : lts₁.Deterministic] [hdet₂ : lts₂.Deterministic] (h : s₁ ~tr[lts₁,lts₂] s₂)
    (htr₁ : lts₁.Tr s₁ μ s₁') (htr₂ : lts₂.Tr s₂ μ s₂') : s₁' ~tr[lts₁,lts₂] s₂' := by
  rw [TraceEq] at h
  simp_rw [TraceEq, Deterministic.traces_of_tr htr₁, Deterministic.traces_of_tr htr₂, h]

/-- In deterministic LTSs, trace equivalence is a simulation.
@isnad1 id=issimula.0h5v.s5.c0ac5b1cc739 from=translated src=- shape=0751895a vocab=b5e10e76
-/
theorem Deterministic.isSimulation_traceEq {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [hdet₁ : lts₁.Deterministic] [hdet₂ : lts₂.Deterministic] :
    IsSimulation lts₁ lts₂ (TraceEq lts₁ lts₂) := by
  intro s₁ s₂ h μ s₁' htr1
  obtain ⟨s₂', htr2⟩ := h.exists_tr_of_tr htr1
  use s₂', htr2, h.traceEq_of_tr_of_tr htr1 htr2

/-- Simulation equivalence implies trace equivalence.
@isnad1 id=traceeq.1h7v.s5.b4eb6f0bbe6b from=translated src=- shape=fff59a41 vocab=4a51557c
-/
theorem SimulationEquiv.traceEq (h : s₁ ≤≥[lts₁,lts₂] s₂) : s₁ ~tr[lts₁,lts₂] s₂ := by
  obtain ⟨⟨_, h, hr⟩, _, h', hr'⟩ := h
  exact (hr.traces_subset h).antisymm (hr'.traces_subset h')

/-- Simulation equivalence and trace equivalence are equivalence for detemrinistic lts's.
@isnad1 id=iff.0h7v.s5.42565b1e5cee from=translated src=- shape=ce60beb4 vocab=fabfc4c3
-/
theorem Deterministic.traceEq_iff_simulationEquiv {lts₁ : LTS State₁ Label}
    {lts₂ : LTS State₂ Label} [hdet₁ : lts₁.Deterministic] [hdet₂ : lts₂.Deterministic]
    (s₁ : State₁) (s₂ : State₂) : (s₁ ~tr[lts₁,lts₂] s₂) ↔ s₁ ≤≥[lts₁,lts₂] s₂ :=
  ⟨fun h =>
    ⟨⟨_, h, Deterministic.isSimulation_traceEq⟩, _, h.symm, Deterministic.isSimulation_traceEq⟩,
    SimulationEquiv.traceEq⟩

end Cslib.LTS
