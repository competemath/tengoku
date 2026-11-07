/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.Cslib.Cslib.Computability.Circuit.Homomorphism
public import Tengoku.Cslib.Cslib.Computability.Circuit.Wire

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Straight-line programs

A program is a topologically ordered sequence of gates. Each `Line` records an
operation and its argument wires. The gate-count index ensures that wires refer
only to original inputs or earlier gates.

This file defines

* lines, their evaluation and depth, and `Line.mapWires` together with the
  transport lemmas `Line.eval_mapWires` and `Line.eval_mapRenaming`;
* programs, their evaluation `Program.eval`, the input-and-gate valuation
  `Program.trace`, gate depths, and the bounded-fan-in predicate
  `Program.FanInAtMost`;
* the scalar views `Program.gateFunction` and `Program.wireFunction`, and the
  widened line collection `Program.lines` with `Program.lines_eval`.

Evaluation of lines and programs commutes with homomorphisms
(`Line.map_eval`, `Program.map_eval`, `Program.map_trace`).
-/

@[expose] public section

namespace Cslib.Circuits

universe v u u₁ u₂

variable {σ : Signature.{v}} {inputCount gateCount : Nat}
variable {sourceInputCount targetInputCount sourceGateCount targetGateCount : Nat}
variable {U : Type u} {U₁ : Type u₁} {U₂ : Type u₂}

/-- One gate together with the wires supplying its arguments.-/
structure Line (σ : Signature) (inputCount gateCount : Nat) where
  /-- The operation performed by the gate.-/
  op : σ.Op
  /-- The wire supplying each argument of the operation.-/
  wires : Fin (σ.Arity op) → Wire inputCount gateCount

/-- A line is an operation symbol together with a tuple of argument wires.-/
def Line.equiv (σ : Signature) (inputCount gateCount : Nat) :
    Line σ inputCount gateCount ≃ Σ op : σ.Op, Fin (σ.Arity op) → Wire inputCount gateCount where
  toFun line := ⟨line.op, line.wires⟩
  invFun line := ⟨line.1, line.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Apply a function to every wire read by a line.-/
def Line.mapWires
    (line : Line σ sourceInputCount sourceGateCount)
    (wireMap : Wire sourceInputCount sourceGateCount → Wire targetInputCount targetGateCount) :
    Line σ targetInputCount targetGateCount where
  op := line.op
  wires := wireMap ∘ line.wires

/--
@isnad1 id=eq.0h7v.s5.08e63d41caab from=translated src=- shape=251049f2 vocab=6ee8ff4a
-/
@[simp] theorem Line.mapWires_op
    (line : Line σ sourceInputCount sourceGateCount)
    (wireMap : Wire sourceInputCount sourceGateCount → Wire targetInputCount targetGateCount) :
    (line.mapWires wireMap).op = line.op := rfl

/--
@isnad1 id=eq.0h8v.s5.338b6854d150 from=translated src=- shape=38af6fd0 vocab=b4b60828
-/
@[simp] theorem Line.mapWires_wires
    (line : Line σ sourceInputCount sourceGateCount)
    (wireMap : Wire sourceInputCount sourceGateCount → Wire targetInputCount targetGateCount)
    (argument : Fin (σ.Arity line.op)) :
    (line.mapWires wireMap).wires argument = wireMap (line.wires argument) := rfl

/-- A topologically ordered straight-line program, indexed by its gate count.-/
inductive Program (σ : Signature.{v}) (inputCount : Nat) : Nat → Type v where
  | empty : Program σ inputCount 0
  | gate {gateCount : Nat} :
      Program σ inputCount gateCount → Line σ inputCount gateCount →
        Program σ inputCount (gateCount + 1)

/-- The empty program is the only program with no gates.-/
def Program.emptyEquiv (σ : Signature) (inputCount : Nat) : Program σ inputCount 0 ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := .empty
  left_inv p := by cases p; rfl
  right_inv x := by cases x; rfl

/-- A nonempty program is a prefix followed by its last gate.-/
def Program.gateEquiv (σ : Signature) (inputCount gateCount : Nat) :
    Program σ inputCount (gateCount + 1) ≃
      Program σ inputCount gateCount × Line σ inputCount gateCount where
  toFun | .gate p line => (p, line)
  invFun p := p.1.gate p.2
  left_inv p := by cases p; rfl
  right_inv _ := rfl

/-- Every gate in a program has at most `r` arguments.-/
def Program.FanInAtMost {gateCount : Nat} : (program : Program σ inputCount gateCount) → Nat → Prop
  | .empty, _ => True
  | .gate program line, r =>
      program.FanInAtMost r ∧ σ.Arity line.op ≤ r

/-- Bounded fan-in is decidable for every concrete program.-/
instance Program.instDecidableFanInAtMost {gateCount : Nat}
    (program : Program σ inputCount gateCount)
    (r : Nat) : Decidable (program.FanInAtMost r) :=
  match program with
  | .empty => isTrue trivial
  | .gate prior line =>
      @instDecidableAnd (prior.FanInAtMost r)
        (σ.Arity line.op ≤ r)
        (Program.instDecidableFanInAtMost prior r) inferInstance

/-- Evaluate a line from the values of the inputs and preceding gates.-/
def Line.eval
    (line : Line σ inputCount gateCount)
    (i : Interpretation σ U)
    (inputs : Fin inputCount → U)
    (gates : Fin gateCount → U) : U :=
  i line.op (Wire.elim inputs gates ∘ line.wires)

/-- Mapping a line's wires preserves evaluation when the new valuation agrees
with the old valuation along the map. The source and target input namespaces
may differ.
@isnad1 id=eq.1h13v.s6.f9b3a66ddbd8 from=translated src=- shape=8174e4de vocab=bbfdf046
-/
theorem Line.eval_mapWires
    (line : Line σ sourceInputCount sourceGateCount)
    (wireMap : Wire sourceInputCount sourceGateCount → Wire targetInputCount targetGateCount)
    (interpretation : Interpretation σ U)
    (oldInputs : Fin sourceInputCount → U)
    (newInputs : Fin targetInputCount → U)
    (oldGates : Fin sourceGateCount → U)
    (newGates : Fin targetGateCount → U)
    (preserves : ∀ wire,
      Wire.elim newInputs newGates (wireMap wire) = Wire.elim oldInputs oldGates wire) :
    (line.mapWires wireMap).eval interpretation newInputs newGates =
      line.eval interpretation oldInputs oldGates := by
  unfold Line.mapWires Line.eval
  congr 1
  funext argument
  simp only [Function.comp_apply]
  exact preserves (line.wires argument)

/-- Specialization of `Line.eval_mapWires` to an input-fixing wire renaming.
@isnad1 id=eq.1h11v.s6.673e4cf1522d from=translated src=- shape=576fdd62 vocab=7da5bf54
-/
theorem Line.eval_mapRenaming
    (line : Line σ inputCount sourceGateCount)
    (ρ : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (interpretation : Interpretation σ U)
    (inputs : Fin inputCount → U)
    (oldGates : Fin sourceGateCount → U)
    (newGates : Fin targetGateCount → U)
    (preservesGates : ∀ gate, Wire.elim inputs newGates (ρ.gates gate) = oldGates gate) :
    (line.mapWires ρ).eval interpretation inputs newGates =
      line.eval interpretation inputs oldGates := by
  apply Line.eval_mapWires
  exact ρ.value_apply inputs oldGates newGates preservesGates

/-- The depth of a line, given the depth of every wire it may read.-/
def Line.depth
    (line : Line σ inputCount gateCount)
    (wireDepths : Wire inputCount gateCount → Nat) : Nat :=
  Nat.succ <| Fin.foldl (σ.Arity line.op)
    (fun depth k => max depth (wireDepths (line.wires k))) 0

/-- Evaluating a line commutes with a homomorphism.
@isnad1 id=eq.0h11v.s6.75f648bea5db from=translated src=- shape=221c74fb vocab=428f1854
-/
theorem Line.map_eval
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    (line : Line σ inputCount gateCount)
    (h : Homomorphism i₁ i₂)
    (inputs : Fin inputCount → U₁)
    (gates : Fin gateCount → U₁) :
    h.map (line.eval i₁ inputs gates) =
      line.eval i₂ (h.map ∘ inputs) (h.map ∘ gates) := by
  rw [Line.eval, Line.eval, h.homomorphic]
  congr 1
  funext k
  simp only [Function.comp_apply]
  cases line.wires k <;> rfl

/-- Evaluate every gate in a program, in program order.-/
def Program.eval {gateCount : Nat}
    (p : Program σ inputCount gateCount)
    (i : Interpretation σ U)
    (x : Fin inputCount → U) : Fin gateCount → U :=
  match p with
  | .empty => Fin.elim0
  | .gate p line =>
      let prior := p.eval i x
      Fin.lastCases (line.eval i x prior) prior

/--
@isnad1 id=eq.0h8v.s6.d9317927b942 from=translated src=- shape=53706b08 vocab=31a0aaee
-/
@[simp] theorem Program.eval_gate_last
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U) :
    (program.gate line).eval interpretation input (Fin.last gateCount) =
      line.eval interpretation input (program.eval interpretation input) := by
  simp [Program.eval]

/--
@isnad1 id=eq.0h9v.s6.cf8918086153 from=translated src=- shape=2a65c9a0 vocab=0c2e503b
-/
@[simp] theorem Program.eval_gate_castSucc
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U)
    (gate : Fin gateCount) :
    (program.gate line).eval interpretation input gate.castSucc =
      program.eval interpretation input gate := by
  simp [Program.eval]

/-- The depth of every gate in a program. Inputs have implicit depth zero.-/
def Program.depths {gateCount : Nat} (p : Program σ inputCount gateCount) : Fin gateCount → Nat :=
  match p with
  | .empty => Fin.elim0
  | .gate p line =>
      let prior := p.depths
      let wireDepths := Wire.elim (fun _ => 0) prior
      Fin.lastCases (line.depth wireDepths) prior

/-- The depth of every input or gate wire in a program.-/
def Program.wireDepths (p : Program σ inputCount gateCount) : Wire inputCount gateCount → Nat :=
  Wire.elim (fun _ => 0) p.depths

/-- The maximum depth of any gate in a program.-/
def Program.depth (p : Program σ inputCount gateCount) : Nat :=
  Fin.foldl gateCount (fun depth k => max depth (p.depths k)) 0

/-- Evaluating a program commutes with a homomorphism.
@isnad1 id=eq.0h10v.s6.901048cb0d07 from=translated src=- shape=aee7511e vocab=32fa8a5c
-/
theorem Program.map_eval
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    (p : Program σ inputCount gateCount)
    (h : Homomorphism i₁ i₂)
    (x : Fin inputCount → U₁) :
    h.map ∘ p.eval i₁ x = p.eval i₂ (h.map ∘ x) := by
  induction p with
  | empty =>
      funext k
      exact Fin.elim0 k
  | gate p line ih =>
      funext k
      refine Fin.lastCases ?_ ?_ k
      · simpa only [Program.eval, Function.comp_apply, Fin.lastCases_last, ih] using
          line.map_eval h x (p.eval i₁ x)
      · intro j
        simpa only [Program.eval, Function.comp_apply, Fin.lastCases_castSucc] using
          congrFun ih j

/-- The value of every input and gate wire.-/
def Program.trace
    (p : Program σ inputCount gateCount)
    (i : Interpretation σ U)
    (x : Fin inputCount → U) : Wire inputCount gateCount → U :=
  Wire.elim x (p.eval i x)

/--
@isnad1 id=eq.0h8v.s5.8656ba5f66ed from=translated src=- shape=2864b5eb vocab=5dc827d3
-/
@[simp] theorem Program.trace_input
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U)
    (sourceInput : Fin inputCount) :
    program.trace interpretation input (Wire.input sourceInput) =
      input sourceInput := rfl

/--
@isnad1 id=eq.0h9v.s6.e225b88d0638 from=translated src=- shape=176746f3 vocab=37d9931e
-/
@[simp] theorem Program.trace_gate_castSucc
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U)
    (wire : Wire inputCount gateCount) :
    (program.gate line).trace interpretation input wire.castSucc =
      program.trace interpretation input wire := by
  cases wire <;> simp [Program.trace]

/-- Evaluating every input and gate wire commutes with a homomorphism.
@isnad1 id=eq.0h10v.s6.9375b47dbab0 from=translated src=- shape=ad7fa973 vocab=27758a48
-/
theorem Program.map_trace
    {i₁ : Interpretation σ U₁}
    {i₂ : Interpretation σ U₂}
    (p : Program σ inputCount gateCount)
    (h : Homomorphism i₁ i₂)
    (x : Fin inputCount → U₁) :
    h.map ∘ p.trace i₁ x = p.trace i₂ (h.map ∘ x) := by
  funext wire
  cases wire with
  | input => rfl
  | gate gate => exact congrFun (p.map_eval h x) gate

/-- The scalar function computed by an internal gate.-/
def Program.gateFunction
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (gate : Fin gateCount)
    (input : Fin inputCount → U) : U :=
  program.eval interpretation input gate

/-- The scalar function carried by an input or internal-gate wire.-/
def Program.wireFunction
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (wire : Wire inputCount gateCount)
    (input : Fin inputCount → U) : U :=
  program.trace interpretation input wire

/--
@isnad1 id=eq.0h8v.s5.d6944a3a4bdf from=translated src=- shape=d5706c8a vocab=cbab4ce7
-/
@[simp] theorem Program.gateFunction_apply
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (gate : Fin gateCount)
    (input : Fin inputCount → U) :
    program.gateFunction interpretation gate input =
      program.eval interpretation input gate := rfl

/--
@isnad1 id=eq.0h7v.s5.4b067db4a56c from=translated src=- shape=c455f113 vocab=c42947b2
-/
@[simp] theorem Program.wireFunction_input
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (inputWire : Fin inputCount) :
    program.wireFunction interpretation (Wire.input inputWire) =
      fun input => input inputWire := rfl

/--
@isnad1 id=eq.0h7v.s5.0451e3b3fecd from=translated src=- shape=65e859b2 vocab=07ed3a1b
-/
@[simp] theorem Program.wireFunction_gate
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (gate : Fin gateCount) :
    program.wireFunction interpretation (Wire.gate gate) =
      program.gateFunction interpretation gate := rfl

/--
@isnad1 id=eq.0h7v.s6.ce5db548a1e7 from=translated src=- shape=47575bf2 vocab=ac1ca5ff
-/
@[simp] theorem Program.gateFunction_gate_last
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount)
    (interpretation : Interpretation σ U) :
    (program.gate line).gateFunction interpretation (Fin.last gateCount) =
      fun input => line.eval interpretation input
        (program.eval interpretation input) := by
  funext input
  exact Program.eval_gate_last program line interpretation input

/--
@isnad1 id=eq.0h8v.s6.52e8743bf37a from=translated src=- shape=0f935280 vocab=b0ad8eb7
-/
@[simp] theorem Program.gateFunction_gate_castSucc
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (gate : Fin gateCount) :
    (program.gate line).gateFunction interpretation gate.castSucc =
      program.gateFunction interpretation gate := by
  funext input
  exact Program.eval_gate_castSucc program line interpretation input gate

/--
@isnad1 id=eq.0h8v.s5.b2b0b863df85 from=translated src=- shape=80e03e8f vocab=e5f6bf7f
-/
@[simp] theorem Program.trace_gateWire
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U)
    (gate : Fin gateCount) :
    program.trace interpretation input (Wire.gate gate) =
      program.gateFunction interpretation gate input := rfl

/-- The program's lines, each widened to the final wire namespace.-/
def Program.lines {gateCount : Nat} :
    (program : Program σ inputCount gateCount) → Fin gateCount → Line σ inputCount gateCount
  | .empty => Fin.elim0
  | @Program.gate _ _ gateCount program line =>
      Fin.lastCases
        (line.mapWires Wire.Renaming.castSucc)
        (fun gate => (program.lines gate).mapWires Wire.Renaming.castSucc)

/--
@isnad1 id=eq.0h5v.s6.23f58d509a0f from=translated src=- shape=6a26ad8a vocab=3f44794f
-/
@[simp] theorem Program.lines_gate_last
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount) :
    (program.gate line).lines (Fin.last gateCount) =
      line.mapWires Wire.Renaming.castSucc := by
  simp [Program.lines]

/--
@isnad1 id=eq.0h6v.s6.f8ee33ebd48e from=translated src=- shape=04c72d91 vocab=1aa84fee
-/
@[simp] theorem Program.lines_gate_castSucc
    (program : Program σ inputCount gateCount)
    (line : Line σ inputCount gateCount)
    (gate : Fin gateCount) :
    (program.gate line).lines gate.castSucc =
      (program.lines gate).mapWires Wire.Renaming.castSucc := by
  simp [Program.lines]

/-- A widened line evaluates to the value of its corresponding program gate.
@isnad1 id=eq.0h8v.s5.fa5b98e09d10 from=translated src=- shape=019e9b2e vocab=90b0e45f
-/
theorem Program.lines_eval
    (program : Program σ inputCount gateCount)
    (interpretation : Interpretation σ U)
    (input : Fin inputCount → U)
    (gate : Fin gateCount) :
    (program.lines gate).eval interpretation input
        (program.eval interpretation input) =
      program.eval interpretation input gate := by
  induction program with
  | empty => exact Fin.elim0 gate
  | @gate gateCount program line ih =>
      have evalWidened (oldLine : Line σ inputCount gateCount) :
          (oldLine.mapWires Wire.Renaming.castSucc).eval interpretation input
              ((program.gate line).eval interpretation input) =
            oldLine.eval interpretation input
              (program.eval interpretation input) := by
        apply Line.eval_mapWires
        intro wire
        simpa only [Wire.Renaming.castSucc_apply, Program.trace] using
          Program.trace_gate_castSucc program line interpretation input wire
      refine Fin.lastCases ?_ (fun priorGate => ?_) gate
      · simpa only [Program.lines_gate_last, Program.eval_gate_last] using
          evalWidened line
      · simp only [Program.lines_gate_castSucc, Program.eval_gate_castSucc]
        exact (evalWidened (program.lines priorGate)).trans (ih priorGate)

/-- A valuation satisfying every gate equation is the program's evaluation.-/
theorem Program.eq_eval_of_forall_lines_eval
    (p : Program σ inputCount gateCount) (i : Interpretation σ U) (x : Fin inputCount → U)
    (values : Fin gateCount → U)
    (h : ∀ gate, (p.lines gate).eval i x values = values gate) :
    values = p.eval i x := by
  induction p with
  | empty => exact Subsingleton.elim _ _
  | @gate g p line ih =>
      have hmap (l : Line σ inputCount g) :
          (l.mapWires Wire.Renaming.castSucc).eval i x values =
            l.eval i x (values ∘ Fin.castSucc) := by
        apply Line.eval_mapWires
        intro w
        cases w <;> rfl
      have hp : values ∘ Fin.castSucc = p.eval i x :=
        ih _ (fun gate => by simpa [hmap] using h gate.castSucc)
      funext gate
      refine Fin.lastCases ?_ (fun gate => ?_) gate
      · simpa [hmap, hp] using (h (Fin.last g)).symm
      · simpa using congrFun hp gate

end Cslib.Circuits
