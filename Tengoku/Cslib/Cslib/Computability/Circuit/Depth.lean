/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.Cslib.Cslib.Computability.Circuit.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Circuit depth bounds

This file proves bounds for `Program.depth`, defined in `Cslib.Computability.Circuit.Program`,
and `Circuit.depth`, defined in `Cslib.Computability.Circuit.Basic`. Program depth is the maximum
depth of its gates; circuit depth is the maximum depth of its designated outputs.
`Program.depth_le_iff` and `Circuit.depth_le_iff` express bounds in terms of the individual
gates and outputs. These characterizations give
`Circuit.depth_le_program_depth` and `Circuit.depth_le_size` without assumptions on the
signature's fan-in or its interpretation.

Constructor simplification lemmas preserve the depth of earlier wires when a gate is added.
Every gate, including a constant gate, contributes one level; selecting outputs contributes
none. A circuit with no outputs has depth zero, even when its program contains gates.
-/

@[expose] public section

namespace Cslib.Circuits

universe v
variable {σ : Signature.{v}} {n g m : Nat}

private theorem foldl_max_le_iff {n : Nat} (f : Fin n → Nat) (initial bound : Nat) :
    Fin.foldl n (fun acc i => max acc (f i)) initial ≤ bound ↔
      initial ≤ bound ∧ ∀ i, f i ≤ bound := by
  induction n generalizing initial with
  | zero => simp
  | succ n ih =>
      rw [Fin.foldl_succ, ih]
      simp [Fin.forall_fin_succ, and_assoc]

/-- Bounding every argument by `d` bounds the gate's depth by `d + 1`.
@isnad1 id=iff.0h6v.s5.d51575a855cb from=translated src=- shape=fdee666f vocab=bbeda513
-/
theorem Line.depth_le_add_one_iff (line : Line σ n g) (depths : Wire n g → Nat) {d : Nat} :
    line.depth depths ≤ d + 1 ↔ ∀ j, depths (line.wires j) ≤ d := by
  simp only [Line.depth, Nat.succ_le_succ_iff]
  simpa using foldl_max_le_iff (fun j => depths (line.wires j)) 0 d

/-- Every gate, including a constant gate, has positive depth.
@isnad1 id=lt.0h5v.s4.10fc5c7da142 from=translated src=- shape=12c3d991 vocab=e4fb3cdc
-/
theorem Line.depth_pos (line : Line σ n g) (depths : Wire n g → Nat) :
    0 < line.depth depths := Nat.zero_lt_succ _

/--
@isnad1 id=eq.0h5v.s5.4403b7c8417c from=translated src=- shape=b499a33c vocab=8aa7f00f
-/
@[simp] theorem Program.depths_gate_last (p : Program σ n g) (line : Line σ n g) :
    (p.gate line).depths (Fin.last g) = line.depth p.wireDepths := by
  simp [Program.depths, Program.wireDepths]

/--
@isnad1 id=eq.0h6v.s5.4c3b0e5da6f5 from=translated src=- shape=5f5651d4 vocab=4994887d
-/
@[simp] theorem Program.depths_gate_castSucc (p : Program σ n g) (line : Line σ n g)
    (j : Fin g) : (p.gate line).depths j.castSucc = p.depths j := by
  simp [Program.depths]

/--
@isnad1 id=eq.0h5v.s4.c6a61b89aa2d from=translated src=- shape=1a39a476 vocab=65b77771
-/
@[simp] theorem Program.wireDepths_input (p : Program σ n g) (i : Fin n) :
    p.wireDepths (.input i) = 0 := rfl

/--
@isnad1 id=eq.0h5v.s4.b52bdebf919e from=translated src=- shape=62fc4b24 vocab=34e3174a
-/
@[simp] theorem Program.wireDepths_gateWire (p : Program σ n g) (j : Fin g) :
    p.wireDepths (.gate j) = p.depths j := rfl

/--
@isnad1 id=eq.0h6v.s5.cbc888058555 from=translated src=- shape=179f53ef vocab=c0675655
-/
@[simp] theorem Program.wireDepths_gate_castSucc (p : Program σ n g) (line : Line σ n g)
    (w : Wire n g) : (p.gate line).wireDepths w.castSucc = p.wireDepths w := by
  cases w <;> simp

/--
@isnad1 id=eq.0h2v.s4.197df22eab27 from=translated src=- shape=663718d7 vocab=2e3db94a
-/
@[simp] theorem Program.depth_empty : (Program.empty : Program σ n 0).depth = 0 := rfl

/--
@isnad1 id=eq.0h5v.s5.c6eb599a0a80 from=translated src=- shape=548adf89 vocab=042eecd3
-/
@[simp] theorem Program.depth_gate (p : Program σ n g) (line : Line σ n g) :
    (p.gate line).depth = max p.depth (line.depth p.wireDepths) := by
  simp [Program.depth, Fin.foldl_succ_last]

/-- Program depth is bounded by `d` exactly when every gate depth is bounded by `d`.
@isnad1 id=iff.0h5v.s5.4f8731e61f95 from=translated src=- shape=c32243f3 vocab=ed91a272
-/
theorem Program.depth_le_iff (p : Program σ n g) {d : Nat} :
    p.depth ≤ d ↔ ∀ j, p.depths j ≤ d := by
  simpa [Program.depth] using foldl_max_le_iff p.depths 0 d

/-- Every gate depth is at most the depth of the program.
@isnad1 id=le.0h5v.s4.a881856d57cf from=translated src=- shape=b3196d0b vocab=ed91a272
-/
theorem Program.depths_le_depth (p : Program σ n g) (j : Fin g) : p.depths j ≤ p.depth :=
  p.depth_le_iff.mp le_rfl j

/-- Every input or gate wire has depth at most the depth of the program.
@isnad1 id=le.0h5v.s4.92a8d1902cbb from=translated src=- shape=c9c6f6ba vocab=e08ca61a
-/
theorem Program.wireDepths_le_depth (p : Program σ n g) (w : Wire n g) :
    p.wireDepths w ≤ p.depth := by
  cases w with
  | input i => exact Nat.zero_le _
  | gate j => exact p.depths_le_depth j

/-- A program's depth is at most its number of gates.
@isnad1 id=le.0h4v.s4.355c2156d132 from=translated src=- shape=08d69f40 vocab=cba2534b
-/
theorem Program.depth_le_gateCount (p : Program σ n g) : p.depth ≤ g := by
  induction p with
  | empty => exact le_rfl
  | gate p line ih =>
      rw [depth_gate, max_le_iff]
      exact ⟨Nat.le_succ_of_le ih, (line.depth_le_add_one_iff p.wireDepths).mpr
        (fun j => (p.wireDepths_le_depth (line.wires j)).trans ih)⟩

/-- Circuit depth is bounded by `d` exactly when every designated output depth is bounded by `d`.
@isnad1 id=iff.0h5v.s5.3a05dd78a42b from=translated src=- shape=c32243f3 vocab=91139358
-/
theorem Circuit.depth_le_iff (c : Circuit σ n m) {d : Nat} :
    c.depth ≤ d ↔ ∀ j, c.outputDepths j ≤ d := by
  simpa [Circuit.depth] using foldl_max_le_iff c.outputDepths 0 d

/-- Every designated output has depth at most the circuit depth.
@isnad1 id=le.0h5v.s4.4f46cfcf2583 from=translated src=- shape=b3196d0b vocab=91139358
-/
theorem Circuit.outputDepths_le_depth (c : Circuit σ n m) (j : Fin m) :
    c.outputDepths j ≤ c.depth := c.depth_le_iff.mp le_rfl j

/-- Selecting outputs cannot increase the maximum depth over all program gates.
@isnad1 id=le.0h4v.s5.470dc4b54e1e from=translated src=- shape=7d4c6cf2 vocab=ab149b86
-/
theorem Circuit.depth_le_program_depth (c : Circuit σ n m) : c.depth ≤ c.program.depth :=
  c.depth_le_iff.mpr fun j => c.program.wireDepths_le_depth (c.outputs j)

/-- Circuit depth is at most the number of gates.
@isnad1 id=le.0h4v.s4.6d09a60b88a3 from=translated src=- shape=6621c849 vocab=ad7cd5bd
-/
theorem Circuit.depth_le_size (c : Circuit σ n m) : c.depth ≤ c.size :=
  c.depth_le_program_depth.trans c.program.depth_le_gateCount

/--
@isnad1 id=eq.0h3v.s4.c7d25a57bbe0 from=translated src=- shape=cff47da5 vocab=bdc39532
-/
@[simp] theorem Circuit.depth_zero_outputs (c : Circuit σ n 0) : c.depth = 0 := rfl

end Cslib.Circuits
