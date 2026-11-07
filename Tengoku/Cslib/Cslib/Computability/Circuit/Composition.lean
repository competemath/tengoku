/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Tengoku.Cslib.Cslib.Computability.Circuit.Basic
public import Tengoku.Seed.Data.Fin.Tuple.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Composing circuits

A program can be continued by a second program whose inputs are read from wires of the first.
Reading them from the outputs of a circuit gives sequential composition, `Circuit.comp`, which
evaluates to the composite of the two functions. Reading them from the original inputs gives
parallel composition on shared inputs, `Circuit.append`, whose outputs are those of the first
circuit followed by those of the second. In both cases the gate counts add.
-/

@[expose] public section

namespace Fin

variable {α : Type*} {m n : ℕ}

/--
@isnad1 id=eq.0h5v.s5.22f1a8dbbbe3 from=translated src=- shape=d5a0988f vocab=138966b7
-/
@[simp] theorem append_comp_castAdd (u : Fin m → α) (v : Fin n → α) :
    append u v ∘ castAdd n = u :=
  funext (append_left u v)

/--
@isnad1 id=eq.0h5v.s5.e3fd5d632aef from=translated src=- shape=35ad0cb5 vocab=f0685677
-/
@[simp] theorem append_comp_natAdd (u : Fin m → α) (v : Fin n → α) :
    append u v ∘ natAdd m = v :=
  funext (append_right u v)

end Fin

namespace Cslib.Circuits

universe v u

variable {σ : Signature.{v}} {U : Type u} {n m p k g₁ g₂ : ℕ}

namespace Program

/-- For programs `p : Program σ n g₁` and `q : Program σ k g₂`, with
`feed : Fin k → Wire n g₁`, map a wire of `q` to its wire in the combined program.
Inputs follow `feed`, and gate indices are shifted past the gates of `p`.
This is the wire map used by `Program.append` below.-/
def appendedWire (feed : Fin k → Wire n g₁) : Wire k g₂ → Wire n (g₁ + g₂)
  | .input i => (feed i).castAdd g₂
  | .gate j => .gate (Fin.natAdd g₁ j)

/--
@isnad1 id=eq.0h6v.s5.5df97b39e086 from=translated src=- shape=abf6a76c vocab=2fd42e1f
-/
@[simp] theorem appendedWire_input (feed : Fin k → Wire n g₁) (i : Fin k) :
    appendedWire (g₂ := g₂) feed (Wire.input i) = (feed i).castAdd g₂ := rfl

/--
@isnad1 id=eq.0h6v.s5.aa0cb11564a5 from=translated src=- shape=c70181b2 vocab=4ca2fd8b
-/
@[simp] theorem appendedWire_gate (feed : Fin k → Wire n g₁) (j : Fin g₂) :
    appendedWire feed (Wire.gate j) = Wire.gate (Fin.natAdd g₁ j) := rfl

/-- Continue `p` by `q`, reading the inputs of `q` from the wires `feed` of `p`.-/
def append (p : Program σ n g₁) (feed : Fin k → Wire n g₁)
    {g₂ : ℕ} (q : Program σ k g₂) : Program σ n (g₁ + g₂) :=
  match q with
  | .empty => p
  | .gate q line => .gate (p.append feed q) (line.mapWires (appendedWire feed))

variable (p : Program σ n g₁) (feed : Fin k → Wire n g₁) (I : Interpretation σ U)
  (x : Fin n → U)

/-- The wires of `p` keep their values after `p` is continued.
@isnad1 id=eq.0h12v.s6.933b7b7be69c from=translated src=- shape=2b8640ca vocab=1b5e2afd
-/
theorem trace_append_castAdd (q : Program σ k g₂) (w : Wire n g₁) :
    (p.append feed q).trace I x (w.castAdd g₂) = p.trace I x w := by
  induction q with
  | empty => cases w <;> rfl
  | gate q line ih => cases w <;> exact (Program.trace_gate_castSucc _ _ I x _).trans ih

/-- A wire of `q` carries, in the continued program, the value it has when `q` runs on the
values of the wires feeding it.
@isnad1 id=eq.0h12v.s6.a4fd033fd48e from=translated src=- shape=21c657e3 vocab=3bd557cb
-/
theorem trace_append_appendedWire (q : Program σ k g₂) (w : Wire k g₂) :
    (p.append feed q).trace I x (appendedWire feed w) =
      q.trace I (fun i => p.trace I x (feed i)) w := by
  induction q with
  | empty =>
    cases w with
    | input i => exact trace_append_castAdd p feed I x .empty (feed i)
    | gate j => exact j.elim0
  | gate q line ih =>
    cases w with
    | input i => exact trace_append_castAdd p feed I x _ (feed i)
    | gate j =>
      refine Fin.lastCases ?_ (fun j => ?_) j
      · refine (Program.eval_gate_last _ _ I x).trans ?_
        refine Eq.trans ?_ (Program.eval_gate_last q line I _).symm
        exact Line.eval_mapWires line (appendedWire feed) I _ x _ _ ih
      · exact (Program.trace_gate_castSucc _ _ I x (.gate (Fin.natAdd _ j))).trans
          ((ih (.gate j)).trans (Program.trace_gate_castSucc q line I _ (.gate j)).symm)

end Program

namespace Circuit

variable {I : Interpretation σ U}

/-- Feed the outputs of `c` to the inputs of `d`.-/
def comp (d : Circuit σ m p) (c : Circuit σ n m) : Circuit σ n p :=
  ⟨c.program.append c.outputs d.program, Program.appendedWire c.outputs ∘ d.outputs⟩

/--
@isnad1 id=eq.0h6v.s5.ce6826848fe8 from=translated src=- shape=c1673921 vocab=fa68adce
-/
@[simp] theorem size_comp (d : Circuit σ m p) (c : Circuit σ n m) :
    (d.comp c).size = c.size + d.size := rfl

/--
@isnad1 id=eq.0h9v.s5.e12271e4ecc4 from=translated src=- shape=9fd0e93d vocab=e0321a4d
-/
@[simp] theorem eval_comp (d : Circuit σ m p) (c : Circuit σ n m) (x : Fin n → U) :
    (d.comp c).eval I x = d.eval I (c.eval I x) := by
  funext o
  exact Program.trace_append_appendedWire c.program c.outputs I x d.program (d.outputs o)

/-- Run `c` and `d` on the same inputs, listing the outputs of `c` before those of `d`.-/
def append (c : Circuit σ n m) (d : Circuit σ n p) : Circuit σ n (m + p) :=
  ⟨c.program.append Wire.input d.program,
    Fin.append (Wire.castAdd d.size ∘ c.outputs)
      (Program.appendedWire Wire.input ∘ d.outputs)⟩

/--
@isnad1 id=eq.0h6v.s5.7ef93c45d547 from=translated src=- shape=6b3b3afa vocab=10d9d96d
-/
@[simp] theorem size_append (c : Circuit σ n m) (d : Circuit σ n p) :
    (c.append d).size = c.size + d.size := rfl

/--
@isnad1 id=eq.0h9v.s6.2f888944a95e from=translated src=- shape=c503c3d9 vocab=11ed64dc
-/
@[simp] theorem eval_append (c : Circuit σ n m) (d : Circuit σ n p) (x : Fin n → U) :
    (c.append d).eval I x = Fin.append (c.eval I x) (d.eval I x) := by
  funext o
  induction o using Fin.addCases with
  | left o =>
    simp only [eval, append, Function.comp_apply, Fin.append_left]
    exact Program.trace_append_castAdd c.program Wire.input I x d.program (c.outputs o)
  | right o =>
    simp only [eval, append, Function.comp_apply, Fin.append_right]
    exact Program.trace_append_appendedWire c.program Wire.input I x d.program _

/-- Feeding a circuit computing `f` into one computing `g` computes `g ∘ f`.
@isnad1 id=computes.2h10v.s6.d8e46843c683 from=translated src=- shape=dd6a9f84 vocab=dc759388
-/
theorem Computes.comp {c : Circuit σ n m} {d : Circuit σ m p}
    {f : (Fin n → U) → Fin m → U} {g : (Fin m → U) → Fin p → U}
    (hc : c.Computes I f) (hd : d.Computes I g) : (d.comp c).Computes I (g ∘ f) := fun x => by
  rw [eval_comp, hc x, hd]
  rfl

/-- Circuits computing `f` and `g`, run side by side, compute their outputs together.
@isnad1 id=computes.2h10v.s6.5ef64de26eb7 from=translated src=- shape=64742826 vocab=c5c1ffd9
-/
theorem Computes.append {c : Circuit σ n m} {d : Circuit σ n p}
    {f : (Fin n → U) → Fin m → U} {g : (Fin n → U) → Fin p → U}
    (hc : c.Computes I f) (hd : d.Computes I g) :
    (c.append d).Computes I (fun x => Fin.append (f x) (g x)) := fun x => by
  rw [eval_append, hc x, hd x]

/-- Feeding a circuit computing `f` on `S` into one computing `g` on the image of `S` computes
`g ∘ f` on `S`.
@isnad1 id=computes.2h11v.s6.3f5c0b2c1a84 from=translated src=- shape=cc0e4ad6 vocab=f1629759
-/
theorem ComputesOn.comp {c : Circuit σ n m} {d : Circuit σ m p} {S : Set (Fin n → U)}
    {f : (Fin n → U) → Fin m → U} {g : (Fin m → U) → Fin p → U}
    (hc : c.ComputesOn I S f) (hd : d.ComputesOn I (f '' S) g) :
    (d.comp c).ComputesOn I S (g ∘ f) := fun x hx => by
  rw [eval_comp, hc hx]
  exact hd ⟨x, hx, rfl⟩

/-- Circuits computing `f` and `g` on `S`, run side by side, compute their outputs together.
@isnad1 id=computes.2h11v.s6.8de7d9a274db from=translated src=- shape=117e18a8 vocab=dcebd24f
-/
theorem ComputesOn.append {c : Circuit σ n m} {d : Circuit σ n p} {S : Set (Fin n → U)}
    {f : (Fin n → U) → Fin m → U} {g : (Fin n → U) → Fin p → U}
    (hc : c.ComputesOn I S f) (hd : d.ComputesOn I S g) :
    (c.append d).ComputesOn I S (fun x => Fin.append (f x) (g x)) := fun x hx => by
  rw [eval_append, hc hx, hd hx]

end Circuit

end Cslib.Circuits
