/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.Cslib.Cslib.Init
public import Tengoku.Seed.Data.Fintype.Sum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Circuit wires and renamings

A `Wire inputCount gateCount` refers to an original input or an internal gate.
A valuation of wires is assembled with `Wire.elim` from values for the inputs and
values for the gates.

`Wire.Renaming` fixes the original inputs and maps each gate to an input or gate
in the target namespace. This file provides identity and composition, extension
by a gate, replacement of the last gate, and renaming by a permutation.
-/

@[expose] public section

namespace Cslib.Circuits

/-- A wire is either an original input or the output of an earlier gate.-/
inductive Wire (inputCount gateCount : Nat) where
  /-- An original input.-/
  | input (input : Fin inputCount)
  /-- The output of an internal gate.-/
  | gate (gate : Fin gateCount)
  deriving DecidableEq

namespace Wire

variable {inputCount gateCount : Nat} {α : Sort*}

/-- Define a function on wires from its values on inputs and on gates.-/
def elim (inputs : Fin inputCount → α) (gates : Fin gateCount → α) :
    Wire inputCount gateCount → α
  | input i => inputs i
  | gate j => gates j

/--
@isnad1 id=eq.0h6v.s5.d8518933b920 from=translated src=- shape=a5a35a5b vocab=7ed09a2e
-/
@[simp] theorem elim_input (inputs : Fin inputCount → α) (gates : Fin gateCount → α)
    (i : Fin inputCount) : elim inputs gates (input i) = inputs i := rfl

/--
@isnad1 id=eq.0h6v.s5.74d72ff005d2 from=translated src=- shape=fabbc32d vocab=12e84b75
-/
@[simp] theorem elim_gate (inputs : Fin inputCount → α) (gates : Fin gateCount → α)
    (j : Fin gateCount) : elim inputs gates (gate j) = gates j := rfl

/-- A wire is an input or a gate.-/
def equiv (inputCount gateCount : Nat) :
    Wire inputCount gateCount ≃ Fin inputCount ⊕ Fin gateCount where
  toFun := elim Sum.inl Sum.inr
  invFun := Sum.elim input gate
  left_inv wire := by cases wire <;> rfl
  right_inv wire := by cases wire <;> rfl

instance : Fintype (Wire inputCount gateCount) :=
  Fintype.ofEquiv _ (equiv inputCount gateCount).symm

/--
@isnad1 id=eq.0h2v.s4.f6ccce70bd95 from=translated src=- shape=fee67a59 vocab=5dcf7256
-/
@[simp] theorem card : Fintype.card (Wire inputCount gateCount) = inputCount + gateCount := by
  simp [Fintype.card_congr (equiv inputCount gateCount)]

/-- Regard a wire as a wire in a namespace with one additional gate.-/
def castSucc : Wire inputCount gateCount → Wire inputCount (gateCount + 1)
  | input i => input i
  | gate j => gate j.castSucc

/--
@isnad1 id=eq.0h3v.s5.ea8f1cc7f401 from=translated src=- shape=a12eb4a9 vocab=4929b5cc
-/
@[simp] theorem castSucc_input (i : Fin inputCount) :
    (input i : Wire inputCount gateCount).castSucc = input i := rfl

/--
@isnad1 id=eq.0h3v.s5.9cfe81093133 from=translated src=- shape=600dd446 vocab=73b538be
-/
@[simp] theorem castSucc_gate (j : Fin gateCount) :
    (gate j : Wire inputCount gateCount).castSucc = gate j.castSucc := rfl

/-- Regard a wire as a wire of the same program continued by `extra` further gates.-/
def castAdd (extra : Nat) : Wire inputCount gateCount → Wire inputCount (gateCount + extra)
  | input i => input i
  | gate j => gate (j.castAdd extra)

/--
@isnad1 id=eq.0h4v.s5.9e7c56a8cf70 from=translated src=- shape=bacb5077 vocab=7c368422
-/
@[simp] theorem castAdd_input (extra : Nat) (i : Fin inputCount) :
    (input i : Wire inputCount gateCount).castAdd extra = input i := rfl

/--
@isnad1 id=eq.0h4v.s5.df74809b0976 from=translated src=- shape=daa32645 vocab=38008634
-/
@[simp] theorem castAdd_gate (extra : Nat) (j : Fin gateCount) :
    (gate j : Wire inputCount gateCount).castAdd extra = gate (j.castAdd extra) := rfl

/-- A wire in a namespace with one additional gate is either the new last gate or an
earlier wire.-/
@[elab_as_elim]
def lastCases {motive : Wire inputCount (gateCount + 1) → Sort*}
    (last : motive (gate (Fin.last gateCount)))
    (castSucc : ∀ wire : Wire inputCount gateCount, motive wire.castSucc) :
    ∀ wire, motive wire
  | input i => castSucc (input i)
  | gate j =>
      Fin.lastCases (motive := fun j => motive (gate j)) last (fun j => castSucc (gate j)) j

end Wire

/-- A renaming of gate wires that fixes every original input. Gate wires may be
sent to either inputs or gates in the target namespace.-/
structure Wire.Renaming (inputCount sourceGateCount targetGateCount : Nat) where
  /-- The target wire representing each source gate.-/
  gates : Fin sourceGateCount → Wire inputCount targetGateCount

namespace Wire.Renaming

variable {inputCount gateCount sourceGateCount middleGateCount targetGateCount : Nat}
variable {U : Type*}

/-- Apply an input-fixing wire renaming.-/
def apply (ρ : Wire.Renaming inputCount sourceGateCount targetGateCount) :
    Wire inputCount sourceGateCount → Wire inputCount targetGateCount :=
  Wire.elim Wire.input ρ.gates

instance : CoeFun (Wire.Renaming inputCount sourceGateCount targetGateCount)
    fun _ => Wire inputCount sourceGateCount → Wire inputCount targetGateCount :=
  ⟨apply⟩

/--
@isnad1 id=eq.0h5v.s4.7bf75ce8692e from=translated src=- shape=66220f2e vocab=85746da7
-/
@[simp] theorem apply_input
    (ρ : Wire.Renaming inputCount sourceGateCount targetGateCount) (input : Fin inputCount) :
    ρ (Wire.input input) = Wire.input input := rfl

/--
@isnad1 id=eq.0h5v.s5.6358f02cac5a from=translated src=- shape=14ee1b67 vocab=e847f967
-/
@[simp] theorem apply_gate
    (ρ : Wire.Renaming inputCount sourceGateCount targetGateCount) (gate : Fin sourceGateCount) :
    ρ (Wire.gate gate) = ρ.gates gate := rfl

/-- The identity wire renaming.-/
def id : Wire.Renaming inputCount gateCount gateCount where
  gates := Wire.gate

/--
@isnad1 id=eq.0h3v.s4.16f7f5ecae6b from=translated src=- shape=eb28c226 vocab=ea8cc975
-/
@[simp] theorem id_apply (wire : Wire inputCount gateCount) :
    (id : Wire.Renaming inputCount gateCount gateCount) wire = wire := by
  cases wire <;> rfl

/-- Compose input-fixing wire renamings.-/
def comp
    (outer : Wire.Renaming inputCount middleGateCount targetGateCount)
    (inner : Wire.Renaming inputCount sourceGateCount middleGateCount) :
    Wire.Renaming inputCount sourceGateCount targetGateCount where
  gates := outer ∘ inner.gates

/--
@isnad1 id=eq.0h7v.s5.176d492f7feb from=translated src=- shape=274b7c38 vocab=930749a9
-/
@[simp] theorem comp_apply
    (outer : Wire.Renaming inputCount middleGateCount targetGateCount)
    (inner : Wire.Renaming inputCount sourceGateCount middleGateCount)
    (wire : Wire inputCount sourceGateCount) :
    (outer.comp inner) wire = outer (inner wire) := by
  cases wire <;> rfl

/-- Include all wires into a namespace with one additional gate.-/
def castSucc : Wire.Renaming inputCount gateCount (gateCount + 1) where
  gates := fun gate => Wire.gate gate.castSucc

/--
@isnad1 id=eq.0h3v.s5.1a1c8a4ceadf from=translated src=- shape=68e62f17 vocab=852cb82f
-/
@[simp] theorem castSucc_apply (wire : Wire inputCount gateCount) :
    (castSucc : Wire.Renaming inputCount gateCount (gateCount + 1)) wire = wire.castSucc := by
  cases wire <;> rfl

/-- Extend a renaming while replacing the new last gate by an existing wire.-/
def skipLast
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (replacement : Wire inputCount targetGateCount) :
    Wire.Renaming inputCount (sourceGateCount + 1) targetGateCount where
  gates := Fin.lastCases replacement prior.gates

/--
@isnad1 id=eq.0h5v.s5.0e683206d24f from=translated src=- shape=d0d466a0 vocab=4d7bed20
-/
@[simp] theorem skipLast_gates_last
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (replacement : Wire inputCount targetGateCount) :
    (prior.skipLast replacement).gates (Fin.last sourceGateCount) = replacement := by
  simp [skipLast]

/--
@isnad1 id=eq.0h6v.s5.b33e4c0cb176 from=translated src=- shape=c19035db vocab=12a0d179
-/
@[simp] theorem skipLast_castSucc
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (replacement : Wire inputCount targetGateCount)
    (wire : Wire inputCount sourceGateCount) :
    prior.skipLast replacement wire.castSucc = prior wire := by
  cases wire <;> simp [skipLast]

/-- Extend a renaming and retain the new last gate as a fresh target gate.-/
def appendLast
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount) :
    Wire.Renaming inputCount (sourceGateCount + 1) (targetGateCount + 1) where
  gates := Fin.lastCases (Wire.gate (Fin.last targetGateCount)) fun gate =>
    (prior.gates gate).castSucc

/--
@isnad1 id=eq.0h4v.s6.05f69db0162e from=translated src=- shape=1b026b95 vocab=87cdefb4
-/
@[simp] theorem appendLast_gates_last
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount) :
    prior.appendLast.gates (Fin.last sourceGateCount) = Wire.gate (Fin.last targetGateCount) := by
  simp [appendLast]

/--
@isnad1 id=eq.0h5v.s6.525c0ce9bf54 from=translated src=- shape=4e68b7e9 vocab=6ce1849a
-/
@[simp] theorem appendLast_castSucc
    (prior : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (wire : Wire inputCount sourceGateCount) :
    prior.appendLast wire.castSucc = (prior wire).castSucc := by
  cases wire <;> simp [appendLast]

/-- Rename gate wires by a permutation.-/
def ofPermutation (permutation : Equiv.Perm (Fin gateCount)) :
    Wire.Renaming inputCount gateCount gateCount where
  gates := fun gate => Wire.gate (permutation gate)

/--
@isnad1 id=eq.0h4v.s5.2f5a334cca64 from=translated src=- shape=a76ddda2 vocab=ee8588d3
-/
theorem ofPermutation_gate
    (permutation : Equiv.Perm (Fin gateCount)) (gate : Fin gateCount) :
    (ofPermutation permutation : Wire.Renaming inputCount gateCount gateCount) (Wire.gate gate) =
      Wire.gate (permutation gate) := rfl

/-- A source and target gate valuation agree along a renaming when they agree
on the image of every source gate. Original inputs agree automatically.
@isnad1 id=eq.1h9v.s6.ff4a2e0c4fcb from=translated src=- shape=60eadc7a vocab=0784ed6b
-/
theorem value_apply
    (ρ : Wire.Renaming inputCount sourceGateCount targetGateCount)
    (inputs : Fin inputCount → U)
    (oldGates : Fin sourceGateCount → U)
    (newGates : Fin targetGateCount → U)
    (preservesGates : ∀ gate, Wire.elim inputs newGates (ρ.gates gate) = oldGates gate)
    (wire : Wire inputCount sourceGateCount) :
    Wire.elim inputs newGates (ρ wire) = Wire.elim inputs oldGates wire := by
  cases wire with
  | input => rfl
  | gate gate => exact preservesGates gate

end Wire.Renaming

end Cslib.Circuits
