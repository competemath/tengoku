/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Tengoku.Algolean.Algolean.Models.Quantum.Indexing
public import Tengoku

/-!
# Gate unitaries on `Fin n → Fin 2`

Construction of the concrete `𝐔[Fin n → Fin 2]` matrices corresponding to
each gate of the `QuantumQuery` syntax. Three strategies appear:

- **Dense single-qubit gates** (`H`, `X`, `Z`, phase): tensor a `𝐔[Qubit]`
  unitary with identity on the other qubits and relabel through
  `Fin.insertNthEquiv`. Implemented by `embedQubitGate`.

- **Permutation gates** (CNOT): construct the underlying permutation of
  `Fin n → Fin 2` directly; unitarity is free from
  `Equiv.Perm.permMatrix_mem_unitaryGroup`. Avoids the two-qubit
  index gymnastics.

- **Parametric gates** (phase `R(θ)`): supplied here because QuantumInfo
  only ships fixed-phase gates (`S`, `T`).

## Main definitions

- `unitaryReindex e U` : `𝐔[d] → 𝐔[d₂]` along `e : d ≃ d₂`.
- `phaseGate θ : 𝐔[Qubit]` : parametric phase gate.
- `embedQubitGate q U : 𝐔[Fin n → Fin 2]` : single-qubit gate on position `q`.
- `cnotUnitary c t h : 𝐔[Fin n → Fin 2]` : CNOT with `control ≠ target`.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

open scoped Matrix

/-! ### Transport of unitaries along index equivalences -/

/-! ### Parametric phase gate -/

/-! ### Single-qubit gate embedding -/

/-! ### CNOT unitary -/

/-- In `Fin 2`, subtracting twice from `1` is the identity. -/
lemma fin2_sub_sub_self (b : Fin 2) : (1 : Fin 2) - (1 - b) = b := by
  fin_cases b <;> rfl

/-- Action of the CNOT gate on bitstrings: flip the target bit iff control is 1. -/
def cnotAction {n : ℕ} (c t : Fin n) : (Fin n → Fin 2) → (Fin n → Fin 2) :=
  fun x => if x c = 1 then Function.update x t (1 - x t) else x

/-- `cnotAction c t` is an involution when control and target differ. -/
lemma cnotAction_involutive {n : ℕ} {c t : Fin n} (h : c ≠ t) :
    Function.Involutive (cnotAction c t) := by
  intro x
  unfold cnotAction
  by_cases hxc : x c = 1
  · rw [ite_eq_left hxc]
    have hc : Function.update x t (1 - x t) c = 1 := by
      rw [Function.update_of_ne h]; exact hxc
    rw [ite_eq_left hc, Function.update_self, Function.update_idem, fin2_sub_sub_self]
    exact Function.update_eq_self t x
  · rw [ite_eq_right hxc, ite_eq_right hxc]

end Algorithms

end Algolean
