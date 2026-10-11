/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.LeanPool.LeanPool.CircuitComplexity.EssentialInput
public import Tengoku.LeanPool.LeanPool.CircuitComplexity.AON.Defs
public import Tengoku

/-! # Internal: Gate Elimination Lower Bound

This internal module proves the gate elimination lower bound: for any circuit
over a bounded fan-in k AND/OR basis, if the computed function depends on n'
essential variables, the circuit has size at least ⌈n'/k⌉.

The public definitions (`IsEssentialInput`, `EssentialInputs`) are in
`Circ.EssentialInput`. The public theorems (`gate_elimination_lower_bound`,
`lower_bound_all_inputs`) are accessible through `Circ.LowerBound`.
-/

@[expose] public section

namespace CircuitComplexity

namespace Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

/-! ## Core insensitivity lemma -/

/-! ## Essential variables must be read -/

/-! ## Counting argument -/

/-- The set of primary inputs directly wired into a gate. -/
def coveredInputs (g : Gate B (N + G)) : Finset (Fin N) :=
  Finset.univ.filter fun i : Fin N =>
    ∃ k : Fin g.fanIn, (g.inputs k).val = i.val

omit [NeZero N] in
theorem mem_coveredInputs (g : Gate B (N + G)) (i : Fin N) :
    i ∈ coveredInputs g ↔ ∃ k : Fin g.fanIn, (g.inputs k).val = i.val := by
  simp [coveredInputs]

theorem card_coveredInputs_le (g : Gate B (N + G)) :
    (coveredInputs g : Finset (Fin N)).card ≤ g.fanIn := by
  suffices coveredInputs g ⊆
      (Finset.univ : Finset (Fin g.fanIn)).image
        (fun k => if h : (g.inputs k).val < N
          then ⟨(g.inputs k).val, h⟩
          else ⟨0, NeZero.pos N⟩) by
    calc (coveredInputs g).card
        ≤ _ := Finset.card_le_card this
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = g.fanIn := by simp
  intro i hi
  rw [mem_coveredInputs] at hi
  obtain ⟨k, hk⟩ := hi
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨k, by simp [hk]⟩

/-- For a gate over bounded fan-in k AON basis, covered inputs has card ≤ k. -/
theorem boundedAON_coveredInputs_card_le {k : Nat}
    (g : Gate (Basis.boundedAON k) (N + G)) :
    (coveredInputs g : Finset (Fin N)).card ≤ k := by
  have hfanIn : g.fanIn ≤ k := by
    have h := g.arityOk
    revert h; cases g.op <;> simp [Basis.boundedAON, Arity.satisfiedBy]
  exact le_trans (card_coveredInputs_le g) hfanIn

/-- Gate accessor for internal and output gates uniformly. -/
private def gateAt (c : Circuit B N M G) : Fin G ⊕ Fin M → Gate B (N + G)
  | .inl g => c.gates g
  | .inr j => c.outputs j

end Circuit

end CircuitComplexity
