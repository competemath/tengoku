/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Basic
import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental

/-! # Disjunctive -/

@[expose] public section

namespace LO
namespace Entailment

variable {F : Type*} [LogicalConnective F]
variable {S : Type*} [Entailment F S]

/-- Imported declaration from the Incompleteness formalization. -/
class Disjunctive (𝓢 : S) : Prop where
  disjunctive : ∀ {φ ψ}, 𝓢 ⊢! φ ⋎ ψ → 𝓢 ⊢! φ ∨ 𝓢 ⊢! ψ

alias disjunctive := Disjunctive.disjunctive

lemma iff_disjunctive {𝓢 : S} : (Disjunctive 𝓢) ↔ ∀ {φ ψ}, 𝓢 ⊢! φ ⋎ ψ → 𝓢 ⊢! φ ∨ 𝓢 ⊢! ψ :=
  ⟨fun h ↦ h.disjunctive, fun d ↦ ⟨d⟩⟩

end Entailment
end LO
