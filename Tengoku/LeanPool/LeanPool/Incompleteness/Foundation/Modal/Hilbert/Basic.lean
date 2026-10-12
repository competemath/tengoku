/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Substitution
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Entailment.Basic
import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental

/-! # Basic -/

@[expose] public section

namespace LO
namespace Modal

open Entailment

variable {α : Type*}

/-- Imported declaration from the Incompleteness formalization. -/
structure Hilbert (α : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  axioms : Set (Formula α)

namespace Hilbert

variable {H H₁ H₂ : Hilbert α}

/-- Imported declaration from the Incompleteness formalization. -/
abbrev axiomInstances (H : Hilbert α) : Set (Formula α) := { φ⟦s⟧ | (φ ∈ H.axioms) (s :
    Substitution α) }

lemma mem_axiomInstances_of_mem_axioms {φ} (h : φ ∈ H.axioms) : φ ∈ H.axiomInstances := by
  use φ;
  constructor;
  · assumption;
  · use Substitution.id;
    simp;

/-- Imported declaration from the Incompleteness formalization. -/
class FiniteAxiomatizable (H : Hilbert α) where
  axioms_fin : Set.Finite H.axioms := by aesop

/-- Imported declaration from the Incompleteness formalization. -/
inductive Deduction (H : Hilbert α) : (Formula α) → Type _
  | maxm {φ}      : φ ∈ H.axiomInstances → Deduction H φ
  | mdp {φ ψ}     : Deduction H (φ ==> ψ) → Deduction H φ → Deduction H ψ
  | nec {φ}       : Deduction H φ → Deduction H (□φ)
  | imply₁ φ ψ    : Deduction H <| Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ  : Deduction H <| Axioms.Imply₂ φ ψ χ
  | ec φ ψ        : Deduction H <| Axioms.ElimContra φ ψ

namespace Deduction

instance : Entailment (Formula α) (Hilbert α) := ⟨Deduction⟩

instance : Entailment.Lukasiewicz H where
  mdp := mdp
  imply₁ := imply₁
  imply₂ := imply₂
  elimContra := ec

instance : Entailment.Classical H where

instance : Entailment.HasDiaDuality H := inferInstance

instance : Entailment.Necessitation H := ⟨nec⟩

lemma «maxm!» {φ} (h : φ ∈ H.axiomInstances) : H ⊢! φ := ⟨maxm h⟩

end Deduction

open Deduction

namespace Deduction

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def «rec!»
  {motive      : (φ : Formula α) → H ⊢! φ → Sort*}
  (maxm       : ∀ {φ}, (h : φ ∈ H.axiomInstances) → motive φ (maxm! h))
  (mdp        : ∀ {φ ψ}, {hpq : H ⊢! φ ==> ψ} → {hp : H ⊢! φ} → motive (φ ==> ψ) hpq →
    motive φ hp → motive ψ (mdp! hpq hp))
  (nec        : ∀ {φ}, {hp : H ⊢! φ} → (ihp : motive φ hp) → motive (□φ) (nec! hp))
  (imply₁     : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) <| ⟨imply₁ φ ψ⟩)
  (imply₂     : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) <| ⟨imply₂ φ ψ χ⟩)
  (ec : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) <| ⟨ec φ ψ⟩)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  intro φ d;
  induction d.some with
  | maxm h => exact maxm h
  | mdp hpq hp ihpq ihp => exact mdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | nec hp ih => exact nec (ih ⟨hp⟩)
  | _ => aesop;

end Deduction

/-- Imported declaration from the Incompleteness formalization. -/
abbrev theorems (H : Hilbert α) := Entailment.theory H

end Hilbert

end Modal
end LO
