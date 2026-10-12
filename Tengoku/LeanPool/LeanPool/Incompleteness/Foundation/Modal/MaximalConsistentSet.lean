/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Formula
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Entailment.Basic
public import Tengoku
import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Modal.Entailment.K

/-! # MaximalConsistentSet -/

@[expose] public section

namespace LO
namespace Modal

open Entailment

variable {α : Type*}
variable {S} [Entailment (Formula α) S]
variable {𝓢 : S}

namespace FormulaSet

variable {T : FormulaSet α}

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Consistent (𝓢 : S) (T : FormulaSet α) := T *⊬[𝓢] ⊥

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Inconsistent (𝓢 : S) (T : FormulaSet α) := ¬(Consistent 𝓢 T)

lemma def_consistent : Consistent 𝓢 T ↔ ∀ Γ, (∀ ψ ∈ Γ, ψ ∈ T) → Γ ⊬[𝓢] ⊥ := by
  constructor;
  · intro h;
    simpa using Context.provable_iff.not.mp h;
  · intro h;
    apply Context.provable_iff.not.mpr; simp_all

lemma def_inconsistent : Inconsistent 𝓢 T ↔ ∃ (Γ :
    List (Formula α)), (∀ ψ ∈ Γ, ψ ∈ T) ∧ Γ ⊢[𝓢]! ⊥ := by
  unfold Inconsistent;
  apply not_iff_not.mp;
  push Not;
  exact def_consistent;

lemma union_consistent : Consistent 𝓢 (T₁ ∪ T₂) → (Consistent 𝓢 T₁) ∧ (Consistent 𝓢 T₂) := by
  intro h;
  replace h := def_consistent.mp h;
  constructor <;> {
    apply def_consistent.mpr;
    intro Γ hΓ;
    exact h Γ <| by tauto_set;
  }

variable [Entailment.Classical 𝓢]

variable [DecidableEq α]

omit [DecidableEq α] in
omit [Entailment.Classical 𝓢] in
lemma exists_consistent_maximal_of_consistent (T_consis : Consistent 𝓢 T)
  : ∃ Z, Consistent 𝓢 Z ∧ T ⊆ Z ∧ ∀ U, U *⊬[𝓢] ⊥ → Z ⊆ U → U = Z := by classical
  obtain ⟨Z, h₁, ⟨h₂, h₃⟩⟩ := zorn_subset_nonempty { T : FormulaSet α | Consistent 𝓢 T} (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    simp only [Set.mem_ofPred_eq];
    constructor;
    · apply def_consistent.mpr;
      intro Γ hΓ; by_contra hC;
      obtain ⟨U, hUc, hUs⟩ :=
        Set.subset_mem_chain_of_finite c hnc chain
          (s := ↑Γ.toFinset) (by simp)
          (by intro φ hp; simp_all);
      simp only [List.coe_toFinset] at hUs;
      have : Consistent 𝓢 U := hc hUc;
      have : Inconsistent 𝓢 U := by
        apply def_inconsistent.mpr;
        use Γ;
        constructor;
        · intro φ hp; exact hUs hp;
        · assumption;
      contradiction;
    · intro s a;
      exact Set.subset_sUnion_of_mem a;
  ) T T_consis;
  use Z;
  simp_all only [Set.mem_ofPred_eq, true_and];
  constructor;
  · assumption;
  · intro U hU hZU;
    apply Set.eq_of_subset_of_subset;
    · exact h₃ hU hZU;
    · assumption;

protected alias lindenbaum := exists_consistent_maximal_of_consistent

end FormulaSet

open FormulaSet

/-- Imported declaration from the Incompleteness formalization. -/
abbrev MaximalConsistentSet (𝓢 : S) := { T :
    FormulaSet α // (Consistent 𝓢 T) ∧ (∀ {U}, T ⊂ U → Inconsistent 𝓢 U)}

namespace MaximalConsistentSet

variable {Ω Ω₁ Ω₂ : MaximalConsistentSet 𝓢}
variable {φ : Formula α}

instance : Membership (Formula α) (MaximalConsistentSet 𝓢) := ⟨fun Ω φ => φ ∈ Ω.1⟩

lemma consistent (Ω : MaximalConsistentSet 𝓢) : Consistent 𝓢 Ω.1 := Ω.2.1

lemma maximal (Ω : MaximalConsistentSet 𝓢) : Ω.1 ⊂ U → Inconsistent 𝓢 U := Ω.2.2

lemma maximal' (Ω : MaximalConsistentSet 𝓢) {φ : Formula α} (hp : φ ∉ Ω) :
    Inconsistent 𝓢 (insert φ Ω.1) :=
  Ω.maximal (Set.ssubset_insert hp)

lemma equality_def : Ω₁ = Ω₂ ↔ Ω₁.1 = Ω₂.1 := by
  constructor;
  · intro h; cases h; rfl;
  · intro h; cases Ω₁; cases Ω₂; simp_all;

variable [DecidableEq α]

omit [DecidableEq α] in
lemma exists_of_consistent (consisT : Consistent 𝓢 T) : ∃ Ω :
    MaximalConsistentSet 𝓢, (T ⊆ Ω.1) := by classical
  have ⟨Ω, hΩ₁, hΩ₂, hΩ₃⟩ := FormulaSet.lindenbaum consisT;
  use ⟨Ω, ?_, ?_⟩;
  · assumption;
  · rintro U ⟨hU₁, _⟩;
    by_contra hC;
    have := hΩ₃ U hC <| hU₁;
    simp_all

alias lindenbaum := exists_of_consistent

section «lp_section_classical»

variable [Entailment.Classical 𝓢]

end «lp_section_classical»

section «lp_section_1»

variable [Entailment.K 𝓢]

variable {Γ : List (Formula α)}

end «lp_section_1»

end MaximalConsistentSet

end Modal
end LO
