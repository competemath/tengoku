import Tengoku.Ulmstheorem.Lib.PGroups.Subgroups

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/elanroth/UlmsTheorem@5545628c78c0, `Lib/PGroups/UlmSubgroups.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Ordinal Ulm subgroups

This file contains the transfinite Ulm filtration `ulmSubgroup` and its basic
structural lemmas.
-/
namespace Tengoku.Ulmstheorem end Tengoku.Ulmstheorem open Tengoku.Ulmstheorem
open Ordinal

variable (p : ℕ) [hp : Fact p.Prime]

/-- `p^α·G` by transfinite recursion:
`p^0·G = G`, `p^(α+1)·G = {p•x | x ∈ p^α·G}`, and
`p^λ·G = ⋂_{β<λ} p^β·G`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.ulmSubgroup {G : Type*} [AddCommGroup G] (α : Ordinal) :
    AddSubgroup G :=
  α.limitRecOn
    ⊤
    (fun _β Hβ ↦ pImage p Hβ)
    (fun o _ho IH ↦ ⨅ (β : Ordinal) (_ : β < o), IH β ‹_›)

section UlmSubgroupLemmas


variable {G : Type*} [AddCommGroup G]

@[simp] lemma _root_.Tengoku.Ulmstheorem.ulmSubgroup_zero : ulmSubgroup p (0 : Ordinal) (G := G) = ⊤ := by
  rw [ulmSubgroup, Ordinal.limitRecOn_zero]

lemma _root_.Tengoku.Ulmstheorem.ulmSubgroup_limit (o : Ordinal) (ho : Order.IsSuccLimit o) :
    ulmSubgroup p o (G := G) = ⨅ (β : Ordinal) (_ : β < o), ulmSubgroup p β := by
  unfold ulmSubgroup
  simpa using
    (Ordinal.limitRecOn_limit o
      (⊤ : AddSubgroup G)
      (fun _β Hβ ↦ pImage p Hβ)
      (fun o _ho IH ↦ ⨅ (β : Ordinal) (_ : β < o), IH β ‹_›)
      ho)

lemma _root_.Tengoku.Ulmstheorem.mem_ulmSubgroup_limit_iff {o : Ordinal} (ho : Order.IsSuccLimit o) (x : G) :
    x ∈ ulmSubgroup p o (G := G) ↔ ∀ β < o, x ∈ ulmSubgroup p β := by
  rw [ulmSubgroup_limit (p := p) (G := G) o ho]
  simp only [AddSubgroup.mem_iInf]

end UlmSubgroupLemmas
-- Tengoku: root names of this library moved to Tengoku.Ulmstheorem so they do not collide with other libraries (generated)
