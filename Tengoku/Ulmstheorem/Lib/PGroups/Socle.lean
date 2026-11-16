import Tengoku.Ulmstheorem.Lib.PGroups.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/elanroth/UlmsTheorem@5545628c78c0, `Lib/PGroups/Socle.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Socle-level constructions

This file contains the p-socle and its interaction with the Ulm filtration.
-/
namespace Tengoku.Ulmstheorem end Tengoku.Ulmstheorem open Tengoku.Ulmstheorem
open Ordinal

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `p`-socle `P = {x | p • x = 0}`.-/
def _root_.Tengoku.Ulmstheorem.pSocle {G : Type*} [AddCommGroup G] : AddSubgroup G where
  carrier   := {x | p • x = 0}
  zero_mem' := by simp
  add_mem'  := by
    rintro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_add, ha, hb, add_zero]
  neg_mem'  := by
    rintro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_neg, ha, neg_zero]

section SocleLemmas


variable {G : Type*} [AddCommGroup G]

/--
@isnad1 id=iff.0h3v.s6.405c84f5be74 from=translated src=- shape=8a33e6ec vocab=a13b6561
-/
@[simp] lemma _root_.Tengoku.Ulmstheorem.mem_pSocle (x : G) : x ∈ pSocle p (G := G) ↔ p • x = 0 := Iff.rfl

/-- The filtered socle `P_α = P ∩ G_α`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.pSocleAt (α : Ordinal) : AddSubgroup G :=
  pSocle p ⊓ ulmSubgroup p α

/--
@isnad1 id=iff.0h4v.s6.9a220600e81b from=translated src=- shape=4aa66a38 vocab=c70414a0
-/
@[simp] lemma _root_.Tengoku.Ulmstheorem.mem_pSocleAt (α : Ordinal) (x : G) :
    x ∈ pSocleAt p α (G := G) ↔ p • x = 0 ∧ x ∈ ulmSubgroup p α := Iff.rfl

noncomputable instance _root_.Tengoku.Ulmstheorem.pSocleAt_ZMod_module (α : Ordinal) :
    Module (ZMod p) (pSocleAt p α (G := G)) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := pSocleAt p α (G := G)) ?_
  intro x
  have hx : p • (x : G) = 0 := (mem_pSocleAt p α (x : G)).1 x.property |>.1
  ext
  simp [hx]

/-- `P_{α+1}` viewed as a subgroup of `P_α`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.pSocleAt_succ_subgroupOf (α : Ordinal) :
    AddSubgroup (pSocleAt p α (G := G)) :=
  (pSocleAt p (Order.succ α) (G := G)).comap
    (AddSubgroup.subtype (pSocleAt p α))

noncomputable instance _root_.Tengoku.Ulmstheorem.pSocleAt_quot_module (α : Ordinal) :
    Module (ZMod p) ((pSocleAt p α (G := G)) ⧸ pSocleAt_succ_subgroupOf p α) := by
  classical
  refine QuotientAddGroup.zmodModule (n := p)
    (G := pSocleAt p α (G := G)) (H := pSocleAt_succ_subgroupOf p α) ?_
  intro x
  have hx' : p • (x : G) = 0 := (mem_pSocleAt p α (x : G)).1 x.property |>.1
  have hx : p • x = 0 := by
    ext
    simp [hx']
  simp [hx]

end SocleLemmas
-- Tengoku: root names of this library moved to Tengoku.Ulmstheorem so they do not collide with other libraries (generated)
