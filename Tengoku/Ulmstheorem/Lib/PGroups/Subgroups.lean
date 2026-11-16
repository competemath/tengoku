import Tengoku.Ulmstheorem.Lib.PGroups.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/elanroth/UlmsTheorem@5545628c78c0, `Lib/PGroups/Subgroups.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Subgroup-level algebra for reduced abelian p-groups

This file contains the basic subgroup constructions used throughout the
development: the natural-number powers `pPow` and the image-of-multiplication
construction `pImage`.
-/
namespace Tengoku.Ulmstheorem end Tengoku.Ulmstheorem open Tengoku.Ulmstheorem
variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Natural-number Ulm subgroups -/

/-- `p^n·G = { p^n • y | y : G }`.-/
def _root_.Tengoku.Ulmstheorem.pPow {G : Type*} [AddCommGroup G] (n : ℕ) : AddSubgroup G where
  carrier   := {x | ∃ y : G, p ^ n • y = x}
  zero_mem' := ⟨0, by simp⟩
  add_mem'  := by
    rintro a b ⟨ya, rfl⟩ ⟨yb, rfl⟩
    exact ⟨ya + yb, smul_add (p ^ n) ya yb⟩
  neg_mem'  := by
    rintro a ⟨y, rfl⟩
    exact ⟨-y, smul_neg (p ^ n) y⟩

section PowLemmas


variable {G : Type*} [AddCommGroup G]

@[simp] lemma _root_.Tengoku.Ulmstheorem.pPow_mem_iff (x : G) (n : ℕ) :
    x ∈ pPow p n ↔ ∃ y : G, p ^ n • y = x := Iff.rfl

end PowLemmas

/-! ### `p`-image of a subgroup -/

/-- `{ p • y | y ∈ H }` as a subgroup of `G`.-/
def _root_.Tengoku.Ulmstheorem.pImage {G : Type*} [AddCommGroup G] (H : AddSubgroup G) : AddSubgroup G where
  carrier   := {x | ∃ y ∈ H, p • y = x}
  zero_mem' := ⟨0, H.zero_mem, by simp⟩
  add_mem'  := by
    rintro a b ⟨ya, hya, rfl⟩ ⟨yb, hyb, rfl⟩
    exact ⟨ya + yb, H.add_mem hya hyb, smul_add p ya yb⟩
  neg_mem'  := by
    rintro a ⟨y, hy, rfl⟩
    exact ⟨-y, H.neg_mem hy, smul_neg p y⟩

section PImageLemmas


variable {G : Type*} [AddCommGroup G]

@[simp] lemma _root_.Tengoku.Ulmstheorem.mem_pImage (H : AddSubgroup G) (x : G) :
    x ∈ pImage p H ↔ ∃ y ∈ H, p • y = x := Iff.rfl

end PImageLemmas
-- Tengoku: root names of this library moved to Tengoku.Ulmstheorem so they do not collide with other libraries (generated)
