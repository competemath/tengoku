import Tengoku.Ulmstheorem.Lib.PGroups.UlmSubgroups

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/elanroth/UlmsTheorem@5545628c78c0, `Lib/PGroups/Heights.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Reducedness and height theory

This file contains the reducedness predicate used in the project and the
basic finite `p`-height calculus.
-/
namespace Tengoku.Ulmstheorem end Tengoku.Ulmstheorem open Tengoku.Ulmstheorem
variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Primary, reduced, and separable groups -/

/-- `G` is `p`-primary if every element is killed by some power of `p`.

This hypothesis is logically independent from reducedness.  In particular, torsion-free
groups such as `ℤ` must not enter Ulm's classification theorem merely because their
`p`-socle is trivial.-/
def _root_.Tengoku.Ulmstheorem.IsPrimaryPGroup (G : Type*) [AddCommGroup G] : Prop :=
  ∀ x : G, ∃ n : ℕ, p ^ n • x = 0

/-- The `p`-Ulm filtration of `G` is reduced if it eventually reaches zero.

For the countable `p`-primary groups classified below, this is equivalent to saying that
`G` has no nontrivial divisible subgroup: the eventual stable Ulm subgroup is the maximal
divisible subgroup.  Crucially, this does *not* require `G_ω = 0`; reduced groups may
contain elements of infinite height and have arbitrary countable Ulm length.-/
def _root_.Tengoku.Ulmstheorem.IsPReduced (G : Type*) [AddCommGroup G] : Prop :=
  ∃ α : Ordinal.{0}, ulmSubgroup p α (G := G) = ⊥

/-- A reduced abelian `p`-group: primary, with zero divisible part.-/
structure _root_.Tengoku.Ulmstheorem.IsReducedPGroup (G : Type*) [AddCommGroup G] : Prop where
  primary : IsPrimaryPGroup p G
  reduced : IsPReduced p G

/-- `G` is `p`-separable if it has no nonzero element of infinite `p`-height.

This was formerly (and incorrectly) called `IsReducedPGroup`.  It is strictly stronger
than reducedness: it says `G_ω = 0`.-/
def _root_.Tengoku.Ulmstheorem.IsPSeparable (G : Type*) [AddCommGroup G] : Prop :=
  ∀ x : G, (∀ n : ℕ, ∃ y : G, p ^ n • y = x) → x = 0

section ReducedLemmas


variable {G : Type*} [AddCommGroup G]

end ReducedLemmas

/-! ### `p`-height -/

/-- The `p`-height of `x`: `⊤` if `x = 0`, otherwise the supremum of
the natural numbers `n` such that `x ∈ p^n·G`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.pHeight {G : Type*} [AddCommGroup G] (x : G) : ℕ∞ :=
  letI : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then ⊤ else sSup (WithTop.some '' {n : ℕ | ∃ y : G, p ^ n • y = x})

section HeightLemmas


variable {G : Type*} [AddCommGroup G]

/--
@isnad1 id=eq.0h2v.s5.f6f2abbd79ae from=translated src=- shape=e318902a vocab=90cbd421
-/
@[simp] lemma _root_.Tengoku.Ulmstheorem.pHeight_zero : pHeight p (0 : G) = ⊤ := by
  simp only [pHeight, ite_true]

end HeightLemmas
-- Tengoku: root names of this library moved to Tengoku.Ulmstheorem so they do not collide with other libraries (generated)
