/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Algebra.Order.Field.Basic
import Tengoku.Seed.Algebra.Group.Pi.Lemmas
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Data.Set.Function
import Tengoku.Seed.Tactic.GCongr
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded discrepancy classes of real valued functions

Given real valued functions `f g : α → ℝ` and a set `s : Set α`, we say that `f` is
*dominated up to bounded discrepancy* by `g` on `s`, written `f ≲[s] g`, if there exists
a constant `C : ℝ` such that `f x ≤ g x + C` for all `x ∈ s`. If both `f ≲[s] g` and
`g ≲[s] f` hold, we write `f ≈[s] g` and say that `f` and `g` are *equal up to bounded
discrepancy* on `s`. The equivalence classes of `≈[s]` are the *BD-classes* of
[mochizuki2010], Definition 1.2 (ii).

These notions are ubiquitous in the theory of height functions in diophantine geometry,
where all interesting statements about heights only hold up to a bounded discrepancy,
e.g. the height function associated to a line bundle is only well defined up to bounded
discrepancy.

## Main definitions

- `DiscrepancyLE f g s` (notation: `f ≲[s] g`): `f ≤ g + C` on `s` for some constant `C`.
- `DiscrepancyEquiv f g s` (notation: `f ≈[s] g`): `f ≲[s] g` and `g ≲[s] f`.

## References

- [mochizuki2010] S. Mochizuki, *Arithmetic elliptic curves in general position*,
  Math. J. Okayama Univ. **52** (2010), 1–28.
-/

variable {α β : Type*}

/-- `DiscrepancyLE f g s`, denoted `f ≲[s] g`, means that `f` is bounded above by `g` up
to a bounded discrepancy on `s`, i.e. there exists a constant `C` such that
`f x ≤ g x + C` for all `x ∈ s`. -/
def DiscrepancyLE (f g : α → ℝ) (s : Set α) : Prop :=
  ∃ C : ℝ, ∀ x ∈ s, f x ≤ g x + C

/-- `DiscrepancyEquiv f g s`, denoted `f ≈[s] g`, means that `f` and `g` agree up to a
bounded discrepancy on `s`, i.e. `|f x - g x|` is bounded on `s`. The equivalence classes
of this relation are called *BD-classes*. -/
def DiscrepancyEquiv (f g : α → ℝ) (s : Set α) : Prop :=
  DiscrepancyLE f g s ∧ DiscrepancyLE g f s

@[inherit_doc]
local notation:50 f:51 " ≲[" s "] " g:51 => DiscrepancyLE f g s

@[inherit_doc]
local notation:50 f:51 " ≈[" s "] " g:51 => DiscrepancyEquiv f g s

namespace DiscrepancyLE

variable {f f₁ f₂ g g₁ g₂ h : α → ℝ} {s t : Set α}

theorem of_forall_le (hfg : ∀ x ∈ s, f x ≤ g x) : f ≲[s] g :=
  ⟨0, fun x hx ↦ by simpa using hfg x hx⟩

protected theorem refl (f : α → ℝ) (s : Set α) : f ≲[s] f :=
  of_forall_le fun _ _ ↦ le_rfl

protected theorem trans (h₁ : f ≲[s] g) (h₂ : g ≲[s] h) : f ≲[s] h := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  exact ⟨C₁ + C₂, fun x hx ↦ by have := hC₁ x hx; have := hC₂ x hx; linarith⟩

theorem mono (hst : t ⊆ s) (hfg : f ≲[s] g) : f ≲[t] g := by
  obtain ⟨C, hC⟩ := hfg
  exact ⟨C, fun x hx ↦ hC x (hst hx)⟩

@[simp]
theorem empty : f ≲[(∅ : Set α)] g :=
  ⟨0, by simp⟩

theorem union (hs : f ≲[s] g) (ht : f ≲[t] g) : f ≲[s ∪ t] g := by
  obtain ⟨C₁, hC₁⟩ := hs
  obtain ⟨C₂, hC₂⟩ := ht
  refine ⟨max C₁ C₂, fun x hx ↦ ?_⟩
  rcases hx with hx | hx
  · exact (hC₁ x hx).trans (by gcongr; exact le_max_left C₁ C₂)
  · exact (hC₂ x hx).trans (by gcongr; exact le_max_right C₁ C₂)

protected theorem add (h₁ : f₁ ≲[s] g₁) (h₂ : f₂ ≲[s] g₂) : f₁ + f₂ ≲[s] g₁ + g₂ := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  refine ⟨C₁ + C₂, fun x hx ↦ ?_⟩
  have := hC₁ x hx
  have := hC₂ x hx
  simp only [Pi.add_apply]
  linarith

protected theorem smul {c : ℝ} (hc : 0 ≤ c) (hfg : f ≲[s] g) : c • f ≲[s] c • g := by
  obtain ⟨C, hC⟩ := hfg
  refine ⟨c * C, fun x hx ↦ ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  calc c * f x ≤ c * (g x + C) := by
        exact mul_le_mul_of_nonneg_left (hC x hx) hc
    _ = c * g x + c * C := by ring

theorem sub_right (hfg : f ≲[s] g) (h : α → ℝ) : f - h ≲[s] g - h := by
  obtain ⟨C, hC⟩ := hfg
  refine ⟨C, fun x hx ↦ ?_⟩
  have := hC x hx
  simp only [Pi.sub_apply]
  linarith

theorem add_right (hfg : f ≲[s] g) (h : α → ℝ) : f + h ≲[s] g + h := by
  simpa using hfg.add (DiscrepancyLE.refl h s)

/-- Bounded discrepancy inequalities are stable under precomposition. -/
theorem comp (hfg : f ≲[s] g) (φ : β → α) {t : Set β} (hφ : Set.MapsTo φ t s) :
    f ∘ φ ≲[t] g ∘ φ := by
  obtain ⟨C, hC⟩ := hfg
  exact ⟨C, fun x hx ↦ hC (φ x) (hφ hx)⟩

/-- A bounded discrepancy inequality descends along a map that is surjective onto the
base set. -/
theorem of_comp_surjOn {φ : β → α} {t : Set β} (hφ : Set.SurjOn φ t s)
    (hfg : f ∘ φ ≲[t] g ∘ φ) : f ≲[s] g := by
  obtain ⟨C, hC⟩ := hfg
  refine ⟨C, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := hφ hx
  exact hC y hy

end DiscrepancyLE

namespace DiscrepancyEquiv

variable {f f₁ f₂ g g₁ g₂ h : α → ℝ} {s t : Set α}

theorem le (hfg : f ≈[s] g) : f ≲[s] g := hfg.1

theorem ge (hfg : f ≈[s] g) : g ≲[s] f := hfg.2

protected theorem refl (f : α → ℝ) (s : Set α) : f ≈[s] f :=
  ⟨.refl f s, .refl f s⟩

protected theorem symm (hfg : f ≈[s] g) : g ≈[s] f :=
  ⟨hfg.2, hfg.1⟩

protected theorem trans (h₁ : f ≈[s] g) (h₂ : g ≈[s] h) : f ≈[s] h :=
  ⟨h₁.le.trans h₂.le, h₂.ge.trans h₁.ge⟩

theorem mono (hst : t ⊆ s) (hfg : f ≈[s] g) : f ≈[t] g :=
  ⟨hfg.le.mono hst, hfg.ge.mono hst⟩

protected theorem add (h₁ : f₁ ≈[s] g₁) (h₂ : f₂ ≈[s] g₂) : f₁ + f₂ ≈[s] g₁ + g₂ :=
  ⟨h₁.le.add h₂.le, h₁.ge.add h₂.ge⟩

protected theorem smul {c : ℝ} (hc : 0 ≤ c) (hfg : f ≈[s] g) : c • f ≈[s] c • g :=
  ⟨hfg.le.smul hc, hfg.ge.smul hc⟩

theorem sub_right (hfg : f ≈[s] g) (h : α → ℝ) : f - h ≈[s] g - h :=
  ⟨hfg.le.sub_right h, hfg.ge.sub_right h⟩

theorem comp (hfg : f ≈[s] g) (φ : β → α) {t : Set β} (hφ : Set.MapsTo φ t s) :
    f ∘ φ ≈[t] g ∘ φ :=
  ⟨hfg.le.comp φ hφ, hfg.ge.comp φ hφ⟩

end DiscrepancyEquiv

namespace DiscrepancyLE

variable {f g h : α → ℝ} {s : Set α}

theorem trans_equiv (h₁ : f ≲[s] g) (h₂ : g ≈[s] h) : f ≲[s] h :=
  h₁.trans h₂.le

theorem equiv_trans (h₁ : f ≈[s] g) (h₂ : g ≲[s] h) : f ≲[s] h :=
  h₁.le.trans h₂

end DiscrepancyLE
-- Tengoku: 2 notation(s) of this module made local so they do not change other libraries (generated)
