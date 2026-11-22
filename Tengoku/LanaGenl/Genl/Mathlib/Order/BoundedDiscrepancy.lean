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
namespace Tengoku.LanaGenl end Tengoku.LanaGenl open Tengoku.LanaGenl
variable {α β : Type*}

/-- `DiscrepancyLE f g s`, denoted `f ≲[s] g`, means that `f` is bounded above by `g` up
to a bounded discrepancy on `s`, i.e. there exists a constant `C` such that
`f x ≤ g x + C` for all `x ∈ s`. -/
def _root_.Tengoku.LanaGenl.DiscrepancyLE (f g : α → ℝ) (s : Set α) : Prop :=
  ∃ C : ℝ, ∀ x ∈ s, f x ≤ g x + C

/-- `DiscrepancyEquiv f g s`, denoted `f ≈[s] g`, means that `f` and `g` agree up to a
bounded discrepancy on `s`, i.e. `|f x - g x|` is bounded on `s`. The equivalence classes
of this relation are called *BD-classes*. -/
def _root_.Tengoku.LanaGenl.DiscrepancyEquiv (f g : α → ℝ) (s : Set α) : Prop :=
  DiscrepancyLE f g s ∧ DiscrepancyLE g f s

@[inherit_doc]
local notation:50 f:51 " ≲[" s "] " g:51 => DiscrepancyLE f g s

@[inherit_doc]
local notation:50 f:51 " ≈[" s "] " g:51 => DiscrepancyEquiv f g s

namespace Tengoku.LanaGenl.DiscrepancyLE

variable {f f₁ f₂ g g₁ g₂ h : α → ℝ} {s t : Set α}

/--
@isnad1 id=discrepa.1h4v.s5.daa018dff17b from=translated src=- shape=ffd29c06 vocab=5f7736f3
-/
theorem of_forall_le (hfg : ∀ x ∈ s, f x ≤ g x) : f ≲[s] g :=
  ⟨0, fun x hx ↦ by simpa using hfg x hx⟩

/--
@isnad1 id=discrepa.0h3v.s3.f23e006ae669 from=translated src=- shape=aa66c1fa vocab=babbbcf8
-/
protected theorem refl (f : α → ℝ) (s : Set α) : f ≲[s] f :=
  of_forall_le fun _ _ ↦ le_rfl

/--
@isnad1 id=discrepa.2h5v.s5.d032463d5663 from=translated src=- shape=630d3c74 vocab=babbbcf8
-/
protected theorem trans (h₁ : f ≲[s] g) (h₂ : g ≲[s] h) : f ≲[s] h := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  exact ⟨C₁ + C₂, fun x hx ↦ by have := hC₁ x hx; have := hC₂ x hx; linarith⟩

/--
@isnad1 id=discrepa.2h5v.s5.6e07911603d7 from=translated src=- shape=f36bb135 vocab=0d4891ee
-/
theorem mono (hst : t ⊆ s) (hfg : f ≲[s] g) : f ≲[t] g := by
  obtain ⟨C, hC⟩ := hfg
  exact ⟨C, fun x hx ↦ hC x (hst hx)⟩

/--
@isnad1 id=discrepa.0h3v.s4.6daaa05eceb3 from=translated src=- shape=086e5701 vocab=2f977086
-/
@[simp]
theorem empty : f ≲[(∅ : Set α)] g :=
  ⟨0, by simp⟩

/--
@isnad1 id=discrepa.2h5v.s5.ae3fb07c8a4d from=translated src=- shape=6e7c1fac vocab=47539cce
-/
theorem union (hs : f ≲[s] g) (ht : f ≲[t] g) : f ≲[s ∪ t] g := by
  obtain ⟨C₁, hC₁⟩ := hs
  obtain ⟨C₂, hC₂⟩ := ht
  refine ⟨max C₁ C₂, fun x hx ↦ ?_⟩
  rcases hx with hx | hx
  · exact (hC₁ x hx).trans (by gcongr; exact le_max_left C₁ C₂)
  · exact (hC₂ x hx).trans (by gcongr; exact le_max_right C₁ C₂)

/--
@isnad1 id=discrepa.2h6v.s6.c1590d166d2a from=translated src=- shape=9b99b6b7 vocab=d9723159
-/
protected theorem add (h₁ : f₁ ≲[s] g₁) (h₂ : f₂ ≲[s] g₂) : f₁ + f₂ ≲[s] g₁ + g₂ := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  refine ⟨C₁ + C₂, fun x hx ↦ ?_⟩
  have := hC₁ x hx
  have := hC₂ x hx
  simp only [Pi.add_apply]
  linarith

/--
@isnad1 id=discrepa.2h5v.s6.773f0b0f8cc5 from=translated src=- shape=d86f0827 vocab=189d01f4
-/
protected theorem smul {c : ℝ} (hc : 0 ≤ c) (hfg : f ≲[s] g) : c • f ≲[s] c • g := by
  obtain ⟨C, hC⟩ := hfg
  refine ⟨c * C, fun x hx ↦ ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  calc c * f x ≤ c * (g x + C) := by
        exact mul_le_mul_of_nonneg_left (hC x hx) hc
    _ = c * g x + c * C := by ring

/--
@isnad1 id=discrepa.1h5v.s6.c845acda48d4 from=translated src=- shape=e1f79327 vocab=1a49bae6
-/
theorem sub_right (hfg : f ≲[s] g) (h : α → ℝ) : f - h ≲[s] g - h := by
  obtain ⟨C, hC⟩ := hfg
  refine ⟨C, fun x hx ↦ ?_⟩
  have := hC x hx
  simp only [Pi.sub_apply]
  linarith

/--
@isnad1 id=discrepa.1h5v.s6.06e6c78c6211 from=translated src=- shape=e1f79327 vocab=d9723159
-/
theorem add_right (hfg : f ≲[s] g) (h : α → ℝ) : f + h ≲[s] g + h := by
  simpa using hfg.add (DiscrepancyLE.refl h s)

/-- Bounded discrepancy inequalities are stable under precomposition.
@isnad1 id=discrepa.2h7v.s5.f1bc0c79bc7b from=translated src=- shape=edf7ce25 vocab=ad874f71
-/
theorem comp (hfg : f ≲[s] g) (φ : β → α) {t : Set β} (hφ : Set.MapsTo φ t s) :
    f ∘ φ ≲[t] g ∘ φ := by
  obtain ⟨C, hC⟩ := hfg
  exact ⟨C, fun x hx ↦ hC (φ x) (hφ hx)⟩

/-- A bounded discrepancy inequality descends along a map that is surjective onto the
base set.
@isnad1 id=discrepa.2h7v.s5.5b0c16586f73 from=translated src=- shape=2cdbdcec vocab=722525f1
-/
theorem of_comp_surjOn {φ : β → α} {t : Set β} (hφ : Set.SurjOn φ t s)
    (hfg : f ∘ φ ≲[t] g ∘ φ) : f ≲[s] g := by
  obtain ⟨C, hC⟩ := hfg
  refine ⟨C, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := hφ hx
  exact hC y hy

end Tengoku.LanaGenl.DiscrepancyLE

namespace Tengoku.LanaGenl.DiscrepancyEquiv

variable {f f₁ f₂ g g₁ g₂ h : α → ℝ} {s t : Set α}

/--
@isnad1 id=discrepa.1h4v.s4.6153c2135e16 from=translated src=- shape=0bbe4d21 vocab=31fab2c8
-/
theorem le (hfg : f ≈[s] g) : f ≲[s] g := hfg.1

/--
@isnad1 id=discrepa.1h4v.s4.6dfcccda530a from=translated src=- shape=001343d5 vocab=31fab2c8
-/
theorem ge (hfg : f ≈[s] g) : g ≲[s] f := hfg.2

/--
@isnad1 id=discrepa.0h3v.s3.584330864fdd from=translated src=- shape=aa66c1fa vocab=dd52330f
-/
protected theorem refl (f : α → ℝ) (s : Set α) : f ≈[s] f :=
  ⟨.refl f s, .refl f s⟩

/--
@isnad1 id=discrepa.1h4v.s4.19f9cb750cd8 from=translated src=- shape=001343d5 vocab=dd52330f
-/
protected theorem symm (hfg : f ≈[s] g) : g ≈[s] f :=
  ⟨hfg.2, hfg.1⟩

/--
@isnad1 id=discrepa.2h5v.s5.bb5cef95bbda from=translated src=- shape=630d3c74 vocab=dd52330f
-/
protected theorem trans (h₁ : f ≈[s] g) (h₂ : g ≈[s] h) : f ≈[s] h :=
  ⟨h₁.le.trans h₂.le, h₂.ge.trans h₁.ge⟩

/--
@isnad1 id=discrepa.2h5v.s5.2a819a94f7e4 from=translated src=- shape=f36bb135 vocab=685b5faf
-/
theorem mono (hst : t ⊆ s) (hfg : f ≈[s] g) : f ≈[t] g :=
  ⟨hfg.le.mono hst, hfg.ge.mono hst⟩

/--
@isnad1 id=discrepa.2h6v.s6.931ff91f1c2a from=translated src=- shape=9b99b6b7 vocab=85041f8e
-/
protected theorem add (h₁ : f₁ ≈[s] g₁) (h₂ : f₂ ≈[s] g₂) : f₁ + f₂ ≈[s] g₁ + g₂ :=
  ⟨h₁.le.add h₂.le, h₁.ge.add h₂.ge⟩

/--
@isnad1 id=discrepa.2h5v.s6.38e7b3869580 from=translated src=- shape=d86f0827 vocab=b281d765
-/
protected theorem smul {c : ℝ} (hc : 0 ≤ c) (hfg : f ≈[s] g) : c • f ≈[s] c • g :=
  ⟨hfg.le.smul hc, hfg.ge.smul hc⟩

/--
@isnad1 id=discrepa.1h5v.s6.e1e4053f3802 from=translated src=- shape=e1f79327 vocab=3cfd6383
-/
theorem sub_right (hfg : f ≈[s] g) (h : α → ℝ) : f - h ≈[s] g - h :=
  ⟨hfg.le.sub_right h, hfg.ge.sub_right h⟩

/--
@isnad1 id=discrepa.2h7v.s5.bdacf97b8db9 from=translated src=- shape=edf7ce25 vocab=6e7f4241
-/
theorem comp (hfg : f ≈[s] g) (φ : β → α) {t : Set β} (hφ : Set.MapsTo φ t s) :
    f ∘ φ ≈[t] g ∘ φ :=
  ⟨hfg.le.comp φ hφ, hfg.ge.comp φ hφ⟩

end Tengoku.LanaGenl.DiscrepancyEquiv

namespace Tengoku.LanaGenl.DiscrepancyLE

variable {f g h : α → ℝ} {s : Set α}

/--
@isnad1 id=discrepa.2h5v.s5.ced934195a9a from=translated src=- shape=630d3c74 vocab=31fab2c8
-/
theorem trans_equiv (h₁ : f ≲[s] g) (h₂ : g ≈[s] h) : f ≲[s] h :=
  h₁.trans h₂.le

/--
@isnad1 id=discrepa.2h5v.s5.262597443450 from=translated src=- shape=417e0f0b vocab=31fab2c8
-/
theorem equiv_trans (h₁ : f ≈[s] g) (h₂ : g ≲[s] h) : f ≲[s] h :=
  h₁.le.trans h₂

end Tengoku.LanaGenl.DiscrepancyLE
-- Tengoku: 2 notation(s) of this module made local so they do not change other libraries (generated)
-- Tengoku: root names of this library moved to Tengoku.LanaGenl so they do not collide with other libraries (generated)
