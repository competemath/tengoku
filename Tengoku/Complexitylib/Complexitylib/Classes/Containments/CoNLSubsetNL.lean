/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Tengoku.Complexitylib.Complexitylib.Classes.L

/-!
# `coNL ⊆ NL`

⚠️ Unreviewed by Bolton

The reverse half of the Immerman–Szelepcsényi theorem.

Either inclusion implies the other, and this file proves that reduction unconditionally: `coNL`
is the complement class of `NL`, so complementing both sides of one inclusion produces the other.
Only one direction therefore has to be proved by inductive counting — see `NLSubsetCoNL`.

## Main results

- `coNL_subset_NL_of_NL_subset_coNL`, `NL_subset_coNL_of_coNL_subset_NL` — the two directions are
  equivalent
- `NL_eq_coNL_of_NL_subset_coNL` — either one settles `NL = coNL`
-/

@[expose] public section

namespace Complexity

/-- **`coNL ⊆ NL`** (Immerman–Szelepcsényi). -/
def CoNLSubsetNL : Prop := coNL ⊆ NL

/-- One inclusion gives the other: complementing `Lᶜ ∈ NL` turns membership in `coNL` into
membership in `NL`.
@isnad1 id=le.1h0v.s3.c0a211b32221 from=translated src=- shape=adadd779 vocab=60a9f3e9
-/
theorem coNL_subset_NL_of_NL_subset_coNL (h : NL ⊆ coNL) : coNL ⊆ NL := by
  intro L hL
  have h₁ : Lᶜ ∈ NL := hL
  have h₂ : (Lᶜ)ᶜ ∈ NL := h h₁
  rwa [compl_compl] at h₂

/-- The mirror implication.
@isnad1 id=le.1h0v.s3.65221167c5f6 from=translated src=- shape=adadd779 vocab=60a9f3e9
-/
theorem NL_subset_coNL_of_coNL_subset_NL (h : coNL ⊆ NL) : NL ⊆ coNL := by
  intro L hL
  have h₁ : Lᶜ ∈ coNL := by
    show (Lᶜ)ᶜ ∈ NL
    rwa [compl_compl]
  exact h h₁

/-- Either inclusion settles the equality.
@isnad1 id=eq.1h0v.s3.33b155977915 from=translated src=- shape=0ad2a4e7 vocab=60a9f3e9
-/
theorem NL_eq_coNL_of_NL_subset_coNL (h : NL ⊆ coNL) : NL = coNL :=
  subset_antisymm h (coNL_subset_NL_of_NL_subset_coNL h)

end Complexity
