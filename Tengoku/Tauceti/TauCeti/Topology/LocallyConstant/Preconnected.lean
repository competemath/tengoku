/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# Locally constant functions on a preconnected set

A function that is locally constant along a preconnected set takes the same value everywhere on
it. Mathlib's `IsLocallyConstant.apply_eq_of_preconnectedSpace` says this for a locally constant
function on a preconnected *space*; the statement below is the relative form, for a preconnected
subset `s` of an ambient space, with local constancy expressed by the `𝓝[s]` neighbourhood filter
rather than by passing to the subtype.

## Main declarations

* `IsPreconnected.apply_eq_of_eventually_eq`: a function whose value is locally constant along a
  preconnected set is constant along it.

The example at the end of the file spells the statement out on the interval `[0, 1] ⊆ ℝ`, where it
says that a map into a discrete space continuous on `[0, 1]` cannot take two different values
there. That is the obstruction to extending a discrete-valued map off a closed subspace of a
space that is not totally disconnected.
-/

public section

open Filter Topology

namespace IsPreconnected

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- A function that is locally constant along a preconnected set is constant along it.

This is `IsLocallyConstant.apply_eq_of_preconnectedSpace` transported to the subspace `s`. -/
theorem apply_eq_of_eventually_eq {Y : Type*} {f : X → Y} (hs : IsPreconnected s)
    (hf : ∀ t ∈ s, ∀ᶠ u in 𝓝[s] t, f u = f t) {a b : X} (ha : a ∈ s) (hb : b ∈ s) :
    f a = f b := by
  have hlc : IsLocallyConstant fun x : s => f x.1 := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨t, ht⟩
    rw [nhds_subtype_eq_comap_nhdsWithin]
    exact Filter.Eventually.comap ((hf t ht).mono fun _ hu => hu) _
  have : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  exact hlc.apply_eq_of_preconnectedSpace ⟨a, ha⟩ ⟨b, hb⟩

end IsPreconnected
