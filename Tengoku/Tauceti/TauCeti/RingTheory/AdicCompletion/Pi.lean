/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# Adic completeness of finite products

For an ideal `I` of a commutative ring `R` and a family of `R`-modules `M i`, the product `∀ i, M i`
is `I`-adically Hausdorff as soon as every factor is. If the family is finite, the analogous result
holds for adic precompleteness and completeness. In particular a finite free module `Fin n → R`
over an `I`-adically complete ring is `I`-adically complete, which is what the complete Nakayama
lemma (`surjective_of_mkQ_comp_surjective`) requires of the source of a map out of a finite free
module.

## Main results

* `AdicCompletion.pi_of`: the product of the completions of the factors receives the canonical
  map from the product as the product of the canonical maps.
* `IsHausdorff.pi`: adic Hausdorffness passes to products.
* `IsPrecomplete.pi`, `IsAdicComplete.pi`: adic precompleteness and completeness pass to finite
  products.
-/

public section

open AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R) {ι : Type*} (M : ι → Type*)
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The canonical map from a product to its adic completion, followed by the comparison map
`AdicCompletion.pi` to the product of the completions, is the product of the canonical maps of the
factors. -/
@[simp]
theorem AdicCompletion.pi_of (x : ∀ i, M i) (j : ι) :
    AdicCompletion.pi I M (of I (∀ i, M i) x) j = of I (M j) (x j) := by
  simp [AdicCompletion.pi, map_of]
