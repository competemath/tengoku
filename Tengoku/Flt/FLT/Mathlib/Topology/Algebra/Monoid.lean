/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kevin Buzzard
-/
module

public import Tengoku

/-!
# Monoid

Material destined for Mathlib.
-/

@[expose] public section

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [ContinuousMul G]
-- TODO: `ContinuousMulConst` would be enough but it doesn't exist, and `ContinuousConstSMul Gᵐᵒᵖ G`
-- should work but doesn't

section induced

variable {R : Type*} [τR : TopologicalSpace R]
variable {A : Type*} [SMul R A]
variable {S : Type*} [τS : TopologicalSpace S] {f : S → R} (hf : Continuous f)
variable {B : Type*} [SMul S B]

open Topology

-- note: use convert not exact to ensure typeclass inference doesn't try to find topology on B
/--
@isnad1 id=continuo.1h6v.s6.b7d4621f3bc9 from=translated src=- shape=2bb76fb6 vocab=1780a2d4
-/
@[to_additive]
theorem induced_continuous_smul [τA : TopologicalSpace A] [ContinuousSMul R A] (g : B →ₑ[f] A)
    (hf : Continuous f) : @ContinuousSMul S B _ _ (TopologicalSpace.induced g τA) := by
  convert IsInducing.continuousSMul (IsInducing.induced g) hf (fun {c} {x} ↦ map_smulₛₗ g c x)

/--
@isnad1 id=continuo.0h3v.s6.555d3c489df6 from=translated src=- shape=0bbc04e2 vocab=4e680c3a
-/
@[to_additive]
theorem induced_continuous_mul [CommMonoid A] [τA : TopologicalSpace A] [ContinuousMul A]
    [CommMonoid B] (h : B →* A) :
    @ContinuousMul B (TopologicalSpace.induced h τA) _ := by
  convert (IsInducing.induced h).continuousMul h

end induced
