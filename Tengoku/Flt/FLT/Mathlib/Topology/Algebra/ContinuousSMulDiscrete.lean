/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Tengoku

/-!
# Continuous actions on discrete modules

The typeclass `ContinuousSMulDiscrete G M`, expressing that a `G`-action on
a (potentially untopologized) `M` is *discretely continuous*: every stabiliser
is open. Equivalent to `ContinuousSMul` once `M` is given the discrete topology.

Material destined for Mathlib.
-/

@[expose] public section

variable {G M : Type*} [TopologicalSpace G] [SMul G M]

/--
`ContinuousSMulDiscrete G M` means that the action `G × M → M` is continuous
when `M` is given the discrete topology (See `continuousSMulDiscrete_iff`).

This class is especially useful when `M` already has another topology and we cannot easily put the
discrete topology on it.
-/
class ContinuousSMulDiscrete (G M : Type*) [TopologicalSpace G] [SMul G M] : Prop where
  isOpen_smul_eq (G) (x y : M) : IsOpen { g : G | g • x = y }

/--
@isnad1 id=iff.0h2v.s4.038812687410 from=translated src=- shape=a847105d vocab=ac791371
-/
lemma continuousSMulDiscrete_iff [TopologicalSpace M] [DiscreteTopology M] :
    ContinuousSMulDiscrete G M ↔ ContinuousSMul G M := by
  refine ⟨fun H ↦ ⟨continuous_discrete_rng.mpr fun y ↦ ?_⟩, fun H ↦ ⟨fun x y ↦ ?_⟩⟩
  · convert_to IsOpen (⋃ x, { g : G | g • x = y } ×ˢ {x})
    · ext; simp
    · exact isOpen_iUnion fun _ ↦
        .prod (ContinuousSMulDiscrete.isOpen_smul_eq _ _ _) (isOpen_discrete _)
  · exact ((isOpen_discrete {y}).preimage continuous_smul).preimage (Continuous.prodMk_left x)

instance (priority := low) [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMulDiscrete G M] : ContinuousSMul G M := by
  rwa [← continuousSMulDiscrete_iff]

/--
@isnad1 id=continuo.0h2v.s4.7dfd1f2d2138 from=translated src=- shape=2e4fa8a7 vocab=ac791371
-/
lemma ContinuousSMulDiscrete.of_continuousSMul [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul G M] : ContinuousSMulDiscrete G M := by
  rwa [continuousSMulDiscrete_iff]

/--
@isnad1 id=iff.0h2v.s6.c44bcbd3ede6 from=translated src=- shape=eb738357 vocab=06487091
-/
lemma continuousSMulDiscrete_iff_isOpen_stabilizer {G M : Type*} [TopologicalSpace G]
    [Group G] [ContinuousMul G] [MulAction G M] :
    ContinuousSMulDiscrete G M ↔ ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G) := by
  refine ⟨fun H x ↦ ContinuousSMulDiscrete.isOpen_smul_eq _ _ _, fun H ↦ ⟨fun x y ↦ ?_⟩⟩
  obtain h | ⟨g, rfl⟩ := Set.eq_empty_or_nonempty {g : G | g • x = y}
  · exact h ▸ isOpen_empty
  · convert (H x).preimage (Homeomorph.mulLeft g⁻¹).continuous using 1
    ext g'
    simp [mul_smul, inv_smul_eq_iff]

/--
@isnad1 id=isopen.0h3v.s5.74c3a66f0b76 from=translated src=- shape=1a5d7708 vocab=3e554310
-/
lemma ContinuousSMulDiscrete.isOpen_stabilizer (G : Type*) {M : Type*} [TopologicalSpace G]
    [Group G] [MulAction G M] [ContinuousSMulDiscrete G M] (x : M) :
      IsOpen (MulAction.stabilizer G x : Set G) := ContinuousSMulDiscrete.isOpen_smul_eq _ _ _
