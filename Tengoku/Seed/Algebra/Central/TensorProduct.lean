/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Central.Basic
public import Tengoku.Seed.RingTheory.Flat.Basic
public import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace

/-!

# Lemmas about tensor products of central algebras

In this file we prove for algebras `B` and `C` over a field `K` that if `B ⊗[K] C` is a central
algebra and `B, C` nontrivial, then both `B` and `C` are central algebras.

## Main Results

- `Algebra.IsCentral.left_of_tensor_of_field`: If `B` `C` are `K`-algebras where `K` is a field,
  `C` is nontrivial and `B ⊗[K] C` is a central algebra over `K`, then `B` is a
  central algebra over `K`.
- `Algebra.IsCentral.right_of_tensor_of_field`: If `B` `C` are `K`-algebras where `K` is a field,
  `B` is nontrivial and `B ⊗[K] C` is a central algebra over `K`, then `C` is a
  central algebra over `K`.

## Tags
Central Algebras, Central Simple Algebras, Noncommutative Algebra
-/

public section

universe u v

open TensorProduct

variable (K B C : Type*) [CommSemiring K] [Semiring B] [Semiring C] [Algebra K B] [Algebra K C]

/--
@isnad1 id=le.0h3v.s8.bc8fece47304 from=seed src=0 shape=30862db0 vocab=ecbb1a0e
-/
lemma Algebra.TensorProduct.includeLeft_map_center_le :
    (Subalgebra.center K B).map includeLeft ≤ Subalgebra.center K (B ⊗[K] C) := by
  intro x hx
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨b, hb0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b' c => simp [hb0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

/--
@isnad1 id=le.0h3v.s8.9ab7f5b8f04c from=seed src=0 shape=df0495be vocab=bf8c174f
-/
lemma Algebra.TensorProduct.includeRight_map_center_le :
    (Subalgebra.center K C).map includeRight ≤ Subalgebra.center K (B ⊗[K] C) := fun x hx ↦ by
  simp only [Subalgebra.mem_map, Subalgebra.mem_center_iff] at hx ⊢
  obtain ⟨c, hc0, rfl⟩ := hx
  intro bc
  induction bc using TensorProduct.induction_on with
  | zero => simp
  | tmul b c' => simp [hc0]
  | add _ _ _ _ => simp_all [add_mul, mul_add]

namespace Algebra.IsCentral

open Algebra.TensorProduct in
/--
@isnad1 id=iscentra.1h3v.s7.bbc1cdd98016 from=seed src=0 shape=d02428b7 vocab=a73f9764
-/
lemma left_of_tensor (inj : Function.Injective (algebraMap K C)) [Module.Flat K B]
    [hbc : Algebra.IsCentral K (B ⊗[K] C)] : IsCentral K B where
  out := (Subalgebra.map_le.mp ((includeLeft_map_center_le K B C).trans hbc.1)).trans
    fun _ ⟨k, hk⟩ ↦ ⟨k, includeLeft_injective (S := K) inj hk⟩

/--
@isnad1 id=iscentra.1h3v.s7.6114a59de753 from=seed src=0 shape=349fd256 vocab=a73f9764
-/
lemma right_of_tensor (inj : Function.Injective (algebraMap K B)) [Module.Flat K C]
    [Algebra.IsCentral K (B ⊗[K] C)] : IsCentral K C :=
  have : IsCentral K (C ⊗[K] B) := IsCentral.of_algEquiv K _ _ <| Algebra.TensorProduct.comm _ _ _
  left_of_tensor K C B inj

/-- Let `B` and `C` be two algebras over a field `K`, if `B ⊗[K] C` is central and `C` is
  non-trivial, then `B` is central.
@isnad1 id=iscentra.0h3v.s7.db93d38ed5c8 from=seed src=0 shape=d1f6c79e vocab=93b58442
-/
lemma left_of_tensor_of_field (K B C : Type*) [Field K] [Ring B] [Ring C] [Nontrivial C]
    [Algebra K B] [Algebra K C] [IsCentral K (B ⊗[K] C)] : IsCentral K B :=
  left_of_tensor K B C <| FaithfulSMul.algebraMap_injective K C

/-- Let `B` and `C` be two algebras over a field `K`, if `B ⊗[K] C` is central and `B` is
  non-trivial, then `C` is central.
@isnad1 id=iscentra.0h3v.s7.7f2b09ac84a6 from=seed src=0 shape=31d2d4ac vocab=93b58442
-/
lemma right_of_tensor_of_field (K B C : Type*) [Field K] [Ring B] [Ring C] [Nontrivial B]
    [Algebra K B] [Algebra K C] [IsCentral K (B ⊗[K] C)] : IsCentral K C :=
  right_of_tensor K B C <| FaithfulSMul.algebraMap_injective K B


end Algebra.IsCentral
