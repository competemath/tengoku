/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Tengoku

/-!
# Properties of centers and centralizers

This file contains theorems about the center and centralizer of a subalgebra.

## Main results

Let `R` be a commutative ring and `A` and `B` two `R`-algebras.
- `Subalgebra.centralizer_sup`: if `S` and `T` are subalgebras of `A`, then the centralizer of
  `S ⊔ T` is the intersection of the centralizer of `S` and the centralizer of `T`.
- `Subalgebra.centralizer_range_includeLeft_eq_center_tensorProduct`: if `B` is free as a module,
  then the centralizer of `A` in `A ⊗ B` is `C(A) ⊗ B` where `C(A)` is the center of `A`.
- `Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct`: if `A` is free as a module,
  then the centralizer of `B` in `A ⊗ B` is `A ⊗ C(B)` where `C(B)` is the center of `B`.
-/

@[expose] public section

namespace Subalgebra

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable {A : Type*} [Semiring A] [Algebra R A]

lemma centralizer_sup (S T : Subalgebra R A) :
    centralizer R ((S ⊔ T : Subalgebra R A) : Set A) = centralizer R S ⊓ centralizer R T := by
  ext x
  simp only [Subalgebra.mem_centralizer_iff, SetLike.mem_coe, Algebra.mem_inf]
  constructor
  · intro h
    exact ⟨fun g hg => h g <| (le_sup_left : S ≤ S ⊔ T) hg,
      fun g hg => h g <| (le_sup_right : T ≤ S ⊔ T) hg⟩
  · rintro ⟨h1, h2⟩ g hg
    induction hg using Algebra.adjoin_induction with
    | mem y hy => exact hy.recOn (fun hy => h1 y hy) (fun hy => h2 y hy)
    | algebraMap r => exact Algebra.commutes r x
    | add _ _ _ _ h h' => simp [add_mul, h, h', mul_add]
    | mul _ _ _ _ h h' => rw [mul_assoc, h', ← mul_assoc, h, mul_assoc]

end CommSemiring

section Free

variable (R : Type*) [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable (B : Type*) [Semiring B] [Algebra R B]

open Finsupp TensorProduct

end Free

end Subalgebra
